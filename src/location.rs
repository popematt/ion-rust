use crate::Span;
use std::cell::RefCell;
use std::rc::Rc;

/// Represents the source location (row, column) of this element in the original Ion text.
///
/// The source location metadata is primarily intended for error reporting and debugging purposes,
/// helping applications provide meaningful feedback to users about the source of issues.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Default)]
pub struct SourceLocation {
    /// A 1-based row and column pair.
    /// INVARIANT: both components must be `0` or both must be non-zero.
    location: (usize, usize),
}

impl SourceLocation {
    /// Constructs a new SourceLocation. If either of `row` or `column` is `0`, returns an instance
    /// with no row/column value (i.e. both row and column are zero). This maintains the invariant
    /// that the location field must be `(0, 0)` or must have two non-zero values.
    pub(crate) fn new(row: usize, column: usize) -> SourceLocation {
        if row == 0 || column == 0 {
            return Self::empty();
        }
        Self {
            location: (row, column),
        }
    }

    /// Constructs a new `SourceLocation` instance that has no row/column available.
    pub(crate) fn empty() -> SourceLocation {
        Self { location: (0, 0) }
    }

    /// If this `SourceLocation` instance has row-column information, returns a tuple containing
    /// the 1-based row and column numbers. Otherwise, returns [`None`].
    pub fn row_column(&self) -> Option<(usize, usize)> {
        match self.location {
            (0, 0) => None,
            other => Some(other),
        }
    }

    /// If this `SourceLocation` instance has row-column information, returns the 1-based row number.
    /// Otherwise, returns [`None`].
    pub fn row(&self) -> Option<usize> {
        match self.location {
            (0, 0) => None,
            (row, _) => Some(row),
        }
    }

    /// If this `SourceLocation` instance has row-column information, returns the 1-based column number.
    /// Otherwise, returns [`None`].
    pub fn column(&self) -> Option<usize> {
        match self.location {
            (0, 0) => None,
            (_, col) => Some(col),
        }
    }
}

#[cfg(test)]
mod source_location_tests {
    use crate::location::SourceLocation;
    #[test]
    fn empty_source_location() {
        let location = SourceLocation::empty();
        assert_eq!(None, location.row_column());
        assert_eq!(None, location.row());
        assert_eq!(None, location.column());
    }

    #[test]
    fn non_empty_source_location() {
        let location = SourceLocation::new(2, 3);
        assert_eq!(Some((2, 3)), location.row_column());
        assert_eq!(Some(2), location.row());
        assert_eq!(Some(3), location.column());
    }
}

/// Encapsulates location tracking state and functionality.
///
/// This struct is cheap to clone because all of its state is behind a reference-counted pointer.
#[derive(Debug, Clone)]
pub(crate) struct SourceLocationState {
    /// A non-empty vec containing the offset of the start of each row.
    /// The first row always starts at offset 0.
    row_start_offsets: Rc<RefCell<Vec<usize>>>,
}
impl SourceLocationState {
    pub fn new() -> Self {
        Self {
            row_start_offsets: Rc::from(RefCell::new(vec![0])),
        }
    }

    /// Updates the location tracking state from the given source data.
    pub fn update_from_source<T: AsRef<[u8]>>(&mut self, stream_offset: usize, data: T) {
        let data = data.as_ref();
        if !data.is_empty() {
            let newlines = memchr::memchr_iter(b'\n', data);
            self.row_start_offsets
                .borrow_mut()
                .extend(newlines.map(|it| it + stream_offset + 1));
        }
    }

    pub fn calculate_location_for_span(&self, span: Span<'_>) -> SourceLocation {
        let range = span.range();
        let (row, row_start_offset) = self
            .row_start_offsets
            .borrow()
            .iter()
            .copied()
            .enumerate()
            .rfind(|&(_, newline_offset)| newline_offset <= range.start)
            // Always safe to unwrap because of the invariant that `newlines` is never empty.
            .unwrap();
        let column = range.start - row_start_offset;
        // Both of these are 0-based counts, and must be incremented to be 1-based row/column
        SourceLocation::new(row + 1, column + 1)
    }
}
