use std::fmt::{Display, Formatter};
use std::ops::Range;
use crate::result::Position;

#[derive(PartialEq, Debug, Clone)]
pub struct ElementPosition {
    // Corresponds to the position of each annotation. Not including the '::' if text.
    pub(crate) annotations: Vec<Span>,
    // May include internal comments or whitespace.
    pub(crate) value: Span,
}

#[derive(PartialEq, Debug, Clone, Default)]
pub(crate) struct ElementPositionBuilder {
    pub(crate) annotations: Vec<Span>,
    pub(crate) value_start_inclusive: Option<Position>,
    pub(crate) value_end_inclusive: Option<Position>,
}
impl ElementPositionBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_annotation(mut self, span: Span) -> Self {
        self.annotations.push(span);
        self
    }

    pub fn with_value_start(mut self, pos: Position) -> Self {
        self.value_start_inclusive.replace(pos);
        self
    }

    pub fn with_value_end(mut self, pos: Position) -> Self {
        self.value_end_inclusive.replace(pos);
        self
    }

    pub fn try_build(self) -> Result<ElementPosition, String> {
        Ok(ElementPosition {
            annotations: self.annotations,
            value: Span::new(
                self.value_start_inclusive.ok_or("No value start position")?,
                self.value_end_inclusive.ok_or("No value end position")?,
            )
        })
    }

    pub fn build(self) -> ElementPosition {
        ElementPosition {
            annotations: self.annotations,
            value: Span::new(
                self.value_start_inclusive.unwrap(),
                self.value_end_inclusive.unwrap(),
            )
        }
    }
}


#[derive(PartialEq, Debug, Clone)]
pub struct Span {
    pub from_inclusive: Position,
    pub to_inclusive: Position,
}
impl Span {
    pub(crate) fn new(from_inclusive: Position, to_inclusive: Position) -> Self {
        Span { from_inclusive, to_inclusive }
    }
}
impl Display for Span {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.from_inclusive {
            Position { byte_offset, line_column: None } => {
                f.write_fmt(format_args!("byte {byte_offset}"))?;
            },
            Position { byte_offset, line_column: Some ((line, column))} => {
                f.write_fmt(format_args!("Line: {line}, Column: {column}; (byte {byte_offset})"))?;
            },
        }
        f.write_str(" to ")?;
        match self.to_inclusive {
            Position { byte_offset, line_column: None } => {
                f.write_fmt(format_args!("byte {byte_offset}"))?;
            },
            Position { byte_offset, line_column: Some ((line, column))} => {
                f.write_fmt(format_args!("Line: {line}, Column: {column}; (byte {byte_offset})"))?;
            },
        }
        Ok(())
    }
}

impl From<Range<usize>> for Span {
    fn from(value: Range<usize>) -> Self {
        Span {
            from_inclusive: Position { byte_offset: value.start, line_column: None },
            to_inclusive: Position { byte_offset: value.end - 1, line_column: None }
        }
    }
}
