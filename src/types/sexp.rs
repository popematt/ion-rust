use crate::element::builders::SequenceBuilder;
use crate::element::iterators::SequenceIterator;
use crate::ion_data::{IonDataHash, IonEq};
use crate::text::text_formatter::FmtValueFormatter;
use crate::{Element, Sequence};
use delegate::delegate;
use std::fmt::{Display, Formatter};
use std::hash::Hasher;

/// An in-memory representation of an Ion s-expression
/// ```
/// use ion_rs::{Element, ion_sexp};
/// # use ion_rs::IonResult;
/// # fn main() -> IonResult<()> {
/// let sexp = ion_sexp!(1 2 3);
/// assert_eq!(sexp.len(), 3);
/// assert_eq!(sexp.get(1), Some(&Element::int(2)));
/// # Ok(())
/// # }
/// ```
/// To build a `SExp` incrementally, see [SequenceBuilder].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SExp(pub Sequence);

impl SExp {
    pub fn new(elements: impl Into<Sequence>) -> Self {
        SExp(elements.into())
    }
}

impl SExp {
    delegate! {
        to self.0 {
            pub fn clone_builder(&self) -> SequenceBuilder;
            pub fn elements(&self) -> SequenceIterator<'_>;
            pub fn get(&self, index: usize) -> Option<&Element>;
            pub fn len(&self) -> usize;
            pub fn is_empty(&self) -> bool;
        }
    }
}

impl IonEq for SExp {
    fn ion_eq(&self, other: &Self) -> bool {
        // The inner `Sequence` of both Lists are IonEq
        self.0.ion_eq(&other.0)
    }
}

impl IonDataHash for SExp {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        self.0.ion_data_hash(state)
    }
}

impl AsRef<Sequence> for SExp {
    fn as_ref(&self) -> &Sequence {
        &self.0
    }
}

impl AsRef<[Element]> for SExp {
    fn as_ref(&self) -> &[Element] {
        self.0.as_ref()
    }
}

// Allows `for element in &sexp {...}` syntax
impl<'a> IntoIterator for &'a SExp {
    type Item = &'a Element;
    type IntoIter = SequenceIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements()
    }
}

impl Display for SExp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut ivf = FmtValueFormatter { output: f };
        ivf.format_sexp(self).map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}

impl From<Sequence> for SExp {
    fn from(sequence: Sequence) -> Self {
        SExp(sequence)
    }
}

impl From<Vec<Element>> for SExp {
    fn from(elements: Vec<Element>) -> Self {
        Self(elements.into())
    }
}

impl FromIterator<Element> for SExp {
    fn from_iter<T: IntoIterator<Item = Element>>(iter: T) -> Self {
        Vec::from_iter(iter).into()
    }
}

impl From<SExp> for Sequence {
    fn from(value: SExp) -> Self {
        value.0
    }
}

#[cfg(test)]
mod tests {
    use crate::{ion_sexp, Element, IonResult, SExp};

    #[test]
    fn for_element_in_sexp() -> IonResult<()> {
        // Simple example to exercise SExp's implementation of IntoIterator
        let sexp = ion_sexp!(1 2 3);
        let mut sum = 0;
        for element in &sexp {
            sum += element.expect_int()?.expect_i64()?;
        }
        assert_eq!(sum, 6i64);
        Ok(())
    }

    #[test]
    fn sexp_from_vec() -> IonResult<()> {
        let elements = vec![Element::int(1), Element::int(2), Element::int(3)];
        let actual: SExp = elements.into();
        let expected = ion_sexp!(1 2 3);
        assert_eq!(actual, expected);
        Ok(())
    }

    #[test]
    fn sexp_from_iter() -> IonResult<()> {
        let elements = vec![Element::int(1), Element::int(2), Element::int(3)];
        let actual: SExp = elements.into_iter().collect();
        let expected = ion_sexp!(1 2 3);
        assert_eq!(actual, expected);
        Ok(())
    }
}
