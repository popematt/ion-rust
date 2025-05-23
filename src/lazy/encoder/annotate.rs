use crate::lazy::encoder::annotation_seq::AnnotationSeq;
use crate::lazy::encoder::value_writer::{AnnotatableWriter, ValueWriter};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::IonResult;

/// Associates a value to serialize with a sequence of annotations.
pub struct Annotated<'a, T: ?Sized, A: 'a> {
    value: &'a T,
    annotations: A,
}

/// Provides implementors with an extension method ([`annotated_with`](Annotatable::annotated_with))
/// that allows them to be serialized with an associated sequence of annotations.
pub trait Annotatable {
    /// Pairs a reference to the provided value with a slice containing annotations.
    ///
    /// ```
    ///# use ion_rs::IonResult;
    ///# #[cfg(feature = "experimental-reader-writer")]
    ///# fn main() -> IonResult<()> {
    /// use ion_rs::{Annotatable, Element, IonData, Writer, v1_0::Text};
    ///
    /// let mut buffer = vec![];
    /// let mut writer = Writer::new(Text, &mut buffer)?;
    ///
    /// writer.write(42_usize.annotated_with(["foo", "bar", "baz"]))?.flush()?;
    ///
    /// let expected = Element::read_one("foo::bar::baz::42")?;
    /// let actual = Element::read_one(&buffer)?;
    ///
    /// assert!(IonData::eq(&expected, &actual));
    ///# Ok(())
    ///# }
    ///# #[cfg(not(feature = "experimental-reader-writer"))]
    ///# fn main() -> IonResult<()> { Ok(()) }
    /// ```
    #[cfg_attr(not(feature = "experimental-reader-writer"), allow(dead_code))]
    fn annotated_with<'a, A: 'a>(&'a self, annotations: A) -> Annotated<'a, Self, A>
    where
        &'a A: AnnotationSeq<'a>;
}

// Any Rust value that can be serialized as an Ion value can call `annotate`.
impl<T> Annotatable for T
where
    T: ?Sized + WriteAsIon,
{
    fn annotated_with<'a, A: 'a>(&'a self, annotations: A) -> Annotated<'a, Self, A>
    where
        &'a A: AnnotationSeq<'a>,
    {
        Annotated {
            value: self,
            annotations,
        }
    }
}

// The `Annotated` struct implements `WriteAsIon` by serializing its sequence of annotations
// and then invoking the inner value's implementation of `WriteAsIon`.
impl<'annotations, T, A: 'annotations> WriteAsIon for Annotated<'annotations, T, A>
where
    for<'x> &'x A: AnnotationSeq<'x>,
    T: WriteAsIon,
{
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        let value_writer = <V as AnnotatableWriter>::with_annotations(writer, &self.annotations)?;
        self.value.write_as_ion(value_writer)
    }
}
