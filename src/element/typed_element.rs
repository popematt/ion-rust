use crate::element::iterators::ElementsIterator;
use crate::element::{Annotations, SExp, Sequence, Value};
use crate::element::{Bytes, Decimal, Int, Str, Struct, Symbol, Timestamp};
use crate::Element;
use crate::IonType;
use std::convert::{From, Infallible, TryFrom};
use std::fmt::{Debug, Display, Formatter};

#[derive(Debug)]
pub struct IonTypeCastError {
    target_type: &'static str,
    acceptable_value_variants: &'static str,
    actual: &'static str,
}
impl IonTypeCastError {
    pub(crate) fn new(
        target_type: &'static str,
        acceptable_value_variants: &'static str,
        actual: &'static str,
    ) -> Self {
        IonTypeCastError {
            target_type,
            acceptable_value_variants,
            actual,
        }
    }
}
impl Display for IonTypeCastError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let &IonTypeCastError {
            target_type,
            acceptable_value_variants,
            actual,
        } = self;
        f.write_fmt(format_args!("Unable to cast to {target_type}; requires {acceptable_value_variants} value, but was {actual} value."))
    }
}
// I don't know why there isn't a blanket `impl <T> From<Infallible> for T` since it's guaranteed
// to always be unreachable.
impl From<Infallible> for IonTypeCastError {
    fn from(_: Infallible) -> Self {
        unreachable!()
    }
}

// TODO: maybe find/make a macro for this:
trait EnumVariantName {
    fn variant_name(&self) -> &'static str;
}
impl EnumVariantName for Value {
    fn variant_name(&self) -> &'static str {
        match self {
            Value::Null(_) => "Null",
            Value::Bool(_) => "Bool",
            Value::Int(_) => "Int",
            Value::Float(_) => "Float",
            Value::Decimal(_) => "Decimal",
            Value::String(_) => "String",
            Value::Symbol(_) => "Symbol",
            Value::Blob(_) => "Blob",
            Value::Clob(_) => "Clob",
            Value::Timestamp(_) => "Timestamp",
            Value::List(_) => "List",
            Value::SExp(_) => "SExp",
            Value::Struct(_) => "Struct",
        }
    }
}

//////// 👇 Point of Interest 👇 \\\\\\\\
pub trait Annotated {
    fn annotations(&self) -> &Annotations;
    fn has_annotation(&self, annotation: &str) -> bool;
}

pub trait IonValue {
    fn value(&self) -> &Value;
    fn into_value(self) -> Value;
    fn ion_type(&self) -> IonType {
        self.value().ion_type()
    }
}

pub trait Components: Annotated + IonValue {
    type ValueType;
    /// Consumes this element and returns owned Annotations and ValueType
    fn into_components(self) -> (Annotations, Self::ValueType);
    /// Borrows the [Annotations] and [Self::ValueType] for this element
    fn components(&self) -> (&Annotations, &Self::ValueType);
}

macro_rules! components {
    // TODO: Clean up use of `ident` vs `ty`
    ($name:ident($($value_variant:ident),+), type ValueType = $value_type:ident) => {
        impl Components for $name {
            type ValueType = $value_type;

            fn into_components(self) -> (Annotations, Self::ValueType) {
                match self {
                    $(
                    $name { annotations, value: Value::$value_variant(v) } => (annotations, v.into()),
                    )+
                    _ => unreachable!(),
                }
            }

            fn components(&self) -> (&Annotations, &Self::ValueType) {
                match self {
                    $(
                    $name { annotations, value: Value::$value_variant(v) } => (annotations, v.into()),
                    )+
                    _ => unreachable!(),
                }
            }
        }
    };
}

macro_rules! typed_element {
    // TODO: Clean up use of `ident` vs `ty`
    ($name:ident$variants:tt : $($sup:ident),*$(; type ValueType = $value_type:ident)?) => {
        #[repr(C)]
        #[derive(Debug, Clone)]
        pub struct $name {
            annotations: Annotations,
            value: Value,
        }
        impl $name {
            pub(crate) fn new(annotations: Annotations, value: Value) -> Self {
                $name { annotations, value }
            }

            pub fn with_annotations(self, annotations: Annotations) -> Self {
                $name { annotations, value: self.value }
            }
        }
        impl Annotated for $name {
            fn has_annotation(&self, annotation: &str) -> bool {
                self.annotations
                    .iter()
                    .any(|a| a.text() == Some(annotation))
            }

            fn annotations(&self) -> &Annotations {
                &self.annotations
            }
        }
        impl IonValue for $name {
            fn value(&self) -> &Value {
                &self.value
            }

            fn into_value(self) -> Value {
                self.value
            }
        }
        impl Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                let mut ivf = crate::text::text_formatter::IonValueFormatter { output: f };
                ivf.format_annotations(&self.annotations)
                    .map_err(|_| std::fmt::Error)?;
                std::fmt::Display::fmt(&self.value, f)
            }
        }
        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                self.value == other.value && self.annotations == other.annotations
            }
        }
        impl Eq for $name {}

        // This implementation allows APIs that require an Into<___Element> to accept references to an existing
        // Element.
        impl<'a> From<&'a $name> for $name {
            fn from(element: &'a $name) -> Self {
                element.clone()
            }
        }
        $(components!($name$variants, type ValueType = $value_type);)?

        $(
        typed_element!(__super__, $sup, $name $variants);
        )*
    };
    (__super__, $sup:ident, $name:ident($($value_variant:ident),+)) => {
        // NOTE -- if it helps clean up the API, we could create our own Widen/Narrow traits to
        // use for casting instead of From and TryFrom.
        impl TryFrom<$sup> for $name {
            type Error = IonTypeCastError;

            fn try_from(element: $sup) -> Result<Self, Self::Error> {
                //////// 👇 Point of Interest 👇 \\\\\\\\
                // For narrowing conversions—since all XyzElement structures have the same memory
                // layout, we check that the Ion type invariant for the destination type would be
                // satisfied, and then we can safely transmute from XxxElement to YyyElement.
                match element.value() {
                    $(Value::$value_variant(_))|+ => Ok(unsafe { std::mem::transmute(element) }),
                    _ => return Err(IonTypeCastError::new(stringify!($name), stringify!($($value_variant), +), element.value().variant_name()))
                }
            }
        }
        impl TryFrom<&$sup> for &$name {
            type Error = IonTypeCastError;

            fn try_from(element: &$sup) -> Result<Self, Self::Error> {
                //////// 👇 Point of Interest 👇 \\\\\\\\
                // For narrowing conversions—since all XyzElement structures have the same memory
                // layout, we check that the Ion type invariant for the destination type would be
                // satisfied, and then we can safely cast the raw pointer to get a reference with a
                // different type than the original value
                if let $(Value::$value_variant(_))|+ = element.value() {
                    Ok(unsafe { & *(element as *const $sup as *const $name) })
                } else {
                    Err(IonTypeCastError::new(stringify!($name), stringify!($($value_variant), +), element.value().variant_name()))
                }
            }
        }
        //////// 👇 Point of Interest 👇 \\\\\\\\
        // For widening conversions—the Ion type invariant will always hold, so this is always safe.
        impl From<$name> for $sup {
            fn from(element: $name) -> Self {
                unsafe { std::mem::transmute(element) }
            }
        }
        impl From<&$name> for &$sup {
            fn from(value: &$name) -> Self {
                unsafe { & *(value as *const $name as *const $sup) }
            }
        }
    };
}

typed_element!(NullElement(Null): Element; type ValueType = IonType);
typed_element!(BoolElement(Bool): Element; type ValueType = bool);
typed_element!(IntElement(Int): Element, NumberElement; type ValueType = Int);
typed_element!(FloatElement(Float): Element, NumberElement; type ValueType = f64);
typed_element!(DecimalElement(Decimal): Element, NumberElement; type ValueType = Decimal);
typed_element!(StringElement(String): Element, TextElement; type ValueType = Str);
typed_element!(SymbolElement(Symbol): Element, TextElement; type ValueType = Symbol);
typed_element!(BlobElement(Blob): Element, LobElement; type ValueType = Bytes);
typed_element!(ClobElement(Clob): Element, LobElement; type ValueType = Bytes);
typed_element!(TimestampElement(Timestamp): Element; type ValueType = Timestamp);
typed_element!(ListElement(List): Element, SequenceElement; type ValueType = Sequence);
typed_element!(SExpElement(SExp): Element, SequenceElement; type ValueType = Sequence);
typed_element!(StructElement(Struct): Element; type ValueType = Struct);

typed_element!(TextElement(String, Symbol): Element); // TODO -- common representation for TextElement
typed_element!(LobElement(Blob, Clob): Element; type ValueType = Bytes);
typed_element!(SequenceElement(List, SExp): Element; type ValueType = Sequence);
// TODO -- do we actually want a NumberElement?
typed_element!(NumberElement(Int, Float, Decimal): Element); // TODO -- common number representation

//////// 👇 Point of Interest 👇 \\\\\\\\
// We can add additional impl outside of what is defined by the macro:
impl SExpElement {
    pub fn head(&self) -> Option<&Element> {
        if let Value::SExp(seq) = &self.value {
            seq.elements().next()
        } else {
            unreachable!()
        }
    }
}

//////// 👇 Point of Interest 👇 \\\\\\\\
// This `SequenceView` trait is automatically applied to everything that decomposes to Sequence.
impl<T: Components<ValueType = Sequence>> SequenceView for T where SequenceElement: From<T> {}
trait SequenceView: Components<ValueType = Sequence> + Sized
where
    SequenceElement: From<Self>,
{
    fn len(&self) -> usize {
        self.components().1.len()
    }
    fn is_empty(&self) -> bool {
        self.components().1.is_empty()
    }
    fn elements(&self) -> ElementsIterator {
        self.components().1.elements()
    }

    fn to_ion_list(self) -> ListElement {
        if self.ion_type() == IonType::List {
            SequenceElement::from(self)
                .try_into()
                .expect("This is infallible because we already checked the Ion type.")
        } else {
            let (annotations, sequence) = self.into_components();
            ListElement::new(annotations, Value::List(sequence))
        }
    }

    fn to_ion_sexp(self) -> SExpElement {
        if self.ion_type() == IonType::SExp {
            SequenceElement::from(self)
                .try_into()
                .expect("This is infallible because we already checked the Ion type.")
        } else {
            let (annotations, sequence) = self.into_components();
            SExpElement::new(annotations, Value::SExp(sequence))
        }
    }
}

#[test]
fn test_typed_element() -> Result<(), IonTypeCastError> {
    let element = Element::read_one("1.23e4").unwrap();

    //////// 👇 Point of Interest 👇 \\\\\\\\
    // We can have simultaneous references to the same object where the references have different types.
    let element_ref: &Element = &element;
    let number_ref: &NumberElement = (&element).try_into()?;
    let float_ref: &FloatElement = (&element).try_into()?;
    println!("{element_ref}, {number_ref}, {float_ref}");

    // Now we have a NumberElement
    let number_element: NumberElement = element.try_into()?;
    println!("{number_element}");

    // This will be an Err because the element is actually a float.
    println!("{:?}", <&IntElement>::try_from(&number_element));

    // This will be an Err because the element is actually a float, but it consumes the element.
    match IntElement::try_from(number_element) {
        Ok(_) => unreachable!(),
        Err(e) => println!("{e}"),
    }

    let element2 = Element::read_one("[1, 2, 3]").unwrap();

    // Casting to ListElement
    let list_element: ListElement = element2.try_into()?;
    println!("{list_element}");
    // Here we're using something from the SequenceView trait
    println!("Len: {}", list_element.len());
    // Conversion (rather than casting) to SExpElement
    let sexp_element = list_element.to_ion_sexp();
    println!("{sexp_element}");

    Ok(())
}
