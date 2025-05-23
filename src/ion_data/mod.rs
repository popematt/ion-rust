mod ion_data_hash;
mod ion_eq;
mod ion_ord;

use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::ops::Deref;

use crate::{Encoding, IonResult, ValueWriter, WriteAsIon, WriteConfig};
pub(crate) use ion_data_hash::{ion_data_hash_bool, ion_data_hash_f64, IonDataHash};
pub(crate) use ion_eq::{ion_eq_bool, ion_eq_f64, IonEq};
pub(crate) use ion_ord::{ion_cmp_bool, ion_cmp_f64, IonDataOrd};

/// A wrapper for lifting Ion compatible data into using Ion-oriented comparisons (versus the Rust
/// value semantics). This enables the default semantics to be what a Rust user expects for native
/// values, but allows a user to opt-in to Ion's structural equivalence/order.
///
/// Equivalence with respect to Ion values means that if two Ion values, `X` and `Y`, are equivalent,
/// they represent the same data and can be substituted for the other without loss of information.
///
/// Some types, such as [`Element`](crate::Element) and [`Value`](crate::element::Value) cannot be
/// used as the key of a map because they adhere to Rust value semantics—these types cannot implement
/// [`Eq`] because they include `NaN` as a possible value.
///
/// For use cases that are concerned with preserving the original Ion data, it is necessary to use
/// Ion value equivalence. Many common use cases, such as writing unit tests for code that produces
/// Ion, can be handled with [`IonData::eq()`].
///
/// For other use cases, such as using Ion data as the key of a map or passing Ion data to an
/// algorithm that depends on [`Eq`], you can lift values using [`IonData::from()`].
///
/// Generally, anything that is treated as Ion data (e.g., [`Element`](crate::Element) and
/// [`Value`](crate::element::Value)), can be converted to [`IonData`].
///
/// [`Hash`] and [`Ord`] are not guaranteed to be implemented for all [`IonData`], but when they are,
/// they are required to be consistent with Ion structural equality (and [`Eq`]).
///
/// __WARNING__—The Ion specification does _not_ define a total ordering over all Ion values. Do
/// not depend on getting any particular result from [Ord]. Use it only as an opaque total ordering
/// over all [IonData]. _The algorithm used for [Ord] may change between versions._
///
/// __WARNING__—The hashing algorithm is _not_ the same as the
/// [Ion Hash Algorithm](https://amazon-ion.github.io/ion-hash). _The algorithm used for [Hash] may change between versions._
#[derive(Debug, Clone)]
pub struct IonData<T>(T);

impl<T: IonEq> IonData<T> {
    /// Checks if two values are equal according to Ion's structural equivalence.
    pub fn eq<R: Deref<Target = T>>(a: R, b: R) -> bool {
        T::ion_eq(a.deref(), b.deref())
    }

    /// Unwraps the value.
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T: IonEq> PartialEq for IonData<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.ion_eq(&other.0)
    }
}

impl<T: IonEq> Eq for IonData<T> {}

impl<T: IonEq> From<T> for IonData<T> {
    fn from(value: T) -> Self {
        IonData(value)
    }
}

impl<T: IonEq> AsRef<T> for IonData<T> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T: Display> Display for IonData<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl<T: IonEq + IonDataOrd> PartialOrd for IonData<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: IonEq + IonDataOrd> Ord for IonData<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        IonDataOrd::ion_cmp(&self.0, &other.0)
    }
}

impl<T: IonDataHash> Hash for IonData<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        IonDataHash::ion_data_hash(&self.0, state)
    }
}

impl<T: WriteAsIon> WriteAsIon for IonData<T> {
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        self.0.write_as_ion(writer)
    }

    fn encode_as<E: Encoding, C: Into<WriteConfig<E>>>(&self, config: C) -> IonResult<E::Output>
    where
        for<'a> &'a Self: WriteAsIon,
    {
        self.0.encode_as(config)
    }

    fn encode_to<E: Encoding, C: Into<WriteConfig<E>>, W: Write>(
        &self,
        config: C,
        output: W,
    ) -> IonResult<W>
    where
        for<'a> &'a Self: WriteAsIon,
    {
        self.0.encode_to(config, output)
    }
}

macro_rules! assert_ion_eq {
        ($left:expr, $right:expr $(, $($tt:tt)*)?) => {
            assert_eq!(
                $left,
                $right
                $(, $($tt)*)?
            )
        };
    }
pub(crate) use assert_ion_eq;

#[cfg(test)]
mod tests {
    use crate::ion_data::{IonDataHash, IonDataOrd, IonEq};
    use crate::lazy::encoding::TextEncoding_1_0;
    use crate::{Element, IonData, Symbol, WriteConfig};
    use rstest::*;
    use std::boxed::Box;
    use std::fmt::Debug;
    use std::hash::{DefaultHasher, Hash, Hasher};
    use std::pin::Pin;
    use std::rc::Rc;
    use std::sync::Arc;

    /// These tests exist primarily to ensure that we don't break any trait implementations
    /// needed to make this all work.
    #[rstest]
    #[case::value(|s| Element::read_one(s).unwrap().value().clone().into())]
    #[case::symbol(|s| Symbol::from(s).into())]
    #[case::element(|s| Element::read_one(s).unwrap().into() )]
    #[case::write_as_ion(|s| Element::read_one(Element::read_one(s).unwrap().encode_as(WriteConfig::<TextEncoding_1_0>::default()).unwrap()).unwrap().into() )]
    #[case::rc_element(|s| Rc::new(Element::read_one(s).unwrap()).into() )]
    #[case::vec_element(|s| Element::read_all(s).unwrap().into() )]
    #[case::rc_vec_element(|s| Rc::new(Element::read_all(s).unwrap()).into() )]
    #[case::box_pin_rc_vec_box_arc_element(|s| Box::new(Pin::new(Rc::new(vec![Box::new(Arc::new(Element::read_one(s).unwrap()))]))).into() )]
    fn can_wrap_data<T: IonEq + IonDataOrd + IonDataHash + Debug>(
        #[case] the_fn: impl Fn(&'static str) -> IonData<T>,
    ) {
        let id1: IonData<_> = the_fn("nan");
        let id2: IonData<_> = the_fn("nan");
        assert_eq!(id1, id2);
        let mut h1 = DefaultHasher::default();
        let mut h2 = DefaultHasher::default();
        id1.hash(&mut h1);
        id2.hash(&mut h2);
        assert_eq!(h1.finish(), h2.finish());

        let id1: IonData<_> = the_fn("1.00");
        let id2: IonData<_> = the_fn("1.0");
        assert_ne!(id1, id2); // Checks `Eq`
        assert!(id1 > id2); // Checks `Ord`
    }
}
