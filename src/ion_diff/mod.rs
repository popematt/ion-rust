use crate::element::Value as IonValue;
use crate::element::{Element, IntoAnnotatedElement, IonSequence, List, SExp};
use crate::{ion_sexp, ion_struct, IonType, Symbol};
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::fmt;

// Seems to be working
// TODO: deal with duplicate field names
// TODO: deal with top-level streams

fn ion_diff(e1: &Element, e2: &Element) -> () {
    let mut d = Recorder::default();
    diff::<Element, _>(e1, e2, &mut d);

    for change in d.calls {
        let e: Element = change.into();
        if !e.has_annotation("unchanged") {
            println!("{}", e)
        }
    }
}


impl From<Key> for Element {
    fn from(value: Key) -> Self {
        match value {
            Key::Index(i) => Element::integer(i),
            Key::Symbol(s) => Element::symbol(s),
        }
    }
}

impl<'a> From<ChangeType<'a, Key, Element>> for Element {
    fn from(value: ChangeType<'a, Key, Element>) -> Self {
        match value {
            ChangeType::Removed(k, v) => {
                let mut kel = SExp::builder();
                for e in k {
                    kel = kel.push(e);
                }
                let s = ion_struct! {
                    "path": kel.build(),
                    "old": v.clone()
                };
                s.with_annotations(["removed"])
            }
            ChangeType::Added(k, v) => {
                let mut kel = SExp::builder();
                for e in k {
                    kel = kel.push(e);
                }
                let s = ion_struct! {
                    "path": kel.build(),
                    "new": v.clone()
                };
                s.with_annotations(["added"])
            }
            ChangeType::Unchanged(k, v) => {
                let mut kel = SExp::builder();
                for e in k {
                    kel = kel.push(e);
                }
                let s = ion_struct! {
                    "path": kel.build(),
                    "value": v.clone()
                };
                s.with_annotations(["unchanged"])
            }
            ChangeType::Modified(k, old, new) => {
                let mut kel = SExp::builder();
                for e in k {
                    kel = kel.push(e);
                }
                let s = ion_struct! {
                    "path": kel.build(),
                    "old": old.clone(),
                    "new": new.clone()
                };
                s.with_annotations(["modified"])
            }
            ChangeType::AnnotationsModified(k, old, new) => {
                let mut kel = SExp::builder();
                for e in k {
                    kel = kel.push(e);
                }
                let mut old_ann = List::builder();
                for e in &old {
                    old_ann = old_ann.push(e.clone());
                }
                let mut new_ann = List::builder();
                for e in &new {
                    new_ann = new_ann.push(e.clone());
                }
                let s = ion_struct! {
                    "path": kel.build(),
                    "old": Element::null(IonType::Null).with_annotations(old),
                    "new": Element::null(IonType::Null).with_annotations(new)
                };
                s.with_annotations(["annotations_modified"])
            }
        }
    }
}

impl Value for Element {
    type Key = Key;
    type Item = Element;

    fn items<'a>(&'a self) -> Option<Box<dyn Iterator<Item = (Self::Key, &'a Self::Item)> + 'a>> {
        match self.value() {
            IonValue::SExp(sexp) => Some(Box::new(
                sexp.elements().enumerate().map(|(k, v)| (Key::Index(k), v)),
            )),
            IonValue::List(list) => Some(Box::new(
                list.elements().enumerate().map(|(k, v)| (Key::Index(k), v)),
            )),
            IonValue::Struct(struct_) => Some(Box::new(
                struct_.fields().map(|(k, v)| (Key::Symbol(k.clone()), v)),
            )),
            _ => None,
        }
    }

    fn annotations<'a>(&'a self) -> Option<Box<dyn Iterator<Item=&'a Symbol> + 'a>> {
        Some(Box::new(self.annotations()))
    }
}

// impl <'b, T: Iterator<Item = &'b Element> + PartialEq + 'b> Value for T {
//     type Key = Key;
//     type Item = Element;
//
//     fn items<'a>(&'a self) -> Option<Box<dyn Iterator<Item=(Self::Key, &'a Self::Item)> + 'a>> {
//         let v = &self.enumerate().map(|(i, e)| (Key::Index(i), e));
//         Some(Box::new(v))
//     }
//
//     fn annotations<'a>(&'a self) -> Option<Box<dyn Iterator<Item=&'a Symbol> + 'a>> {
//         None
//     }
// }

#[test]
fn test_diff() {
    let e1 = Element::read_one(
        r#"
        type::{
  name: CustomerFieldTypes,
  fields: closed::{
    title: { valid_values: ["Dr.", "Mr.", "Mrs.", "Ms."] },
    firstName: string,
    middleName: string,
    lastName: string,
    suffix: { valid_values: ["Jr.", "Sr.", "PhD"] },
    preferredName: string,
    customerId: {
      one_of: [
        { type: string, codepoint_length: 18 },
        { type: int, valid_values: range::[100000, 999999] },
      ],
    },
    addresses: { type: list, element: Address },
    lastUpdated: { timestamp_precision: second },
  },
}
    "#,
    )
        .unwrap();

    let e2 = Element::read_one(
        r#"
type::{
  name: CustomerFieldTypes,
  fields: closed::{
    title: { valid_values: ["Dr.", "Mr.", "Mrs.", "Ms."] },
    firstName: string,
    middleName: $string,
    lastName: string,
    suffix: { valid_values: ["Jr.", "Sr.", "PhD"] },
    preferredName: string,
    customerId: {
      one_of: [
        { type: string, codepoint_length: 18 },
        { type: int, valid_values: range::[100000, 999999] },
        { type: blob, byte_length: 18 },
      ],
    },
    addresses: { type: list, element: Address },
    lastUpdated: { timestamp_precision: second },
    created: { timestamp_precision: second },
  },
}
    "#,
    )
        .unwrap();

    ion_diff(&e1, &e2);
}


/// A generic diff algorithm suitable for `Value` types as seen in serialization/deserialization
/// libraries.
///
/// Such types can represent any tree-like data structure, which will be traversed to find
/// *additions*, *removals*, *modifications* and even portions that did not change at all.
///
/// # Parameters
/// * `l` - the left Value
/// * `r` - the right Value
/// * `d` - a `Delegate` to receive information about changes between `l` and `r`
pub fn diff<'a, V, D>(l: &'a V, r: &'a V, d: &mut D)
    where
        V: Value<Item = V>,
        V::Key: Ord + Clone,
        D: Delegate<'a, V::Key, V>,
{
    match (l.items(), r.items()) {
        // two scalars, equal
        (None, None) if l == r => d.unchanged(l),
        // two scalars, different
        (None, None) => {
            match (l.annotations(), r.annotations()) {
                (Some(la), Some(ra)) => {
                    let r_ann: Vec<_> = ra.cloned().collect();
                    let l_ann: Vec<_> = la.cloned().collect();
                    if r_ann != l_ann {
                        d.annotations_modified(l_ann, r_ann);
                    }
                }
                (None, None) => {}
                _ => unreachable!("Whether a value could have annotations depends on its type")
            }
            d.modified(l, r)
        },
        // two objects, equal
        (Some(_), Some(_)) if l == r => d.unchanged(l),
        // object and scalar
        (Some(_), None) | (None, Some(_)) => d.modified(l, r),
        // two objects, different
        (Some(li), Some(ri)) => {
            let mut sl: BTreeSet<OrdByKey<_, _>> = BTreeSet::new();
            // let mut sl: Vec<OrdByKey<_, _>> = Vec::new();
            sl.extend(li.map(Into::into));
            let mut sr: BTreeSet<OrdByKey<_, _>> = BTreeSet::new();
            // let mut sr: Vec<OrdByKey<_, _>> = Vec::new();
            sr.extend(ri.map(Into::into));
            for k in sr.intersection(&sl) {
                let v1 = sl.get(k).expect("intersection to work");
                let v2 = sr.get(k).expect("intersection to work");
                d.push(&k.0);
                diff(v1.1, v2.1, d);
                d.pop();
            }
            for k in sr.difference(&sl) {
                d.added(&k.0, sr.get(k).expect("difference to work").1);
            }
            for k in sl.difference(&sr) {
                d.removed(&k.0, sl.get(k).expect("difference to work").1);
            }

            match (l.annotations(), r.annotations()) {
                (Some(la), Some(ra)) => {
                    let r_ann: Vec<_> = ra.cloned().collect();
                    let l_ann: Vec<_> = la.cloned().collect();
                    if r_ann != l_ann {
                        d.annotations_modified(l_ann, r_ann);
                    }
                }
                (None, None) => {}
                _ => unreachable!()
            }

        }
    }


}

struct OrdByKey<'a, K, V: 'a>(pub K, pub &'a V);

impl<'a, K, V> From<(K, &'a V)> for OrdByKey<'a, K, V> {
    fn from(src: (K, &'a V)) -> Self {
        OrdByKey(src.0, src.1)
    }
}

impl<'a, K, V> Eq for OrdByKey<'a, K, V> where K: Eq + PartialOrd {}

impl<'a, K, V> PartialEq for OrdByKey<'a, K, V>
    where
        K: PartialOrd,
{
    fn eq(&self, other: &OrdByKey<'a, K, V>) -> bool {
        self.0.eq(&other.0)
    }
}

impl<'a, K, V> PartialOrd for OrdByKey<'a, K, V>
    where
        K: PartialOrd,
{
    fn partial_cmp(&self, other: &OrdByKey<'a, K, V>) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<'a, K, V> Ord for OrdByKey<'a, K, V>
    where
        K: Ord + PartialOrd + Eq,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

/// Represents a scalar value or an associative array.
pub trait Value: PartialEq<Self> {
    /// The Key type used to find Values in a mapping.
    type Key;
    /// The Value type itself.
    type Item;

    /// Returns `None` if this is a scalar value, and an iterator yielding (Key, Value) pairs
    /// otherwise. It is entirely possible for it to yield no values though.
    #[allow(clippy::type_complexity)]
    fn items<'a>(&'a self) -> Option<Box<dyn Iterator<Item = (Self::Key, &'a Self::Item)> + 'a>>;

    /// Returns an iterator yielding (Key, Value) pairs if the implementing type could have
    /// annotations (i.e. it's an [Element]). It is entirely possible for it to yield no values.
    /// Returns [None] if it's not possible for the value to have annotations (e.g. because it's
    /// [Vec<Element>]).
    #[allow(clippy::type_complexity)]
    fn annotations<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a Symbol> + 'a>>;
}

/// The delegate receiving callbacks by the `diff` algorithm, which compares an old to a new value.
///
/// # Type Parameters
/// * `K` is the Key's type
/// * `V` is the Value's type
///
/// Methods will be called if...
pub trait Delegate<'a, K, V> {
    /// ... we recurse into the `Value` at the given `Key`.
    ///
    /// Delegates should memoize the current Key path to be able to compute
    /// the full Key path when needed.
    fn push(&mut self, _k: &K) {}
    /// ... we have processed all items and leave the object previously `push`ed.
    fn pop(&mut self) {}
    /// ... the Value `v` at the given Key `k` should be removed.
    ///
    /// *Note* that the Key is partial, and should be used in conjunction with the recorded Keys
    /// received via `push(...)`
    fn removed<'b>(&mut self, _k: &'b K, _v: &'a V) {}
    /// .. the Value `v` at the given Key `k` should be added.
    ///
    /// *Note* that the Key is partial, and should be used in conjunction with the recorded Keys
    /// received via `push(...)`
    fn added<'b>(&mut self, _k: &'b K, _v: &'a V) {}
    /// The Value `v` was not changed.
    fn unchanged(&mut self, _v: &'a V) {}

    /// ... the `old` Value was modified, and is now the `new` Value.
    fn modified(&mut self, _old: &'a V, _new: &'a V) {}

    /// ... the `old` Value was modified, and is now the `new` Value.
    fn annotations_modified(&mut self, _old: Vec<Symbol>, _new: Vec<Symbol>);
}

/// Identifies a type of change at a given Key path, for use with the `Recorder`.
///
/// The Key path is followed to know what happened with the Value `V` contained in the variants.
#[derive(Debug, PartialEq)]
pub enum ChangeType<'a, K, V: 'a> {
    /// The Value was removed
    Removed(Vec<K>, &'a V),
    /// The Value was added
    Added(Vec<K>, &'a V),
    /// No change was performed to the Value
    Unchanged(Vec<K>, &'a V),
    /// The first Value was modified and became the second Value
    Modified(Vec<K>, &'a V, &'a V),
    AnnotationsModified(Vec<K>, Vec<Symbol>, Vec<Symbol>),
}

/// A `Delegate` to record all calls made to it.
///
/// It can be useful if you don't want to implement your own custom delegate, but instead just want
/// to quickly see a flat list of all results of the `diff` run.
///
/// # Examples
/// Please see the [tests][tests] for how to use this type.
///
/// [tests]: https://github.com/Byron/treediff-rs/blob/master/tests/diff.rs#L21
#[derive(Debug, PartialEq)]
pub struct Recorder<'a, K, V: 'a> {
    cursor: Vec<K>,
    /// A list of all calls the `diff` function made on us.
    pub calls: Vec<ChangeType<'a, K, V>>,
}

impl<'a, K, V> Default for Recorder<'a, K, V> {
    fn default() -> Self {
        Recorder {
            cursor: Vec::new(),
            calls: Vec::new(),
        }
    }
}

fn mk<K>(c: &[K], k: Option<&K>) -> Vec<K>
    where
        K: Clone,
{
    let mut c = Vec::from(c);
    match k {
        Some(k) => {
            c.push(k.clone());
            c
        }
        None => c,
    }
}

impl<'a, K, V> Delegate<'a, K, V> for Recorder<'a, K, V>
    where
        K: Clone,
{
    fn push(&mut self, k: &K) {
        self.cursor.push(k.clone())
    }
    fn pop(&mut self) {
        self.cursor.pop();
    }
    fn removed<'b>(&mut self, k: &'b K, v: &'a V) {
        self.calls
            .push(ChangeType::Removed(mk(&self.cursor, Some(k)), v));
    }
    fn added<'b>(&mut self, k: &'b K, v: &'a V) {
        self.calls
            .push(ChangeType::Added(mk(&self.cursor, Some(k)), v));
    }
    fn unchanged<'b>(&mut self, v: &'a V) {
        self.calls
            .push(ChangeType::Unchanged(self.cursor.clone(), v));
    }
    fn modified<'b>(&mut self, v1: &'a V, v2: &'a V) {
        self.calls
            .push(ChangeType::Modified(mk(&self.cursor, None), v1, v2));
    }
    fn annotations_modified(&mut self, v1: Vec<Symbol>, v2: Vec<Symbol>) {
        self.calls.push(ChangeType::AnnotationsModified(
            mk(&self.cursor, None),
            v1,
            v2,
        ));
    }
}

/// A representation of all key types typical Value types will assume.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub enum Key {
    /// An array index
    Index(usize),
    /// A string index for mappings
    Symbol(Symbol),
}

impl fmt::Display for Key {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Key::Symbol(ref v) => v.fmt(f),
            Key::Index(ref v) => v.fmt(f),
        }
    }
}
