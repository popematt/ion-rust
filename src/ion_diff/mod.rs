use crate::element::{Value as IonValue, Value};
use crate::element::{Element, IntoAnnotatedElement, IonSequence, List, SExp};
use crate::{ion_sexp, ion_struct, IonType, Symbol};
use std::cmp::{max, min, Ordering};
use std::collections::BTreeSet;
use std::fmt;
use std::hash::{Hash, Hasher};
use similar::{Algorithm, capture_diff_slices, DiffOp};

// Seems to be working
// TODO: Consider handling insert/removal in the middle of a list more gracefully.
// TODO: deal with duplicate field names -- need a total ordering over Element for this. Can be arbitrary and internal only.
// TODO: deal with top-level streams

/// TODO: get rid of this function
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
                let mut path_sexp = SExp::builder();
                for e in k {
                    path_sexp = path_sexp.push(e);
                }
                let s = ion_struct! {
                    "path": path_sexp.build(),
                    "old": v.clone()
                };
                s.with_annotations(["removed"])
            }
            ChangeType::Added(k, v) => {
                let mut path_sexp = SExp::builder();
                for e in k {
                    path_sexp = path_sexp.push(e);
                }
                let s = ion_struct! {
                    "path": path_sexp.build(),
                    "new": v.clone()
                };
                s.with_annotations(["added"])
            }
            ChangeType::Unchanged(k, v) => {
                let mut path_sexp = SExp::builder();
                for e in k {
                    path_sexp = path_sexp.push(e);
                }
                let s = ion_struct! {
                    "path": path_sexp.build(),
                    "value": v.clone()
                };
                s.with_annotations(["unchanged"])
            }
            ChangeType::ValueModified(k, old, new) => {
                let mut path_sexp = SExp::builder();
                for e in k {
                    path_sexp = path_sexp.push(e);
                }
                let s = ion_struct! {
                    "path": path_sexp.build(),
                    "old": old.clone(),
                    "new": new.clone()
                };
                s.with_annotations(["value_modified"])
            }
            ChangeType::AnnotationsModified(k, old, new) => {
                let mut path_sexp = SExp::builder();
                for e in k {
                    path_sexp = path_sexp.push(e);
                }
                let s = ion_struct! {
                    "path": path_sexp.build(),
                    "old": Element::null(IonType::Null).with_annotations(old),
                    "new": Element::null(IonType::Null).with_annotations(new)
                };
                s.with_annotations(["annotations_modified"])
            }
            ChangeType::IndexChanged(k1, k2, v) => {
                let mut path_sexp_1 = SExp::builder();
                for e in k1 {
                    path_sexp_1 = path_sexp_1.push(e);
                }
                let mut path_sexp_2 = SExp::builder();
                for e in k2 {
                    path_sexp_2 = path_sexp_2.push(e);
                }
                let s = ion_struct! {
                    "old_path": path_sexp_1.build(),
                    "new_path": path_sexp_2.build(),
                    "value": v.clone()
                };
                s.with_annotations(["moved"])
            }
        }
    }
}

impl DiffableValue for Element {
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

    fn value<'a>(&'a self) -> Option<&'a Value> {
        match self.value() {
            Value::SExp(_) |
            Value::List(_) |
            Value::Struct(_) => None,
            other => Some(other),
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
              foo: abc::2,
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
              foo: bar::1,
              name: CustomerFieldTypes,
              fields: closed::{
                title: { valid_values: ["Dr.", "Mr.", "Mrs.", "Ms."] },
                firstName: string,
                middleName: $string, // Change to nullable
                lastName: string,
                suffix: { valid_values: ["Jr.", "Sr.", "PhD"] },
                preferredName: string,
                customerId: {
                  one_of: [
                    { type: string, codepoint_length: 18 },
                    { type: blob, byte_length: 18 }, // New variant
                    { type: int, valid_values: range::[100000, 999999] },
                  ],
                },
                addresses: { type: list, element: Address },
                lastUpdated: { timestamp_precision: second },
                created: { timestamp_precision: second },  // New field
              },
            }
    "#,
    )
        .unwrap();

    ion_diff(&e1, &e2);
}


#[test]
fn test_diff_vec() {
    let e1 = Element::read_all("a b c d e").unwrap();
    let e2 = Element::read_all("c d e a b").unwrap();

    let mut d = Recorder::default();
    diff_iterator(e1.iter(), e2.iter(), &mut d);

    for change in d.calls {
        let e: Element = change.into();
        if !e.has_annotation("unchanged") && !e.has_annotation("moved") {
            println!("{}", e)
        }
    }
}


impl Hash for Element {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u8(self.ion_type() as u8);
    }
}

impl PartialOrd<Self> for Element {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Element {
    fn cmp(&self, other: &Self) -> Ordering {
        let ord = IonType::partial_cmp(&self.ion_type(), &other.ion_type()).unwrap();
        if !ord.is_eq() { return ord; }

        let a1 = self.annotations().map(|s| s.text()).collect::<Vec<_>>();
        let a2 = other.annotations().map(|s| s.text()).collect::<Vec<_>>();

        let ord = a1.cmp(&a2);
        if !ord.is_eq() { return ord; }

        match self.value() {
            Value::Null(_) => Ordering::Equal,
            Value::Int(this) => this.cmp(other.as_int().unwrap()),
            Value::Float(this) => this.total_cmp(&other.as_float().unwrap()),
            Value::Decimal(this) => this.cmp(other.as_decimal().unwrap()),
            Value::Timestamp(this) => this.cmp(other.as_timestamp().unwrap()),
            Value::String(this) => this.as_str().cmp(other.as_string().unwrap()),
            Value::Symbol(this) => this.cmp(other.as_symbol().unwrap()),
            Value::Bool(this) => this.cmp(&other.as_bool().unwrap()),
            Value::Blob(this) => this.as_slice().cmp(other.as_blob().unwrap()),
            Value::Clob(this) => this.as_slice().cmp(other.as_clob().unwrap()),
            Value::SExp(this) => this.elements().collect::<Vec<_>>().cmp(&other.as_sexp().unwrap().elements().collect()),
            Value::List(this) => this.elements().collect::<Vec<_>>().cmp(&other.as_list().unwrap().elements().collect()),
            Value::Struct(this) => {
                this.fields().collect::<Vec<_>>().cmp(&other.as_struct().unwrap().fields().collect())
            }
        }
    }
}



pub trait Diffable {
    fn diff_with<D>(&self, other: &Self, d: &mut D);
}


/*
pub fn diff_iterable<'a, V, D, I1: IntoIterator<Item = &'a V> + 'a, I2: IntoIterator<Item = &'a V> + 'a>(l: &'a I1, r: &'a I2, d: &mut D)
    where
        V: 'a,
        V: DiffableValue<Item = V>,
        V::Key: Ord + Clone  + From<usize>,
        D: Delegate<'a, V::Key, V>,
{
    diff_iterator((&l).into_iter(), (&r).into_iter(), d)
}
*/


pub fn diff_iterator<'a, V, D, I1: Iterator<Item = &'a V> + 'a, I2: Iterator<Item = &'a V> + 'a>(l: I1, r: I2, d: &mut D)
    where
        V: 'a + Hash + Ord + DiffableValue<Item = V>,
        V::Key: Ord + Clone  + From<usize>,
        D: Delegate<'a, V::Key, V>,
{

    let a = l.collect::<Vec<_>>();
    let b = r.collect::<Vec<_>>();

    let ops = capture_diff_slices(Algorithm::Myers, &a, &b);

    for op in ops {
        match op {
            DiffOp::Equal { old_index, new_index, len } => {
                for i in 0..len {
                    d.moved(&(i + old_index).into(), &(i + new_index).into(), a.get(i + old_index).unwrap());
                }
            }
            DiffOp::Delete { old_index, old_len, new_index } => {
                for i in 0..old_len {
                    let k: V::Key = (old_index + i).into();
                    d.removed(&k, a.get(old_index + i).unwrap());
                }
            }
            DiffOp::Insert { old_index, new_index, new_len } => {
                for i in 0..new_len {
                    let k: V::Key = (new_index + i).into();
                    d.added(&k, b.get(new_index + i).unwrap());
                }
            }
            DiffOp::Replace { old_index, old_len, new_index, new_len } => {
                let old_range = old_index..(old_index + old_len);
                let new_range = new_index..(new_index + new_len);

                for i in min(old_index, new_index)..max(old_index + old_len, new_index + new_len) {

                    match i {
                        i if old_range.contains(&i) && new_range.contains(&i) => {
                            d.push(&i.into());
                            diff(a.get(i).unwrap().clone(), b.get(i).unwrap().clone(), d);
                            d.pop();
                        }
                        i if old_range.contains(&i) => {
                            d.removed(&i.into(), a.get(i).unwrap())
                        }
                        i if new_range.contains(&i) => {
                            d.removed(&i.into(), b.get(i).unwrap())
                        }
                        _ => {}
                    }
                }
            }
        }
    }




    // let li = l.enumerate().map(|(i, e)| (i.into(), e));
    // let ri = r.enumerate().map(|(i, e)| (i.into(), e));
    //
    // let mut sl: BTreeSet<OrdByKey<_, _>> = BTreeSet::new();
    // sl.extend(li.map(Into::into));
    // let mut sr: BTreeSet<OrdByKey<_, _>> = BTreeSet::new();
    // sr.extend(ri.map(Into::into));
    // for k in sr.intersection(&sl) {
    //     let v1 = sl.get(k).expect("intersection to work");
    //     let v2 = sr.get(k).expect("intersection to work");
    //     d.push(&k.0);
    //     diff(v1.1, v2.1, d);
    //     d.pop();
    // }
    // for k in sr.difference(&sl) {
    //     d.added(&k.0, sr.get(k).expect("difference to work").1);
    // }
    // for k in sl.difference(&sr) {
    //     d.removed(&k.0, sl.get(k).expect("difference to work").1);
    // }
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
        V: DiffableValue<Item = V>,
        V::Key: Ord + Clone,
        D: Delegate<'a, V::Key, V>,
{
    match (l.items(), r.items()) {
        // two scalars, equal
        (None, None) if l == r => d.unchanged(l),
        // two scalars, different
        (None, None) => {
            let (lv, rv) = if let (Some(lv), Some(rv)) = (l.value(), r.value()) {
                (lv, rv)
            } else {
                unreachable!("We already know that these are both scalars")
            };
            if lv != rv {
                // TODO: get rid of annotations
                d.modified(l, r)
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
                _ => unreachable!("Whether a value could have annotations depends on its type, so L and R must both be Some or both be None")
            }
            // d.modified(l, r)
        },
        // two objects, equal
        (Some(_), Some(_)) if l == r => d.unchanged(l),
        // object and scalar
        // TODO: separate out the annotation changes and the value changes
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
pub trait DiffableValue: PartialEq<Self> {
    /// The Key type used to find Values in a mapping.
    type Key;
    /// The type of child items.
    type Item;

    /// Returns `None` if this is a scalar value, and an iterator yielding (Key, Value) pairs
    /// otherwise. It is entirely possible for it to yield no values though.
    #[allow(clippy::type_complexity)]
    fn items<'a>(&'a self) -> Option<Box<dyn Iterator<Item = (Self::Key, &'a Self::Item)> + 'a>>;


    /// Returns `None` if this is a scalar value, and an iterator yielding (Key, Value) pairs
    /// otherwise. It is entirely possible for it to yield no values though.
    #[allow(clippy::type_complexity)]
    fn value<'a>(&'a self) -> Option<&'a Value>;

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

    fn moved<'b>(&mut self, _old_location: &'b K, _new_location: &'b K, _value: &'a V);
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
    ValueModified(Vec<K>, &'a V, &'a V),

    AnnotationsModified(Vec<K>, Vec<Symbol>, Vec<Symbol>),

    // Something got moved in a list of sexp because of a prior insertion or deletion
    IndexChanged(Vec<K>, Vec<K>, &'a V),
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
            .push(ChangeType::ValueModified(mk(&self.cursor, None), v1, v2));
    }
    fn annotations_modified(&mut self, v1: Vec<Symbol>, v2: Vec<Symbol>) {
        self.calls.push(ChangeType::AnnotationsModified(
            mk(&self.cursor, None),
            v1,
            v2,
        ));
    }
    fn moved<'b>(&mut self, _old_location: &'b K, _new_location: &'b K, _value: &'a V) {
        self.calls.push(
            ChangeType::IndexChanged(
                mk(&self.cursor, Some(_old_location)),
                mk(&self.cursor, Some(_new_location)),
                _value
            )
        );
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

impl From<usize> for Key {
    fn from(value: usize) -> Self {
        Key::Index(value)
    }
}

impl fmt::Display for Key {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Key::Symbol(ref v) => v.fmt(f),
            Key::Index(ref v) => v.fmt(f),
        }
    }
}
