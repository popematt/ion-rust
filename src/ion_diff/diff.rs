// Copyright Amazon.com, Inc. or its affiliates.

use std::cmp::{max, min, Ordering};
use crate::element::{IonSequence, List, SExp, Struct, Value};
use crate::ion_diff::{ContainedElements, ContainsElements, ChangeListener, Diffable, Key};
use crate::{Element, IonType, Symbol};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Deref;
use similar::{Algorithm, capture_diff_slices, DiffOp};
use crate::ion_diff::ord_element::OrdElement;

impl ContainsElements for Struct {
    fn get_children<'a>(&'a self) -> Box<dyn Iterator<Item = (Key, &'a Element)> + 'a> {
        Box::new(self.fields().map(|(k, v)| (k.into(), v)))
    }
}

// impl<T: IonSequence> ContainsElements for T {
//     fn get_children<'a>(&'a self) -> Box<dyn Iterator<Item = (Key, &'a Element)> + 'a> {
//         Box::new(self.elements().enumerate().map(|(k, v)| (k.into(), v)))
//     }
// }
// impl <I: IntoIterator<Item = Element>> ContainsElements for I {
//     fn get_children<'a>(&'a self) -> Box<dyn Iterator<Item = (Key, &'a Element)> + 'a> {
//         Box::new(&self.into_iter().enumerate().map(|(k, v)| (k.into(), &v)))
//     }
// }


fn maybe_get_children(value: &Value) -> Option<ContainedElements> {
    match value {
        Value::SExp(sexp) => Some(Box::new(sexp.elements().enumerate().map(|(k, v)| (k.into(), v)))),
        Value::List(list) => Some(Box::new(list.elements().enumerate().map(|(k, v)| (k.into(), v)))),
        Value::Struct(struct_) => Some(struct_.get_children()),
        _ => None,
    }
}

impl Diffable for Element {
    fn diff_with_delegate<'a, D: ChangeListener<'a>>(d: &mut D, left: &'a Self, right: &'a Self) {
        diff_element(left, right, d);
    }
}
impl <T: ContainsElements> Diffable for T {
    fn diff_with_delegate<'a, D: ChangeListener<'a>>(d: &mut D, left: &'a Self, right: &'a Self) {
        let li = left.get_children();
        let ri = right.get_children();
        diff_children(li, ri, d)
    }
}

fn diff_element3<'a, D>(l: &'a Element, r: &'a Element, d: &mut D)
    where
        D: ChangeListener<'a>,
{
    let l_items: Option<Box<dyn Iterator<Item = (Key, &Element)>>> = maybe_get_children(l.value());
    let r_items: Option<Box<dyn Iterator<Item = (Key, &Element)>>> = maybe_get_children(r.value());

    match (l_items, r_items) {
        // two scalars, equal
        (None, None) if l == r => d.unchanged(l),
        // two scalars, different
        (None, None) => {
            diff_annotations(l, r, d);
            if l.value() != r.value() {
                d.value_modified(l.value(), r.value())
            }
        }
        // two containers, equal
        (Some(_), Some(_)) if l == r => d.unchanged(l),
        // container and scalar
        (Some(_), None) | (None, Some(_)) => {
            diff_annotations(l, r, d);
            d.value_modified(l.value(), r.value())
        }
        // two containers, different
        (Some(li), Some(ri)) => {
            diff_children(li, ri, d);
            diff_annotations(l, r, d);
        }
    }
}

fn diff_element<'a, D>(l: &'a Element, r: &'a Element, d: &mut D)
    where
        D: ChangeListener<'a>,
{
    diff_annotations(l, r, d);
    match (l.ion_type(), r.ion_type()) {
        // two equal
        (_, _) if l == r => d.unchanged(l),
        (IonType::SExp, IonType::SExp) |
        (IonType::List, IonType::List) => {
            diff_sequence(l.as_sequence().unwrap().elements().collect(), r.as_sequence().unwrap().elements().collect(), d);
        }
        (IonType::Struct, IonType::Struct) => {
            diff_fields(l.as_struct().unwrap().fields(), r.as_struct().unwrap().fields(), d);
        }
        // Two unequal, at least one is a scalar OR they are different container types
        (_, _) => {
            if l.value() != r.value() {
                d.value_modified(l.value(), r.value())
            }
        }
    }
}

fn diff_annotations<'a, D: ChangeListener<'a>>(l: &'a Element, r: &'a Element, d: &mut D) {
    let la: Vec<_> = l.annotations().cloned().collect();
    let ra: Vec<_> = r.annotations().cloned().collect();
    if la != ra {
        d.annotations_modified(la, ra);
    }
}

fn diff_children<'a, D: ChangeListener<'a>>(
    li: ContainedElements<'a>,
    ri: ContainedElements<'a>,
    d: &mut D,
) {
    let mut sl: BTreeSet<OrdByKey> = BTreeSet::new();
    sl.extend(li.map(Into::into));

    let mut sr: BTreeSet<OrdByKey> = BTreeSet::new();
    sr.extend(ri.map(Into::into));

    for k in sr.intersection(&sl) {
        let v1 = sl.get(k).expect("intersection to work");
        let v2 = sr.get(k).expect("intersection to work");
        d.push(&k.0);
        diff_element(v1.1.into(), v2.1.into(), d);
        d.pop();
    }
    // Possible modifications

    for k in sr.difference(&sl) {
        d.added(&k.0, sr.get(k).expect("difference to work").1.into());
    }
    for k in sl.difference(&sr) {
        d.removed(&k.0, sl.get(k).expect("difference to work").1.into());
    }
}

fn diff_fields<'a, I: Iterator<Item = (&'a Symbol, &'a Element)> + 'a, D: ChangeListener<'a>>(
    li: I,
    ri: I,
    d: &mut D,
) {
    let mut sl: BTreeMap<&Symbol, Vec<OrdElement>> = BTreeMap::new();
    for (k, element) in li {
        sl.entry(k).or_insert_with(Vec::new).push(element.into());
    }
    sl.iter_mut().for_each(|(_, vec)| vec.sort());
    let mut sr: BTreeMap<&Symbol, Vec<OrdElement>> = BTreeMap::new();
    for (k, element) in ri {
        sr.entry(k).or_insert_with(Vec::new).push(element.into());
    }
    sr.iter_mut().for_each(|(_, vec)| vec.sort());

    let mut all_keys : BTreeSet<&Symbol> = BTreeSet::new();
    all_keys.extend(sl.keys());
    all_keys.extend(sr.keys());

    for field_name in all_keys {
        let k: Key = field_name.into();
        match (sl.get(field_name), sr.get(field_name)) {
            (Some(lv), Some(mut rv)) => {
                diff_for_field_name(field_name, lv, rv, d);
            }
            (Some(lv), None) => {
                for &x in lv {
                    d.removed(&k, x.into());
                }
            }
            (None, Some(rv)) => {
                for &x in rv {
                    d.added(&k, x.into());
                }
            }
            (None, None) => unreachable!("The key must be in at least one of the maps")
        }
    }
}

fn diff_for_field_name<'a, 'b, D: ChangeListener<'a>>(field_name: &'a Symbol, lv: &'b Vec<OrdElement<'a>>, rv: &'b Vec<OrdElement<'a>>, d: &mut D) {
    let mut l_iter = lv.iter();
    let mut r_iter = rv.iter();
    let mut l_curr = l_iter.next();
    let mut r_curr = r_iter.next();
    let k: Key = field_name.into();
    loop {
        match (l_curr, r_curr) {
            (None, None) => { return; }
            (Some(&v), None) => { d.removed(&k, v.into()); break; }
            (None, Some(&v)) => { d.added(&k, v.into()); break; }
            (Some(&l), Some(&r)) => {
                let o = l.cmp(&r);
                match o {
                    Ordering::Less => {
                        d.removed(&k, l.into());
                        l_curr = l_iter.next();
                    }
                    Ordering::Equal => {
                        d.push(&k);
                        d.unchanged(r.into());
                        d.pop();
                        r_curr = r_iter.next();
                        l_curr = l_iter.next();
                    }
                    Ordering::Greater => {
                        d.added(&k, r.into());
                        r_curr = r_iter.next();
                    }
                }
            }
        }
    }

    // Only one of these iterators can still have anything left at this point.

    while let Some (&l) = l_iter.next() {
        d.removed(&k, l.into())
    }
    while let Some (&r) = r_iter.next() {
        d.added(&k, r.into())
    }
}

fn diff_sequence<'a, D: ChangeListener<'a>>(
    li: Vec<&'a Element>,
    ri: Vec<&'a Element>,
    d: &mut D,
) {
    for i in 0..max(li.len(), ri.len()) {
        match (li.get(i), ri.get(i)) {
            (Some(&l), Some(&r)) => {
                d.push(&i.into());
                diff_element(l, r, d);
                d.pop();
            }
            (Some(&l), None) => d.removed(&i.into(), l),
            (None, Some(&r)) => d.added(&i.into(), r),
            (None, None) => {
                unreachable!("We can't go past the end of both lists.")
            }
        }
    }
}




/// A struct that allows us to use a BTreeSet as an associative array but still take advantage of
/// the `intersect()` and `difference()` functions of Sets.
#[derive(Ord, PartialOrd, Eq, PartialEq)]
pub(crate) struct OrdByKey<'a>(pub Key, pub OrdElement<'a>);

impl<'a> From<(Key, &'a Element)> for OrdByKey<'a> {
    fn from(src: (Key, &'a Element)) -> Self {
        OrdByKey(src.0, OrdElement::from(src.1))
    }
}

#[derive(Ord, PartialOrd, Eq, PartialEq)]
pub(crate) struct GroupedFieldValues<'a>(pub Key, pub Vec<OrdElement<'a>>);

