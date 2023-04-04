

use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::ops::Deref;
use crate::element::{Element, IonSequence, Struct, Value};
use crate::{IonType, Symbol};

#[derive(Copy, Clone)]
pub(crate) struct OrdElement<'a>(&'a Element);

impl <'a> Display for OrdElement<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self.0, f)
    }
}

impl <'a> From<&'a Element> for OrdElement<'a> {
    fn from(value: &'a Element) -> Self {
        OrdElement(value)
    }
}
impl <'a> From<&&'a Element> for OrdElement<'a> {
    fn from(value: &&'a Element) -> Self {
        OrdElement(value)
    }
}

impl <'a> From<OrdElement<'a>> for &'a Element {
    fn from(value: OrdElement<'a>) -> Self {
        value.0
    }
}

impl <'a> From<&'a OrdElement<'a>> for &'a Element {
    fn from(value: &'a OrdElement<'a>) -> Self {
        value.0
    }
}

impl <'a> PartialEq for OrdElement<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl <'a> Eq for OrdElement<'a> {}

impl <'a> PartialOrd for OrdElement<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl <'a> Ord for OrdElement<'a> {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_elements(&self.0, &other.0)
    }
}

fn cmp_elements(this: &Element, that: &Element) -> Ordering {
    let ord = IonType::partial_cmp(&this.ion_type(), &that.ion_type()).unwrap();
    if !ord.is_eq() { return ord; }

    let a1 = this.annotations().map(|s| s.text()).collect::<Vec<_>>();
    let a2 = that.annotations().map(|s| s.text()).collect::<Vec<_>>();

    let ord = a1.cmp(&a2);
    if !ord.is_eq() { return ord; }

    match this.value() {
        Value::Null(_) => Ordering::Equal,
        Value::Int(this) => this.cmp(that.as_int().unwrap()),
        Value::Float(this) => this.total_cmp(&that.as_float().unwrap()),
        Value::Decimal(this) => this.cmp(that.as_decimal().unwrap()),
        Value::Timestamp(this) => this.cmp(that.as_timestamp().unwrap()),
        Value::String(this) => this.as_str().cmp(that.as_string().unwrap()),
        Value::Symbol(this) => this.cmp(that.as_symbol().unwrap()),
        Value::Bool(this) => this.cmp(&that.as_bool().unwrap()),
        Value::Blob(this) => this.as_slice().cmp(that.as_blob().unwrap()),
        Value::Clob(this) => this.as_slice().cmp(that.as_clob().unwrap()),
        Value::SExp(this) => cmp_seq_by(this.elements(), that.as_list().unwrap().elements(), cmp_elements),
        Value::List(this) => cmp_seq_by(this.elements(), that.as_list().unwrap().elements(), cmp_elements),
        Value::Struct(this) => cmp_structs(this, &that.as_struct().unwrap()),
    }
}

fn cmp_structs(this: &Struct, that: &Struct) -> Ordering {
    let mut these_fields = this.fields().collect::<Vec<(&Symbol, &Element)>>();
    let mut those_fields = that.fields().collect::<Vec<(&Symbol, &Element)>>();
    these_fields.sort_by(cmp_fields);
    those_fields.sort_by(cmp_fields);
    cmp_seq_by(these_fields.iter().map(|x|x), those_fields.iter().map(|x|x), cmp_fields)
}

fn cmp_fields(this: &(&Symbol, &Element), that: &(&Symbol, &Element)) -> Ordering {
    let ord = this.0.text().cmp(&that.0.text());
    if !ord.is_eq() { return ord; }
    cmp_elements(this.1, that.1)
}

fn cmp_seq_by<T, R: Deref<Target = T>, I1: IntoIterator<Item = R>, I2: IntoIterator<Item = R>>(this: I1, that: I2, cmp: fn(&T, &T) -> Ordering) -> Ordering {
    let mut that = that.into_iter();
    for this_i in this {
        let that_i = that.next();
        let ord = match that_i {
            Some(that_i) => cmp(&this_i, &that_i),
            None => Ordering::Greater,
        };
        if !ord.is_eq() { return ord; }
    }
    if that.next().is_some() {
        Ordering::Less
    } else {
        Ordering::Equal
    }
}
