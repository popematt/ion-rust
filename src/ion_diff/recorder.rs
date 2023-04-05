// Copyright Amazon.com, Inc. or its affiliates.

use crate::element::builders::ListBuilder;
use crate::element::{IntoAnnotatedElement, List, SExp, Value};
use crate::ion_diff::{ChangeListener, Key};
use crate::{ion_struct, Element, IonType, Symbol};

/// Identifies a type of change at a given Key path, for use with the [DefaultChangeListener].
#[derive(Debug, PartialEq)]
pub enum ChangeType<'a> {
    /// The Value was removed
    Removed(Vec<Key>, &'a Element),
    /// The Value was added
    Added(Vec<Key>, &'a Element),
    /// No change was performed to the Value
    Unchanged(Vec<Key>, &'a Element),
    /// The first Value was modified and became the second Value
    ValueModified(Vec<Key>, &'a Value, &'a Value),
    /// The annotations on the value were modified
    AnnotModified(Vec<Key>, Vec<Symbol>, Vec<Symbol>),
    /// The value was moved to a new position in a list or sexp (because an element was added
    /// or removed prior to this element in the list or sexp).
    IndexModified(Vec<Key>, Vec<Key>, &'a Element),
}

impl<'a> From<Vec<&'a ChangeType<'a>>> for Element {
    fn from(value: Vec<&'a ChangeType<'a>>) -> Self {
        let mut lb = ListBuilder::new();
        for v in value {
            lb = lb.push(v);
        }
        lb.into()
    }
}

impl<'a> From<Vec<ChangeType<'a>>> for Element {
    fn from(value: Vec<ChangeType<'a>>) -> Self {
        let mut lb = ListBuilder::new();
        for v in value {
            lb = lb.push(v);
        }
        lb.into()
    }
}

impl<'a> From<ChangeType<'a>> for Element {
    fn from(value: ChangeType<'a>) -> Self {
        Element::from(&value)
    }
}

impl<'a> From<&ChangeType<'a>> for Element {
    fn from(value: &ChangeType<'a>) -> Self {
        match value {
            ChangeType::Removed(k, v) => {
                let mut path_builder = SExp::builder();
                for e in k {
                    path_builder = path_builder.push(e);
                }
                let s = ion_struct! {
                    "path": path_builder.build(),
                    "old": v.clone()
                };
                s.with_annotations(["removed"])
            }
            ChangeType::Added(k, v) => {
                let mut path_builder = SExp::builder();
                for e in k {
                    path_builder = path_builder.push(e);
                }
                let s = ion_struct! {
                    "path": path_builder.build(),
                    "new": v.clone()
                };
                s.with_annotations(["added"])
            }
            ChangeType::Unchanged(k, v) => {
                let mut path_builder = SExp::builder();
                for e in k {
                    path_builder = path_builder.push(e);
                }
                let s = ion_struct! {
                    "path": path_builder.build(),
                    "value": v.clone()
                };
                s.with_annotations(["unchanged"])
            }
            ChangeType::ValueModified(k, old, new) => {
                let mut path_builder = SExp::builder();
                for e in k {
                    path_builder = path_builder.push(e);
                }
                let s = ion_struct! {
                    "path": path_builder.build(),
                    "old": (*old).clone(),
                    "new": (*new).clone()
                };
                s.with_annotations(["value_modified"])
            }
            ChangeType::AnnotModified(k, old, new) => {
                let mut path_builder = SExp::builder();
                for e in k {
                    path_builder = path_builder.push(e);
                }
                let mut old_ann = List::builder();
                for e in old {
                    old_ann = old_ann.push(e.clone());
                }
                let mut new_ann = List::builder();
                for e in new {
                    new_ann = new_ann.push(e.clone());
                }
                let s = ion_struct! {
                    "path": path_builder.build(),
                    "old": Element::null(IonType::Null).with_annotations(old),
                    "new": Element::null(IonType::Null).with_annotations(new)
                };
                s.with_annotations(["annotations_modified"])
            }
            ChangeType::IndexModified(k1, k2, v) => {
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

/// A [ChangeListener] to record all calls made to it and persist them as a flat list of changes.
#[derive(Debug, PartialEq)]
pub struct DefaultChangeListener<'a> {
    cursor: Vec<Key>,
    /// A list of all calls the `diff` function made on us.
    pub calls: Vec<ChangeType<'a>>,
}
impl<'a> DefaultChangeListener<'a> {
    fn make_path_to(&self, k: &Key) -> Vec<Key> {
        let mut c: Vec<Key> = Vec::with_capacity(self.cursor.len() + 1);
        c.extend_from_slice(self.cursor.as_slice());
        c.push(k.clone());
        c
    }

    fn current_path(&self) -> Vec<Key> {
        self.cursor.clone()
    }
}

impl<'a> Default for DefaultChangeListener<'a> {
    fn default() -> Self {
        DefaultChangeListener {
            cursor: Vec::new(),
            calls: Vec::new(),
        }
    }
}

impl<'a> ChangeListener<'a> for DefaultChangeListener<'a> {
    fn push(&mut self, k: &Key) {
        self.cursor.push(k.clone())
    }
    fn pop(&mut self) {
        self.cursor.pop();
    }
    fn removed<'b>(&mut self, k: &'b Key, v: &'a Element) {
        let path = self.make_path_to(k);
        self.calls.push(ChangeType::Removed(path, v));
    }
    fn added<'b>(&mut self, k: &'b Key, v: &'a Element) {
        let path = self.make_path_to(k);
        self.calls.push(ChangeType::Added(path, v));
    }
    fn unchanged<'b>(&mut self, v: &'a Element) {
        self.calls
            .push(ChangeType::Unchanged(self.current_path(), v));
    }
    fn value_modified<'b>(&mut self, v1: &'a Value, v2: &'a Value) {
        self.calls
            .push(ChangeType::ValueModified(self.current_path(), v1, v2));
    }
    fn annotations_modified(&mut self, v1: Vec<Symbol>, v2: Vec<Symbol>) {
        self.calls
            .push(ChangeType::AnnotModified(self.current_path(), v1, v2));
    }
    fn moved<'b>(&mut self, _old_location: &'b Key, _new_location: &'b Key, _value: &'a Element) {
        self.calls.push(ChangeType::IndexModified(
            self.make_path_to(_old_location),
            self.make_path_to(_new_location),
            _value,
        ));
    }
}
