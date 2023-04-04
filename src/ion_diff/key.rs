// Copyright Amazon.com, Inc. or its affiliates.

use crate::element::Value;
use crate::Symbol;
use std::fmt;

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

impl From<&Symbol> for Key {
    fn from(value: &Symbol) -> Self {
        Key::Symbol(value.clone())
    }
}
impl From<usize> for Key {
    fn from(value: usize) -> Self {
        Key::Index(value)
    }
}

impl From<&Key> for Value {
    fn from(value: &Key) -> Self {
        match value {
            Key::Index(i) => Value::Int((*i).into()),
            Key::Symbol(s) => Value::Symbol(s.into()),
        }
    }
}

