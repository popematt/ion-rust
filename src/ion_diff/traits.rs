// Copyright Amazon.com, Inc. or its affiliates.

use crate::element::Value;
use crate::ion_diff::Key;
use crate::{Element, Symbol};
use crate::ion_diff::recorder::{ChangeType, DefaultChangeListener};

pub trait Diffable {
    fn diff_with_delegate<'a, D: ChangeListener<'a>>(d: &mut D, left: &'a Self, right: &'a Self);

    fn diff<'a>(&'a self, other: &'a Self) -> Vec<ChangeType<'a>> {
        let mut recorder = DefaultChangeListener::default();
        Diffable::diff_with_delegate(&mut recorder, self, other);
        recorder.calls
    }
}

/// The ChangeListener receiving callbacks by the `diff` algorithm, which compares an old to a new value.
///
/// # Type Parameters
/// * `K` is the Key's type
/// * `V` is the Value's type
///
/// Methods will be called if...
pub trait ChangeListener<'a> {
    /// ... we recurse into the `Value` at the given `Key`.
    ///
    /// Delegates should memoize the current Key path to be able to compute
    /// the full Key path when needed.
    fn push(&mut self, _k: &Key) {}

    /// ... we have processed all items and leave the object previously `push`ed.
    fn pop(&mut self) {}

    /// ... the Value `v` at the given Key `k` should be removed.
    ///
    /// *Note* that the Key is partial, and should be used in conjunction with the recorded Keys
    /// received via `push(...)`
    fn removed<'b>(&mut self, _k: &'b Key, _v: &'a Element) {}

    /// .. the Value `v` at the given Key `k` should be added.
    ///
    /// *Note* that the Key is partial, and should be used in conjunction with the recorded Keys
    /// received via `push(...)`
    fn added<'b>(&mut self, _k: &'b Key, _v: &'a Element) {}

    /// The Value `v` was not changed.
    fn unchanged(&mut self, _v: &'a Element) {}

    /// ... the `old` Value was modified, and is now the `new` Value, and one of the values is a scalar value.
    fn value_modified(&mut self, _old: &'a Value, _new: &'a Value) {}

    /// ... the `old` annotations were modified, and are now the `new` annotations.
    fn annotations_modified(&mut self, _old: Vec<Symbol>, _new: Vec<Symbol>) {}

    fn moved<'b>(&mut self, _old_location: &'b Key, _new_location: &'b Key, _value: &'a Element);
}
