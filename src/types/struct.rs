use crate::element::builders::StructBuilder;
use crate::element::Element;
use crate::ion_data::{IonDataHash, IonDataOrd, IonEq};
use crate::symbol_ref::AsSymbolRef;
use crate::text::text_formatter::FmtValueFormatter;
use crate::Symbol;
use hashbrown::HashTable;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::sync::OnceLock;

/// Threshold below which linear scan is used instead of building a hash table.
const LINEAR_SCAN_THRESHOLD: usize = 8;

// This collection is broken out into its own type to allow instances of it to be shared with Arc/Rc.
#[derive(Debug, Clone)]
struct Fields {
    /// All fields in insertion order. The ONLY place field names and values live.
    slots: Vec<(Symbol, Element)>,
    /// Lazily-built hash table mapping field names to slot indices.
    /// Only constructed on first lookup call for structs with more than
    /// LINEAR_SCAN_THRESHOLD fields.
    #[allow(clippy::type_complexity)]
    table: OnceLock<HashTable<u32>>,
}

impl Fields {
    /// Creates a new `Fields` from the given slots without building the hash table.
    fn new(slots: Vec<(Symbol, Element)>) -> Self {
        Fields {
            slots,
            table: OnceLock::new(),
        }
    }

    /// Gets the last value associated with the given field name.
    ///
    /// Note that the Ion data model views a struct as a bag of (name, value) pairs and does not
    /// have a notion of field ordering. In most use cases, field names are distinct and the last
    /// appearance of a field in the struct's serialized form will have been the _only_ appearance.
    /// If a field name appears more than once, this method makes the arbitrary decision to return
    /// the value associated with the last appearance. If your application uses structs that repeat
    /// field names, you are encouraged to use [`get_all`](Self::get_all) instead.
    fn get_last<A: AsSymbolRef>(&self, field_name: A) -> Option<&Element> {
        let symbol_ref = field_name.as_symbol_ref();
        match symbol_ref.text() {
            Some(text) => self.get_last_by_text(text),
            None => self.get_last_unknown_text(),
        }
    }

    /// Gets the last value for a field with the given text name.
    fn get_last_by_text(&self, text: &str) -> Option<&Element> {
        if self.slots.len() <= LINEAR_SCAN_THRESHOLD {
            // Linear scan for small structs — iterate in reverse to find last match
            self.slots
                .iter()
                .rev()
                .find(|(sym, _)| sym.text() == Some(text))
                .map(|(_, value)| value)
        } else {
            // Use hash table for large structs.
            // For "get last", we scan all matching entries and take the one with highest index.
            let table = self.get_or_build_table();
            let hash = hash_text(text);
            let mut last_idx: Option<u32> = None;
            // Iterate all entries with matching hash and equality
            for &idx in table.iter_hash(hash) {
                if self.slots[idx as usize].0.text() == Some(text) {
                    match last_idx {
                        Some(prev) if idx > prev => last_idx = Some(idx),
                        None => last_idx = Some(idx),
                        _ => {}
                    }
                }
            }
            last_idx.map(|idx| &self.slots[idx as usize].1)
        }
    }

    /// Gets the last value for a field with unknown text ($0).
    fn get_last_unknown_text(&self) -> Option<&Element> {
        self.slots
            .iter()
            .rev()
            .find(|(sym, _)| sym.text().is_none())
            .map(|(_, value)| value)
    }

    /// Iterates over all of the values associated with the given field name.
    fn get_all<A: AsSymbolRef>(&self, field_name: A) -> FieldValuesIterator<'_> {
        let symbol_ref = field_name.as_symbol_ref();
        FieldValuesIterator {
            slots: &self.slots,
            text: symbol_ref
                .text()
                .map(|t| FieldNameMatch::Text(t.to_owned())),
            current: 0,
        }
    }

    /// Returns an iterator that yields all values for fields matching a text name,
    /// along with the count of matching fields.
    fn get_all_with_count<A: AsSymbolRef>(
        &self,
        field_name: A,
    ) -> (FieldValuesIterator<'_>, usize) {
        let symbol_ref = field_name.as_symbol_ref();
        let text = symbol_ref.text();
        let count = self
            .slots
            .iter()
            .filter(|(sym, _)| sym.text() == text)
            .count();
        let iter = FieldValuesIterator {
            slots: &self.slots,
            text: text.map(|t| FieldNameMatch::Text(t.to_owned())),
            current: 0,
        };
        (iter, count)
    }

    /// Iterates over all of the (field name, field value) pairs in the struct.
    fn iter(&self) -> impl Iterator<Item = &(Symbol, Element)> {
        self.slots.iter()
    }

    /// Gets or builds the hash table for large struct lookups.
    fn get_or_build_table(&self) -> &HashTable<u32> {
        self.table.get_or_init(|| build_table(&self.slots))
    }

    /// Returns an iterator over distinct field names (by text) along with a count.
    /// Used for equality checks.
    fn distinct_field_names(&self) -> DistinctFieldNamesIterator<'_> {
        DistinctFieldNamesIterator {
            slots: &self.slots,
            seen_index: 0,
        }
    }
}

/// Builds the hash table mapping field name hashes to slot indices.
fn build_table(slots: &[(Symbol, Element)]) -> HashTable<u32> {
    let mut table = HashTable::with_capacity(slots.len());
    for (i, (symbol, _)) in slots.iter().enumerate() {
        let hash = hash_symbol(symbol);
        table.insert_unique(hash, i as u32, |&idx| hash_symbol(&slots[idx as usize].0));
    }
    table
}

/// Hashes a Symbol by its text (or "" for unknown text).
fn hash_symbol(symbol: &Symbol) -> u64 {
    hash_text(symbol.text().unwrap_or(""))
}

/// Hashes a text string using FxHasher for fast lookups.
fn hash_text(text: &str) -> u64 {
    let mut hasher = rustc_hash::FxHasher::default();
    text.hash(&mut hasher);
    hasher.finish()
}

/// Helper enum for matching field names during iteration.
#[derive(Clone)]
enum FieldNameMatch {
    Text(String),
}

/// Iterates over distinct field names in a struct, yielding each unique field name text
/// (or None for unknown text) exactly once.
struct DistinctFieldNamesIterator<'a> {
    slots: &'a [(Symbol, Element)],
    seen_index: usize,
}

impl<'a> Iterator for DistinctFieldNamesIterator<'a> {
    // Yields (field_name_text, count_of_fields_with_this_name)
    type Item = (Option<&'a str>, usize);

    fn next(&mut self) -> Option<Self::Item> {
        while self.seen_index < self.slots.len() {
            let current_text = self.slots[self.seen_index].0.text();
            // Check if we already saw this field name earlier
            let already_seen = self.slots[..self.seen_index]
                .iter()
                .any(|(sym, _)| sym.text() == current_text);
            self.seen_index += 1;
            if !already_seen {
                // Count how many fields have this name
                let count = self
                    .slots
                    .iter()
                    .filter(|(sym, _)| sym.text() == current_text)
                    .count();
                return Some((current_text, count));
            }
        }
        None
    }
}

/// Iterates over the (field name, field value) pairs in a Struct.
pub struct FieldIterator<'a> {
    values: Option<std::slice::Iter<'a, (Symbol, Element)>>,
}

impl<'a> FieldIterator<'a> {
    fn new(data: &'a [(Symbol, Element)]) -> Self {
        FieldIterator {
            values: Some(data.iter()),
        }
    }
}

impl<'a> Iterator for FieldIterator<'a> {
    type Item = (&'a Symbol, &'a Element);

    fn next(&mut self) -> Option<Self::Item> {
        self.values
            .as_mut()
            // Get the next &(name, value) and convert it to (&name, &value)
            .and_then(|iter| iter.next().map(|field| (&field.0, &field.1)))
    }
}

/// Iterates over the (field name, field value) pairs in a Struct.
pub struct OwnedFieldIterator {
    fields: VecDeque<(Symbol, Element)>,
}

impl OwnedFieldIterator {
    fn new(data: Vec<(Symbol, Element)>) -> Self {
        OwnedFieldIterator {
            fields: data.into(),
        }
    }
}

impl Iterator for OwnedFieldIterator {
    type Item = (Symbol, Element);

    fn next(&mut self) -> Option<Self::Item> {
        self.fields.pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.fields.len();
        (len, Some(len))
    }
}

/// Iterates over the values associated with a given field name in a Struct.
pub(crate) struct FieldValuesIterator<'a> {
    slots: &'a [(Symbol, Element)],
    text: Option<FieldNameMatch>,
    current: usize,
}

impl<'a> Iterator for FieldValuesIterator<'a> {
    type Item = &'a Element;

    fn next(&mut self) -> Option<Self::Item> {
        while self.current < self.slots.len() {
            let idx = self.current;
            self.current += 1;
            let (sym, value) = &self.slots[idx];
            match &self.text {
                Some(FieldNameMatch::Text(t)) => {
                    if sym.text() == Some(t.as_str()) {
                        return Some(value);
                    }
                }
                None => {
                    // Looking for unknown text ($0)
                    if sym.text().is_none() {
                        return Some(value);
                    }
                }
            }
        }
        None
    }
}

/// An in-memory representation of an Ion Struct
/// ```
/// use ion_rs::{Element, ion_struct};
/// # use ion_rs::IonResult;
/// # fn main() -> IonResult<()> {
/// let struct_ = ion_struct! {
///   "foo": 1,
///   "bar": true,
///   "baz": "hello"
/// };
/// assert_eq!(struct_.len(), 3);
/// assert_eq!(struct_.get("baz"), Some(&Element::string("hello")));
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct Struct {
    fields: Fields,
}

impl Display for Struct {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut ivf = FmtValueFormatter { output: f };
        ivf.format_struct(self).map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}

impl Struct {
    pub fn builder() -> StructBuilder {
        StructBuilder::new()
    }

    pub fn clone_builder(&self) -> StructBuilder {
        StructBuilder::with_initial_fields(&self.fields.slots)
    }

    /// Returns an iterator over the field name/value pairs in this Struct.
    #[allow(clippy::map_identity)]
    // ^-- This is a temporary workaround for a bug in Clippy that should be fixed in the next release.
    // See: https://github.com/rust-lang/rust-clippy/issues/9280
    pub fn fields(&self) -> impl Iterator<Item = (&Symbol, &Element)> {
        self.fields
            .iter()
            // Here we convert from &(name, value) to (&name, &value).
            // The former makes a stronger assertion about how the data is being stored. We don't
            // want that to be a mandatory part of the public API.
            .map(|(name, element)| (name, element))
    }

    fn fields_eq(&self, other: &Self) -> bool {
        // For each distinct field name in `self`, check that `other` has the same
        // set of values for that field name.
        for (field_text, self_count) in self.fields.distinct_field_names() {
            let (other_iter, other_count) = match field_text {
                Some(text) => other.fields.get_all_with_count(text),
                None => other.fields.get_all_with_count(Symbol::unknown_text()),
            };

            if self_count != other_count {
                // The other struct has fields with the same name, but a different number of them.
                return false;
            }

            // Get all values for this field name in self
            let self_iter: FieldValuesIterator<'_> = match field_text {
                Some(text) => self.fields.get_all(text),
                None => self.fields.get_all(Symbol::unknown_text()),
            };

            for field_value in self_iter {
                if other_iter
                    .slots
                    .iter()
                    .filter(|(sym, _)| sym.text() == field_text)
                    .map(|(_, v)| v)
                    .all(|other_value| !field_value.ion_eq(other_value))
                {
                    // Couldn't find an equivalent field in the other struct
                    return false;
                }
            }
        }

        // If all of the above conditions hold, the two structs are equal.
        true
    }

    /// Returns the number of fields in this Struct.
    pub fn len(&self) -> usize {
        self.fields.slots.len()
    }

    /// Returns `true` if this struct has zero fields.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> FieldIterator<'_> {
        FieldIterator::new(&self.fields.slots)
    }

    /// Returns the value associated with the specified field name.
    ///
    /// If more than one field in this struct has that name, this method will return the value of
    /// the _last_ field with that name. To access other fields with the same name, see
    /// [`get_all`](Self::get_all).
    pub fn get<A: AsSymbolRef>(&self, field_name: A) -> Option<&Element> {
        self.fields.get_last(field_name)
    }

    /// Returns an iterator over all of the values associated with the specified field name.
    pub fn get_all<A: AsSymbolRef>(&self, field_name: A) -> impl Iterator<Item = &Element> {
        self.fields.get_all(field_name)
    }
}

// Allows `for (name, value) in &my_struct {...}` syntax
impl<'a> IntoIterator for &'a Struct {
    type Item = (&'a Symbol, &'a Element);
    type IntoIter = FieldIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

// Allows `for (name, value) in my_struct {...}` syntax
impl IntoIterator for Struct {
    type Item = (Symbol, Element);
    type IntoIter = OwnedFieldIterator;

    fn into_iter(self) -> Self::IntoIter {
        OwnedFieldIterator::new(self.fields.slots)
    }
}

impl<K, V> FromIterator<(K, V)> for Struct
where
    K: Into<Symbol>,
    V: Into<Element>,
{
    /// Returns an owned struct from the given iterator of field names/values.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let slots: Vec<(Symbol, Element)> = iter
            .into_iter()
            .map(|(k, v)| (k.into(), v.into()))
            .collect();
        let fields = Fields::new(slots);
        Self { fields }
    }
}

impl PartialEq for Struct {
    fn eq(&self, other: &Self) -> bool {
        // check if both fields have same length
        self.len() == other.len()
            // we need to test equality in both directions for both fields
            // A good example for this is annotated vs not annotated values in struct
            //  { a:4, a:4 } vs. { a:4, a:a::4 } // returns true
            //  { a:4, a:a::4 } vs. { a:4, a:4 } // returns false
            && self.fields_eq(other) && other.fields_eq(self)
    }
}

impl Eq for Struct {}

impl IonEq for Struct {
    fn ion_eq(&self, other: &Self) -> bool {
        self == other
    }
}

impl IonDataOrd for Struct {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        let mut these_fields = self.fields.slots.iter().collect::<Vec<_>>();
        let mut those_fields = other.fields.slots.iter().collect::<Vec<_>>();
        these_fields.sort_by(ion_cmp_field);
        those_fields.sort_by(ion_cmp_field);

        let mut i0 = these_fields.iter();
        let mut i1 = those_fields.iter();
        loop {
            match [i0.next(), i1.next()] {
                [None, Some(_)] => return Ordering::Less,
                [None, None] => return Ordering::Equal,
                [Some(_), None] => return Ordering::Greater,
                [Some(a), Some(b)] => {
                    let ord = ion_cmp_field(a, b);
                    if ord != Ordering::Equal {
                        return ord;
                    }
                }
            }
        }
    }
}

fn ion_cmp_field(this: &&(Symbol, Element), that: &&(Symbol, Element)) -> Ordering {
    let ord = this.0.ion_cmp(&that.0);
    if !ord.is_eq() {
        return ord;
    }
    IonDataOrd::ion_cmp(&this.1, &that.1)
}

impl IonDataHash for Struct {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        let mut these_fields = self.fields.slots.iter().collect::<Vec<_>>();
        these_fields.sort_by(ion_cmp_field);
        for (name, value) in these_fields {
            name.ion_data_hash(state);
            value.ion_data_hash(state);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::element::Element;
    use crate::ion_struct;

    #[test]
    fn for_field_in_struct() {
        // Simple example to exercise Struct's implementation of IntoIterator
        let s = ion_struct! { "foo": 1, "bar": 2, "baz": 3};
        let _fields = s.clone().iter().collect::<Vec<_>>(); // exercises `size_hint`
        let mut baz_value = None;
        for (name, value) in &s {
            if *name == "baz" {
                baz_value = Some(value);
            }
        }
        assert_eq!(baz_value, Some(&Element::int(3)));
    }

    #[test]
    fn for_field_in_owned_struct() {
        // Simple example to exercise Struct's implementation of IntoIterator
        let s = ion_struct! { "foo": 1, "bar": 2, "baz": 3};
        let _fields = s.clone().into_iter().collect::<Vec<_>>(); // exercises `size_hint`
        let mut baz_value = None;
        for (name, value) in s {
            if name == "baz" {
                baz_value = Some(value);
            }
        }
        assert_eq!(baz_value, Some(Element::int(3)));
    }
}
