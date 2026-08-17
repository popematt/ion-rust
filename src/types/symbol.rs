use crate::bytecode::arc_substr::ArcSubstr;
use crate::ion_data::{IonDataHash, IonDataOrd, IonEq};
use crate::result::IonFailure;
use crate::{IonResult, SymbolRef};
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// A raw pointer to an `Arc<str>` held elsewhere (for example: arena
/// reader symbol table or constant pool).
///
/// # Safety
///
/// This pointer may only be constructed when the pointed-to `Arc<str>`
/// will remain at a stable address and live for the entire duration that
/// safe code can observe any `ArenaBorrowed` symbol using it.
#[derive(Copy, Clone, Debug)]
pub(crate) struct ArcStrRef(*const Arc<str>);

// SAFETY: `Arc<str>` is Send + Sync, and this wrapper only forwards
// shared access to the pointed-to value.
unsafe impl Send for ArcStrRef {}
unsafe impl Sync for ArcStrRef {}

impl PartialEq for ArcStrRef {
    fn eq(&self, other: &Self) -> bool {
        // SAFETY: Constructor invariants guarantee both pointers remain
        // valid while safe code can access them.
        unsafe { *self.0 == *other.0 }
    }
}

impl Eq for ArcStrRef {}

impl ArcStrRef {
    /// Creates a new `ArcStrRef`.
    ///
    /// # Safety
    ///
    /// `ptr` must point to a valid `Arc<str>` that remains at a stable
    /// address for the entire duration that this reference may be
    /// dereferenced through safe code.
    pub(crate) unsafe fn new(ptr: *const Arc<str>) -> Self {
        Self(ptr)
    }

    /// Returns the referenced text.
    ///
    /// # Safety
    ///
    /// Caller must ensure pointer remains valid.
    pub(crate) unsafe fn text(&self) -> &str {
        &**self.0
    }

    /// Clones the referenced `Arc<str>`.
    ///
    /// # Safety
    ///
    /// Caller must ensure pointer remains valid.
    pub(crate) unsafe fn to_arc(&self) -> Arc<str> {
        Arc::clone(&*self.0)
    }
}

/// Stores or points to the text of a given [Symbol].
#[derive(Debug, Eq)]
pub(crate) enum SymbolText {
    // This Symbol refers to a string in the active symbol table
    Shared(Arc<str>),
    // This Symbol owns its own text
    // TODO: Turn this into a Box<str>.
    //       Symbols are read-only, so there's no chance we'll add data to the `String`. Using
    //       a `Box<str>` shrinks this value from 24 bytes to 8 bytes.
    Owned(String),
    // This symbol has text that is statically defined (e.g. system symbol table text)
    Static(&'static str),
    // This Symbol borrows an existing `Arc<str>` slot via raw pointer.
    ArenaBorrowed(ArcStrRef),
    // This Symbol is a zero-copy sub-slice of a source buffer via Arc.
    SourceSlice(ArcSubstr),
    // This Symbol is equivalent to SID zero (`$0`)
    Unknown,
}

impl SymbolText {
    fn text(&self) -> Option<&str> {
        let text = match self {
            SymbolText::Shared(s) => s.as_ref(),
            SymbolText::Owned(s) => s.as_str(),
            SymbolText::Static(s) => s,
            // SAFETY: Constructor invariants guarantee pointer validity
            // for the duration of any observable borrow.
            SymbolText::ArenaBorrowed(ptr) => unsafe { ptr.text() },
            SymbolText::SourceSlice(s) => s.as_str(),
            SymbolText::Unknown => return None,
        };
        Some(text)
    }
}

impl Hash for SymbolText {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let text = self.text().unwrap_or("");
        text.hash(state)
    }
}

impl Clone for SymbolText {
    fn clone(&self) -> Self {
        match self {
            SymbolText::Owned(text) => SymbolText::Owned(text.to_owned()),
            SymbolText::Shared(text) => SymbolText::Shared(Arc::clone(text)),
            SymbolText::Static(text) => SymbolText::Static(text),
            SymbolText::ArenaBorrowed(ptr) => {
                // SAFETY: Same lifetime invariant as above. Cloning
                // upgrades to independently owned `Arc<str>`.
                SymbolText::Shared(unsafe { ptr.to_arc() })
            }
            SymbolText::SourceSlice(s) => SymbolText::SourceSlice(s.clone()),
            SymbolText::Unknown => SymbolText::Unknown,
        }
    }
}

impl PartialEq<Self> for SymbolText {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl PartialOrd<Self> for SymbolText {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SymbolText {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.text(), other.text()) {
            // If both Symbols have known text, delegate the comparison to their text.
            (Some(s1), Some(s2)) => s1.cmp(s2),
            // Otherwise, $0 (unknown text) is treated as 'less than' known text
            (Some(_), None) => Ordering::Greater,
            (None, Some(_)) => Ordering::Less,
            (None, None) => Ordering::Equal,
        }
    }
}

/// The text of a fully resolved field name, annotation, or symbol value. If the symbol has known
/// text (that is: the symbol is not `$0`), it will be stored as either a `String` or a shared
/// reference to text in a symbol table.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Symbol {
    pub(crate) text: SymbolText,
}

impl Symbol {
    pub fn owned<I: Into<String>>(text: I) -> Symbol {
        Symbol {
            text: SymbolText::Owned(text.into()),
        }
    }

    pub fn shared(text: Arc<str>) -> Symbol {
        Symbol {
            text: SymbolText::Shared(text),
        }
    }

    pub const fn static_text(text: &'static str) -> Symbol {
        Symbol {
            text: SymbolText::Static(text),
        }
    }

    pub fn unknown_text() -> Symbol {
        Symbol {
            text: SymbolText::Unknown,
        }
    }

    pub(crate) fn source_slice(substr: ArcSubstr) -> Symbol {
        Symbol {
            text: SymbolText::SourceSlice(substr),
        }
    }

    /// Creates a symbol that borrows an existing `Arc<str>` slot.
    ///
    /// # Safety
    ///
    /// `arc` must remain at a stable address and live for the entire
    /// duration that any safe code can observe the returned symbol.
    pub(crate) unsafe fn arena_borrowed(arc: &Arc<str>) -> Symbol {
        Symbol {
            text: SymbolText::ArenaBorrowed(unsafe { ArcStrRef::new(arc as *const Arc<str>) }),
        }
    }

    pub fn text(&self) -> Option<&str> {
        self.text.text()
    }

    pub fn expect_text(&self) -> IonResult<&str> {
        match self.text() {
            Some(text) => Ok(text),
            None => IonResult::decoding_error("symbol has unknown text"),
        }
    }
}

impl IonEq for Symbol {
    fn ion_eq(&self, other: &Self) -> bool {
        self == other
    }
}

impl IonDataOrd for Symbol {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.cmp(other)
    }
}

impl IonDataHash for Symbol {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        self.hash(state)
    }
}

// We cannot use a blanket impl for AsRef<str> as that would prevent us from
// optimizing the From<String> case, a conversion which can be performed
// without cloning.

impl From<&str> for Symbol {
    fn from(text: &str) -> Self {
        Symbol::owned(text)
    }
}

impl From<String> for Symbol {
    fn from(text: String) -> Self {
        Symbol::owned(text)
    }
}

impl From<&String> for Symbol {
    fn from(text: &String) -> Self {
        text.as_str().into()
    }
}

impl<'a> From<&'a Symbol> for Symbol {
    fn from(text: &'a Symbol) -> Self {
        text.clone()
    }
}

impl<'a> From<SymbolRef<'a>> for Symbol {
    fn from(symbol_ref: SymbolRef<'a>) -> Self {
        symbol_ref.to_owned()
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.text() {
            None => write!(f, "$0"),
            Some(text) => write!(f, "'{text}'"),
        }
    }
}

impl<A: AsRef<str>> PartialEq<A> for Symbol {
    fn eq(&self, other: &A) -> bool {
        self.text()
            // If the symbol has known text, compare it to the provide text
            .map(|t| t == other.as_ref())
            // If there's no text, it's definitely not equivalent to the provided text
            .unwrap_or(false)
    }
}

impl PartialEq<Symbol> for String {
    fn eq(&self, other: &Symbol) -> bool {
        other.text().map(|t| t == self.as_str()).unwrap_or(false)
    }
}

impl PartialEq<Symbol> for &str {
    fn eq(&self, other: &Symbol) -> bool {
        other.text().map(|t| &t == self).unwrap_or(false)
    }
}

// Note that if the Symbol has no text, this will return the empty string. This is unfortunate,
// but implementing this trait is necessary to allow `Symbol` to be used as a HashMap key.
// See issue https://github.com/amazon-ion/ion-rust/issues/444 for more information.
impl Borrow<str> for Symbol {
    fn borrow(&self) -> &str {
        // If the
        self.text().unwrap_or("")
    }
}

#[cfg(test)]
mod symbol_tests {
    use super::*;

    /// This is a test to ensure that the static_text function is const.
    const TEST_STATIC_TEXT_IS_CONST: Symbol = Symbol::static_text("foo");

    #[test]
    fn test_static_text_is_const() {
        // Uses the above `const` to prevent it from being considered dead code.
        assert_eq!(TEST_STATIC_TEXT_IS_CONST, "foo")
    }

    #[test]
    fn ordering_and_eq() {
        let mut symbols = vec![
            Symbol::owned("foo"),
            Symbol::shared(Arc::from("bar")),
            Symbol::shared(Arc::from("baz")),
            Symbol::owned("quux"),
        ];
        // Sort the list to demonstrate that our Ord implementation works.
        symbols.as_mut_slice().sort();
        // Equality testing doesn't depend on what kind of Symbol it is, just the text.
        // We can compare the sorted version of the vec above to this one and it will
        // be considered equal.
        let expected = vec![
            Symbol::owned("bar"),
            Symbol::owned("baz"),
            Symbol::owned("foo"),
            Symbol::owned("quux"),
        ];
        assert_eq!(symbols, expected)
    }

    #[test]
    fn partial_eq_str() {
        let symbols = vec![
            Symbol::shared(Arc::from("bar")),
            Symbol::shared(Arc::from("baz")),
            Symbol::owned("foo"),
            Symbol::owned("quux"),
        ];
        // Equality testing for a rust str with symbol
        let expected = vec!["bar", "baz", "foo", "quux"];
        assert_eq!(symbols, expected)
    }
}
