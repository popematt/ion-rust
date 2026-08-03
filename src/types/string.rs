use crate::bytecode::arc_substr::ArcSubstr;
use crate::ion_data::{IonDataHash, IonDataOrd, IonEq};
use crate::text::text_formatter::FmtValueFormatter;
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};

/// Internal representation for `Str`.
#[derive(Clone)]
enum StrRepr {
    Owned(String),
    Source(ArcSubstr),
}

/// An owned, immutable in-memory representation of an Ion `string`.
///
/// ```
/// use ion_rs::Str;
/// let s: Str = "hello!".into();
/// assert_eq!(s, "hello!");
/// ```
pub struct Str {
    text: StrRepr,
}

impl Str {
    /// Returns the number of UTF-8 encoded bytes in this string.
    ///
    /// ```
    /// use ion_rs::Str;
    /// let s: Str = "hello!".into();
    /// assert_eq!(s.len(), 6);
    /// // Note that the length returned is a number of UTF-8 bytes, not codepoints or graphemes.
    /// let s: Str = "\u{1f680}\u{1f680}\u{1f680}".into();
    /// assert_eq!(s.len(), 12);
    /// ```
    pub fn len(&self) -> usize {
        self.text().len()
    }

    /// Returns `true` if this is the empty string (`""`); otherwise, returns `false`.
    ///
    /// ```
    /// use ion_rs::Str;
    /// let s: Str = "".into();
    /// assert!(s.is_empty());
    /// let s: Str = "hello!".into();
    /// assert!(!s.is_empty());
    /// ```
    // This method is largely here because clippy complains if you provide a `len()` method but not
    // an accompanying `is_empty()` method.
    pub fn is_empty(&self) -> bool {
        self.text().is_empty()
    }

    /// Returns a `&str` representation of this string's text.
    ///
    /// ```
    /// use ion_rs::Str;
    /// let s: Str = "hello, world!".into();
    /// assert!(s.text().contains("world"));
    /// assert!(s.text().is_ascii());
    /// ```
    pub fn text(&self) -> &str {
        match &self.text {
            StrRepr::Owned(s) => s.as_str(),
            StrRepr::Source(s) => s.as_str(),
        }
    }

    /// Creates a `Str` from a zero-copy source sub-slice.
    pub(crate) fn from_source(substr: ArcSubstr) -> Str {
        Str {
            text: StrRepr::Source(substr),
        }
    }
}

impl Clone for Str {
    fn clone(&self) -> Self {
        Str {
            text: self.text.clone(),
        }
    }
}

impl Debug for Str {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Str").field("text", &self.text()).finish()
    }
}

impl Hash for Str {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.text().hash(state)
    }
}

impl Eq for Str {}

impl PartialOrd for Str {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Str {
    fn cmp(&self, other: &Self) -> Ordering {
        self.text().cmp(other.text())
    }
}

impl Display for Str {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut formatter = FmtValueFormatter { output: f };
        formatter
            .format_string(self.as_ref())
            .map_err(|_| std::fmt::Error)
    }
}

impl From<&str> for Str {
    fn from(value: &str) -> Self {
        Str {
            text: StrRepr::Owned(value.to_string()),
        }
    }
}

impl From<String> for Str {
    fn from(value: String) -> Self {
        Str {
            text: StrRepr::Owned(value),
        }
    }
}

impl From<Str> for String {
    fn from(value: Str) -> Self {
        match value.text {
            StrRepr::Owned(s) => s,
            StrRepr::Source(s) => s.as_str().to_owned(),
        }
    }
}

impl AsRef<str> for Str {
    fn as_ref(&self) -> &str {
        self.text()
    }
}

impl<S> PartialEq<S> for Str
where
    S: AsRef<str>,
{
    fn eq(&self, other: &S) -> bool {
        let other_text: &str = other.as_ref();
        self.text() == other_text
    }
}

impl PartialEq<Str> for &str {
    fn eq(&self, other: &Str) -> bool {
        self.eq(&other.text())
    }
}

impl PartialEq<Str> for String {
    fn eq(&self, other: &Str) -> bool {
        let self_text: &str = self.as_str();
        self_text.eq(other.text())
    }
}

impl IonEq for Str {
    fn ion_eq(&self, other: &Self) -> bool {
        self == other
    }
}

impl IonDataOrd for Str {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.cmp(other)
    }
}

impl IonDataHash for Str {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        self.hash(state)
    }
}
