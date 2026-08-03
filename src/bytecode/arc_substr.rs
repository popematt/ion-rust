use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// A zero-copy substring of an `Arc<str>`. Shares ownership of the
/// source buffer -- no allocation per value, just an Arc refcount bump.
#[derive(Clone)]
pub(crate) struct ArcSubstr {
    source: Arc<str>,
    offset: u32,
    len: u32,
}

impl ArcSubstr {
    #[inline]
    pub fn new(source: &Arc<str>, offset: u32, len: u32) -> Self {
        debug_assert!((offset as usize) + (len as usize) <= source.len());
        Self {
            source: Arc::clone(source),
            offset,
            len,
        }
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        &self.source[self.offset as usize..(self.offset + self.len) as usize]
    }
}

impl std::ops::Deref for ArcSubstr {
    type Target = str;
    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<str> for ArcSubstr {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl fmt::Debug for ArcSubstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl fmt::Display for ArcSubstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl PartialEq for ArcSubstr {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for ArcSubstr {}

impl Hash for ArcSubstr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

impl PartialOrd for ArcSubstr {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ArcSubstr {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_substr() {
        let source = Arc::from("hello world");
        let substr = ArcSubstr::new(&source, 6, 5);
        assert_eq!(substr.as_str(), "world");
        assert_eq!(&*substr, "world");
    }

    #[test]
    fn equality_and_hash() {
        use std::collections::hash_map::DefaultHasher;

        let source = Arc::from("foobar");
        let a = ArcSubstr::new(&source, 0, 3);
        let b = ArcSubstr::new(&source, 0, 3);
        assert_eq!(a, b);

        let hash_a = {
            let mut h = DefaultHasher::new();
            a.hash(&mut h);
            h.finish()
        };
        let hash_b = {
            let mut h = DefaultHasher::new();
            b.hash(&mut h);
            h.finish()
        };
        assert_eq!(hash_a, hash_b);
    }

    #[test]
    fn ordering() {
        let source = Arc::from("abcxyz");
        let a = ArcSubstr::new(&source, 0, 3); // "abc"
        let b = ArcSubstr::new(&source, 3, 3); // "xyz"
        assert!(a < b);
    }

    #[test]
    fn clone_shares_arc() {
        let source = Arc::from("shared");
        let original = ArcSubstr::new(&source, 0, 6);
        let cloned = original.clone();
        assert_eq!(original.as_str(), cloned.as_str());
        // Both hold a reference to the same Arc
        assert_eq!(Arc::strong_count(&source), 3);
    }
}
