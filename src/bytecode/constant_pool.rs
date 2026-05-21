use std::sync::Arc;

use crate::{Decimal, Int, Timestamp};

/// A value stored in the constant pool.
///
/// Values too large to inline in a bytecode instruction (arbitrary-precision
/// integers, decimals, timestamps, strings, byte slices) are stored here and
/// referenced by index from CP-variant instructions.
///
/// Each variant wraps an `Arc` so that:
/// - Macro-owned constants persist across refills (refcount > 1 while
///   referenced by macro bytecode).
/// - User-value constants are freed when the pool is truncated (refcount
///   drops to 0).
/// - Cloning a constant for the caller is cheap (Arc::clone).
/// - Strings can be shared directly with `Symbol::shared(Arc<str>)`.
#[derive(Clone, Debug)]
pub(crate) enum Constant {
    BigInt(Arc<Int>),
    Decimal(Arc<Decimal>),
    Timestamp(Arc<Timestamp>),
    String(Arc<str>),
    Bytes(Arc<[u8]>),
}

/// A pool of constants referenced by bytecode CP-variant instructions.
///
/// Constants are added during bytecode generation and retrieved during
/// value materialization. The pool supports truncation so that ephemeral
/// user-value constants from a refill cycle can be discarded while
/// retaining macro-owned constants.
#[derive(Debug)]
pub(crate) struct ConstantPool {
    entries: Vec<Constant>,
}

impl ConstantPool {
    pub fn new() -> Self {
        Self {
            entries: Vec::with_capacity(32),
        }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Adds a constant and returns its index.
    pub fn add(&mut self, constant: Constant) -> u32 {
        let index = self.entries.len() as u32;
        self.entries.push(constant);
        index
    }

    /// Returns the constant at the given index.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    pub fn get(&self, index: u32) -> &Constant {
        &self.entries[index as usize]
    }

    /// Truncates the pool to `len`, dropping entries beyond that point.
    ///
    /// Used after refill to discard ephemeral user constants while
    /// retaining macro-owned constants (indices 0..len).
    pub fn truncate(&mut self, len: usize) {
        self.entries.truncate(len);
    }

    /// Removes all entries.
    pub fn clear(&mut self) {
        self.entries.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_and_get_big_int() {
        let mut pool = ConstantPool::new();
        let value = Int::from(i64::MAX as i128 + 1);
        let index = pool.add(Constant::BigInt(Arc::new(value.clone())));
        assert_eq!(index, 0);
        match pool.get(0) {
            Constant::BigInt(rc) => assert_eq!(**rc, value),
            _ => panic!("expected BigInt"),
        }
    }

    #[test]
    fn add_and_get_string() {
        let mut pool = ConstantPool::new();
        let index = pool.add(Constant::String(Arc::from("hello")));
        assert_eq!(index, 0);
        match pool.get(index) {
            Constant::String(rc) => assert_eq!(&**rc, "hello"),
            _ => panic!("expected String"),
        }
    }

    #[test]
    fn add_and_get_bytes() {
        let mut pool = ConstantPool::new();
        let data: &[u8] = &[0xCA, 0xFE, 0xBA, 0xBE];
        let index = pool.add(Constant::Bytes(Arc::from(data)));
        assert_eq!(index, 0);
        match pool.get(index) {
            Constant::Bytes(rc) => assert_eq!(&**rc, data),
            _ => panic!("expected Bytes"),
        }
    }

    #[test]
    fn multiple_entries_get_sequential_indices() {
        let mut pool = ConstantPool::new();
        let i0 = pool.add(Constant::BigInt(Arc::new(Int::from(1))));
        let i1 = pool.add(Constant::String(Arc::from("two")));
        let i2 = pool.add(Constant::BigInt(Arc::new(Int::from(3))));
        assert_eq!(i0, 0);
        assert_eq!(i1, 1);
        assert_eq!(i2, 2);
        assert_eq!(pool.len(), 3);
    }

    #[test]
    fn truncate_removes_trailing_entries() {
        let mut pool = ConstantPool::new();
        pool.add(Constant::BigInt(Arc::new(Int::from(1))));
        pool.add(Constant::BigInt(Arc::new(Int::from(2))));
        pool.add(Constant::BigInt(Arc::new(Int::from(3))));
        assert_eq!(pool.len(), 3);

        pool.truncate(1);
        assert_eq!(pool.len(), 1);
        // First entry is still accessible
        match pool.get(0) {
            Constant::BigInt(rc) => assert_eq!(**rc, Int::from(1)),
            _ => panic!("expected BigInt"),
        }
    }

    #[test]
    #[should_panic]
    fn get_after_truncate_panics() {
        let mut pool = ConstantPool::new();
        pool.add(Constant::BigInt(Arc::new(Int::from(1))));
        pool.add(Constant::BigInt(Arc::new(Int::from(2))));
        pool.truncate(1);
        // This should panic — index 1 was truncated.
        let _ = pool.get(1);
    }

    #[test]
    fn clear_removes_all_entries() {
        let mut pool = ConstantPool::new();
        pool.add(Constant::BigInt(Arc::new(Int::from(1))));
        pool.add(Constant::String(Arc::from("hello")));
        assert_eq!(pool.len(), 2);
        pool.clear();
        assert_eq!(pool.len(), 0);
    }

    #[test]
    fn rc_clone_survives_truncation() {
        let mut pool = ConstantPool::new();
        let value = Arc::new(Int::from(42));
        pool.add(Constant::BigInt(Arc::clone(&value)));
        // We hold a clone of the Arc outside the pool.
        pool.truncate(0);
        assert_eq!(pool.len(), 0);
        // The value is still accessible via our external Arc clone.
        assert_eq!(*value, Int::from(42));
    }
}
