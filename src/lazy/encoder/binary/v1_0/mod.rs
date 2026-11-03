use std::cell::RefCell;

use crate::lazy::encoder::binary::v1_0::writer::LazyRawBinaryWriter_1_0;
use crate::lazy::encoder::{Encoder, SymbolCreationPolicy};
use crate::lazy::encoding::BinaryEncoding_1_0;
use std::io::Write;

mod container_writers;
pub mod value_writer;
pub mod writer;

impl Encoder for BinaryEncoding_1_0 {
    const SUPPORTS_TEXT_TOKENS: bool = false;
    const DEFAULT_SYMBOL_CREATION_POLICY: SymbolCreationPolicy =
        SymbolCreationPolicy::RequireSymbolId;

    type Writer<W: Write> = LazyRawBinaryWriter_1_0<W>;
}

/// The initial capacity of a newly allocated encoding buffer, both top-level and per-container.
// This value was chosen somewhat arbitrarily and can be modified as needed. Choosing a value that
// is too low will lead to performance degradation as the buffer will require multiple
// reallocations/copies.
pub(crate) const DEFAULT_ENCODING_BUFFER_SIZE: usize = 512;

/// Pooled buffers shared by every value writer and container writer of a
/// [`LazyRawBinaryWriter_1_0`].
pub(crate) struct EncodingResources {
    // Emptied encoding buffers for length-prefixed containers to reuse. Container writers acquire
    // one when they open and release it when they close, so buffers stay warm across values and
    // flushes.
    buffers: RefCell<Vec<Vec<u8>>>,
}

impl EncodingResources {
    pub(crate) fn new() -> Self {
        Self {
            buffers: RefCell::new(Vec::new()),
        }
    }

    #[inline]
    pub(crate) fn acquire_buffer(&self) -> Vec<u8> {
        self.buffers
            .borrow_mut()
            .pop()
            .unwrap_or_else(|| Vec::with_capacity(DEFAULT_ENCODING_BUFFER_SIZE))
    }

    #[inline]
    pub(crate) fn release_buffer(&self, mut buffer: Vec<u8>) {
        buffer.clear();
        self.buffers.borrow_mut().push(buffer);
    }

    /// The number of bytes of memory held by the pooled buffers.
    pub(crate) fn retained_bytes(&self) -> usize {
        self.buffers.borrow().iter().map(Vec::capacity).sum()
    }
}

#[cfg(test)]
mod tests {
    use super::{EncodingResources, DEFAULT_ENCODING_BUFFER_SIZE};

    #[test]
    fn acquire_from_an_empty_pool_allocates_a_default_buffer() {
        let resources = EncodingResources::new();
        let buffer = resources.acquire_buffer();
        assert!(buffer.is_empty());
        assert_eq!(buffer.capacity(), DEFAULT_ENCODING_BUFFER_SIZE);
        assert_eq!(resources.retained_bytes(), 0);
    }

    #[test]
    fn released_buffer_is_emptied_and_reused_with_its_grown_capacity() {
        let resources = EncodingResources::new();
        let mut buffer = resources.acquire_buffer();
        buffer.extend_from_slice(&[0u8; DEFAULT_ENCODING_BUFFER_SIZE * 4]);
        let grown_capacity = buffer.capacity();
        // Precondition: the buffer outgrew the capacity a freshly allocated one would have, so the
        // assertions below can tell a reused buffer from a new one.
        assert!(grown_capacity > DEFAULT_ENCODING_BUFFER_SIZE);

        resources.release_buffer(buffer);
        assert_eq!(resources.retained_bytes(), grown_capacity);

        let reused = resources.acquire_buffer();
        assert!(
            reused.is_empty(),
            "a pooled buffer was handed out with stale content"
        );
        assert_eq!(reused.capacity(), grown_capacity);
        assert_eq!(resources.retained_bytes(), 0);
    }
}
