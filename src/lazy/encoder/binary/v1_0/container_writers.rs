use std::mem;

use crate::binary::var_uint::VarUInt;
use crate::lazy::encoder::binary::v1_0::value_writer::{BinaryValueWriter_1_0, MAX_INLINE_LENGTH};
use crate::lazy::encoder::binary::v1_0::EncodingResources;
use crate::lazy::encoder::value_writer::internal::{FieldEncoder, MakeValueWriter};
use crate::lazy::encoder::value_writer::{SequenceWriter, StructWriter};
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::result::cold_error;
use crate::{v1_0, ContextWriter, Encoding, IonResult, RawSymbolRef, ValueWriterConfig};

/// A helper type that holds fields and logic that is common to [`BinaryListWriter_1_0`],
/// [`BinarySExpWriter_1_0`], and [`BinaryStructWriter_1_0`].
pub struct BinaryContainerWriter_1_0<'value, 'top> {
    // A byte containing the high nibble of the encoded container's type descriptor.
    type_code: u8,
    // Pooled buffers shared with nested container writers
    resources: &'top EncodingResources,
    // The container's VarUInt-encoded annotation symbol IDs (if any), followed by its encoded
    // body. When this writer is finished encoding its own data, headers will be written to the
    // parent and then the annotations and body will be copied over.
    child_values_buffer: Vec<u8>,
    // The number of leading bytes in `child_values_buffer` that hold the annotations sequence.
    annotations_length: usize,
    parent_buffer: &'value mut Vec<u8>,
}

impl<'value, 'top> BinaryContainerWriter_1_0<'value, 'top> {
    pub fn new(
        type_code: u8,
        resources: &'top EncodingResources,
        buffer: &'value mut Vec<u8>,
    ) -> Self {
        Self {
            type_code,
            resources,
            child_values_buffer: resources.acquire_buffer(),
            annotations_length: 0,
            parent_buffer: buffer,
        }
    }

    /// Encodes `annotations` into the front of `child_values_buffer`.
    ///
    /// Must be called at most once, before any child value is written: everything already in the
    /// buffer would be counted as part of the annotations sequence.
    pub fn with_annotations<S: AsRawSymbolRef, I: IntoIterator<Item = S>>(
        mut self,
        annotations: I,
    ) -> IonResult<Self> {
        for annotation in annotations {
            let symbol_address = match annotation.as_raw_symbol_ref() {
                RawSymbolRef::SymbolId(symbol_id) => symbol_id,
                other_token => {
                    return cold_error!(
                        encoding_error,
                        "binary Ion 1.0 only supports symbol ID annotations (received '{other_token:?}')"
                    );
                }
            };
            VarUInt::write_u64(&mut self.child_values_buffer, symbol_address as u64)?;
        }
        // An empty iterator leaves `annotations_length` at 0, as though this was never called at
        // all. This prevents writing out an empty annotations sequence in binary, which is illegal.
        self.annotations_length = self.child_values_buffer.len();
        Ok(self)
    }

    pub fn child_values_buffer(&self) -> &[u8] {
        &self.child_values_buffer[self.annotations_length..]
    }

    pub fn end(mut self) -> IonResult<()> {
        let result = self.write_value_to_parent_buffer();
        self.resources
            .release_buffer(mem::take(&mut self.child_values_buffer));
        result
    }

    /// Encodes the container's annotations wrapper (if any) and header, then copies the
    /// annotations sequence and body bytes to the parent encoding buffer.
    fn write_value_to_parent_buffer(&mut self) -> IonResult<()> {
        let (annotations, body) = self.child_values_buffer.split_at(self.annotations_length);
        let parent = &mut *self.parent_buffer;
        if !annotations.is_empty() {
            // The container's header (including its length) is written after the annotations
            // sequence; factor its size into the annotations wrapper's declared length.
            let container_header_length = match body.len() {
                0..=MAX_INLINE_LENGTH => 1,
                length => 1 + VarUInt::encoded_size_of(length as u64),
            };
            let envelope_length = VarUInt::encoded_size_of(annotations.len() as u64)
                + annotations.len()
                + container_header_length
                + body.len();
            match envelope_length {
                0..=MAX_INLINE_LENGTH => parent.push(0xE0u8 | envelope_length as u8),
                _ => {
                    parent.push(0xEE); // Annotations wrapper w/VarUInt-encoded length
                    VarUInt::write_u64(parent, envelope_length as u64)?;
                }
            }
            VarUInt::write_u64(parent, annotations.len() as u64)?;
            parent.extend_from_slice(annotations);
        }

        // Write the appropriate opcode for a container of this length.
        match body.len() {
            encoded_length @ 0..=MAX_INLINE_LENGTH => {
                parent.push(self.type_code | encoded_length as u8);
            }
            encoded_length => {
                parent.push(self.type_code | 0x0E); // Container w/VarUInt length
                VarUInt::write_u64(parent, encoded_length as u64)?;
            }
        }
        parent.extend_from_slice(body);
        Ok(())
    }
}

pub struct BinaryListWriter_1_0<'value, 'top> {
    pub(crate) container_writer: BinaryContainerWriter_1_0<'value, 'top>,
}

impl<'value, 'top> BinaryListWriter_1_0<'value, 'top> {
    pub(crate) fn with_container_writer(
        container_writer: BinaryContainerWriter_1_0<'value, 'top>,
    ) -> Self {
        Self { container_writer }
    }

    pub(crate) fn new(resources: &'top EncodingResources, buffer: &'value mut Vec<u8>) -> Self {
        const LIST_TYPE_CODE: u8 = 0xB0;
        BinaryListWriter_1_0::with_container_writer(BinaryContainerWriter_1_0::new(
            LIST_TYPE_CODE,
            resources,
            buffer,
        ))
    }

    pub(crate) fn with_annotations<S: AsRawSymbolRef, I: IntoIterator<Item = S>>(
        mut self,
        annotations: I,
    ) -> IonResult<Self> {
        self.container_writer = self.container_writer.with_annotations(annotations)?;
        Ok(self)
    }
}

impl<'top> ContextWriter for BinaryListWriter_1_0<'_, 'top> {
    type NestedValueWriter<'a>
        = BinaryValueWriter_1_0<'a, 'top>
    where
        Self: 'a;
}

impl MakeValueWriter for BinaryListWriter_1_0<'_, '_> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        BinaryValueWriter_1_0::new(
            self.container_writer.resources,
            &mut self.container_writer.child_values_buffer,
        )
    }
}

impl SequenceWriter for BinaryListWriter_1_0<'_, '_> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.container_writer.end()
    }
}

impl<'top> ContextWriter for BinarySExpWriter_1_0<'_, 'top> {
    type NestedValueWriter<'a>
        = BinaryValueWriter_1_0<'a, 'top>
    where
        Self: 'a;
}

impl MakeValueWriter for BinarySExpWriter_1_0<'_, '_> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        BinaryValueWriter_1_0::new(
            self.container_writer.resources,
            &mut self.container_writer.child_values_buffer,
        )
    }
}

impl SequenceWriter for BinarySExpWriter_1_0<'_, '_> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.container_writer.end()
    }
}

pub struct BinarySExpWriter_1_0<'value, 'top> {
    container_writer: BinaryContainerWriter_1_0<'value, 'top>,
}

impl<'value, 'top> BinarySExpWriter_1_0<'value, 'top> {
    pub(crate) fn with_container_writer(
        container_writer: BinaryContainerWriter_1_0<'value, 'top>,
    ) -> Self {
        Self { container_writer }
    }

    pub(crate) fn new(resources: &'top EncodingResources, buffer: &'value mut Vec<u8>) -> Self {
        const SEXP_TYPE_CODE: u8 = 0xC0;
        let container_writer = BinaryContainerWriter_1_0::new(SEXP_TYPE_CODE, resources, buffer);
        Self::with_container_writer(container_writer)
    }

    pub(crate) fn with_annotations<S: AsRawSymbolRef, I: IntoIterator<Item = S>>(
        mut self,
        annotations: I,
    ) -> IonResult<Self> {
        self.container_writer = self.container_writer.with_annotations(annotations)?;
        Ok(self)
    }

    pub fn buffer(&self) -> &[u8] {
        self.container_writer.child_values_buffer()
    }
}

pub struct BinaryStructWriter_1_0<'value, 'top> {
    container_writer: BinaryContainerWriter_1_0<'value, 'top>,
}

impl<'value, 'top> BinaryStructWriter_1_0<'value, 'top> {
    pub(crate) fn with_container_writer(
        container: BinaryContainerWriter_1_0<'value, 'top>,
    ) -> Self {
        Self {
            container_writer: container,
        }
    }

    pub(crate) fn new(resources: &'top EncodingResources, buffer: &'value mut Vec<u8>) -> Self {
        const STRUCT_TYPE_CODE: u8 = 0xD0;
        Self::with_container_writer(BinaryContainerWriter_1_0::new(
            STRUCT_TYPE_CODE,
            resources,
            buffer,
        ))
    }

    pub(crate) fn with_annotations<S: AsRawSymbolRef, I: IntoIterator<Item = S>>(
        mut self,
        annotations: I,
    ) -> IonResult<Self> {
        self.container_writer = self.container_writer.with_annotations(annotations)?;
        Ok(self)
    }

    pub fn buffer(&self) -> &[u8] {
        self.container_writer.child_values_buffer()
    }
}

impl FieldEncoder for BinaryStructWriter_1_0<'_, '_> {
    fn encode_field_name(&mut self, name: impl AsRawSymbolRef) -> IonResult<()> {
        // Write the field name
        let sid = match name.as_raw_symbol_ref() {
            RawSymbolRef::SymbolId(sid) => sid,
            other => {
                return cold_error!(
                    encoding_error,
                    "the v1.0 raw binary writer only supports symbol ID struct field names, received {other:?}"
                );
            }
        };
        VarUInt::write_u64(&mut self.container_writer.child_values_buffer, sid as u64)?;
        Ok(())
    }
}

impl<'top> ContextWriter for BinaryStructWriter_1_0<'_, 'top> {
    type NestedValueWriter<'a>
        = BinaryValueWriter_1_0<'a, 'top>
    where
        Self: 'a;
}

impl MakeValueWriter for BinaryStructWriter_1_0<'_, '_> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        BinaryValueWriter_1_0::new(
            self.container_writer.resources,
            &mut self.container_writer.child_values_buffer,
        )
    }
}

impl StructWriter for BinaryStructWriter_1_0<'_, '_> {
    fn close(self) -> IonResult<()> {
        self.container_writer.end()
    }

    fn config(&self) -> ValueWriterConfig {
        v1_0::Binary::default_value_writer_config()
    }
}
