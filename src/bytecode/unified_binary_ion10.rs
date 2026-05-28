//! Unified Ion 1.0 binary bytecode generator.
//!
//! Implements Phase 2 of the generator consolidation plan: a single
//! generator struct generic over a `BinaryIonSource` trait, eliminating
//! the ~95% code duplication between `ion10.rs` (in-memory) and
//! `streaming_ion10.rs` (streaming).
//!
//! Two source implementations are provided:
//! - `InMemorySource<S: AsRef<[u8]>>` — direct access to a byte slice
//! - `StreamingSource<R: Read>` — buffered reads from an `impl Read`
//!
//! The `BinaryIonSource` trait abstracts byte access so the generator
//! code is written once. For in-memory sources, `ensure_available` is
//! a bounds check that the optimizer can often elide entirely.

use std::io::Read;
use std::ops::Neg;
use std::sync::Arc;

use crate::bytecode::constant_pool::{Constant, ConstantPool};
use crate::bytecode::generator::BytecodeGenerator;
use crate::bytecode::instruction::instr;
use crate::result::IonFailure;
use crate::{Decimal, Int, IonResult, Timestamp, UInt};

// ─── Constants ─────────────────────────────────────────────────────────

/// Ion 1.0 binary IVM bytes.
const IVM_BYTES: [u8; 4] = [0xE0, 0x01, 0x00, 0xEA];

/// Bit masks for VarUInt/VarInt encoding.
const VARINT_STOP_BIT: u8 = 0x80;
const VARINT_SIGN_BIT: u8 = 0x40;
const VARINT_FIRST_BYTE_DATA_MASK: u8 = 0x3F;
const VARUINT_DATA_MASK: u8 = 0x7F;

/// Ion 1.0 type codes (high nibble of type descriptor).
mod type_code {
    pub const NOP: u8 = 0;
    pub const BOOL: u8 = 1;
    pub const POS_INT: u8 = 2;
    pub const NEG_INT: u8 = 3;
    pub const FLOAT: u8 = 4;
    pub const DECIMAL: u8 = 5;
    pub const TIMESTAMP: u8 = 6;
    pub const SYMBOL: u8 = 7;
    pub const STRING: u8 = 8;
    pub const CLOB: u8 = 9;
    pub const BLOB: u8 = 10;
    pub const LIST: u8 = 11;
    pub const SEXP: u8 = 12;
    pub const STRUCT: u8 = 13;
    pub const ANNOTATION: u8 = 14;
}

/// Sentinel value for typed null (distinct from any valid length).
const NULL_SENTINEL: usize = usize::MAX;

/// Ion 1.0 system symbol SIDs.
mod system_symbol {
    pub const ION_SYMBOL_TABLE: u32 = 3;
    pub const SYMBOLS: u32 = 7;
}

/// Default internal buffer capacity for streaming sources.
const DEFAULT_BUFFER_CAPACITY: usize = 8 * 1024;

/// Minimum number of bytes to request in a single read call.
const MIN_READ_SIZE: usize = 4096;

// ─── BinaryIonSource trait ─────────────────────────────────────────────

/// Provides access to Ion binary bytes for parsing.
///
/// Implementations guarantee that after a successful
/// `ensure_available(n)` returning `Ok(true)`, at least `n` bytes
/// starting at `position()` are accessible via `bytes()`.
pub(crate) trait BinaryIonSource {
    /// The underlying byte slice. For in-memory sources, this is the
    /// complete input. For streaming sources, this is the internal
    /// buffer (stable between refills).
    fn bytes(&self) -> &[u8];

    /// Ensures at least `n` bytes are available from the current
    /// position. Returns `Ok(true)` if available, `Ok(false)` if EOF
    /// reached before `n` bytes could be obtained.
    ///
    /// For in-memory sources: a bounds check (optimized away by the
    /// compiler when provably in-bounds).
    /// For streaming sources: reads from the underlying `Read` and
    /// performs buffer growth as needed.
    fn ensure_available(&mut self, n: usize) -> IonResult<bool>;

    /// Current read position within `bytes()`.
    fn position(&self) -> usize;

    /// Advance the read position by `n` bytes.
    fn advance(&mut self, n: usize);

    /// Set the read position to an absolute offset.
    fn set_position(&mut self, pos: usize);

    /// The total number of valid bytes accessible via `bytes()`.
    fn filled(&self) -> usize;

    /// Returns whether the source is fully exhausted (no more data).
    fn is_exhausted(&self) -> bool;

    /// Compact the source buffer. For streaming sources, discards
    /// `consumed` bytes from the front. For in-memory sources, no-op.
    fn compact(&mut self, consumed: usize);
}

// ─── InMemorySource ────────────────────────────────────────────────────

/// An in-memory byte source for the unified binary generator.
///
/// All bytes are available up-front; `ensure_available` is a simple
/// bounds check that the optimizer can often eliminate entirely.
pub(crate) struct InMemorySource<S: AsRef<[u8]>> {
    source: S,
    position: usize,
}

impl<S: AsRef<[u8]>> InMemorySource<S> {
    pub fn new(source: S) -> Self {
        Self {
            source,
            position: 0,
        }
    }
}

impl<S: AsRef<[u8]>> BinaryIonSource for InMemorySource<S> {
    #[inline(always)]
    fn bytes(&self) -> &[u8] {
        self.source.as_ref()
    }

    #[inline(always)]
    fn ensure_available(&mut self, n: usize) -> IonResult<bool> {
        Ok(self.position + n <= self.source.as_ref().len())
    }

    #[inline(always)]
    fn position(&self) -> usize {
        self.position
    }

    #[inline(always)]
    fn advance(&mut self, n: usize) {
        self.position += n;
    }

    #[inline(always)]
    fn set_position(&mut self, pos: usize) {
        self.position = pos;
    }

    #[inline(always)]
    fn filled(&self) -> usize {
        self.source.as_ref().len()
    }

    #[inline(always)]
    fn is_exhausted(&self) -> bool {
        self.position >= self.source.as_ref().len()
    }

    #[inline(always)]
    fn compact(&mut self, _consumed: usize) {
        // No-op for in-memory sources.
    }
}

// ─── StreamingSource ───────────────────────────────────────────────────

/// A streaming byte source backed by an `impl Read`.
///
/// Manages an internal buffer, growing it as needed and compacting
/// consumed bytes at the start of each refill cycle.
pub(crate) struct StreamingSource<R: Read> {
    reader: R,
    buffer: Vec<u8>,
    /// Number of valid bytes in `buffer`.
    filled: usize,
    /// Current parse position within the buffer.
    position: usize,
    /// Whether EOF has been reached on the reader.
    eof: bool,
}

impl<R: Read> StreamingSource<R> {
    pub fn new(reader: R) -> Self {
        Self {
            reader,
            buffer: vec![0u8; DEFAULT_BUFFER_CAPACITY],
            filled: 0,
            position: 0,
            eof: false,
        }
    }

    #[allow(dead_code)]
    pub fn with_peeked(reader: R, peeked: &[u8]) -> Self {
        let capacity = DEFAULT_BUFFER_CAPACITY.max(peeked.len());
        let mut buffer = vec![0u8; capacity];
        buffer[..peeked.len()].copy_from_slice(peeked);
        Self {
            reader,
            buffer,
            filled: peeked.len(),
            position: 0,
            eof: false,
        }
    }

    /// Reads more data from the underlying reader into the buffer.
    fn read_more(&mut self) -> IonResult<()> {
        // Grow the buffer if needed
        if self.filled >= self.buffer.len() {
            let new_cap = self.buffer.len() * 2;
            self.buffer.resize(new_cap, 0);
        }

        // Ensure we request at least MIN_READ_SIZE bytes
        let available = self.buffer.len() - self.filled;
        if available < MIN_READ_SIZE {
            self.buffer.resize(self.filled + MIN_READ_SIZE, 0);
        }

        let n = self
            .reader
            .read(&mut self.buffer[self.filled..])
            .map_err(|e| {
                crate::IonError::decoding_error(format!("I/O error reading binary source: {e}"))
            })?;
        if n == 0 {
            self.eof = true;
        } else {
            self.filled += n;
        }
        Ok(())
    }
}

impl<R: Read> BinaryIonSource for StreamingSource<R> {
    #[inline(always)]
    fn bytes(&self) -> &[u8] {
        &self.buffer[..self.filled]
    }

    fn ensure_available(&mut self, n: usize) -> IonResult<bool> {
        while self.filled - self.position < n {
            if self.eof {
                return Ok(false);
            }
            self.read_more()?;
        }
        Ok(true)
    }

    #[inline(always)]
    fn position(&self) -> usize {
        self.position
    }

    #[inline(always)]
    fn advance(&mut self, n: usize) {
        self.position += n;
    }

    #[inline(always)]
    fn set_position(&mut self, pos: usize) {
        self.position = pos;
    }

    #[inline(always)]
    fn filled(&self) -> usize {
        self.filled
    }

    #[inline(always)]
    fn is_exhausted(&self) -> bool {
        self.filled - self.position == 0 && self.eof
    }

    fn compact(&mut self, consumed: usize) {
        if consumed > 0 {
            self.buffer.copy_within(consumed..self.filled, 0);
            self.filled -= consumed;
            self.position -= consumed;
        }
    }
}

// ─── Unified Generator ─────────────────────────────────────────────────

/// A unified Ion 1.0 binary bytecode generator, generic over the byte
/// source.
///
/// For in-memory use: `UnifiedBinaryIon10Generator<InMemorySource<&[u8]>>`
/// For streaming use: `UnifiedBinaryIon10Generator<StreamingSource<R>>`
pub struct UnifiedBinaryIon10Generator<S: BinaryIonSource> {
    source: S,
}

impl<S: BinaryIonSource> UnifiedBinaryIon10Generator<S> {
    /// Creates a new unified generator from the given source.
    pub fn new(source: S) -> Self {
        Self { source }
    }

    /// Returns a byte at the given position in the source.
    #[inline(always)]
    fn byte_at(&self, pos: usize) -> u8 {
        self.source.bytes()[pos]
    }

    /// Returns a slice of the source bytes.
    #[inline(always)]
    fn bytes_range(&self, start: usize, len: usize) -> &[u8] {
        &self.source.bytes()[start..start + len]
    }

    /// Returns the current position.
    #[inline(always)]
    fn position(&self) -> usize {
        self.source.position()
    }

    /// Sets the current position.
    #[inline(always)]
    fn set_position(&mut self, pos: usize) {
        self.source.set_position(pos);
    }

    /// Advances the position by n bytes.
    #[inline(always)]
    fn advance(&mut self, n: usize) {
        self.source.advance(n);
    }

    /// Reads a VarUInt at the current position.
    fn read_var_uint(&mut self) -> usize {
        let mut result: usize = 0;
        loop {
            let byte = self.byte_at(self.position());
            self.advance(1);
            result = (result << 7) | (byte & VARUINT_DATA_MASK) as usize;
            if byte & VARINT_STOP_BIT != 0 {
                return result;
            }
        }
    }

    /// Reads an unsigned integer of the given byte length.
    fn read_uint(&mut self, length: usize) -> u64 {
        let pos = self.position();
        let mut result: u64 = 0;
        for i in 0..length {
            result = (result << 8) | self.byte_at(pos + i) as u64;
        }
        self.advance(length);
        result
    }

    /// Reads a type descriptor byte and returns (type_code, length).
    fn read_type_descriptor(&mut self) -> (u8, usize) {
        let td = self.byte_at(self.position());
        self.advance(1);
        let tc = td >> 4;
        let low = td & 0x0F;

        match tc {
            type_code::NOP => {
                if low == 0x0F {
                    (tc, NULL_SENTINEL)
                } else if low == 0x0E {
                    let length = self.read_var_uint();
                    (tc, length)
                } else {
                    (tc, low as usize)
                }
            }
            type_code::ANNOTATION => {
                if low == 0x0E {
                    let length = self.read_var_uint();
                    (tc, length)
                } else {
                    (tc, low as usize)
                }
            }
            type_code::STRUCT => {
                if low == 0x0F {
                    (tc, NULL_SENTINEL)
                } else if low == 0x0E || low == 0x01 {
                    let length = self.read_var_uint();
                    (tc, length)
                } else {
                    (tc, low as usize)
                }
            }
            _ => {
                if low == 0x0F {
                    (tc, NULL_SENTINEL)
                } else if low == 0x0E {
                    let length = self.read_var_uint();
                    (tc, length)
                } else {
                    (tc, low as usize)
                }
            }
        }
    }

    /// Checks if the current position starts an IVM sequence.
    fn is_at_ivm(&self) -> bool {
        let pos = self.position();
        pos + 4 <= self.source.filled() && self.bytes_range(pos, 4) == IVM_BYTES
    }

    /// Determines the total byte size of a top-level value starting at
    /// the current position (for streaming pre-read). Does NOT advance
    /// position.
    fn determine_value_size(&mut self) -> IonResult<Option<usize>> {
        if !self.source.ensure_available(1)? {
            return Ok(None);
        }

        let start = self.position();
        let td = self.byte_at(start);
        let tc = td >> 4;
        let low = td & 0x0F;

        let mut header_size: usize = 1;

        let body_length: usize = match tc {
            type_code::NOP => {
                if low == 0x0F {
                    0
                } else if low == 0x0E {
                    match self.read_varuint_at(start + 1, &mut header_size)? {
                        Some(len) => len,
                        None => return Ok(None),
                    }
                } else {
                    low as usize
                }
            }
            type_code::BOOL => {
                // For bool, the low nibble encodes the value (0/1),
                // not a body length. The bool has no body bytes.
                0
            }
            type_code::ANNOTATION => {
                if low == 0x0E {
                    match self.read_varuint_at(start + 1, &mut header_size)? {
                        Some(len) => len,
                        None => return Ok(None),
                    }
                } else {
                    low as usize
                }
            }
            type_code::STRUCT => {
                if low == 0x0F {
                    0
                } else if low == 0x0E || low == 0x01 {
                    match self.read_varuint_at(start + 1, &mut header_size)? {
                        Some(len) => len,
                        None => return Ok(None),
                    }
                } else {
                    low as usize
                }
            }
            _ => {
                if low == 0x0F {
                    0
                } else if low == 0x0E {
                    match self.read_varuint_at(start + 1, &mut header_size)? {
                        Some(len) => len,
                        None => return Ok(None),
                    }
                } else {
                    low as usize
                }
            }
        };

        let total = header_size + body_length;
        if !self.source.ensure_available(total)? {
            return Ok(None);
        }
        Ok(Some(total))
    }

    /// Helper: reads a VarUInt starting at `offset` without advancing
    /// position. Updates `header_size` with VarUInt byte count.
    fn read_varuint_at(
        &mut self,
        offset: usize,
        header_size: &mut usize,
    ) -> IonResult<Option<usize>> {
        let mut result: usize = 0;
        let mut pos = offset;
        loop {
            let needed = pos - self.position() + 1;
            if !self.source.ensure_available(needed)? {
                return Ok(None);
            }
            let byte = self.byte_at(pos);
            pos += 1;
            *header_size += 1;
            result = (result << 7) | (byte & VARUINT_DATA_MASK) as usize;
            if byte & VARINT_STOP_BIT != 0 {
                return Ok(Some(result));
            }
        }
    }

    /// Reads a VarUInt safely (used for streaming NOP padding).
    fn read_var_uint_safe(&mut self) -> IonResult<usize> {
        let mut result: usize = 0;
        loop {
            if !self.source.ensure_available(1)? {
                return IonResult::decoding_error("unexpected EOF reading VarUInt");
            }
            let byte = self.byte_at(self.position());
            self.advance(1);
            result = (result << 7) | (byte & VARUINT_DATA_MASK) as usize;
            if byte & VARINT_STOP_BIT != 0 {
                return Ok(result);
            }
        }
    }

    /// Emits bytecode for a single value. Returns `true` if it was an LST.
    fn emit_value(&mut self, destination: &mut Vec<u32>, constant_pool: &mut ConstantPool) -> bool {
        let (tc, length) = self.read_type_descriptor();
        self.emit_value_body(tc, length, destination, constant_pool)
    }

    /// Emits the body of a value given its type code and length.
    fn emit_value_body(
        &mut self,
        tc: u8,
        length: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> bool {
        if length == NULL_SENTINEL && tc <= type_code::STRUCT {
            self.emit_null(tc, destination);
            return false;
        }

        match tc {
            type_code::NOP => {
                self.advance(length);
            }
            type_code::BOOL => {
                self.emit_bool(length, destination);
            }
            type_code::POS_INT | type_code::NEG_INT => {
                self.emit_int(tc, length, destination, constant_pool);
            }
            type_code::FLOAT => {
                self.emit_float(length, destination);
            }
            type_code::DECIMAL => {
                self.emit_decimal(length, destination);
            }
            type_code::TIMESTAMP => {
                self.emit_timestamp_ref(length, destination);
            }
            type_code::SYMBOL => {
                self.emit_symbol(length, destination);
            }
            type_code::STRING => {
                self.emit_string(length, destination);
            }
            type_code::CLOB => {
                self.emit_lob_ref(instr::CLOB_REF, length, destination);
            }
            type_code::BLOB => {
                self.emit_lob_ref(instr::BLOB_REF, length, destination);
            }
            type_code::LIST => {
                self.emit_container(instr::LIST_START, length, false, destination, constant_pool);
            }
            type_code::SEXP => {
                self.emit_container(instr::SEXP_START, length, false, destination, constant_pool);
            }
            type_code::STRUCT => {
                self.emit_container(
                    instr::STRUCT_START,
                    length,
                    true,
                    destination,
                    constant_pool,
                );
            }
            type_code::ANNOTATION => {
                return self.emit_annotation_wrapper(length, destination, constant_pool);
            }
            _ => {
                self.advance(length);
            }
        }
        false
    }

    /// Emits a typed null instruction.
    fn emit_null(&self, tc: u8, destination: &mut Vec<u32>) {
        let null_instr = match tc {
            type_code::BOOL => instr::NULL_BOOL,
            type_code::POS_INT | type_code::NEG_INT => instr::NULL_INT,
            type_code::FLOAT => instr::NULL_FLOAT,
            type_code::DECIMAL => instr::NULL_DECIMAL,
            type_code::TIMESTAMP => instr::NULL_TIMESTAMP,
            type_code::SYMBOL => instr::NULL_SYMBOL,
            type_code::STRING => instr::NULL_STRING,
            type_code::CLOB => instr::NULL_CLOB,
            type_code::BLOB => instr::NULL_BLOB,
            type_code::LIST => instr::NULL_LIST,
            type_code::SEXP => instr::NULL_SEXP,
            type_code::STRUCT => instr::NULL_STRUCT,
            _ => instr::NULL_NULL,
        };
        destination.push(null_instr);
    }

    /// Emits a boolean value.
    fn emit_bool(&self, low_nibble: usize, destination: &mut Vec<u32>) {
        let value = if low_nibble == 0 { 0u32 } else { 1u32 };
        destination.push(instr::BOOL | value);
    }

    /// Emits an integer value.
    fn emit_int(
        &mut self,
        tc: u8,
        length: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) {
        if length == 0 {
            destination.push(instr::INT_I16);
            return;
        }

        let is_negative = tc == type_code::NEG_INT;

        if length <= 8 {
            let magnitude = self.read_uint(length);
            self.emit_int_from_magnitude(magnitude, is_negative, destination, constant_pool);
        } else {
            self.emit_big_int(length, is_negative, destination, constant_pool);
        }
    }

    /// Given a magnitude and sign, emits the appropriate integer instruction.
    fn emit_int_from_magnitude(
        &self,
        magnitude: u64,
        is_negative: bool,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) {
        if !is_negative {
            if magnitude <= i16::MAX as u64 {
                destination.push(instr::INT_I16 | magnitude as u32);
            } else if magnitude <= i32::MAX as u64 {
                destination.push(instr::INT_I32);
                destination.push(magnitude as u32);
            } else if magnitude <= i64::MAX as u64 {
                let v = magnitude as i64;
                destination.push(instr::INT_I64);
                destination.push((v >> 32) as u32);
                destination.push(v as u32);
            } else {
                let value = Int::from(magnitude as i128);
                let idx = constant_pool.add(Constant::BigInt(Arc::new(value)));
                destination.push(instr::INT_CP | idx);
            }
        } else {
            let neg_value = -(magnitude as i128);
            if neg_value >= i16::MIN as i128 {
                destination.push(instr::INT_I16 | (neg_value as i16 as u16 as u32));
            } else if neg_value >= i32::MIN as i128 {
                destination.push(instr::INT_I32);
                destination.push(neg_value as i32 as u32);
            } else if neg_value >= i64::MIN as i128 {
                let v = neg_value as i64;
                destination.push(instr::INT_I64);
                destination.push((v >> 32) as u32);
                destination.push(v as u32);
            } else {
                let value = Int::from(neg_value);
                let idx = constant_pool.add(Constant::BigInt(Arc::new(value)));
                destination.push(instr::INT_CP | idx);
            }
        }
    }

    /// Emits a big integer (> 8 bytes) using the constant pool.
    fn emit_big_int(
        &mut self,
        length: usize,
        is_negative: bool,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) {
        let pos = self.position();
        let bytes = self.bytes_range(pos, length);
        let magnitude = UInt::from_be_bytes(bytes);
        let value: Int = if is_negative {
            Int::from(&magnitude).neg()
        } else {
            Int::from(&magnitude)
        };
        self.advance(length);
        let idx = constant_pool.add(Constant::BigInt(Arc::new(value)));
        destination.push(instr::INT_CP | idx);
    }

    /// Emits a float value.
    fn emit_float(&mut self, length: usize, destination: &mut Vec<u32>) {
        match length {
            0 => {
                destination.push(instr::FLOAT_F32);
                destination.push(0u32);
            }
            4 => {
                let bits = self.read_uint(4) as u32;
                destination.push(instr::FLOAT_F32);
                destination.push(bits);
            }
            8 => {
                let bits = self.read_uint(8);
                destination.push(instr::FLOAT_F64);
                destination.push((bits >> 32) as u32);
                destination.push(bits as u32);
            }
            _ => {
                self.advance(length);
            }
        }
    }

    /// Emits a decimal value as DECIMAL_REF.
    fn emit_decimal(&mut self, length: usize, destination: &mut Vec<u32>) {
        if length == 0 {
            destination.push(instr::DECIMAL_REF);
            destination.push(self.position() as u32);
            return;
        }
        let offset = self.position() as u32;
        debug_assert!(
            length as u32 <= 0x003F_FFFF,
            "decimal length exceeds 22-bit data field"
        );
        destination.push(instr::DECIMAL_REF | (length as u32 & 0x003F_FFFF));
        destination.push(offset);
        self.advance(length);
    }

    /// Emits a timestamp value as TIMESTAMP_REF.
    fn emit_timestamp_ref(&mut self, length: usize, destination: &mut Vec<u32>) {
        let offset = self.position() as u32;
        debug_assert!(
            length as u32 <= 0x003F_FFFF,
            "timestamp length exceeds 22-bit data field"
        );
        destination.push(instr::TIMESTAMP_REF | (length as u32 & 0x003F_FFFF));
        destination.push(offset);
        self.advance(length);
    }

    /// Emits a symbol value as SYMBOL_SID.
    fn emit_symbol(&mut self, length: usize, destination: &mut Vec<u32>) {
        if length == 0 {
            destination.push(instr::SYMBOL_SID);
            return;
        }
        let sid = self.read_uint(length) as u32;
        debug_assert!(sid <= 0x003F_FFFF, "SID exceeds 22-bit data field");
        destination.push(instr::SYMBOL_SID | (sid & 0x003F_FFFF));
    }

    /// Emits a string as STRING_REF.
    fn emit_string(&mut self, length: usize, destination: &mut Vec<u32>) {
        let offset = self.position() as u32;
        debug_assert!(
            length as u32 <= 0x003F_FFFF,
            "string length exceeds 22-bit data field"
        );
        destination.push(instr::STRING_REF | (length as u32 & 0x003F_FFFF));
        destination.push(offset);
        self.advance(length);
    }

    /// Emits a lob (blob or clob) as a REF instruction.
    fn emit_lob_ref(&mut self, instr_base: u32, length: usize, destination: &mut Vec<u32>) {
        let offset = self.position() as u32;
        debug_assert!(
            length as u32 <= 0x003F_FFFF,
            "lob length exceeds 22-bit data field"
        );
        destination.push(instr_base | (length as u32 & 0x003F_FFFF));
        destination.push(offset);
        self.advance(length);
    }

    /// Emits a container (list, sexp, or struct).
    fn emit_container(
        &mut self,
        start_instr: u32,
        content_length: usize,
        is_struct: bool,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) {
        let start_index = destination.len();
        destination.push(0); // placeholder

        let end_position = self.position() + content_length;
        while self.position() < end_position {
            if is_struct {
                let field_sid = self.read_var_uint() as u32;

                // Check for NOP padding in structs
                let peek_td = self.byte_at(self.position());
                let peek_tc = peek_td >> 4;
                let peek_low = peek_td & 0x0F;
                if peek_tc == type_code::NOP && peek_low != 0x0F {
                    let (_nop_tc, nop_length) = self.read_type_descriptor();
                    self.advance(nop_length);
                    continue;
                }

                debug_assert!(
                    field_sid <= 0x003F_FFFF,
                    "field name SID exceeds 22-bit data field"
                );
                destination.push(instr::FIELD_NAME_SID | (field_sid & 0x003F_FFFF));
            }
            let _ = self.emit_value(destination, constant_pool);
        }

        destination.push(instr::END_CONTAINER);
        let bytecode_length = destination.len() - start_index - 1;
        debug_assert!(
            bytecode_length <= 0x003F_FFFF,
            "container bytecode length exceeds 22-bit data field"
        );
        destination[start_index] = start_instr | (bytecode_length as u32 & 0x003F_FFFF);
    }

    /// Emits an annotation wrapper.
    /// Returns `true` if this was a local symbol table (system value).
    fn emit_annotation_wrapper(
        &mut self,
        wrapper_length: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> bool {
        let wrapper_end = self.position() + wrapper_length;

        // Read annotations length (VarUInt)
        let annot_length = self.read_var_uint();
        let annot_end = self.position() + annot_length;

        // Collect annotation SIDs
        let mut annotation_sids = Vec::new();
        while self.position() < annot_end {
            let sid = self.read_var_uint() as u32;
            annotation_sids.push(sid);
        }

        // Check for LST
        if annotation_sids.len() == 1
            && annotation_sids[0] == system_symbol::ION_SYMBOL_TABLE
            && self.position() < wrapper_end
        {
            let peek_td = self.byte_at(self.position());
            let peek_tc = peek_td >> 4;
            if peek_tc == type_code::STRUCT {
                self.parse_local_symbol_table(wrapper_end, destination);
                return true;
            }
        }

        // Not an LST -- emit annotation SIDs
        for sid in annotation_sids {
            debug_assert!(
                sid <= 0x003F_FFFF,
                "annotation SID exceeds 22-bit data field"
            );
            destination.push(instr::ANNOTATION_SID | (sid & 0x003F_FFFF));
        }

        // Emit the annotated value
        let _ = self.emit_value(destination, constant_pool);

        // Advance to wrapper_end
        self.set_position(wrapper_end);
        false
    }

    /// Parses a local symbol table struct and emits a
    /// `DIRECTIVE_SET_SYMBOLS` directive.
    fn parse_local_symbol_table(&mut self, wrapper_end: usize, destination: &mut Vec<u32>) {
        let (tc, struct_length) = self.read_type_descriptor();
        debug_assert_eq!(tc, type_code::STRUCT);
        let struct_end = self.position() + struct_length;

        let mut new_symbols: Vec<Option<(usize, usize)>> = Vec::new();

        while self.position() < struct_end {
            let field_sid = self.read_var_uint() as u32;
            let (value_tc, value_length) = self.read_type_descriptor();

            if field_sid == system_symbol::SYMBOLS && value_tc == type_code::LIST {
                let list_end = self.position() + value_length;
                while self.position() < list_end {
                    let (elem_tc, elem_length) = self.read_type_descriptor();
                    if elem_tc == type_code::STRING && elem_length != NULL_SENTINEL {
                        new_symbols.push(Some((self.position(), elem_length)));
                        self.advance(elem_length);
                    } else if elem_length == NULL_SENTINEL {
                        new_symbols.push(None);
                    } else {
                        new_symbols.push(None);
                        self.advance(elem_length);
                    }
                }
            } else {
                // Skip fields we don't care about
                if value_length != NULL_SENTINEL {
                    self.advance(value_length);
                }
            }
        }

        // Emit the DIRECTIVE_SET_SYMBOLS bytecode
        destination.push(instr::DIRECTIVE_SET_SYMBOLS);
        for entry in &new_symbols {
            match entry {
                Some((offset, length)) => {
                    destination.push(instr::STRING_REF | *length as u32);
                    destination.push(*offset as u32);
                }
                None => {
                    destination.push(instr::SYMBOL_SID);
                }
            }
        }
        destination.push(instr::END_CONTAINER);

        self.set_position(wrapper_end);
    }
}

// ─── BytecodeGenerator impl ────────────────────────────────────────────

/// Reads a VarUInt from a byte slice (for `read_*_ref` methods).
fn read_var_uint_from_slice(bytes: &[u8], pos: &mut usize) -> IonResult<u32> {
    let mut result: u32 = 0;
    let mut bytes_read: usize = 0;
    loop {
        if *pos >= bytes.len() {
            return IonResult::decoding_error("unterminated VarUInt in timestamp field");
        }
        bytes_read += 1;
        if bytes_read > 5 {
            return IonResult::decoding_error("VarUInt exceeds u32 range");
        }
        let byte = bytes[*pos];
        *pos += 1;
        result = (result << 7) | (byte & VARUINT_DATA_MASK) as u32;
        if byte & VARINT_STOP_BIT != 0 {
            return Ok(result);
        }
    }
}

/// Reads a signed VarInt from a byte slice.
fn read_var_int_from_slice(bytes: &[u8], pos: &mut usize) -> IonResult<i64> {
    if *pos >= bytes.len() {
        return IonResult::decoding_error("unexpected end of data reading VarInt");
    }
    let first = bytes[*pos];
    *pos += 1;
    let is_negative = (first & VARINT_SIGN_BIT) != 0;
    let mut magnitude: i64 = (first & VARINT_FIRST_BYTE_DATA_MASK) as i64;

    if (first & VARINT_STOP_BIT) == 0 {
        let mut bytes_read: usize = 1;
        loop {
            if *pos >= bytes.len() {
                return IonResult::decoding_error("unterminated VarInt");
            }
            if bytes_read > 9 {
                return IonResult::decoding_error("VarInt exceeds i64 range");
            }
            let byte = bytes[*pos];
            *pos += 1;
            bytes_read += 1;
            magnitude = (magnitude << 7) | (byte & VARUINT_DATA_MASK) as i64;
            if (byte & VARINT_STOP_BIT) != 0 {
                break;
            }
        }
    }

    Ok(if is_negative { -magnitude } else { magnitude })
}

impl<S: BinaryIonSource> BytecodeGenerator for UnifiedBinaryIon10Generator<S> {
    fn refill(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        // Compact: discard consumed bytes from previous refill cycle.
        let consumed = self.source.position();
        self.source.compact(consumed);

        // Try to get at least 1 byte to check for exhaustion.
        if !self.source.ensure_available(1)? {
            destination.push(instr::END_OF_INPUT);
            return Ok(());
        }

        // Process top-level values until we hit an IVM, LST, or EOF.
        loop {
            if self.source.is_exhausted() {
                destination.push(instr::END_OF_INPUT);
                return Ok(());
            }

            if !self.source.ensure_available(1)? {
                destination.push(instr::END_OF_INPUT);
                return Ok(());
            }

            // Check for IVM (need 4 bytes)
            if self.source.ensure_available(4)? && self.is_at_ivm() {
                self.advance(4);
                let version_data = 1u32 << 8;
                destination.push(instr::IVM | version_data);
                destination.push(instr::REFILL);
                return Ok(());
            }

            // Peek at the type descriptor to check for NOP at top level
            let td = self.byte_at(self.position());
            let tc = td >> 4;
            let low = td & 0x0F;

            if tc == type_code::NOP && low != 0x0F {
                // Skip NOP padding
                self.advance(1);
                if low == 0x0E {
                    let pad_len = self.read_var_uint_safe()?;
                    if !self.source.ensure_available(pad_len)? {
                        return IonResult::decoding_error("unexpected EOF in NOP padding");
                    }
                    self.advance(pad_len);
                } else {
                    if !self.source.ensure_available(low as usize)? {
                        return IonResult::decoding_error("unexpected EOF in NOP padding");
                    }
                    self.advance(low as usize);
                }
                continue;
            }

            // For streaming: determine full value size and buffer it.
            let value_size = self.determine_value_size()?;
            match value_size {
                Some(_size) => {
                    let is_system_value = self.emit_value(destination, constant_pool);
                    if is_system_value {
                        destination.push(instr::REFILL);
                        return Ok(());
                    }
                }
                None => {
                    return IonResult::decoding_error(
                        "unexpected EOF: incomplete value in binary stream",
                    );
                }
            }
        }
    }

    fn read_int_ref(&self, position: u32, length: u32) -> IonResult<Int> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.source.filled() {
            return IonResult::decoding_error("int reference out of bounds");
        }
        let bytes = self.bytes_range(start, length as usize);
        if length <= 16 {
            let mut buf = [0u8; 16];
            let pad = if !bytes.is_empty() && (bytes[0] & 0x80) != 0 {
                0xFF
            } else {
                0x00
            };
            buf[..16 - bytes.len()].fill(pad);
            buf[16 - bytes.len()..].copy_from_slice(bytes);
            let value = i128::from_be_bytes(buf);
            Ok(Int::from(value))
        } else {
            let mut le_bytes: Vec<u8> = bytes.to_vec();
            le_bytes.reverse();
            Ok(Int::from_le_signed_bytes(&le_bytes))
        }
    }

    fn read_decimal_ref(&self, position: u32, length: u32) -> IonResult<Decimal> {
        if length == 0 {
            return Ok(Decimal::new(0i32, 0i64));
        }

        let start = position as usize;
        let end = start + length as usize;
        if end > self.source.filled() {
            return IonResult::decoding_error("decimal reference out of bounds");
        }
        let bytes = self.bytes_range(start, length as usize);

        let mut exp_pos: usize = 0;
        let exponent = read_var_int_from_slice(bytes, &mut exp_pos)?;
        let coeff_bytes = &bytes[exp_pos..];

        if coeff_bytes.is_empty() {
            return Ok(Decimal::new(0i32, exponent));
        }

        let is_negative_coeff = (coeff_bytes[0] & 0x80) != 0;

        if coeff_bytes.len() <= 16 {
            let first_magnitude_byte = (coeff_bytes[0] & 0x7F) as u128;
            let magnitude = coeff_bytes[1..]
                .iter()
                .fold(first_magnitude_byte, |acc, &b| (acc << 8) | b as u128);

            if magnitude == 0 && is_negative_coeff {
                return Ok(Decimal::negative_zero_with_exponent(exponent));
            }

            let coefficient: i128 = if is_negative_coeff {
                -(magnitude as i128)
            } else {
                magnitude as i128
            };

            Ok(Decimal::new(coefficient, exponent))
        } else {
            let mut magnitude_bytes = coeff_bytes.to_vec();
            magnitude_bytes[0] &= 0x7F;

            let magnitude = UInt::from_be_bytes(&magnitude_bytes);
            if magnitude == UInt::ZERO && is_negative_coeff {
                return Ok(Decimal::negative_zero_with_exponent(exponent));
            }

            let coefficient: Int = if is_negative_coeff {
                Int::from(&magnitude).neg()
            } else {
                Int::from(&magnitude)
            };

            Ok(Decimal::new(coefficient, exponent))
        }
    }

    fn read_timestamp_ref(&self, position: u32, length: u32) -> IonResult<Timestamp> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.source.filled() {
            return IonResult::decoding_error("timestamp reference out of bounds");
        }
        let bytes = self.bytes_range(start, length as usize);

        if bytes.len() < 2 {
            return IonResult::decoding_error("timestamp too short");
        }

        let mut pos = 0;

        let first_byte = bytes[pos];
        let is_negative_offset = (first_byte & VARINT_SIGN_BIT) != 0;
        let offset_raw = read_var_int_from_slice(bytes, &mut pos)?;
        let offset_magnitude = offset_raw.unsigned_abs() as i64;

        if offset_magnitude > 1440 {
            return IonResult::decoding_error("timestamp UTC offset exceeds valid range");
        }

        let is_known_offset = !(is_negative_offset && offset_magnitude == 0);
        let offset_minutes: i32 = if is_negative_offset {
            -(offset_magnitude as i32)
        } else {
            offset_magnitude as i32
        };

        if pos >= bytes.len() {
            return IonResult::decoding_error("timestamp missing year");
        }
        let year = read_var_uint_from_slice(bytes, &mut pos)?;

        let builder = Timestamp::with_year(year);
        if pos >= bytes.len() {
            let timestamp = builder.build()?;
            return Ok(timestamp);
        }

        let month = read_var_uint_from_slice(bytes, &mut pos)?;
        let builder = builder.with_month(month);
        if pos >= bytes.len() {
            let timestamp = builder.build()?;
            return Ok(timestamp);
        }

        let day = read_var_uint_from_slice(bytes, &mut pos)?;
        let builder = builder.with_day(day);
        if pos >= bytes.len() {
            let timestamp = builder.build()?;
            return Ok(timestamp);
        }

        let hour = read_var_uint_from_slice(bytes, &mut pos)?;
        if pos >= bytes.len() {
            return IonResult::decoding_error("timestamps with an hour must also specify a minute");
        }

        let minute = read_var_uint_from_slice(bytes, &mut pos)?;
        let builder = builder.with_hour_and_minute(hour, minute);
        if pos >= bytes.len() {
            let timestamp = if is_known_offset {
                builder.build_utc_fields_at_offset(offset_minutes)
            } else {
                builder.build()
            }?;
            return Ok(timestamp);
        }

        let second = read_var_uint_from_slice(bytes, &mut pos)?;
        let builder = builder.with_second(second);
        if pos >= bytes.len() {
            let timestamp = if is_known_offset {
                builder.build_utc_fields_at_offset(offset_minutes)
            } else {
                builder.build()
            }?;
            return Ok(timestamp);
        }

        let frac_exponent = read_var_int_from_slice(bytes, &mut pos)?;
        let coeff_bytes = &bytes[pos..];

        if coeff_bytes.len() > 16 {
            return IonResult::decoding_error("timestamp fractional coefficient exceeds 128 bits");
        }

        let fractional_seconds = if coeff_bytes.is_empty() {
            Decimal::new(0i32, frac_exponent)
        } else {
            let is_negative_coeff = (coeff_bytes[0] & 0x80) != 0;
            let first_magnitude_byte = (coeff_bytes[0] & 0x7F) as i128;
            let magnitude = coeff_bytes[1..]
                .iter()
                .fold(first_magnitude_byte, |acc, &b| (acc << 8) | b as i128);

            if is_negative_coeff {
                if magnitude == 0 {
                    Decimal::new(0i32, frac_exponent)
                } else {
                    return IonResult::decoding_error(
                        "timestamp fractional seconds coefficient \
                         must not be negative",
                    );
                }
            } else {
                Decimal::new(magnitude, frac_exponent)
            }
        };

        let builder = builder.with_fractional_seconds(fractional_seconds);
        let timestamp = if is_known_offset {
            builder.build_utc_fields_at_offset(offset_minutes)
        } else {
            builder.build()
        }?;
        Ok(timestamp)
    }

    fn read_text_ref(&self, position: u32, length: u32) -> IonResult<&str> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.source.filled() {
            return IonResult::decoding_error("text reference out of bounds");
        }
        let bytes = self.bytes_range(start, length as usize);
        std::str::from_utf8(bytes).map_err(|e| {
            crate::IonError::decoding_error(format!(
                "invalid UTF-8 in string at offset {position}: {e}"
            ))
        })
    }

    fn read_bytes_ref(&self, position: u32, length: u32) -> IonResult<&[u8]> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.source.filled() {
            return IonResult::decoding_error("bytes reference out of bounds");
        }
        Ok(self.bytes_range(start, length as usize))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::instruction::{op, Instruction};
    use std::io::Cursor;

    /// Helper: generate bytecode from Ion 1.0 binary bytes using
    /// the unified in-memory generator.
    fn generate_in_memory(source: Vec<u8>) -> (Vec<u32>, ConstantPool) {
        let src = InMemorySource::new(source);
        let mut gen = UnifiedBinaryIon10Generator::new(src);
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();
        gen.refill(&mut dest, &mut cp).unwrap();
        (dest, cp)
    }

    /// Helper: generate bytecode consuming all refills (in-memory).
    fn generate_all_in_memory(source: Vec<u8>) -> (Vec<u32>, ConstantPool) {
        let src = InMemorySource::new(source);
        let mut gen = UnifiedBinaryIon10Generator::new(src);
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();
        loop {
            gen.refill(&mut dest, &mut cp).unwrap();
            let last = *dest.last().unwrap();
            if last == instr::END_OF_INPUT {
                break;
            }
        }
        (dest, cp)
    }

    /// Helper: generate bytecode from streaming source.
    fn generate_streaming(source: Vec<u8>) -> (Vec<u32>, ConstantPool) {
        let src = StreamingSource::new(Cursor::new(source));
        let mut gen = UnifiedBinaryIon10Generator::new(src);
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();
        gen.refill(&mut dest, &mut cp).unwrap();
        (dest, cp)
    }

    /// Helper: generate bytecode consuming all refills (streaming).
    fn generate_all_streaming(source: Vec<u8>) -> (Vec<u32>, ConstantPool) {
        let src = StreamingSource::new(Cursor::new(source));
        let mut gen = UnifiedBinaryIon10Generator::new(src);
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();
        loop {
            gen.refill(&mut dest, &mut cp).unwrap();
            let last = *dest.last().unwrap();
            if last == instr::END_OF_INPUT {
                break;
            }
        }
        (dest, cp)
    }

    #[test]
    fn ivm_detection_in_memory() {
        let source = vec![0xE0, 0x01, 0x00, 0xEA];
        let (dest, _cp) = generate_in_memory(source);
        let ivm_instr = Instruction::from_raw(dest[0]);
        assert_eq!(ivm_instr.operation(), op::IVM);
    }

    #[test]
    fn ivm_detection_streaming() {
        let source = vec![0xE0, 0x01, 0x00, 0xEA];
        let (dest, _cp) = generate_streaming(source);
        let ivm_instr = Instruction::from_raw(dest[0]);
        assert_eq!(ivm_instr.operation(), op::IVM);
    }

    #[test]
    fn int_values_in_memory() {
        // int 5
        let source = vec![0x21, 0x05];
        let (dest, _cp) = generate_in_memory(source);
        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), 5);
    }

    #[test]
    fn int_values_streaming() {
        let source = vec![0x21, 0x05];
        let (dest, _cp) = generate_streaming(source);
        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), 5);
    }

    #[test]
    fn multiple_values_in_memory() {
        let source = vec![0x21, 0x01, 0x11, 0x21, 0x02];
        let (dest, _cp) = generate_in_memory(source);
        let i1 = Instruction::from_raw(dest[0]);
        assert_eq!(i1.data_as_i16(), 1);
        let b = Instruction::from_raw(dest[1]);
        assert_eq!(b.operation(), op::BOOL);
        let i2 = Instruction::from_raw(dest[2]);
        assert_eq!(i2.data_as_i16(), 2);
        assert_eq!(dest[3], instr::END_OF_INPUT);
    }

    #[test]
    fn list_container_in_memory() {
        let source = vec![0xB4, 0x21, 0x01, 0x21, 0x02];
        let (dest, _cp) = generate_in_memory(source);
        let list_start = Instruction::from_raw(dest[0]);
        assert_eq!(list_start.operation(), op::LIST_START);
        assert_eq!(list_start.data(), 3);
    }

    #[test]
    fn string_ref_in_memory() {
        let source = vec![0x85, b'h', b'e', b'l', b'l', b'o'];
        let src = InMemorySource::new(source);
        let mut gen = UnifiedBinaryIon10Generator::new(src);
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();
        gen.refill(&mut dest, &mut cp).unwrap();

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::STRING_REF);
        assert_eq!(instr_word.data(), 5);

        let text = gen.read_text_ref(dest[1], 5).unwrap();
        assert_eq!(text, "hello");
    }

    #[test]
    fn equivalence_in_memory_vs_streaming() {
        use crate::bytecode::materialize::{
            read_all_v3_unified_binary, read_all_v3_unified_streaming_binary,
        };
        use crate::lazy::encoding::Encoding;
        use crate::v1_0;
        use crate::Element;

        // These test cases produce valid Ion 1.0 binary (starting with
        // IVM) via the encoder. The streaming path requires full values
        // to be buffered, which works correctly when the IVM is present.
        let test_cases = &[
            "5",
            "-42",
            "true",
            "null",
            "null.int",
            "\"hello world\"",
            "[1, 2, 3]",
            "{foo: 1, bar: 2}",
            "foo::bar::5",
            "1.23",
            "2024-01-15T10:30:00Z",
        ];

        for text in test_cases {
            let elements = Element::read_all(text.as_bytes()).unwrap();
            let binary = v1_0::Binary::encode_all(elements.iter()).unwrap();

            // Verify it starts with IVM (valid Ion binary)
            assert!(
                binary.starts_with(&[0xE0, 0x01, 0x00, 0xEA]),
                "binary encoding should start with IVM for '{text}'"
            );

            let in_mem = read_all_v3_unified_binary(&binary)
                .unwrap_or_else(|e| panic!("in-memory failed for '{text}': {e}"));
            let streaming = read_all_v3_unified_streaming_binary(&binary)
                .unwrap_or_else(|e| panic!("streaming failed for '{text}': {e}"));
            assert_eq!(in_mem, streaming, "mismatch for input: {text}");
        }
    }

    #[test]
    fn null_values() {
        let test_cases: Vec<(u8, u8)> = vec![
            (0x0F, op::NULL_NULL),
            (0x1F, op::NULL_BOOL),
            (0x2F, op::NULL_INT),
            (0x3F, op::NULL_INT),
            (0x4F, op::NULL_FLOAT),
            (0x5F, op::NULL_DECIMAL),
            (0x6F, op::NULL_TIMESTAMP),
            (0x7F, op::NULL_SYMBOL),
            (0x8F, op::NULL_STRING),
            (0x9F, op::NULL_CLOB),
            (0xAF, op::NULL_BLOB),
            (0xBF, op::NULL_LIST),
            (0xCF, op::NULL_SEXP),
            (0xDF, op::NULL_STRUCT),
        ];

        for (byte, expected_op) in test_cases {
            let source = vec![byte];
            let (dest, _cp) = generate_in_memory(source);
            let instr_word = Instruction::from_raw(dest[0]);
            assert_eq!(
                instr_word.operation(),
                expected_op,
                "byte {byte:#04X} should produce op {expected_op:#04X}"
            );
        }
    }
}
