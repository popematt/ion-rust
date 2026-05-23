//! Streaming Ion 1.0 binary bytecode generator.
//!
//! Parses Ion 1.0 binary data from an `impl Read` source and produces
//! bytecode instructions for the bytecode reader. Uses a length-prefix
//! pre-read strategy: determine the complete value size from the type
//! descriptor before parsing, blocking on reads as needed.
//!
//! Each `refill()` call emits bytecode for one or more top-level values
//! (stopping at IVM/LST boundaries or buffer exhaustion), or
//! `END_OF_INPUT` when the source is fully consumed.

use std::io::Read;
use std::ops::Neg;
use std::sync::Arc;

use crate::bytecode::constant_pool::{Constant, ConstantPool};
use crate::bytecode::generator::BytecodeGenerator;
use crate::bytecode::instruction::instr;
use crate::result::IonFailure;
use crate::{Decimal, Int, IonResult, Timestamp, UInt};

/// Ion 1.0 binary IVM bytes.
const IVM_BYTES: [u8; 4] = [0xE0, 0x01, 0x00, 0xEA];

/// Default internal buffer capacity in bytes.
const DEFAULT_BUFFER_CAPACITY: usize = 8 * 1024;

/// Minimum number of bytes to request in a single read call.
const MIN_READ_SIZE: usize = 4096;

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

/// A streaming bytecode generator for Ion 1.0 binary data.
///
/// Reads from an `impl Read` source, buffering data internally.
/// Each `refill()` call blocks until at least one complete top-level
/// value is available (or EOF is reached), then emits bytecode.
///
/// # REF Lifetime Contract
///
/// REF instructions emitted during a `refill()` call store positions
/// into the internal buffer. These positions are valid only until the
/// next `refill()` call, at which point the buffer may be compacted.
/// Callers must resolve all REF instructions before calling
/// `refill()` again.
pub struct StreamingBinaryIon10Generator<R: Read> {
    source: R,
    /// Internal buffer holding bytes read from the source.
    buffer: Vec<u8>,
    /// Number of valid bytes in `buffer`.
    filled: usize,
    /// Current parse position within buffer.
    position: usize,
    /// Bytes `[0..consumed]` have been fully processed and their
    /// REFs resolved. Discarded at the start of the next refill.
    consumed: usize,
    /// Whether EOF has been reached on the source.
    eof: bool,
}

impl<R: Read> StreamingBinaryIon10Generator<R> {
    /// Creates a new streaming binary generator from the given reader.
    ///
    /// Do NOT wrap the reader in `BufReader` — this generator performs
    /// its own internal buffering.
    pub fn new(reader: R) -> Self {
        Self {
            source: reader,
            buffer: vec![0u8; DEFAULT_BUFFER_CAPACITY],
            filled: 0,
            position: 0,
            consumed: 0,
            eof: false,
        }
    }

    /// Creates a new streaming binary generator with pre-seeded bytes
    /// already in the buffer (e.g., from peeking for format detection).
    pub fn with_peeked(reader: R, peeked: &[u8]) -> Self {
        let capacity = DEFAULT_BUFFER_CAPACITY.max(peeked.len());
        let mut buffer = vec![0u8; capacity];
        buffer[..peeked.len()].copy_from_slice(peeked);
        Self {
            source: reader,
            buffer,
            filled: peeked.len(),
            position: 0,
            consumed: 0,
            eof: false,
        }
    }

    /// Compacts the buffer by removing already-consumed bytes.
    fn compact(&mut self) {
        if self.consumed > 0 {
            self.buffer.copy_within(self.consumed..self.filled, 0);
            self.filled -= self.consumed;
            self.position -= self.consumed;
            self.consumed = 0;
        }
    }

    /// Ensures at least `n` bytes are available starting at `self.position`.
    /// Blocks on reads until enough data is buffered or EOF is reached.
    /// Returns `Ok(true)` if `n` bytes are available, `Ok(false)` if EOF
    /// was reached before `n` bytes could be gathered.
    fn ensure_available(&mut self, n: usize) -> IonResult<bool> {
        while self.filled - self.position < n {
            if self.eof {
                return Ok(false);
            }
            self.read_more()?;
        }
        Ok(true)
    }

    /// Reads more data from the source into the buffer.
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
            .source
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

    /// Returns the number of buffered bytes available from position.
    fn available(&self) -> usize {
        self.filled - self.position
    }

    /// Returns true if the source has been fully consumed (EOF reached
    /// and no buffered bytes remain).
    fn is_exhausted(&self) -> bool {
        self.available() == 0 && self.eof
    }

    /// Reads a VarUInt from the buffer at the current position.
    /// Caller must ensure enough bytes are available.
    fn read_var_uint(&mut self) -> usize {
        let mut result: usize = 0;
        loop {
            let byte = self.buffer[self.position];
            self.position += 1;
            result = (result << 7) | (byte & VARUINT_DATA_MASK) as usize;
            if byte & VARINT_STOP_BIT != 0 {
                return result;
            }
        }
    }

    /// Reads a VarUInt safely, ensuring bytes are available from the source.
    /// Used during top-level NOP padding parsing where we've already consumed
    /// the type descriptor byte and need to read a VarUInt length.
    fn read_var_uint_safe(&mut self) -> IonResult<usize> {
        let mut result: usize = 0;
        loop {
            if !self.ensure_available(1)? {
                return IonResult::decoding_error("unexpected EOF reading VarUInt");
            }
            let byte = self.buffer[self.position];
            self.position += 1;
            result = (result << 7) | (byte & VARUINT_DATA_MASK) as usize;
            if byte & VARINT_STOP_BIT != 0 {
                return Ok(result);
            }
        }
    }

    /// Reads an unsigned integer of the given byte length from the buffer.
    fn read_uint(&mut self, length: usize) -> u64 {
        let mut result: u64 = 0;
        for i in 0..length {
            result = (result << 8) | self.buffer[self.position + i] as u64;
        }
        self.position += length;
        result
    }

    /// Reads a type descriptor byte and returns (type_code, length).
    /// This may read additional VarUInt bytes for extended lengths.
    fn read_type_descriptor(&mut self) -> (u8, usize) {
        let td = self.buffer[self.position];
        self.position += 1;
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
        self.available() >= 4 && self.buffer[self.position..self.position + 4] == IVM_BYTES
    }

    /// Determines how many bytes a top-level value occupies starting at
    /// `self.position`, including the type descriptor and any VarUInt
    /// length bytes. Does NOT advance position. Returns `Ok(Some(size))`
    /// if enough data is available, `Ok(None)` if EOF was reached before
    /// the full value could be buffered.
    fn determine_value_size(&mut self) -> IonResult<Option<usize>> {
        // We need at least 1 byte for the type descriptor.
        if !self.ensure_available(1)? {
            return Ok(None);
        }

        let start = self.position;
        let td = self.buffer[start];
        let tc = td >> 4;
        let low = td & 0x0F;

        // Size of the type descriptor itself (1 byte)
        let mut header_size: usize = 1;

        let body_length: usize = match tc {
            type_code::NOP => {
                if low == 0x0F {
                    0 // null.null has no body
                } else if low == 0x0E {
                    match self.read_varuint_at(start + 1, &mut header_size)? {
                        Some(len) => len,
                        None => return Ok(None),
                    }
                } else {
                    low as usize
                }
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

        // Ensure the full value is buffered.
        if !self.ensure_available(total)? {
            return Ok(None);
        }

        Ok(Some(total))
    }

    /// Helper to read a VarUInt starting at `offset` within the buffer.
    /// Updates `header_size` with the number of VarUInt bytes read.
    /// Returns `Ok(Some(value))` or `Ok(None)` if EOF before completion.
    fn read_varuint_at(
        &mut self,
        offset: usize,
        header_size: &mut usize,
    ) -> IonResult<Option<usize>> {
        let mut result: usize = 0;
        let mut pos = offset;
        loop {
            // Ensure byte at `pos` is available
            let needed = pos - self.position + 1;
            if !self.ensure_available(needed)? {
                return Ok(None);
            }
            let byte = self.buffer[pos];
            pos += 1;
            *header_size += 1;
            result = (result << 7) | (byte & VARUINT_DATA_MASK) as usize;
            if byte & VARINT_STOP_BIT != 0 {
                return Ok(Some(result));
            }
        }
    }

    /// Emits bytecode for a single value at the current position.
    /// Returns `true` if the value was a system value (LST).
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
                self.position += length;
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
                self.position += length;
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
        let bytes = &self.buffer[self.position..self.position + length];
        let magnitude = UInt::from_be_bytes(bytes);
        let value: Int = if is_negative {
            Int::from(&magnitude).neg()
        } else {
            Int::from(&magnitude)
        };
        self.position += length;
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
                self.position += length;
            }
        }
    }

    /// Emits a decimal value as DECIMAL_REF.
    fn emit_decimal(&mut self, length: usize, destination: &mut Vec<u32>) {
        if length == 0 {
            destination.push(instr::DECIMAL_REF);
            destination.push(self.position as u32);
            return;
        }
        let offset = self.position as u32;
        debug_assert!(
            length as u32 <= 0x003F_FFFF,
            "decimal length exceeds 22-bit data field"
        );
        destination.push(instr::DECIMAL_REF | (length as u32 & 0x003F_FFFF));
        destination.push(offset);
        self.position += length;
    }

    /// Emits a timestamp value as TIMESTAMP_REF.
    fn emit_timestamp_ref(&mut self, length: usize, destination: &mut Vec<u32>) {
        let offset = self.position as u32;
        debug_assert!(
            length as u32 <= 0x003F_FFFF,
            "timestamp length exceeds 22-bit data field"
        );
        destination.push(instr::TIMESTAMP_REF | (length as u32 & 0x003F_FFFF));
        destination.push(offset);
        self.position += length;
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
        let offset = self.position as u32;
        debug_assert!(
            length as u32 <= 0x003F_FFFF,
            "string length exceeds 22-bit data field"
        );
        destination.push(instr::STRING_REF | (length as u32 & 0x003F_FFFF));
        destination.push(offset);
        self.position += length;
    }

    /// Emits a lob (blob or clob) as a REF instruction.
    fn emit_lob_ref(&mut self, instr_base: u32, length: usize, destination: &mut Vec<u32>) {
        let offset = self.position as u32;
        debug_assert!(
            length as u32 <= 0x003F_FFFF,
            "lob length exceeds 22-bit data field"
        );
        destination.push(instr_base | (length as u32 & 0x003F_FFFF));
        destination.push(offset);
        self.position += length;
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

        let end_position = self.position + content_length;
        while self.position < end_position {
            if is_struct {
                let field_sid = self.read_var_uint() as u32;

                // Check for NOP padding in structs
                let peek_td = self.buffer[self.position];
                let peek_tc = peek_td >> 4;
                let peek_low = peek_td & 0x0F;
                if peek_tc == type_code::NOP && peek_low != 0x0F {
                    let (_nop_tc, nop_length) = self.read_type_descriptor();
                    self.position += nop_length;
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
        let wrapper_end = self.position + wrapper_length;

        // Read annotations length (VarUInt)
        let annot_length = self.read_var_uint();
        let annot_end = self.position + annot_length;

        // Collect annotation SIDs
        let mut annotation_sids = Vec::new();
        while self.position < annot_end {
            let sid = self.read_var_uint() as u32;
            annotation_sids.push(sid);
        }

        // Check for LST
        if annotation_sids.len() == 1
            && annotation_sids[0] == system_symbol::ION_SYMBOL_TABLE
            && self.position < wrapper_end
        {
            let peek_td = self.buffer[self.position];
            let peek_tc = peek_td >> 4;
            if peek_tc == type_code::STRUCT {
                self.parse_local_symbol_table(wrapper_end, destination);
                return true;
            }
        }

        // Not an LST — emit annotation SIDs
        for sid in annotation_sids {
            debug_assert!(
                sid <= 0x003F_FFFF,
                "annotation SID exceeds 22-bit data field"
            );
            destination.push(instr::ANNOTATION_SID | (sid & 0x003F_FFFF));
        }

        // Emit the annotated value
        let _ = self.emit_value(destination, constant_pool);

        // Advance to wrapper_end in case of padding
        self.position = wrapper_end;
        false
    }

    /// Parses a local symbol table struct and emits a
    /// `DIRECTIVE_SET_SYMBOLS` directive.
    fn parse_local_symbol_table(&mut self, wrapper_end: usize, destination: &mut Vec<u32>) {
        let (tc, struct_length) = self.read_type_descriptor();
        debug_assert_eq!(tc, type_code::STRUCT);
        let struct_end = self.position + struct_length;

        let mut new_symbols: Vec<Option<(usize, usize)>> = Vec::new();

        while self.position < struct_end {
            let field_sid = self.read_var_uint() as u32;
            let (value_tc, value_length) = self.read_type_descriptor();

            if field_sid == system_symbol::SYMBOLS && value_tc == type_code::LIST {
                let list_end = self.position + value_length;
                while self.position < list_end {
                    let (elem_tc, elem_length) = self.read_type_descriptor();
                    if elem_tc == type_code::STRING && elem_length != NULL_SENTINEL {
                        new_symbols.push(Some((self.position, elem_length)));
                        self.position += elem_length;
                    } else if elem_length == NULL_SENTINEL {
                        new_symbols.push(None);
                    } else {
                        new_symbols.push(None);
                        self.position += elem_length;
                    }
                }
            } else {
                // Skip fields we don't care about
                if value_length != NULL_SENTINEL {
                    self.position += value_length;
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

        self.position = wrapper_end;
    }
}

/// Reads a VarUInt from a byte slice (used by `read_*_ref` methods).
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

impl<R: Read> BytecodeGenerator for StreamingBinaryIon10Generator<R> {
    fn refill(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        // Compact: discard consumed bytes from previous refill cycle.
        self.consumed = self.position;
        self.compact();

        // Try to get at least 1 byte to check for exhaustion.
        if !self.ensure_available(1)? {
            destination.push(instr::END_OF_INPUT);
            return Ok(());
        }

        // Process top-level values until we hit an IVM, LST, or EOF.
        loop {
            if self.is_exhausted() {
                destination.push(instr::END_OF_INPUT);
                return Ok(());
            }

            // Check if data is available for another value.
            if !self.ensure_available(1)? {
                destination.push(instr::END_OF_INPUT);
                return Ok(());
            }

            // Check for IVM (need 4 bytes)
            if self.ensure_available(4)? && self.is_at_ivm() {
                self.position += 4;
                let version_data = 1u32 << 8;
                destination.push(instr::IVM | version_data);
                destination.push(instr::REFILL);
                return Ok(());
            }

            // Peek at the type descriptor to check for NOP at top level
            let td = self.buffer[self.position];
            let tc = td >> 4;
            let low = td & 0x0F;

            if tc == type_code::NOP && low != 0x0F {
                // Skip NOP padding
                self.position += 1;
                if low == 0x0E {
                    let pad_len = self.read_var_uint_safe()?;
                    if !self.ensure_available(pad_len)? {
                        return IonResult::decoding_error("unexpected EOF in NOP padding");
                    }
                    self.position += pad_len;
                } else {
                    if !self.ensure_available(low as usize)? {
                        return IonResult::decoding_error("unexpected EOF in NOP padding");
                    }
                    self.position += low as usize;
                }
                continue;
            }

            // Determine the full value size and ensure it's buffered.
            let value_size = self.determine_value_size()?;
            match value_size {
                Some(_size) => {
                    // The entire value is now buffered — parse it.
                    let is_system_value = self.emit_value(destination, constant_pool);
                    if is_system_value {
                        destination.push(instr::REFILL);
                        return Ok(());
                    }
                }
                None => {
                    // EOF reached mid-value (incomplete data).
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
        if end > self.filled {
            return IonResult::decoding_error("int reference out of bounds");
        }
        let bytes = &self.buffer[start..end];
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
        if end > self.filled {
            return IonResult::decoding_error("decimal reference out of bounds");
        }
        let bytes = &self.buffer[start..end];

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
        if end > self.filled {
            return IonResult::decoding_error("timestamp reference out of bounds");
        }
        let bytes = &self.buffer[start..end];

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
                Decimal::new(magnitude as i128, frac_exponent)
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
        if end > self.filled {
            return IonResult::decoding_error("text reference out of bounds");
        }
        let bytes = &self.buffer[start..end];
        std::str::from_utf8(bytes).map_err(|e| {
            crate::IonError::decoding_error(format!(
                "invalid UTF-8 in string at offset {position}: {e}"
            ))
        })
    }

    fn read_bytes_ref(&self, position: u32, length: u32) -> IonResult<&[u8]> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.filled {
            return IonResult::decoding_error("bytes reference out of bounds");
        }
        Ok(&self.buffer[start..end])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::constant_pool::ConstantPool;
    use crate::bytecode::instruction::{op, Instruction};
    use std::io::Cursor;

    /// Helper: generate bytecode from Ion 1.0 binary bytes using the
    /// streaming generator.
    fn generate(source: Vec<u8>) -> (Vec<u32>, ConstantPool) {
        let mut gen = StreamingBinaryIon10Generator::new(Cursor::new(source));
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();
        gen.refill(&mut dest, &mut cp).unwrap();
        (dest, cp)
    }

    /// Helper: generate bytecode, consuming all refills until END_OF_INPUT.
    fn generate_all(source: Vec<u8>) -> (Vec<u32>, ConstantPool) {
        let mut gen = StreamingBinaryIon10Generator::new(Cursor::new(source));
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
    fn empty_input_gives_end_of_input() {
        let (dest, _cp) = generate(vec![]);
        assert_eq!(dest.len(), 1);
        assert_eq!(dest[0], instr::END_OF_INPUT);
    }

    #[test]
    fn ivm_detection() {
        let source = vec![0xE0, 0x01, 0x00, 0xEA];
        let (dest, _cp) = generate(source);

        let ivm_instr = Instruction::from_raw(dest[0]);
        assert_eq!(ivm_instr.operation(), op::IVM);
        let data = ivm_instr.data();
        assert_eq!(data >> 8, 1); // major
        assert_eq!(data & 0xFF, 0); // minor
    }

    #[test]
    fn ivm_then_int() {
        let source = vec![0xE0, 0x01, 0x00, 0xEA, 0x21, 0x01];
        let (dest, _cp) = generate_all(source);

        let ivm = Instruction::from_raw(dest[0]);
        assert_eq!(ivm.operation(), op::IVM);

        let int_idx = dest
            .iter()
            .position(|&w| Instruction::from_raw(w).operation() == op::INT_I16)
            .expect("should have INT_I16");
        let int_instr = Instruction::from_raw(dest[int_idx]);
        assert_eq!(int_instr.data_as_i16(), 1);
    }

    #[test]
    fn int_zero() {
        let source = vec![0x20];
        let (dest, _cp) = generate(source);
        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), 0);
    }

    #[test]
    fn int_positive() {
        let source = vec![0x21, 0x05];
        let (dest, _cp) = generate(source);
        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), 5);
    }

    #[test]
    fn int_negative() {
        let source = vec![0x31, 0x05];
        let (dest, _cp) = generate(source);
        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), -5);
    }

    #[test]
    fn bool_values() {
        let source = vec![0x10]; // false
        let (dest, _cp) = generate(source);
        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::BOOL);
        assert_eq!(instr_word.data() & 1, 0);

        let source = vec![0x11]; // true
        let (dest, _cp) = generate(source);
        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::BOOL);
        assert_eq!(instr_word.data() & 1, 1);
    }

    #[test]
    fn multiple_values_single_refill() {
        // int 1, bool true, int 2
        let source = vec![0x21, 0x01, 0x11, 0x21, 0x02];
        let (dest, _cp) = generate(source);

        let i1 = Instruction::from_raw(dest[0]);
        assert_eq!(i1.operation(), op::INT_I16);
        assert_eq!(i1.data_as_i16(), 1);

        let b = Instruction::from_raw(dest[1]);
        assert_eq!(b.operation(), op::BOOL);

        let i2 = Instruction::from_raw(dest[2]);
        assert_eq!(i2.operation(), op::INT_I16);
        assert_eq!(i2.data_as_i16(), 2);

        assert_eq!(dest[3], instr::END_OF_INPUT);
    }

    #[test]
    fn list_with_ints() {
        let source = vec![0xB4, 0x21, 0x01, 0x21, 0x02];
        let (dest, _cp) = generate(source);

        let list_start = Instruction::from_raw(dest[0]);
        assert_eq!(list_start.operation(), op::LIST_START);
        assert_eq!(list_start.data(), 3); // 2 ints + END_CONTAINER
    }

    #[test]
    fn string_ref_and_read() {
        let source = vec![0x85, b'h', b'e', b'l', b'l', b'o'];
        let mut gen = StreamingBinaryIon10Generator::new(Cursor::new(source));
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
    fn with_peeked_bytes() {
        let data = vec![0x21, 0x05]; // int 5
        let peeked = &data[..];
        let mut gen = StreamingBinaryIon10Generator::with_peeked(Cursor::new(vec![]), peeked);
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();
        gen.refill(&mut dest, &mut cp).unwrap();

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), 5);
    }

    #[test]
    fn chunked_read() {
        use std::io;

        struct ChunkedReader {
            data: Vec<u8>,
            pos: usize,
            chunk_size: usize,
        }

        impl io::Read for ChunkedReader {
            fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
                let remaining = self.data.len() - self.pos;
                if remaining == 0 {
                    return Ok(0);
                }
                let to_read = remaining.min(self.chunk_size).min(buf.len());
                buf[..to_read].copy_from_slice(&self.data[self.pos..self.pos + to_read]);
                self.pos += to_read;
                Ok(to_read)
            }
        }

        // IVM + int 42
        let data = vec![0xE0, 0x01, 0x00, 0xEA, 0x21, 0x2A];
        let reader = ChunkedReader {
            data,
            pos: 0,
            chunk_size: 1, // one byte at a time
        };

        let mut gen = StreamingBinaryIon10Generator::new(reader);
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();

        // First refill: IVM
        gen.refill(&mut dest, &mut cp).unwrap();
        let ivm = Instruction::from_raw(dest[0]);
        assert_eq!(ivm.operation(), op::IVM);

        // Second refill: int 42
        dest.clear();
        gen.refill(&mut dest, &mut cp).unwrap();
        let int_instr = Instruction::from_raw(dest[0]);
        assert_eq!(int_instr.operation(), op::INT_I16);
        assert_eq!(int_instr.data_as_i16(), 42);
    }

    #[test]
    fn nop_padding_skipped() {
        // NOP(3 bytes) + int 1
        let source = vec![0x03, 0x00, 0x00, 0x00, 0x21, 0x01];
        let (dest, _cp) = generate(source);
        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), 1);
    }

    #[test]
    fn nop_varuint_length() {
        // NOP with VarUInt length 3, then int 1
        let source = vec![0x0E, 0x83, 0x00, 0x00, 0x00, 0x21, 0x01];
        let (dest, _cp) = generate(source);
        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), 1);
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
            let (dest, _cp) = generate(source);
            let instr_word = Instruction::from_raw(dest[0]);
            assert_eq!(
                instr_word.operation(),
                expected_op,
                "byte {byte:#04X} should produce op {expected_op:#04X}"
            );
        }
    }

    /// Builds an Ion 1.0 binary LST with the given symbol strings.
    fn build_lst_bytes(symbols: &[&str]) -> Vec<u8> {
        let mut list_content = Vec::new();
        for sym in symbols {
            let bytes = sym.as_bytes();
            let len = bytes.len();
            if len < 14 {
                list_content.push(0x80 | len as u8);
            } else {
                list_content.push(0x8E);
                list_content.push(0x80 | len as u8);
            }
            list_content.extend_from_slice(bytes);
        }

        let mut struct_content = Vec::new();
        struct_content.push(0x87); // VarUInt SID 7
        let list_len = list_content.len();
        if list_len < 14 {
            struct_content.push(0xB0 | list_len as u8);
        } else {
            struct_content.push(0xBE);
            struct_content.push(0x80 | list_len as u8);
        }
        struct_content.extend_from_slice(&list_content);

        let struct_len = struct_content.len();
        let mut struct_td = Vec::new();
        if struct_len < 14 {
            struct_td.push(0xD0 | struct_len as u8);
        } else {
            struct_td.push(0xDE);
            struct_td.push(0x80 | struct_len as u8);
        }
        struct_td.extend_from_slice(&struct_content);

        let annot_sids = vec![0x83u8]; // SID 3
        let annot_length_varuint = vec![0x81u8]; // VarUInt 1
        let wrapper_content_len = annot_length_varuint.len() + annot_sids.len() + struct_td.len();

        let mut result = Vec::new();
        if wrapper_content_len < 14 {
            result.push(0xE0 | wrapper_content_len as u8);
        } else {
            result.push(0xEE);
            result.push(0x80 | wrapper_content_len as u8);
        }
        result.extend_from_slice(&annot_length_varuint);
        result.extend_from_slice(&annot_sids);
        result.extend_from_slice(&struct_td);

        result
    }

    #[test]
    fn lst_emits_directive() {
        let lst_bytes = build_lst_bytes(&["foo", "bar", "baz"]);
        let (dest, _cp) = generate_all(lst_bytes);

        let dir_idx = dest
            .iter()
            .position(|&w| Instruction::from_raw(w).operation() == op::DIRECTIVE_SET_SYMBOLS)
            .expect("should have DIRECTIVE_SET_SYMBOLS");
        assert_eq!(
            Instruction::from_raw(dest[dir_idx]).operation(),
            op::DIRECTIVE_SET_SYMBOLS
        );
    }

    #[test]
    fn lst_triggers_refill_boundary() {
        let lst_bytes = build_lst_bytes(&["foo", "bar"]);
        let mut gen = StreamingBinaryIon10Generator::new(Cursor::new(lst_bytes));
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();

        gen.refill(&mut dest, &mut cp).unwrap();
        let last = *dest.last().unwrap();
        assert_eq!(
            Instruction::from_raw(last).operation(),
            op::REFILL,
            "LST should trigger a REFILL boundary"
        );
    }

    #[test]
    fn equivalence_with_in_memory_generator() {
        use crate::bytecode::materialize::{read_all_v3_binary, read_all_v3_streaming_binary};
        use crate::lazy::encoding::Encoding;
        use crate::v1_0;
        use crate::Element;

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

            let expected = read_all_v3_binary(&binary).unwrap();
            let actual = read_all_v3_streaming_binary(&binary).unwrap();
            assert_eq!(expected, actual, "mismatch for input: {text}");
        }
    }
}
