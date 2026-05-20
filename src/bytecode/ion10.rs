//! Ion 1.0 binary bytecode generator.
//!
//! Parses Ion 1.0 binary data and produces bytecode instructions for the
//! bytecode reader. Handles the Ion 1.0 type descriptor format, VarUInt
//! encoding, and sign/magnitude integer representation.

use std::ops::Neg;
use std::rc::Rc;

use crate::bytecode::constant_pool::{Constant, ConstantPool};
use crate::bytecode::generator::BytecodeGenerator;
use crate::bytecode::instruction::instr;
use crate::result::IonFailure;
use crate::{Decimal, Int, IonResult, Timestamp};

/// Ion 1.0 binary IVM bytes.
const IVM_BYTES: [u8; 4] = [0xE0, 0x01, 0x00, 0xEA];

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

/// Sentinel value returned by `read_type_descriptor` to indicate a typed
/// null. This must be distinct from any valid representation length. Using
/// `usize::MAX` ensures no collision with VarUInt-decoded lengths.
const NULL_SENTINEL: usize = usize::MAX;

/// Ion 1.0 system symbol SIDs.
mod system_symbol {
    pub const ION_SYMBOL_TABLE: u32 = 3;
    pub const SYMBOLS: u32 = 7;
}

/// Ion 1.0 system symbol table (SIDs 1-9).
const SYSTEM_SYMBOLS: [&str; 9] = [
    "$ion",
    "$ion_1_0",
    "$ion_symbol_table",
    "name",
    "version",
    "imports",
    "symbols",
    "max_id",
    "$ion_shared_symbol_table",
];

/// A bytecode generator for Ion 1.0 binary data.
///
/// Translates Ion 1.0 binary bytes into bytecode instructions. Each call
/// to `refill` processes one or more top-level values (stopping at IVM
/// boundaries or end of input).
pub struct BinaryIon10Generator {
    source: Vec<u8>,
    position: usize,
    /// The current local symbol table. Initialized with system symbols
    /// (SIDs 1-9). Extended when an LST is encountered.
    symbol_table: Vec<Option<String>>,
}

impl BinaryIon10Generator {
    /// Creates a new generator from the given Ion 1.0 binary data.
    pub fn new(source: Vec<u8>) -> Self {
        let symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(s.to_string())).collect();
        Self {
            source,
            position: 0,
            symbol_table,
        }
    }

    /// Returns a reference to the current symbol table.
    #[cfg(test)]
    pub fn symbol_table(&self) -> &[Option<String>] {
        &self.symbol_table
    }

    /// Returns true if the source is exhausted.
    fn is_exhausted(&self) -> bool {
        self.position >= self.source.len()
    }

    /// Reads a VarUInt (variable-length unsigned integer) from the source.
    ///
    /// Ion 1.0 VarUInt encoding: each byte contributes 7 bits of data.
    /// The high bit (0x80) is set on the *last* byte (stop bit).
    fn read_var_uint(&mut self) -> usize {
        let mut result: usize = 0;
        loop {
            let byte = self.source[self.position];
            self.position += 1;
            result = (result << 7) | (byte & 0x7F) as usize;
            if byte & 0x80 != 0 {
                return result;
            }
        }
    }

    /// Reads an unsigned integer of the given byte length from the source.
    /// Returns the value as a u64. Suitable for lengths 1-8.
    fn read_uint(&mut self, length: usize) -> u64 {
        let mut result: u64 = 0;
        for i in 0..length {
            result = (result << 8) | self.source[self.position + i] as u64;
        }
        self.position += length;
        result
    }

    /// Reads a type descriptor byte and returns (type_code, length).
    ///
    /// Ion 1.0 type descriptor rules:
    /// - Type 0: L=0-14 is NOP pad length. L=15 is null.null.
    /// - Types 1-13: L=0-13 is inline length. L=14 means VarUInt
    ///   length follows. L=15 means typed null.
    /// - Type 14 (annotations): L=3-13 is inline wrapper length.
    ///   L=14 means VarUInt wrapper length follows.
    ///
    /// For bool (type 1), the low nibble encodes the value (0=false,
    /// 1=true) when not null; this is handled by the caller since the
    /// "length" returned for bool IS the low nibble value.
    fn read_type_descriptor(&mut self) -> (u8, usize) {
        let td = self.source[self.position];
        self.position += 1;
        let tc = td >> 4;
        let low = td & 0x0F;

        match tc {
            type_code::NOP => {
                if low == 0x0F {
                    // null.null — return sentinel to indicate null
                    (tc, NULL_SENTINEL)
                } else if low == 0x0E {
                    // VarUInt padding length follows
                    let length = self.read_var_uint();
                    (tc, length)
                } else {
                    // NOP pad: low nibble is the padding byte count
                    (tc, low as usize)
                }
            }
            type_code::ANNOTATION => {
                if low == 0x0E {
                    // VarUInt wrapper length
                    let length = self.read_var_uint();
                    (tc, length)
                } else {
                    // Inline wrapper length (L=3-13 typically)
                    (tc, low as usize)
                }
            }
            _ => {
                // Types 1-13
                if low == 0x0F {
                    // Typed null
                    (tc, NULL_SENTINEL)
                } else if low == 0x0E {
                    // VarUInt representation length
                    let length = self.read_var_uint();
                    (tc, length)
                } else {
                    // Inline representation length (0-13)
                    (tc, low as usize)
                }
            }
        }
    }

    /// Checks if the current position starts an IVM sequence.
    fn is_at_ivm(&self) -> bool {
        self.position + 4 <= self.source.len()
            && self.source[self.position..self.position + 4] == IVM_BYTES
    }

    /// Emits bytecode for a single value at the current position.
    /// Returns `true` if the value was a system value (LST) that should
    /// trigger a REFILL boundary.
    fn emit_value(&mut self, destination: &mut Vec<u32>, constant_pool: &mut ConstantPool) -> bool {
        let (tc, length) = self.read_type_descriptor();
        self.emit_value_body(tc, length, destination, constant_pool)
    }

    /// Emits the body of a value given its type code and length.
    /// Returns `true` if the value was a system value (LST).
    fn emit_value_body(
        &mut self,
        tc: u8,
        length: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> bool {
        // Check for null (NULL_SENTINEL returned by read_type_descriptor
        // when the type descriptor's low nibble is 0x0F)
        if length == NULL_SENTINEL && tc <= type_code::STRUCT {
            self.emit_null(tc, destination);
            return false;
        }

        match tc {
            type_code::NOP => {
                // Skip NOP padding bytes
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
                todo!("Decimal encoding is deferred")
            }
            type_code::TIMESTAMP => {
                todo!("Timestamp encoding is deferred")
            }
            type_code::SYMBOL => {
                self.emit_symbol(length, destination);
            }
            type_code::STRING => {
                self.emit_string(length, destination);
            }
            type_code::CLOB => {
                todo!("Clob encoding is deferred")
            }
            type_code::BLOB => {
                todo!("Blob encoding is deferred")
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
                // Unknown type code — skip the bytes
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

    /// Emits a boolean value. Low nibble: 0=false, 1=true.
    fn emit_bool(&self, low_nibble: usize, destination: &mut Vec<u32>) {
        let value = if low_nibble == 0 { 0u32 } else { 1u32 };
        destination.push(instr::BOOL | value);
    }

    /// Emits an integer value with sign determined by the type code.
    fn emit_int(
        &mut self,
        tc: u8,
        length: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) {
        if length == 0 {
            // int 0
            destination.push(instr::INT_I16);
            return;
        }

        let is_negative = tc == type_code::NEG_INT;

        if length <= 8 {
            let magnitude = self.read_uint(length);
            self.emit_int_from_magnitude(magnitude, is_negative, destination, constant_pool);
        } else {
            // Too large for i64 — use constant pool
            self.emit_big_int(length, is_negative, destination, constant_pool);
        }
    }

    /// Given a magnitude (up to 8 bytes) and sign, emits the appropriate
    /// integer instruction.
    fn emit_int_from_magnitude(
        &self,
        magnitude: u64,
        is_negative: bool,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) {
        // For positive values, the magnitude is the value directly.
        // For negative values, we negate. Must handle the case where
        // magnitude exceeds i64::MAX.
        if !is_negative {
            // Positive: magnitude fits in u64
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
                // magnitude > i64::MAX, need constant pool
                let value = Int::from(magnitude as i128);
                let idx = constant_pool.add(Constant::BigInt(Rc::new(value)));
                destination.push(instr::INT_CP | idx);
            }
        } else {
            // Negative: negate the magnitude
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
                // Doesn't fit in i64 — use constant pool
                let value = Int::from(neg_value);
                let idx = constant_pool.add(Constant::BigInt(Rc::new(value)));
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
        // Read magnitude bytes as big-endian unsigned.
        // Note: for truly large integers (> 16 bytes), this would overflow
        // u128. For now, we handle up to 16 bytes. Larger values would need
        // a proper BigInt library integration.
        let bytes = &self.source[self.position..self.position + length];
        let magnitude_u128 = bytes.iter().fold(0u128, |acc, &b| (acc << 8) | b as u128);
        let value = if is_negative {
            // Build the positive magnitude as Int, then negate. This
            // correctly handles magnitudes > i128::MAX via BigInt.
            Int::from(magnitude_u128).neg()
        } else {
            Int::from(magnitude_u128)
        };
        self.position += length;
        let idx = constant_pool.add(Constant::BigInt(Rc::new(value)));
        destination.push(instr::INT_CP | idx);
    }

    /// Emits a float value.
    fn emit_float(&mut self, length: usize, destination: &mut Vec<u32>) {
        match length {
            0 => {
                // Float zero (0e0) — emit as f32 with zero bits
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
                // Invalid float length — skip
                self.position += length;
            }
        }
    }

    /// Emits a symbol value as SYMBOL_SID.
    fn emit_symbol(&mut self, length: usize, destination: &mut Vec<u32>) {
        if length == 0 {
            // Symbol with SID 0 ($0)
            destination.push(instr::SYMBOL_SID);
            return;
        }
        let sid = self.read_uint(length) as u32;
        destination.push(instr::SYMBOL_SID | sid);
    }

    /// Emits a string as STRING_REF pointing to the source bytes.
    fn emit_string(&mut self, length: usize, destination: &mut Vec<u32>) {
        let offset = self.position as u32;
        destination.push(instr::STRING_REF | length as u32);
        destination.push(offset);
        self.position += length;
    }

    /// Emits a container (list, sexp, or struct) with reserve/backpatch.
    fn emit_container(
        &mut self,
        start_instr: u32,
        content_length: usize,
        is_struct: bool,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) {
        let start_index = destination.len();
        destination.push(0); // placeholder for start instruction

        let end_position = self.position + content_length;
        while self.position < end_position {
            if is_struct {
                // Struct fields are prefixed by a VarUInt SID
                let field_sid = self.read_var_uint() as u32;
                destination.push(instr::FIELD_NAME_SID | field_sid);
            }
            // LSTs only appear at the top level, not inside containers.
            let _ = self.emit_value(destination, constant_pool);
        }

        destination.push(instr::END_CONTAINER);
        let bytecode_length = destination.len() - start_index - 1;
        destination[start_index] = start_instr | bytecode_length as u32;
    }

    /// Emits an annotation wrapper: annotation SIDs followed by the
    /// annotated value. Detects local symbol tables (LSTs) and handles
    /// them as system values.
    ///
    /// Returns `true` if this was a local symbol table (system value),
    /// `false` if it was a normal annotated user value.
    fn emit_annotation_wrapper(
        &mut self,
        wrapper_length: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> bool {
        let wrapper_end = self.position + wrapper_length;

        // Read the annotations length (VarUInt)
        let annot_length = self.read_var_uint();
        let annot_end = self.position + annot_length;

        // Collect annotation SIDs to check for LST
        let mut annotation_sids = Vec::new();
        while self.position < annot_end {
            let sid = self.read_var_uint() as u32;
            annotation_sids.push(sid);
        }

        // Check if this is a local symbol table:
        // exactly one annotation, SID 3 ($ion_symbol_table), and the
        // value is a struct (type code 13).
        if annotation_sids.len() == 1
            && annotation_sids[0] == system_symbol::ION_SYMBOL_TABLE
            && self.position < wrapper_end
        {
            let peek_td = self.source[self.position];
            let peek_tc = peek_td >> 4;
            if peek_tc == type_code::STRUCT {
                self.parse_local_symbol_table(wrapper_end, destination);
                return true;
            }
        }

        // Not an LST — emit as normal annotated value.
        // Re-emit the annotation SIDs we already read.
        for sid in annotation_sids {
            destination.push(instr::ANNOTATION_SID | sid);
        }

        // Emit the annotated value (remaining bytes in wrapper)
        debug_assert!(
            self.position <= wrapper_end,
            "annotation SIDs overran wrapper"
        );
        // Nested annotation wrappers cannot be LSTs (LSTs are top-level only).
        let _ = self.emit_value(destination, constant_pool);

        // Ensure we consumed the entire wrapper
        debug_assert_eq!(
            self.position, wrapper_end,
            "annotation wrapper length mismatch"
        );
        false
    }

    /// Parses a local symbol table struct and emits a
    /// `DIRECTIVE_SET_SYMBOLS` directive.
    ///
    /// This simplified implementation:
    /// - Ignores the `imports` field
    /// - Always treats LSTs as "set" (replace), not "append"
    /// - Only handles the `symbols` field (SID 7) containing a list
    fn parse_local_symbol_table(&mut self, wrapper_end: usize, destination: &mut Vec<u32>) {
        // Read the struct type descriptor to get its content length
        let (tc, struct_length) = self.read_type_descriptor();
        debug_assert_eq!(tc, type_code::STRUCT);
        let struct_end = self.position + struct_length;

        // Collect symbols with their source positions from the `symbols` field.
        // Each entry is either Some((offset, length)) for a string or None for
        // null/unknown text.
        let mut new_symbols: Vec<Option<(usize, usize)>> = Vec::new();

        while self.position < struct_end {
            // Each struct field is: VarUInt field_name_sid, then value
            let field_sid = self.read_var_uint() as u32;
            let (value_tc, value_length) = self.read_type_descriptor();

            if field_sid == system_symbol::SYMBOLS && value_tc == type_code::LIST {
                // Parse the symbols list
                let list_end = self.position + value_length;
                while self.position < list_end {
                    let (elem_tc, elem_length) = self.read_type_descriptor();
                    if elem_tc == type_code::STRING && elem_length != NULL_SENTINEL {
                        // String value — record its position in the source
                        new_symbols.push(Some((self.position, elem_length)));
                        self.position += elem_length;
                    } else if elem_length == NULL_SENTINEL {
                        // Null value — unknown symbol text
                        new_symbols.push(None);
                    } else {
                        // Non-string, non-null — treat as unknown text
                        new_symbols.push(None);
                        self.position += elem_length;
                    }
                }
            } else {
                // Skip fields we don't care about
                if value_length != NULL_SENTINEL {
                    self.skip_value_body(value_tc, value_length);
                }
                // If value_length == NULL_SENTINEL, it's a typed null — no body bytes
            }
        }

        // Update the generator's symbol table: system symbols + new symbols
        self.symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(s.to_string())).collect();
        for entry in &new_symbols {
            match entry {
                Some((offset, length)) => {
                    let text_bytes = &self.source[*offset..*offset + *length];
                    let text = String::from_utf8_lossy(text_bytes).into_owned();
                    self.symbol_table.push(Some(text));
                }
                None => {
                    self.symbol_table.push(None);
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
                    // Unknown/null text: emit SYMBOL_SID 0
                    destination.push(instr::SYMBOL_SID);
                }
            }
        }
        destination.push(instr::END_CONTAINER);

        // Advance position to end of wrapper in case struct didn't
        // consume all bytes exactly
        self.position = wrapper_end;
    }

    /// Skips over a value body given its type code and length.
    /// Used when parsing LST fields we don't care about.
    fn skip_value_body(&mut self, tc: u8, length: usize) {
        match tc {
            type_code::STRUCT => {
                // Struct has field SID prefixes — just skip raw bytes
                self.position += length;
            }
            type_code::LIST | type_code::SEXP => {
                self.position += length;
            }
            type_code::ANNOTATION => {
                // Annotation wrappers contain nested values — skip raw
                self.position += length;
            }
            _ => {
                self.position += length;
            }
        }
    }
}

impl BytecodeGenerator for BinaryIon10Generator {
    fn refill(&mut self, destination: &mut Vec<u32>, constant_pool: &mut ConstantPool) {
        if self.is_exhausted() {
            destination.push(instr::END_OF_INPUT);
            return;
        }

        // Process top-level values until we hit an IVM or exhaust input.
        // An IVM is emitted and then we stop (system value boundary).
        loop {
            if self.is_exhausted() {
                destination.push(instr::END_OF_INPUT);
                return;
            }

            // Check for IVM
            if self.is_at_ivm() {
                self.position += 4;
                // Encode major=1, minor=0 in the data field
                // Encode major=1 in bits 8-15, minor=0 in bits 0-7
                let version_data = 1u32 << 8;
                destination.push(instr::IVM | version_data);
                // Stop after IVM — system value boundary
                destination.push(instr::REFILL);
                return;
            }

            // Peek at the type descriptor to check for NOP
            let td = self.source[self.position];
            let tc = td >> 4;
            let low = td & 0x0F;

            if tc == type_code::NOP && low != 0x0F {
                // Skip NOP padding (type 0, L=0-13 inline, L=14 VarUInt)
                self.position += 1;
                if low == 0x0E {
                    let pad_len = self.read_var_uint();
                    self.position += pad_len;
                } else {
                    self.position += low as usize;
                }
                continue;
            }

            // Emit the value
            let is_system_value = self.emit_value(destination, constant_pool);
            if is_system_value {
                // LST was processed — trigger a REFILL boundary so
                // the reader processes the directive before seeing
                // more values.
                destination.push(instr::REFILL);
                return;
            }
        }
    }

    fn read_int_ref(&self, position: u32, length: u32) -> IonResult<Int> {
        let start = position as usize;
        let end = start + length as usize;
        let bytes = &self.source[start..end];
        let value = bytes.iter().fold(0i128, |acc, &b| (acc << 8) | b as i128);
        Ok(Int::from(value))
    }

    fn read_decimal_ref(&self, _position: u32, _length: u32) -> IonResult<Decimal> {
        todo!("Decimal REF reading is deferred")
    }

    fn read_timestamp_ref(&self, _position: u32, _length: u32) -> IonResult<Timestamp> {
        todo!("Timestamp REF reading is deferred")
    }

    fn read_text_ref(&self, position: u32, length: u32) -> IonResult<&str> {
        let start = position as usize;
        let end = start + length as usize;
        let bytes = &self.source[start..end];
        std::str::from_utf8(bytes).map_err(|e| {
            crate::IonError::decoding_error(format!(
                "invalid UTF-8 in string at offset {position}: {e}"
            ))
        })
    }

    fn read_bytes_ref(&self, position: u32, length: u32) -> IonResult<&[u8]> {
        let start = position as usize;
        let end = start + length as usize;
        Ok(&self.source[start..end])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::instruction::{op, Instruction};

    /// Helper: generate bytecode from Ion 1.0 binary bytes.
    fn generate(source: Vec<u8>) -> (Vec<u32>, ConstantPool) {
        let mut gen = BinaryIon10Generator::new(source);
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();
        gen.refill(&mut dest, &mut cp);
        (dest, cp)
    }

    /// Helper: generate bytecode, consuming all refills until END_OF_INPUT.
    fn generate_all(source: Vec<u8>) -> (Vec<u32>, ConstantPool) {
        let mut gen = BinaryIon10Generator::new(source);
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();
        loop {
            gen.refill(&mut dest, &mut cp);
            let last = *dest.last().unwrap();
            if last == instr::END_OF_INPUT {
                break;
            }
        }
        (dest, cp)
    }

    #[test]
    fn ivm_detection() {
        let source = vec![0xE0, 0x01, 0x00, 0xEA];
        let (dest, _cp) = generate(source);

        let ivm_instr = Instruction::from_raw(dest[0]);
        assert_eq!(ivm_instr.operation(), op::IVM);
        // major=1, minor=0 encoded in data
        let data = ivm_instr.data();
        assert_eq!(data >> 8, 1); // major
        assert_eq!(data & 0xFF, 0); // minor
    }

    #[test]
    fn ivm_then_int() {
        // IVM + int 1
        let source = vec![0xE0, 0x01, 0x00, 0xEA, 0x21, 0x01];
        let (dest, _cp) = generate_all(source);

        // First refill: IVM + REFILL
        // Second refill: INT_I16(1) + END_OF_INPUT
        let ivm = Instruction::from_raw(dest[0]);
        assert_eq!(ivm.operation(), op::IVM);

        // Find the INT_I16 instruction
        let int_idx = dest
            .iter()
            .position(|&w| Instruction::from_raw(w).operation() == op::INT_I16)
            .expect("should have INT_I16");
        let int_instr = Instruction::from_raw(dest[int_idx]);
        assert_eq!(int_instr.data_as_i16(), 1);
    }

    #[test]
    fn int_zero() {
        // Type 2 (pos int), length 0 = int 0
        let source = vec![0x20];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), 0);
    }

    #[test]
    fn int_positive_1_byte() {
        // 0x21 0x05 = pos int, length 1, value 5
        let source = vec![0x21, 0x05];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), 5);
    }

    #[test]
    fn int_positive_2_bytes() {
        // 0x22, 0x01, 0x00 = pos int, length 2, value 256
        let source = vec![0x22, 0x01, 0x00];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), 256);
    }

    #[test]
    fn int_positive_3_bytes_needs_i32() {
        // 0x23, 0x01, 0x00, 0x00 = pos int, length 3, value 65536
        let source = vec![0x23, 0x01, 0x00, 0x00];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I32);
        let operand = dest[1] as i32;
        assert_eq!(operand, 65536);
    }

    #[test]
    fn int_negative_1_byte() {
        // 0x31 0x05 = neg int, length 1, value -5
        let source = vec![0x31, 0x05];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), -5);
    }

    #[test]
    fn int_negative_large() {
        // 0x35, 0x01, 0x00, 0x00, 0x00, 0x01 = neg int, length 5,
        // magnitude = 0x0100000001 = 4294967297
        // value = -4294967297
        let source = vec![0x35, 0x01, 0x00, 0x00, 0x00, 0x01];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I64);
        let hi = dest[1] as i64;
        let lo = dest[2] as u32 as i64;
        let value = (hi << 32) | lo;
        assert_eq!(value, -4294967297i64);
    }

    #[test]
    fn int_i64_max() {
        // Positive int, 8 bytes, value = i64::MAX = 0x7FFFFFFFFFFFFFFF
        let mut source = vec![0x28]; // type 2, length 8
        source.extend_from_slice(&0x7FFF_FFFF_FFFF_FFFFu64.to_be_bytes());
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I64);
        let hi = dest[1];
        let lo = dest[2];
        let value = ((hi as u64) << 32) | lo as u64;
        assert_eq!(value as i64, i64::MAX);
    }

    #[test]
    fn int_needs_constant_pool() {
        // Positive int, 9 bytes — exceeds i64, goes to constant pool
        let mut source = vec![0x29]; // type 2, length 9
        source.extend_from_slice(&[0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01]);
        let (dest, cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_CP);
        let cp_idx = instr_word.data();
        match cp.get(cp_idx) {
            Constant::BigInt(v) => {
                // Value should be 0x010000000000000001
                let expected = Int::from(0x01_0000_0000_0000_0001i128);
                assert_eq!(**v, expected);
            }
            _ => panic!("expected BigInt in constant pool"),
        }
    }

    #[test]
    fn int_negative_needs_constant_pool() {
        // Negative int, 9 bytes — exceeds i64, goes to constant pool
        let mut source = vec![0x39]; // type 3 (neg), length 9
        source.extend_from_slice(&[0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01]);
        let (dest, cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_CP);
        let cp_idx = instr_word.data();
        match cp.get(cp_idx) {
            Constant::BigInt(v) => {
                // Value should be -(0x010000000000000001)
                let expected = Int::from(-0x01_0000_0000_0000_0001i128);
                assert_eq!(**v, expected);
            }
            _ => panic!("expected BigInt in constant pool"),
        }
    }

    #[test]
    fn int_negative_large_magnitude_constant_pool() {
        // Negative int with magnitude > i64::MAX but <= 8 bytes
        // This exercises the emit_int_from_magnitude path for magnitude > i64::MAX
        // magnitude = 0x8000000000000000 (2^63), which is i64::MIN in abs value
        // but as unsigned = i64::MAX + 1. Since -(2^63) = i64::MIN, it should
        // still fit in i64 representation.
        let mut source = vec![0x38]; // type 3 (neg), length 8
        source.extend_from_slice(&0x8000_0000_0000_0000u64.to_be_bytes());
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I64);
        let hi = dest[1];
        let lo = dest[2];
        let value = ((hi as u64) << 32) | lo as u64;
        assert_eq!(value as i64, i64::MIN);
    }

    #[test]
    fn bool_false() {
        // 0x10 = bool false
        let source = vec![0x10];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::BOOL);
        assert_eq!(instr_word.data() & 1, 0);
    }

    #[test]
    fn bool_true() {
        // 0x11 = bool true
        let source = vec![0x11];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::BOOL);
        assert_eq!(instr_word.data() & 1, 1);
    }

    #[test]
    fn null_bool() {
        // 0x1F = null.bool
        let source = vec![0x1F];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::NULL_BOOL);
    }

    #[test]
    fn null_values() {
        // null (0x0F) — type 0 with low nibble F is actually a special
        // case. In Ion 1.0, 0x0F is null.null.
        // But type 0 is NOP — this is a quirk. Actually in the Ion spec,
        // type code 0 with L=0xF is null.null, not NOP padding.
        // Let me verify: type 0, L != 0xF is NOP pad. L = 0xF is null.null.
        //
        // Actually: The Ion 1.0 spec says:
        // - Type 0, L=0 through L=14: NOP with L bytes of padding
        // - Type 0, L=15: This is actually NOP with VarUInt length
        //
        // And null.null is encoded as type 1, variant 15? No.
        // Actually null.null uses the special byte 0x0F which is type 0, L=15.
        // Wait, no. In Ion 1.0 binary:
        // - 0x0F is indeed null.null (type=0, L=15 means null.null)
        //
        // Let me correct: per the Ion spec, for type code 0:
        // - L = 0 through 14: NOP pad of L bytes
        // - L = 15 (0x0F byte): This is null.null
        //
        // Let me double-check by testing each typed null.
        let test_cases: Vec<(u8, u8)> = vec![
            (0x0F, op::NULL_NULL), // null.null
            (0x1F, op::NULL_BOOL),
            (0x2F, op::NULL_INT),
            (0x3F, op::NULL_INT), // null.int via negint
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

    #[test]
    fn float_zero() {
        // 0x40 = float 0e0 (length 0)
        let source = vec![0x40];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::FLOAT_F32);
        assert_eq!(dest[1], 0); // zero bits
    }

    #[test]
    fn float_f32() {
        // 0x44 + 4 bytes = 32-bit float
        let value: f32 = 3.14;
        let mut source = vec![0x44];
        source.extend_from_slice(&value.to_bits().to_be_bytes());
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::FLOAT_F32);
        let bits = dest[1];
        assert_eq!(f32::from_bits(bits), value);
    }

    #[test]
    fn float_f64() {
        // 0x48 + 8 bytes = 64-bit float
        let value: f64 = 2.718281828459045;
        let mut source = vec![0x48];
        source.extend_from_slice(&value.to_bits().to_be_bytes());
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::FLOAT_F64);
        let hi = dest[1] as u64;
        let lo = dest[2] as u64;
        let bits = (hi << 32) | lo;
        assert_eq!(f64::from_bits(bits), value);
    }

    #[test]
    fn symbol_sid() {
        // 0x71 0x04 = symbol, length 1, SID 4
        let source = vec![0x71, 0x04];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::SYMBOL_SID);
        assert_eq!(instr_word.data(), 4);
    }

    #[test]
    fn symbol_sid_zero() {
        // 0x70 = symbol, length 0, SID 0
        let source = vec![0x70];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::SYMBOL_SID);
        assert_eq!(instr_word.data(), 0);
    }

    #[test]
    fn string_ref() {
        // 0x85 + 5 bytes = string "hello"
        let source = vec![0x85, b'h', b'e', b'l', b'l', b'o'];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::STRING_REF);
        assert_eq!(instr_word.data(), 5); // length
        assert_eq!(dest[1], 1); // offset (after type descriptor byte)
    }

    #[test]
    fn string_read_text_ref() {
        let source = vec![0x85, b'h', b'e', b'l', b'l', b'o'];
        let gen = BinaryIon10Generator::new(source);

        let text = gen.read_text_ref(1, 5).unwrap();
        assert_eq!(text, "hello");
    }

    #[test]
    fn list_with_two_ints() {
        // list [1, 2]:
        // 0xB2 = list, length 2
        //   0x21 0x01 = int 1
        //   0x21 0x02 = int 2  -- oops, each int is 2 bytes
        // Actually: 0xB4 = list, length 4
        let source = vec![0xB4, 0x21, 0x01, 0x21, 0x02];
        let (dest, _cp) = generate(source);

        let list_start = Instruction::from_raw(dest[0]);
        assert_eq!(list_start.operation(), op::LIST_START);

        // Children: INT_I16(1), INT_I16(2), END_CONTAINER
        let child1 = Instruction::from_raw(dest[1]);
        assert_eq!(child1.operation(), op::INT_I16);
        assert_eq!(child1.data_as_i16(), 1);

        let child2 = Instruction::from_raw(dest[2]);
        assert_eq!(child2.operation(), op::INT_I16);
        assert_eq!(child2.data_as_i16(), 2);

        let end = Instruction::from_raw(dest[3]);
        assert_eq!(end.operation(), op::END_CONTAINER);

        // Bytecode length = 3 (two ints + END_CONTAINER)
        assert_eq!(list_start.data(), 3);
    }

    #[test]
    fn sexp_with_values() {
        // sexp (1 2):
        // 0xC4 = sexp, length 4
        //   0x21 0x01, 0x21 0x02
        let source = vec![0xC4, 0x21, 0x01, 0x21, 0x02];
        let (dest, _cp) = generate(source);

        let sexp_start = Instruction::from_raw(dest[0]);
        assert_eq!(sexp_start.operation(), op::SEXP_START);
        assert_eq!(sexp_start.data(), 3); // 2 values + END
    }

    #[test]
    fn struct_with_two_fields() {
        // struct {name: 1, value: 2}:
        // Field names are VarUInt SIDs.
        // SID 4 = "name", SID 5 = "value" (example)
        // 0xD6 = struct, length 6
        //   0x84 = VarUInt SID 4 (0x80 | 4)
        //   0x21 0x01 = int 1
        //   0x85 = VarUInt SID 5 (0x80 | 5)
        //   0x21 0x02 = int 2
        let source = vec![0xD6, 0x84, 0x21, 0x01, 0x85, 0x21, 0x02];
        let (dest, _cp) = generate(source);

        let struct_start = Instruction::from_raw(dest[0]);
        assert_eq!(struct_start.operation(), op::STRUCT_START);

        // Field 1: FIELD_NAME_SID(4), INT_I16(1)
        let field1_name = Instruction::from_raw(dest[1]);
        assert_eq!(field1_name.operation(), op::FIELD_NAME_SID);
        assert_eq!(field1_name.data(), 4);

        let field1_value = Instruction::from_raw(dest[2]);
        assert_eq!(field1_value.operation(), op::INT_I16);
        assert_eq!(field1_value.data_as_i16(), 1);

        // Field 2: FIELD_NAME_SID(5), INT_I16(2)
        let field2_name = Instruction::from_raw(dest[3]);
        assert_eq!(field2_name.operation(), op::FIELD_NAME_SID);
        assert_eq!(field2_name.data(), 5);

        let field2_value = Instruction::from_raw(dest[4]);
        assert_eq!(field2_value.operation(), op::INT_I16);
        assert_eq!(field2_value.data_as_i16(), 2);

        let end = Instruction::from_raw(dest[5]);
        assert_eq!(end.operation(), op::END_CONTAINER);

        // Bytecode length = 5 (2 field names + 2 values + END)
        assert_eq!(struct_start.data(), 5);
    }

    #[test]
    fn annotation_wrapper() {
        // Annotated value: $4::true
        // Annotation wrapper format:
        //   0xE3 = annotation type (14), wrapper length 3
        //     0x81 = VarUInt annot_length 1
        //     0x84 = VarUInt SID 4
        //     0x11 = bool true
        let source = vec![0xE3, 0x81, 0x84, 0x11];
        let (dest, _cp) = generate(source);

        let annot = Instruction::from_raw(dest[0]);
        assert_eq!(annot.operation(), op::ANNOTATION_SID);
        assert_eq!(annot.data(), 4);

        let value = Instruction::from_raw(dest[1]);
        assert_eq!(value.operation(), op::BOOL);
        assert_eq!(value.data() & 1, 1);
    }

    #[test]
    fn multiple_annotations() {
        // Annotated value: $4::$5::42
        // Wrapper length = annot_length_varuint + annot_bytes + value_bytes
        //   annot_length = 2 (two 1-byte VarUInt SIDs)
        //   value = 0x21 0x2A (int 42, 2 bytes)
        //   wrapper_length = 1 (annot_length VarUInt) + 2 + 2 = 5
        // 0xE5 = annotation type, wrapper length 5
        //   0x82 = VarUInt annot_length 2
        //   0x84 = VarUInt SID 4
        //   0x85 = VarUInt SID 5
        //   0x21 0x2A = int 42
        let source = vec![0xE5, 0x82, 0x84, 0x85, 0x21, 0x2A];
        let (dest, _cp) = generate(source);

        let annot1 = Instruction::from_raw(dest[0]);
        assert_eq!(annot1.operation(), op::ANNOTATION_SID);
        assert_eq!(annot1.data(), 4);

        let annot2 = Instruction::from_raw(dest[1]);
        assert_eq!(annot2.operation(), op::ANNOTATION_SID);
        assert_eq!(annot2.data(), 5);

        let value = Instruction::from_raw(dest[2]);
        assert_eq!(value.operation(), op::INT_I16);
        assert_eq!(value.data_as_i16(), 42);
    }

    #[test]
    fn nop_padding_skipped() {
        // 0x03 = NOP, 3 bytes padding; then int 1
        // NOP type descriptor: type=0, L=3, so skip 3 bytes
        let source = vec![0x03, 0x00, 0x00, 0x00, 0x21, 0x01];
        let (dest, _cp) = generate(source);

        // NOP is skipped; first instruction should be the int
        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), 1);
    }

    #[test]
    fn nop_zero_length() {
        // 0x00 = NOP, 0 bytes padding; then bool true
        let source = vec![0x00, 0x11];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::BOOL);
        assert_eq!(instr_word.data() & 1, 1);
    }

    #[test]
    fn nop_varuint_length() {
        // 0x0E = NOP with VarUInt length. VarUInt 0x90 0x00 = 2048 would
        // be large. Let's use a small VarUInt: 0x83 = 3 bytes of padding.
        // Then followed by int 1.
        let source = vec![0x0E, 0x83, 0x00, 0x00, 0x00, 0x21, 0x01];
        let (dest, _cp) = generate(source);

        // NOP is skipped; first instruction should be the int
        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), 1);
    }

    #[test]
    fn varuint_length_string() {
        // String with VarUInt length. In Ion 1.0, L=14 (0xE) means
        // VarUInt length follows (L=15 means null.string).
        // 0x8E = string type (8), L=0xE => VarUInt length follows
        // VarUInt 14 = 0x8E (single byte, high bit set = stop)
        // Then 14 bytes of string content
        let mut source = vec![0x8E, 0x8E]; // string, VarUInt length=14
        source.extend_from_slice(b"hello, world!?"); // 14 bytes
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::STRING_REF);
        assert_eq!(instr_word.data(), 14); // length
        assert_eq!(dest[1], 2); // offset after TD + VarUInt
    }

    #[test]
    fn string_read_varuint_length() {
        let mut source = vec![0x8E, 0x8E]; // string, VarUInt length=14
        source.extend_from_slice(b"hello, world!?");
        let gen = BinaryIon10Generator::new(source.clone());

        let text = gen.read_text_ref(2, 14).unwrap();
        assert_eq!(text, "hello, world!?");
    }

    #[test]
    fn nested_list() {
        // [[1, 2], 3]
        // Inner list: 0xB4, 0x21, 0x01, 0x21, 0x02 (5 bytes)
        // Int 3: 0x21, 0x03 (2 bytes)
        // Outer list content = 7 bytes
        // 0xB7 = list, length 7
        let source = vec![
            0xB7, // outer list, length 7
            0xB4, 0x21, 0x01, 0x21, 0x02, // inner list [1, 2]
            0x21, 0x03, // int 3
        ];
        let (dest, _cp) = generate(source);

        let outer = Instruction::from_raw(dest[0]);
        assert_eq!(outer.operation(), op::LIST_START);

        // Inner list
        let inner = Instruction::from_raw(dest[1]);
        assert_eq!(inner.operation(), op::LIST_START);
        assert_eq!(inner.data(), 3); // 2 ints + END

        let i1 = Instruction::from_raw(dest[2]);
        assert_eq!(i1.data_as_i16(), 1);
        let i2 = Instruction::from_raw(dest[3]);
        assert_eq!(i2.data_as_i16(), 2);
        let inner_end = Instruction::from_raw(dest[4]);
        assert_eq!(inner_end.operation(), op::END_CONTAINER);

        // Int 3
        let i3 = Instruction::from_raw(dest[5]);
        assert_eq!(i3.data_as_i16(), 3);

        // Outer END
        let outer_end = Instruction::from_raw(dest[6]);
        assert_eq!(outer_end.operation(), op::END_CONTAINER);

        // Outer bytecode length: inner_start + 2ints + inner_end +
        // int3 + outer_end = 6
        assert_eq!(outer.data(), 6);
    }

    #[test]
    fn end_of_input_on_empty() {
        let source = vec![];
        let (dest, _cp) = generate(source);

        assert_eq!(dest.len(), 1);
        assert_eq!(dest[0], instr::END_OF_INPUT);
    }

    #[test]
    fn multiple_top_level_values() {
        // int 1, bool true, int 2
        let source = vec![0x21, 0x01, 0x11, 0x21, 0x02];
        let (dest, _cp) = generate(source);

        let i1 = Instruction::from_raw(dest[0]);
        assert_eq!(i1.operation(), op::INT_I16);
        assert_eq!(i1.data_as_i16(), 1);

        let b = Instruction::from_raw(dest[1]);
        assert_eq!(b.operation(), op::BOOL);
        assert_eq!(b.data() & 1, 1);

        let i2 = Instruction::from_raw(dest[2]);
        assert_eq!(i2.operation(), op::INT_I16);
        assert_eq!(i2.data_as_i16(), 2);

        assert_eq!(dest[3], instr::END_OF_INPUT);
    }

    #[test]
    fn int_positive_max_i16() {
        // i16::MAX = 32767 = 0x7FFF
        // 0x22, 0x7F, 0xFF = pos int, length 2, value 32767
        let source = vec![0x22, 0x7F, 0xFF];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), i16::MAX);
    }

    #[test]
    fn int_positive_exceeds_i16() {
        // 32768 = 0x8000 — exceeds i16::MAX, needs i32
        let source = vec![0x22, 0x80, 0x00];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I32);
        assert_eq!(dest[1] as i32, 32768);
    }

    #[test]
    fn int_negative_min_i16() {
        // -32768 = neg int with magnitude 32768 = 0x8000
        // 0x32, 0x80, 0x00
        let source = vec![0x32, 0x80, 0x00];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I16);
        assert_eq!(instr_word.data_as_i16(), i16::MIN);
    }

    #[test]
    fn int_negative_exceeds_i16() {
        // -32769: magnitude = 32769 = 0x8001
        let source = vec![0x32, 0x80, 0x01];
        let (dest, _cp) = generate(source);

        let instr_word = Instruction::from_raw(dest[0]);
        assert_eq!(instr_word.operation(), op::INT_I32);
        assert_eq!(dest[1] as i32, -32769);
    }

    /// Helper: generate bytecode, consuming all refills, returning the
    /// generator for inspection of symbol table state.
    fn generate_all_with_gen(source: Vec<u8>) -> (Vec<u32>, ConstantPool, BinaryIon10Generator) {
        let mut gen = BinaryIon10Generator::new(source);
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();
        loop {
            gen.refill(&mut dest, &mut cp);
            let last = *dest.last().unwrap();
            if last == instr::END_OF_INPUT {
                break;
            }
        }
        (dest, cp, gen)
    }

    /// Builds an Ion 1.0 binary LST annotation wrapper with the given
    /// symbol strings.
    fn build_lst_bytes(symbols: &[&str]) -> Vec<u8> {
        // Build the symbols list
        let mut list_content = Vec::new();
        for sym in symbols {
            let bytes = sym.as_bytes();
            let len = bytes.len();
            if len < 14 {
                // Inline length
                list_content.push(0x80 | len as u8); // string type (8), length
            } else {
                list_content.push(0x8E); // string type, VarUInt length follows
                list_content.push(0x80 | len as u8); // VarUInt (assumes < 128)
            }
            list_content.extend_from_slice(bytes);
        }

        // Build the struct content:
        // field SID 7 (symbols): VarUInt 0x87, then list
        let mut struct_content = Vec::new();
        struct_content.push(0x87); // VarUInt SID 7 (symbols)
                                   // List type descriptor
        let list_len = list_content.len();
        if list_len < 14 {
            struct_content.push(0xB0 | list_len as u8); // list type (11), inline length
        } else {
            struct_content.push(0xBE); // list type, VarUInt length
            struct_content.push(0x80 | list_len as u8); // VarUInt (assumes < 128)
        }
        struct_content.extend_from_slice(&list_content);

        // Struct type descriptor
        let struct_len = struct_content.len();
        let mut struct_td = Vec::new();
        if struct_len < 14 {
            struct_td.push(0xD0 | struct_len as u8); // struct type (13), inline length
        } else {
            struct_td.push(0xDE); // struct type, VarUInt length
            struct_td.push(0x80 | struct_len as u8);
        }
        struct_td.extend_from_slice(&struct_content);

        // Annotation wrapper:
        //   annot_length = 1 (one annotation SID, VarUInt 0x83 = SID 3)
        //   annotation SID 3 = VarUInt 0x83
        //   then the struct
        let annot_sids = vec![0x83u8]; // SID 3
        let annot_length_varuint = vec![0x81u8]; // VarUInt 1

        let wrapper_content_len = annot_length_varuint.len() + annot_sids.len() + struct_td.len();

        let mut result = Vec::new();
        if wrapper_content_len < 14 {
            result.push(0xE0 | wrapper_content_len as u8); // annotation type (14), inline length
        } else {
            result.push(0xEE); // annotation type, VarUInt length
            result.push(0x80 | wrapper_content_len as u8);
        }
        result.extend_from_slice(&annot_length_varuint);
        result.extend_from_slice(&annot_sids);
        result.extend_from_slice(&struct_td);

        result
    }

    #[test]
    fn lst_updates_symbol_table() {
        let lst_bytes = build_lst_bytes(&["foo", "bar", "baz"]);
        let (dest, _cp, gen) = generate_all_with_gen(lst_bytes);

        // Verify symbol table was updated
        let sym_table = gen.symbol_table();
        // System symbols (9) + 3 new symbols = 12
        assert_eq!(sym_table.len(), 12);
        assert_eq!(sym_table[9], Some("foo".to_string()));
        assert_eq!(sym_table[10], Some("bar".to_string()));
        assert_eq!(sym_table[11], Some("baz".to_string()));

        // Verify DIRECTIVE_SET_SYMBOLS was emitted
        let dir_idx = dest
            .iter()
            .position(|&w| Instruction::from_raw(w).operation() == op::DIRECTIVE_SET_SYMBOLS)
            .expect("should have DIRECTIVE_SET_SYMBOLS");
        assert_eq!(
            Instruction::from_raw(dest[dir_idx]).operation(),
            op::DIRECTIVE_SET_SYMBOLS
        );

        // Verify END_CONTAINER terminates the directive
        let end_idx = dest[dir_idx..]
            .iter()
            .position(|&w| Instruction::from_raw(w).operation() == op::END_CONTAINER)
            .expect("should have END_CONTAINER after directive");
        // There should be 3 STRING_REF entries between directive and end
        let directive_body = &dest[dir_idx + 1..dir_idx + end_idx];
        let string_ref_count = directive_body
            .iter()
            .filter(|&&w| Instruction::from_raw(w).operation() == op::STRING_REF)
            .count();
        assert_eq!(string_ref_count, 3);
    }

    #[test]
    fn lst_emits_refill_boundary() {
        let lst_bytes = build_lst_bytes(&["foo", "bar"]);
        let mut gen = BinaryIon10Generator::new(lst_bytes);
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();

        // First refill should process the LST and end with REFILL
        gen.refill(&mut dest, &mut cp);
        let last = *dest.last().unwrap();
        assert_eq!(
            Instruction::from_raw(last).operation(),
            op::REFILL,
            "LST should trigger a REFILL boundary"
        );
    }

    #[test]
    fn lst_not_emitted_as_user_value() {
        let lst_bytes = build_lst_bytes(&["foo"]);
        let (dest, _cp, _gen) = generate_all_with_gen(lst_bytes);

        // There should be no STRUCT_START or ANNOTATION_SID in the output,
        // because the LST is a system value, not a user value.
        for &word in &dest {
            let instr = Instruction::from_raw(word);
            assert_ne!(
                instr.operation(),
                op::STRUCT_START,
                "LST should not emit STRUCT_START"
            );
            assert_ne!(
                instr.operation(),
                op::ANNOTATION_SID,
                "LST should not emit ANNOTATION_SID"
            );
        }
    }

    #[test]
    fn lst_followed_by_symbol_values() {
        // LST with symbols ["foo", "bar"], then symbol values using those SIDs
        let mut source = build_lst_bytes(&["foo", "bar"]);
        // Symbol value SID 10 (first user symbol = system symbols 9 + 1)
        source.push(0x71); // symbol type, length 1
        source.push(0x0A); // SID 10
                           // Symbol value SID 11
        source.push(0x71); // symbol type, length 1
        source.push(0x0B); // SID 11

        let (dest, _cp, gen) = generate_all_with_gen(source);

        // Verify the symbol table has the expected entries
        assert_eq!(gen.symbol_table()[9], Some("foo".to_string()));
        assert_eq!(gen.symbol_table()[10], Some("bar".to_string()));

        // Find SYMBOL_SID instructions after the directive
        let symbol_sids: Vec<u32> = dest
            .iter()
            .filter(|&&w| Instruction::from_raw(w).operation() == op::SYMBOL_SID)
            .map(|&w| Instruction::from_raw(w).data())
            .collect();

        // Should have SID 10 and SID 11 (and possibly SID 0 from null
        // text in the directive — but our test LST has no nulls).
        assert!(
            symbol_sids.contains(&10),
            "should have SYMBOL_SID 10, got: {symbol_sids:?}"
        );
        assert!(
            symbol_sids.contains(&11),
            "should have SYMBOL_SID 11, got: {symbol_sids:?}"
        );
    }

    #[test]
    fn read_text_ref_returns_correct_string() {
        // Verify that read_text_ref works for STRING_REF instructions
        let source = vec![0x85, b'h', b'e', b'l', b'l', b'o'];
        let gen = BinaryIon10Generator::new(source);

        // The string "hello" starts at offset 1, length 5
        let text = gen.read_text_ref(1, 5).unwrap();
        assert_eq!(text, "hello");
    }

    #[test]
    fn read_text_ref_invalid_utf8() {
        // Verify that read_text_ref returns an error for invalid UTF-8
        let source = vec![0x82, 0xFF, 0xFE]; // string type, 2 bytes of invalid UTF-8
        let gen = BinaryIon10Generator::new(source);

        let result = gen.read_text_ref(1, 2);
        assert!(result.is_err());
    }

    #[test]
    fn lst_with_null_symbol() {
        // Build an LST with a null in the symbols list
        // struct { symbols: ["foo", null, "bar"] }
        // We need to manually build this since build_lst_bytes doesn't
        // support nulls.
        let mut list_content = Vec::new();
        // "foo" — string type 8, length 3
        list_content.extend_from_slice(&[0x83, b'f', b'o', b'o']);
        // null.string — type 8, L=15
        list_content.push(0x8F);
        // "bar" — string type 8, length 3
        list_content.extend_from_slice(&[0x83, b'b', b'a', b'r']);

        let list_len = list_content.len();
        let mut struct_content = Vec::new();
        struct_content.push(0x87); // VarUInt SID 7 (symbols)
        struct_content.push(0xB0 | list_len as u8); // list type, inline length
        struct_content.extend_from_slice(&list_content);

        let struct_len = struct_content.len();
        let mut struct_td = Vec::new();
        struct_td.push(0xD0 | struct_len as u8); // struct type, inline length
        struct_td.extend_from_slice(&struct_content);

        // Annotation wrapper: SID 3
        let wrapper_content_len = 1 + 1 + struct_td.len(); // annot_len_varuint + sid + struct
        let mut source = Vec::new();
        if wrapper_content_len < 14 {
            source.push(0xE0 | wrapper_content_len as u8);
        } else {
            source.push(0xEE); // annotation type, VarUInt length
            source.push(0x80 | wrapper_content_len as u8);
        }
        source.push(0x81); // annot_length = 1
        source.push(0x83); // SID 3
        source.extend_from_slice(&struct_td);

        let (_dest, _cp, gen) = generate_all_with_gen(source);

        // Verify: system symbols (9) + 3 new (foo, None, bar) = 12
        let sym_table = gen.symbol_table();
        assert_eq!(sym_table.len(), 12);
        assert_eq!(sym_table[9], Some("foo".to_string()));
        assert_eq!(sym_table[10], None); // null symbol text
        assert_eq!(sym_table[11], Some("bar".to_string()));
    }
}
