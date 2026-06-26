//! Parallel TLV materializer for Ion binary data.
//!
//! Materializes top-level values (TLVs) in parallel using Rayon. Since TLVs
//! within a single refill batch are independent (symbol table and constant
//! pool are read-only during materialization), they can be processed
//! concurrently.
//!
//! # Architecture
//!
//! 1. Run the generator sequentially to produce all bytecode
//! 2. Process IVM/DIRECTIVE instructions to build symbol table state
//! 3. Scan TLV boundaries in the bytecode
//! 4. Materialize TLVs in parallel using `rayon::par_iter`
//! 5. Collect results preserving original order

use std::sync::Arc;

use rayon::prelude::*;

use crate::bytecode::constant_pool::{Constant, ConstantPool};
use crate::bytecode::generator::BytecodeGenerator;
use crate::bytecode::instruction::{op, operation_kind, Instruction};
use crate::bytecode::ion10::BinaryIon10Generator;
use crate::bytecode::materialize::SYSTEM_SYMBOLS;
use crate::element::Annotations;
use crate::result::IonFailure;
use crate::{
    Bytes, Decimal, Element, Int, IonResult, IonType, Sequence, Str, Struct, Symbol, Timestamp,
    UInt, Value,
};

/// Reads all top-level values from binary Ion data, materializing TLVs in
/// parallel using Rayon.
///
/// This function:
/// 1. Generates all bytecode sequentially (generator is not Sync)
/// 2. Processes system values (IVM, directives) to build symbol table
/// 3. Identifies TLV boundaries
/// 4. Materializes each TLV in parallel
///
/// Falls back to sequential processing for inputs with fewer than 2 TLVs.
pub fn read_all_v3_parallel(data: &[u8]) -> IonResult<Sequence> {
    if data.first() != Some(&0xE0) {
        // Only binary Ion is supported for parallel materialization.
        // Fall back to the sequential path for text.
        return crate::bytecode::materialize::read_all_v3(data);
    }

    // Phase 1: Generate all bytecode sequentially.
    let mut generator = BinaryIon10Generator::new(data);
    let mut bytecode: Vec<u32> = Vec::new();
    let mut constant_pool = ConstantPool::new();

    // We do NOT truncate the constant pool between refills so that all CP
    // indices remain valid for the lifetime of the bytecode buffer.
    loop {
        generator.refill(&mut bytecode, &mut constant_pool)?;
        // Check if the last instruction is END_OF_INPUT
        if let Some(&last) = bytecode.last() {
            let instr = Instruction::from_raw(last);
            if instr.operation() == op::END_OF_INPUT {
                break;
            }
        }
        // If bytecode is empty after refill, the source is exhausted
        if bytecode.is_empty() {
            break;
        }
    }

    if bytecode.is_empty() {
        return Ok(Sequence::from(Vec::<Element>::new()));
    }

    // Phase 2 & 3: Process system values and scan TLV boundaries.
    let segments = scan_segments(&bytecode, &generator, &constant_pool)?;

    if segments.is_empty() {
        return Ok(Sequence::from(Vec::<Element>::new()));
    }

    // Phase 4: Chunk TLVs into N groups for coarse-grained parallelism.
    // This reduces Rayon dispatch overhead vs per-TLV scheduling.
    let num_chunks = rayon::current_num_threads().min(segments.len());
    let chunk_size = (segments.len() + num_chunks - 1) / num_chunks;
    let chunks: Vec<&[TlvSegment]> = segments.chunks(chunk_size).collect();

    // Phase 5: Materialize chunks in parallel. Each chunk produces a Vec.
    let chunk_results: Vec<IonResult<Vec<Element>>> = chunks
        .par_iter()
        .map(|chunk| {
            let mut elements = Vec::with_capacity(chunk.len());
            for segment in chunk.iter() {
                let mut materializer = TlvMaterializer {
                    bytecode: &bytecode[segment.start..segment.end],
                    pos: 0,
                    source: data,
                    symbol_table: &segment.symbol_table,
                    constant_pool: &constant_pool,
                };
                elements.push(materializer.read_element()?);
            }
            Ok(elements)
        })
        .collect();

    // Phase 6: Flatten results in order, propagating errors.
    let total = segments.len();
    let mut elements = Vec::with_capacity(total);
    for result in chunk_results {
        elements.extend(result?);
    }
    Ok(elements.into())
}

/// A segment represents a single TLV with its associated symbol table.
struct TlvSegment {
    /// Start index in the bytecode buffer (inclusive).
    start: usize,
    /// End index in the bytecode buffer (exclusive).
    end: usize,
    /// The symbol table snapshot at the point this TLV appears.
    symbol_table: Arc<[Option<Arc<str>>]>,
}

/// Scans the bytecode buffer to find TLV boundaries, processing IVM and
/// DIRECTIVE instructions along the way to maintain symbol table state.
fn scan_segments<S: AsRef<[u8]>>(
    bytecode: &[u32],
    generator: &BinaryIon10Generator<S>,
    constant_pool: &ConstantPool,
) -> IonResult<Vec<TlvSegment>> {
    let mut segments = Vec::new();
    let mut pos = 0;
    let mut symbol_table: Vec<Option<Arc<str>>> =
        SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
    let mut current_symtab: Option<Arc<[Option<Arc<str>>]>> = None;

    while pos < bytecode.len() {
        let instr = Instruction::from_raw(bytecode[pos]);
        match instr.operation_kind() {
            operation_kind::END => {
                // END_OF_INPUT, END_CONTAINER, END_TEMPLATE -- stop
                break;
            }
            operation_kind::REFILL => {
                // Skip REFILL markers (we already generated everything)
                pos += 1;
            }
            operation_kind::IVM => {
                // Reset symbol table
                symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
                current_symtab = None;
                pos += 1;
            }
            operation_kind::DIRECTIVE => {
                pos += 1;
                // Process directive to update symbol table
                process_directive(
                    bytecode,
                    &mut pos,
                    instr,
                    &mut symbol_table,
                    generator,
                    constant_pool,
                )?;
                current_symtab = None;
            }
            operation_kind::METADATA => {
                // Skip metadata instructions
                pos += 1;
                let oc = instr.operand_count_bits();
                if oc > 0 && oc < 3 {
                    pos += oc as usize;
                }
            }
            _ => {
                // This is the start of a TLV (possibly preceded by annotations).
                let tlv_start = pos;

                // Lazily create the Arc snapshot for this symbol table state
                let symtab =
                    current_symtab.get_or_insert_with(|| Arc::from(symbol_table.as_slice()));

                // Skip past this entire TLV to find where it ends.
                let tlv_end = skip_top_level_value(bytecode, pos);

                segments.push(TlvSegment {
                    start: tlv_start,
                    end: tlv_end,
                    symbol_table: Arc::clone(symtab),
                });

                pos = tlv_end;
            }
        }
    }

    Ok(segments)
}

/// Processes a DIRECTIVE instruction, updating the symbol table.
fn process_directive<S: AsRef<[u8]>>(
    bytecode: &[u32],
    pos: &mut usize,
    instr: Instruction,
    symbol_table: &mut Vec<Option<Arc<str>>>,
    generator: &BinaryIon10Generator<S>,
    constant_pool: &ConstantPool,
) -> IonResult<()> {
    let operation = instr.operation();
    match operation {
        op::DIRECTIVE_SET_SYMBOLS | op::DIRECTIVE_ADD_SYMBOLS => {
            if operation == op::DIRECTIVE_SET_SYMBOLS {
                *symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
            }

            // Read directive content until END_CONTAINER
            loop {
                let dir_instr = Instruction::from_raw(bytecode[*pos]);
                *pos += 1;
                match dir_instr.operation() {
                    op::END_CONTAINER => break,
                    op::STRING_REF => {
                        let length = dir_instr.data();
                        let position = bytecode[*pos];
                        *pos += 1;
                        match generator.read_text_ref(position, length) {
                            Ok(text) => {
                                symbol_table.push(Some(Arc::from(text)));
                            }
                            Err(_) => symbol_table.push(None),
                        }
                    }
                    op::STRING_CP => {
                        let index = dir_instr.data();
                        match constant_pool.get(index) {
                            Constant::String(arc) => {
                                symbol_table.push(Some(Arc::from(arc.as_ref())));
                            }
                            _ => symbol_table.push(None),
                        }
                    }
                    op::SYMBOL_SID => {
                        // SID 0 = unknown/null text
                        symbol_table.push(None);
                    }
                    _ => {
                        // Skip unknown instructions within the directive.
                        let oc = dir_instr.operand_count_bits();
                        if oc == 3 {
                            *pos += dir_instr.data() as usize;
                        } else {
                            *pos += oc as usize;
                        }
                    }
                }
            }
        }
        _ => {
            // For other directives: skip until END_CONTAINER.
            loop {
                let dir_instr = Instruction::from_raw(bytecode[*pos]);
                *pos += 1;
                if dir_instr.operation() == op::END_CONTAINER {
                    break;
                }
                let oc = dir_instr.operand_count_bits();
                if oc == 3 {
                    *pos += dir_instr.data() as usize;
                } else {
                    *pos += oc as usize;
                }
            }
        }
    }
    Ok(())
}

/// Skips a top-level value (including any preceding annotations or metadata)
/// and returns the position immediately after it.
fn skip_top_level_value(bytecode: &[u32], mut pos: usize) -> usize {
    // Skip leading annotations and metadata
    loop {
        let instr = Instruction::from_raw(bytecode[pos]);
        let kind = instr.operation_kind();
        if kind == operation_kind::ANNOTATIONS || kind == operation_kind::METADATA {
            pos += 1;
            let oc = instr.operand_count_bits();
            if oc > 0 && oc < 3 {
                pos += oc as usize;
            }
        } else {
            break;
        }
    }

    // Now skip the value itself
    skip_value(bytecode, pos)
}

/// Skips a single value instruction (and its children if container) and
/// returns the position immediately after.
fn skip_value(bytecode: &[u32], pos: usize) -> usize {
    let instr = Instruction::from_raw(bytecode[pos]);
    let oc = instr.operand_count_bits();
    if oc == 3 {
        // Container: data field = bytecode length of children (including END_CONTAINER)
        pos + 1 + instr.data() as usize
    } else {
        // Scalar: 1 instruction word + operand count words
        pos + 1 + oc as usize
    }
}

// ─── TLV Materializer ──────────────────────────────────────────────────

/// A materializer that walks a bytecode slice and produces an `Element`.
/// Designed to be called from parallel tasks -- holds only shared references.
struct TlvMaterializer<'a> {
    bytecode: &'a [u32],
    pos: usize,
    source: &'a [u8],
    symbol_table: &'a [Option<Arc<str>>],
    constant_pool: &'a ConstantPool,
}

impl<'a> TlvMaterializer<'a> {
    /// Reads the instruction at the current position and advances pos.
    #[inline(always)]
    fn consume(&mut self) -> Instruction {
        let raw = self.bytecode[self.pos];
        self.pos += 1;
        Instruction::from_raw(raw)
    }

    /// Reads the raw u32 at the current position and advances pos.
    #[inline(always)]
    fn consume_raw(&mut self) -> u32 {
        let raw = self.bytecode[self.pos];
        self.pos += 1;
        raw
    }

    /// Resolves a symbol ID to a `Symbol`.
    fn resolve_sid(&self, sid: usize) -> Symbol {
        if sid == 0 {
            return Symbol::unknown_text();
        }
        match self.symbol_table.get(sid - 1) {
            Some(Some(arc)) => Symbol::shared(Arc::clone(arc)),
            _ => Symbol::unknown_text(),
        }
    }

    /// Reads a complete element (annotations + value) at the current position.
    fn read_element(&mut self) -> IonResult<Element> {
        // Skip metadata
        while self.pos < self.bytecode.len() {
            let peek = Instruction::from_raw(self.bytecode[self.pos]);
            if peek.operation_kind() == operation_kind::METADATA {
                self.pos += 1;
                let oc = peek.operand_count_bits();
                if oc > 0 && oc < 3 {
                    self.pos += oc as usize;
                }
            } else {
                break;
            }
        }

        let annotations = self.read_annotations()?;
        let instr = self.consume();
        let value = self.read_value(instr)?;
        Ok(Element::new(annotations, value))
    }

    /// Reads annotations (if any) before the next value.
    fn read_annotations(&mut self) -> IonResult<Annotations> {
        let start = self.pos;
        let mut count: usize = 0;
        loop {
            if self.pos >= self.bytecode.len() {
                break;
            }
            let peek = Instruction::from_raw(self.bytecode[self.pos]);
            if peek.operation_kind() != operation_kind::ANNOTATIONS {
                break;
            }
            count += 1;
            self.pos += 1;
            let oc = peek.operand_count_bits();
            if oc > 0 && oc < 3 {
                self.pos += oc as usize;
            }
        }
        if count == 0 {
            return Ok(Annotations::empty());
        }
        // Go back and resolve them
        let mut symbols = Vec::with_capacity(count);
        let mut p = start;
        for _ in 0..count {
            let instr = Instruction::from_raw(self.bytecode[p]);
            p += 1;
            let data = instr.data();
            let symbol = match instr.operation() {
                op::ANNOTATION_SID => self.resolve_sid(data as usize),
                op::ANNOTATION_CP => match self.constant_pool.get(data) {
                    Constant::String(arc) => Symbol::shared(Arc::clone(arc)),
                    _ => return IonResult::decoding_error("annotation CP entry is not a string"),
                },
                op::ANNOTATION_REF => {
                    let position = self.bytecode[p];
                    p += 1;
                    let text = self.read_text_ref(position, data)?;
                    Symbol::from(text)
                }
                _ => return IonResult::decoding_error("expected annotation instruction"),
            };
            symbols.push(symbol);
        }
        Ok(Annotations::from(symbols))
    }

    /// Reads a value given its instruction.
    fn read_value(&mut self, instr: Instruction) -> IonResult<Value> {
        match instr.operation() {
            op::BOOL => Ok(Value::Bool(instr.data() & 1 == 1)),
            op::NULL_BOOL => Ok(Value::Null(IonType::Bool)),

            op::INT_I16 => Ok(Value::Int(Int::from(instr.data_as_i16() as i64))),
            op::INT_I32 => {
                let v = self.consume_raw() as i32;
                Ok(Value::Int(Int::from(v as i64)))
            }
            op::INT_I64 => {
                let hi = self.consume_raw() as u64;
                let lo = self.consume_raw() as u64;
                Ok(Value::Int(Int::from(((hi << 32) | lo) as i64)))
            }
            op::INT_CP => match self.constant_pool.get(instr.data()) {
                Constant::BigInt(arc) => Ok(Value::Int(arc.as_ref().clone())),
                _ => IonResult::decoding_error("CP entry is not BigInt"),
            },
            op::INT_REF => {
                let position = self.consume_raw();
                Ok(Value::Int(self.read_int_ref(position, instr.data())?))
            }
            op::NULL_INT => Ok(Value::Null(IonType::Int)),

            op::FLOAT_F32 => {
                let bits = self.consume_raw();
                Ok(Value::Float(f32::from_bits(bits) as f64))
            }
            op::FLOAT_F64 => {
                let hi = self.consume_raw() as u64;
                let lo = self.consume_raw() as u64;
                Ok(Value::Float(f64::from_bits((hi << 32) | lo)))
            }
            op::NULL_FLOAT => Ok(Value::Null(IonType::Float)),

            op::DECIMAL_CP => match self.constant_pool.get(instr.data()) {
                Constant::Decimal(arc) => Ok(Value::Decimal(arc.as_ref().clone())),
                _ => IonResult::decoding_error("CP entry is not Decimal"),
            },
            op::DECIMAL_REF => {
                let position = self.consume_raw();
                Ok(Value::Decimal(
                    self.read_decimal_ref(position, instr.data())?,
                ))
            }
            op::NULL_DECIMAL => Ok(Value::Null(IonType::Decimal)),

            op::TIMESTAMP_CP => match self.constant_pool.get(instr.data()) {
                Constant::Timestamp(arc) => Ok(Value::Timestamp(arc.as_ref().clone())),
                _ => IonResult::decoding_error("CP entry is not Timestamp"),
            },
            op::SHORT_TIMESTAMP_REF | op::TIMESTAMP_REF => {
                let position = self.consume_raw();
                Ok(Value::Timestamp(
                    self.read_timestamp_ref(position, instr.data())?,
                ))
            }
            op::NULL_TIMESTAMP => Ok(Value::Null(IonType::Timestamp)),

            op::STRING_CP => match self.constant_pool.get(instr.data()) {
                Constant::String(arc) => Ok(Value::String(Str::from(arc.as_ref()))),
                _ => IonResult::decoding_error("CP entry is not String"),
            },
            op::STRING_REF => {
                let position = self.consume_raw();
                let text = self.read_text_ref(position, instr.data())?;
                Ok(Value::String(Str::from(text)))
            }
            op::NULL_STRING => Ok(Value::Null(IonType::String)),

            op::SYMBOL_SID => {
                let sid = instr.data() as usize;
                Ok(Value::Symbol(self.resolve_sid(sid)))
            }
            op::SYMBOL_CP => match self.constant_pool.get(instr.data()) {
                Constant::String(arc) => Ok(Value::Symbol(Symbol::shared(Arc::clone(arc)))),
                _ => IonResult::decoding_error("CP entry is not String"),
            },
            op::SYMBOL_CHAR => {
                let ch = char::from_u32(instr.data()).ok_or_else(|| {
                    IonResult::<()>::decoding_error("invalid char code").unwrap_err()
                })?;
                let mut buf = [0u8; 4];
                let s = ch.encode_utf8(&mut buf);
                Ok(Value::Symbol(Symbol::from(&*s)))
            }
            op::SYMBOL_REF => {
                let position = self.consume_raw();
                let text = self.read_text_ref(position, instr.data())?;
                Ok(Value::Symbol(Symbol::from(text)))
            }
            op::NULL_SYMBOL => Ok(Value::Null(IonType::Symbol)),

            op::BLOB_CP => match self.constant_pool.get(instr.data()) {
                Constant::Bytes(arc) => Ok(Value::Blob(Bytes::from(arc.as_ref()))),
                _ => IonResult::decoding_error("CP entry is not Bytes"),
            },
            op::BLOB_REF => {
                let position = self.consume_raw();
                let bytes = self.read_bytes_ref(position, instr.data())?;
                Ok(Value::Blob(Bytes::from(bytes)))
            }
            op::NULL_BLOB => Ok(Value::Null(IonType::Blob)),

            op::CLOB_CP => match self.constant_pool.get(instr.data()) {
                Constant::Bytes(arc) => Ok(Value::Clob(Bytes::from(arc.as_ref()))),
                _ => IonResult::decoding_error("CP entry is not Bytes"),
            },
            op::CLOB_REF => {
                let position = self.consume_raw();
                let bytes = self.read_bytes_ref(position, instr.data())?;
                Ok(Value::Clob(Bytes::from(bytes)))
            }
            op::NULL_CLOB => Ok(Value::Null(IonType::Clob)),

            op::LIST_START => Ok(Value::List(self.read_sequence()?)),
            op::NULL_LIST => Ok(Value::Null(IonType::List)),

            op::SEXP_START => Ok(Value::SExp(self.read_sequence()?)),
            op::NULL_SEXP => Ok(Value::Null(IonType::SExp)),

            op::STRUCT_START => Ok(Value::Struct(self.read_struct()?)),
            op::NULL_STRUCT => Ok(Value::Null(IonType::Struct)),

            op::NULL_NULL => Ok(Value::Null(IonType::Null)),

            _ => IonResult::decoding_error(format!(
                "unexpected operation {:#04X} in parallel materializer",
                instr.operation()
            )),
        }
    }

    /// Reads a sequence (list or sexp children) until END_CONTAINER.
    fn read_sequence(&mut self) -> IonResult<Sequence> {
        let mut elements = Vec::new();
        loop {
            let peek = Instruction::from_raw(self.bytecode[self.pos]);
            if peek.operation() == op::END_CONTAINER {
                self.pos += 1;
                break;
            }
            elements.push(self.read_element()?);
        }
        Ok(Sequence::from(elements))
    }

    /// Reads a struct (field name/value pairs) until END_CONTAINER.
    fn read_struct(&mut self) -> IonResult<Struct> {
        let mut fields: Vec<(Symbol, Element)> = Vec::new();
        loop {
            let peek = Instruction::from_raw(self.bytecode[self.pos]);
            if peek.operation() == op::END_CONTAINER {
                self.pos += 1;
                break;
            }
            let field_name = self.read_field_name()?;
            let element = self.read_element()?;
            fields.push((field_name, element));
        }
        Ok(Struct::from_iter(fields))
    }

    /// Reads a field name instruction and resolves it to a `Symbol`.
    fn read_field_name(&mut self) -> IonResult<Symbol> {
        let instr = self.consume();
        let data = instr.data();
        match instr.operation() {
            op::FIELD_NAME_SID => Ok(self.resolve_sid(data as usize)),
            op::FIELD_NAME_CP => match self.constant_pool.get(data) {
                Constant::String(arc) => Ok(Symbol::shared(Arc::clone(arc))),
                _ => IonResult::decoding_error("field name CP entry is not a string"),
            },
            op::FIELD_NAME_REF => {
                let position = self.consume_raw();
                let text = self.read_text_ref(position, data)?;
                Ok(Symbol::from(text))
            }
            _ => IonResult::decoding_error("expected field name instruction"),
        }
    }

    // ─── REF resolution (operates directly on source bytes) ─────────

    /// Reads UTF-8 text from the source at the given position/length.
    fn read_text_ref(&self, position: u32, length: u32) -> IonResult<&'a str> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.source.len() {
            return IonResult::decoding_error("text reference out of bounds");
        }
        let bytes = &self.source[start..end];
        std::str::from_utf8(bytes).map_err(|e| {
            crate::IonError::decoding_error(format!(
                "invalid UTF-8 in string at offset {position}: {e}"
            ))
        })
    }

    /// Reads raw bytes from the source at the given position/length.
    fn read_bytes_ref(&self, position: u32, length: u32) -> IonResult<&'a [u8]> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.source.len() {
            return IonResult::decoding_error("bytes reference out of bounds");
        }
        Ok(&self.source[start..end])
    }

    /// Reads a big integer from the source at the given position/length.
    fn read_int_ref(&self, position: u32, length: u32) -> IonResult<Int> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.source.len() {
            return IonResult::decoding_error("int reference out of bounds");
        }
        let bytes = &self.source[start..end];
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

    /// Reads a decimal from the source at the given position/length.
    fn read_decimal_ref(&self, position: u32, length: u32) -> IonResult<Decimal> {
        if length == 0 {
            return Ok(Decimal::new(0i32, 0i64));
        }

        let start = position as usize;
        let end = start + length as usize;
        if end > self.source.len() {
            return IonResult::decoding_error("decimal reference out of bounds");
        }
        let bytes = &self.source[start..end];

        // Read VarInt exponent
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
                use std::ops::Neg;
                Int::from(&magnitude).neg()
            } else {
                Int::from(&magnitude)
            };

            Ok(Decimal::new(coefficient, exponent))
        }
    }

    /// Reads a timestamp from the source at the given position/length.
    fn read_timestamp_ref(&self, position: u32, length: u32) -> IonResult<Timestamp> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.source.len() {
            return IonResult::decoding_error("timestamp reference out of bounds");
        }
        let bytes = &self.source[start..end];

        if bytes.len() < 2 {
            return IonResult::decoding_error("timestamp too short");
        }

        let mut pos = 0;

        // Read VarInt offset
        let first_byte = bytes[pos];
        let is_negative_offset = (first_byte & 0x40) != 0;
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

        // Read VarUInt year
        if pos >= bytes.len() {
            return IonResult::decoding_error("timestamp missing year");
        }
        let year = read_var_uint_from_slice(bytes, &mut pos)?;

        let builder = Timestamp::with_year(year);
        if pos >= bytes.len() {
            return builder.build();
        }

        let month = read_var_uint_from_slice(bytes, &mut pos)?;
        let builder = builder.with_month(month);
        if pos >= bytes.len() {
            return builder.build();
        }

        let day = read_var_uint_from_slice(bytes, &mut pos)?;
        let builder = builder.with_day(day);
        if pos >= bytes.len() {
            return builder.build();
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

        // Fractional seconds
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
                        "timestamp fractional seconds coefficient must not be negative",
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
}

// ─── VarInt/VarUInt helpers (duplicated from ion10.rs since they are private) ─

/// VarUInt encoding constants.
const VARINT_STOP_BIT: u8 = 0x80;
const VARINT_SIGN_BIT: u8 = 0x40;
const VARINT_FIRST_BYTE_DATA_MASK: u8 = 0x3F;
const VARUINT_DATA_MASK: u8 = 0x7F;

/// Reads a VarUInt from a byte slice.
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

/// Reads a VarInt from a byte slice.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lazy::encoding::Encoding;
    use crate::v1_0;
    use rstest::rstest;

    /// Helper: encodes Ion text as binary Ion 1.0.
    fn encode_as_binary(text: &str) -> Vec<u8> {
        let elements = Element::read_all(text).unwrap();
        v1_0::Binary::encode_all(elements.iter()).unwrap()
    }

    #[rstest]
    #[case::integers("1 2 3")]
    #[case::booleans_and_null("true false null")]
    #[case::list("[1, 2, 3]")]
    #[case::struct_with_string("{foo: 1, bar: \"hello\"}")]
    #[case::annotated_int("ann::42")]
    #[case::decimals("1.23 -4.56d2")]
    #[case::timestamp("2024-01-15T10:30:00Z")]
    #[case::blob("{{aGVsbG8=}}")]
    #[case::positive_int("5")]
    #[case::negative_int("-100")]
    #[case::bool_true("true")]
    #[case::bool_false("false")]
    #[case::null_untyped("null")]
    #[case::null_bool("null.bool")]
    #[case::null_int("null.int")]
    #[case::null_string("null.string")]
    #[case::null_float("null.float")]
    #[case::null_decimal("null.decimal")]
    #[case::null_timestamp("null.timestamp")]
    #[case::null_symbol("null.symbol")]
    #[case::null_blob("null.blob")]
    #[case::null_clob("null.clob")]
    #[case::null_list("null.list")]
    #[case::null_sexp("null.sexp")]
    #[case::null_struct("null.struct")]
    #[case::string("\"hello world\"")]
    #[case::struct_multi_field("{foo: 1, bar: 2}")]
    #[case::multi_annotation("foo::bar::5")]
    #[case::nested_lists("[[[]]]")]
    #[case::nested_sexp("(1 2 (3 4))")]
    #[case::decimal_frac("1.23")]
    #[case::negative_zero_decimal("-0.")]
    #[case::decimal_exp("123d2")]
    #[case::timestamp_year("2024T")]
    #[case::timestamp_month("2024-01T")]
    #[case::timestamp_day("2024-01-15")]
    #[case::timestamp_minute("2024-01-15T10:30Z")]
    #[case::timestamp_second("2024-01-15T10:30:00Z")]
    #[case::timestamp_millis("2024-01-15T10:30:00.123Z")]
    #[case::timestamp_neg_offset("2024-01-15T10:30:00-00:00")]
    #[case::timestamp_pos_offset("2024-01-15T10:30:00+05:30")]
    #[case::clob("{{\"hello\"}}")]
    #[case::system_symbol("name")]
    #[case::empty_list("[]")]
    #[case::empty_sexp("()")]
    #[case::empty_struct("{}")]
    #[case::float_pi("3.14e0")]
    #[case::float_zero("0e0")]
    #[case::annotated_list("ann::[1,2]")]
    #[case::multiple_values("1 true \"hello\" [1, 2] {a: 1}")]
    #[case::many_structs("{a: 1} {b: 2} {c: 3} {d: 4} {e: 5}")]
    #[case::user_symbols("hello world foo bar baz")]
    fn parallel_matches_sequential(#[case] text: &str) -> IonResult<()> {
        let binary = encode_as_binary(text);
        let expected = Element::read_all(&binary)?;
        let parallel = read_all_v3_parallel(&binary)?;
        assert_eq!(
            expected, parallel,
            "mismatch for input: {text}\nexpected: {expected:?}\nparallel: {parallel:?}"
        );
        Ok(())
    }

    #[test]
    fn parallel_200_strings() -> IonResult<()> {
        let mut text_values = Vec::new();
        for i in 0..200 {
            text_values.push(format!("\"string_value_{i}\""));
        }
        let text = text_values.join(" ");
        let binary = encode_as_binary(&text);
        let expected = Element::read_all(&binary)?;
        let parallel = read_all_v3_parallel(&binary)?;
        assert_eq!(expected.len(), parallel.len());
        for (i, (e, p)) in expected.iter().zip(parallel.iter()).enumerate() {
            assert_eq!(e, p, "mismatch at index {i}");
        }
        Ok(())
    }

    #[test]
    fn parallel_empty_input() -> IonResult<()> {
        // Binary Ion with just the IVM and nothing else
        let binary: Vec<u8> = vec![0xE0, 0x01, 0x00, 0xEA];
        let expected = Element::read_all(&binary)?;
        let parallel = read_all_v3_parallel(&binary)?;
        assert_eq!(expected, parallel);
        Ok(())
    }

    #[test]
    fn parallel_mixed_types() -> IonResult<()> {
        let text = r#"
            1 -42 true false null null.int null.string
            3.14e0 1.23 -0. 123d2
            2024-01-15T10:30:00Z
            "hello" name
            {{aGVsbG8=}} {{"hello"}}
            [1, 2, 3] (a b c) {x: 1, y: 2}
            foo::bar::5
        "#;
        let binary = encode_as_binary(text);
        let expected = Element::read_all(&binary)?;
        let parallel = read_all_v3_parallel(&binary)?;
        assert_eq!(expected, parallel, "mismatch for mixed types input");
        Ok(())
    }
}
