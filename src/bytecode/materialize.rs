//! Element materialization from the bytecode reader.
//!
//! Provides functions to recursively build `Element` values from the
//! bytecode reader's state. The entry points (`read_all_v2` and
//! `read_one_v2`) detect the input format, create the appropriate
//! generator, and wire up the pipeline.
//!
//! `read_all_v3` bypasses the `BytecodeReader` entirely, walking bytecode
//! linearly to produce `Element` values directly for the "always
//! materialize everything" use case.

use std::sync::Arc;

use crate::bytecode::constant_pool::{Constant, ConstantPool};
use crate::bytecode::generator::BytecodeGenerator;
use crate::bytecode::instruction::{op, operation_kind, Instruction};
use crate::bytecode::ion10::BinaryIon10Generator;
use crate::bytecode::reader::{BytecodeReader, SymbolToken};
use crate::element::Annotations;
use crate::result::IonFailure;
use crate::{Bytes, Element, Int, IonResult, IonType, Sequence, Str, Struct, Symbol, Value};

/// Reads all top-level values from Ion data using the bytecode reader
/// pipeline. Auto-detects binary (starts with 0xE0) vs text format.
pub fn read_all_v2(data: &[u8]) -> IonResult<Sequence> {
    if data.first() == Some(&0xE0) {
        let generator = BinaryIon10Generator::new(data);
        let mut reader = BytecodeReader::with_generator(generator);
        let mut elements = Vec::new();
        while reader.next()?.is_some() {
            elements.push(materialize_element(&mut reader)?);
        }
        Ok(elements.into())
    } else {
        let source = std::str::from_utf8(data)
            .map_err(|_| crate::IonError::decoding_error("invalid UTF-8 in text Ion input"))?;
        use crate::bytecode::str_text10::StrTextIon10Generator;
        let generator = StrTextIon10Generator::new(source);
        let mut reader = BytecodeReader::with_generator(generator);
        let mut elements = Vec::new();
        while reader.next()?.is_some() {
            elements.push(materialize_element(&mut reader)?);
        }
        Ok(elements.into())
    }
}

/// Reads a single top-level value from binary Ion data using the
/// bytecode reader pipeline. Returns the first materialized `Element`.
pub(crate) fn read_one_v2(data: &[u8]) -> IonResult<Element> {
    let generator = BinaryIon10Generator::new(data);
    let mut reader = BytecodeReader::with_generator(generator);
    match reader.next()? {
        Some(_) => materialize_element(&mut reader),
        None => IonResult::decoding_error("empty input"),
    }
}

// ─── read_all_v3: linear bytecode walker ────────────────────────────

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

/// Reads all top-level values from Ion data by walking the bytecode
/// linearly, bypassing the `BytecodeReader` state machine. This is
/// optimized for the "always materialize everything" use case.
/// Auto-detects binary (starts with 0xE0) vs text format.
pub fn read_all_v3(data: &[u8]) -> IonResult<Sequence> {
    if data.first() == Some(&0xE0) {
        let generator = BinaryIon10Generator::new(data);
        let mut iter = BytecodeElementIterator::new(generator)?;
        let mut elements = Vec::new();
        for result in &mut iter {
            elements.push(result?);
        }
        Ok(elements.into())
    } else {
        let source = std::str::from_utf8(data)
            .map_err(|_| crate::IonError::decoding_error("invalid UTF-8 in text Ion input"))?;
        use crate::bytecode::str_text10::StrTextIon10Generator;
        let generator = StrTextIon10Generator::new(source);
        let mut iter = BytecodeElementIterator::new(generator)?;
        let mut elements = Vec::new();
        for result in &mut iter {
            elements.push(result?);
        }
        Ok(elements.into())
    }
}

/// Reads all top-level values from text Ion data using the streaming
/// text generator. This simulates reading from an `io::Read` source.
pub fn read_all_v3_streaming_text(data: &[u8]) -> IonResult<Sequence> {
    use crate::bytecode::text10::StreamingTextIon10Generator;
    use std::io::Cursor;
    let generator = StreamingTextIon10Generator::new(Cursor::new(data));
    let mut iter = BytecodeElementIterator::new(generator)?;
    let mut elements = Vec::new();
    for result in &mut iter {
        elements.push(result?);
    }
    Ok(elements.into())
}

/// Reads all top-level values from binary Ion data using the v3 direct
/// materializer. Forces the binary path regardless of content.
pub fn read_all_v3_binary(data: &[u8]) -> IonResult<Sequence> {
    let generator = BinaryIon10Generator::new(data);
    let mut iter = BytecodeElementIterator::new(generator)?;
    let mut elements = Vec::new();
    for result in &mut iter {
        elements.push(result?);
    }
    Ok(elements.into())
}

/// Reads all top-level values from text Ion data using the in-memory
/// `&str` generator. Forces the str-text path regardless of content.
pub fn read_all_v3_str_text(data: &[u8]) -> IonResult<Sequence> {
    let source = std::str::from_utf8(data)
        .map_err(|_| crate::IonError::decoding_error("invalid UTF-8 in text Ion input"))?;
    use crate::bytecode::str_text10::StrTextIon10Generator;
    let generator = StrTextIon10Generator::new(source);
    let mut iter = BytecodeElementIterator::new(generator)?;
    let mut elements = Vec::new();
    for result in &mut iter {
        elements.push(result?);
    }
    Ok(elements.into())
}

/// An iterator that walks bytecode linearly, producing materialized
/// `Element` values without the overhead of the `BytecodeReader` state
/// machine.
struct BytecodeElementIterator<G: BytecodeGenerator> {
    generator: G,
    bytecode: Vec<u32>,
    pos: usize,
    symbol_table: Vec<Option<Arc<str>>>,
    constant_pool: ConstantPool,
    first_local_constant: usize,
}

impl<G: BytecodeGenerator> BytecodeElementIterator<G> {
    fn new(generator: G) -> IonResult<Self> {
        let symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
        let mut iter = Self {
            generator,
            bytecode: Vec::new(),
            pos: 0,
            symbol_table,
            constant_pool: ConstantPool::new(),
            first_local_constant: 0,
        };
        // Perform initial refill to populate bytecode.
        iter.refill()?;
        Ok(iter)
    }

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

    /// Clears the bytecode buffer, truncates the constant pool, and asks
    /// the generator to refill.
    fn refill(&mut self) -> IonResult<()> {
        self.constant_pool.truncate(self.first_local_constant);
        self.bytecode.clear();
        self.generator
            .refill(&mut self.bytecode, &mut self.constant_pool)?;
        self.pos = 0;
        Ok(())
    }

    /// Handles an IVM instruction — resets the symbol table to system
    /// symbols only.
    fn handle_ivm(&mut self, _instruction: Instruction) {
        self.symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
    }

    /// Handles a directive instruction. Reads the directive content
    /// (symbol entries until END_CONTAINER) and updates the symbol table.
    fn handle_directive(&mut self, instruction: Instruction) -> IonResult<()> {
        let operation = instruction.operation();
        match operation {
            op::DIRECTIVE_SET_SYMBOLS | op::DIRECTIVE_ADD_SYMBOLS => {
                if operation == op::DIRECTIVE_SET_SYMBOLS {
                    self.symbol_table =
                        SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
                }

                // Read directive content until END_CONTAINER
                loop {
                    let instr = self.consume();
                    match instr.operation() {
                        op::END_CONTAINER => break,
                        op::STRING_REF => {
                            let length = instr.data();
                            let position = self.consume_raw();
                            match self.generator.read_text_ref(position, length) {
                                Ok(text) => {
                                    self.symbol_table.push(Some(Arc::from(text)));
                                }
                                Err(_) => self.symbol_table.push(None),
                            }
                        }
                        op::STRING_CP => {
                            let index = instr.data();
                            match self.constant_pool.get(index) {
                                Constant::String(rc) => {
                                    self.symbol_table.push(Some(Arc::from(rc.as_ref())));
                                }
                                _ => self.symbol_table.push(None),
                            }
                        }
                        op::SYMBOL_SID => {
                            // SID 0 = unknown/null text
                            self.symbol_table.push(None);
                        }
                        _ => {
                            // Skip unknown instructions within the directive.
                            let oc = instr.operand_count_bits();
                            if oc == 3 {
                                self.pos += instr.data() as usize;
                            } else {
                                self.pos += oc as usize;
                            }
                        }
                    }
                }
            }
            _ => {
                // For other directives: skip until END_CONTAINER.
                loop {
                    let instr = self.consume();
                    if instr.operation() == op::END_CONTAINER {
                        break;
                    }
                    let oc = instr.operand_count_bits();
                    if oc == 3 {
                        self.pos += instr.data() as usize;
                    } else {
                        self.pos += oc as usize;
                    }
                }
            }
        }
        Ok(())
    }

    /// Reads annotations (if any) before the next value.
    fn read_annotations(&mut self) -> IonResult<Annotations> {
        // Peek at upcoming instructions — collect ANNOTATION_* until we
        // hit a non-annotation.
        let start = self.pos;
        let mut count: usize = 0;
        loop {
            let peek = Instruction::from_raw(self.bytecode[self.pos]);
            if peek.operation_kind() != operation_kind::ANNOTATIONS {
                break;
            }
            count += 1;
            self.pos += 1;
            // Skip operand for ANNOTATION_REF
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
                    let text = self.generator.read_text_ref(position, data)?;
                    Symbol::from(text)
                }
                _ => return IonResult::decoding_error("expected annotation instruction"),
            };
            symbols.push(symbol);
        }
        Ok(Annotations::from(symbols))
    }

    /// Reads a complete element (annotations + value) at the current
    /// position.
    fn read_element(&mut self) -> IonResult<Element> {
        let annotations = self.read_annotations()?;
        let instr = self.consume();
        let value = self.read_value(instr)?;
        Ok(Element::new(annotations, value))
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
                Ok(Value::Int(
                    self.generator.read_int_ref(position, instr.data())?,
                ))
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
                    self.generator.read_decimal_ref(position, instr.data())?,
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
                    self.generator.read_timestamp_ref(position, instr.data())?,
                ))
            }
            op::NULL_TIMESTAMP => Ok(Value::Null(IonType::Timestamp)),

            op::STRING_CP => match self.constant_pool.get(instr.data()) {
                Constant::String(arc) => Ok(Value::String(Str::from(arc.as_ref()))),
                _ => IonResult::decoding_error("CP entry is not String"),
            },
            op::STRING_REF => {
                let position = self.consume_raw();
                let text = self.generator.read_text_ref(position, instr.data())?;
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
                let text = self.generator.read_text_ref(position, instr.data())?;
                Ok(Value::Symbol(Symbol::from(text)))
            }
            op::NULL_SYMBOL => Ok(Value::Null(IonType::Symbol)),

            op::BLOB_CP => match self.constant_pool.get(instr.data()) {
                Constant::Bytes(arc) => Ok(Value::Blob(Bytes::from(arc.as_ref()))),
                _ => IonResult::decoding_error("CP entry is not Bytes"),
            },
            op::BLOB_REF => {
                let position = self.consume_raw();
                let bytes = self.generator.read_bytes_ref(position, instr.data())?;
                Ok(Value::Blob(Bytes::from(bytes)))
            }
            op::NULL_BLOB => Ok(Value::Null(IonType::Blob)),

            op::CLOB_CP => match self.constant_pool.get(instr.data()) {
                Constant::Bytes(arc) => Ok(Value::Clob(Bytes::from(arc.as_ref()))),
                _ => IonResult::decoding_error("CP entry is not Bytes"),
            },
            op::CLOB_REF => {
                let position = self.consume_raw();
                let bytes = self.generator.read_bytes_ref(position, instr.data())?;
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
                "unexpected operation {:#04X}",
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
                let text = self.generator.read_text_ref(position, data)?;
                Ok(Symbol::from(text))
            }
            _ => IonResult::decoding_error("expected field name instruction"),
        }
    }
}

impl<G: BytecodeGenerator> Iterator for BytecodeElementIterator<G> {
    type Item = IonResult<Element>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.pos >= self.bytecode.len() {
                return None;
            }
            let peek = Instruction::from_raw(self.bytecode[self.pos]);
            match peek.operation_kind() {
                operation_kind::END => {
                    return None;
                }
                operation_kind::REFILL => {
                    if let Err(e) = self.refill() {
                        return Some(Err(e));
                    }
                    continue;
                }
                operation_kind::IVM => {
                    self.pos += 1;
                    self.handle_ivm(peek);
                    continue;
                }
                operation_kind::DIRECTIVE => {
                    self.pos += 1;
                    if let Err(e) = self.handle_directive(peek) {
                        return Some(Err(e));
                    }
                    continue;
                }
                operation_kind::METADATA => {
                    // Skip metadata instructions (offset, rowcol, comment)
                    self.pos += 1;
                    let oc = peek.operand_count_bits();
                    if oc > 0 && oc < 3 {
                        self.pos += oc as usize;
                    }
                    continue;
                }
                _ => {
                    return Some(self.read_element());
                }
            }
        }
    }
}

// ─── read_all_v2 / read_one_v2: reader-based materialization ────────

/// Materializes the current value from the reader into an `Element`.
///
/// The reader must be positioned on a value (i.e., `next()` returned
/// `Some`). This function reads annotations, resolves the value based
/// on its Ion type, and recursively processes containers.
fn materialize_element<G: BytecodeGenerator>(reader: &mut BytecodeReader<G>) -> IonResult<Element> {
    // Read annotations
    let annotations = materialize_annotations(reader)?;

    // Read the value
    let value = materialize_value(reader)?;

    Ok(Element::new(annotations, value))
}

/// Resolves annotations from the reader into an `Annotations` value.
fn materialize_annotations<G: BytecodeGenerator>(
    reader: &BytecodeReader<G>,
) -> IonResult<Annotations> {
    if !reader.has_annotations() {
        return Ok(Annotations::empty());
    }

    let mut symbols = Vec::with_capacity(reader.annotation_count() as usize);
    for token_result in reader.annotations() {
        let token = token_result?;
        symbols.push(resolve_symbol_token(&token, reader.symbol_table()));
    }
    Ok(Annotations::from(symbols))
}

/// Converts a `SymbolToken` to a `Symbol` using the symbol table.
fn resolve_symbol_token(token: &SymbolToken, symbol_table: &[Option<Arc<str>>]) -> Symbol {
    match token {
        SymbolToken::Sid(sid) => {
            // SID 0 is always unknown text
            if *sid == 0 {
                return Symbol::unknown_text();
            }
            // Look up in symbol table (1-indexed: SID 1 = index 0)
            let index = *sid - 1;
            match symbol_table.get(index) {
                Some(Some(arc)) => Symbol::shared(Arc::clone(arc)),
                Some(None) | None => Symbol::unknown_text(),
            }
        }
        SymbolToken::Text(arc) => Symbol::shared(Arc::clone(arc)),
    }
}

/// Reads the current value from the reader based on its Ion type.
fn materialize_value<G: BytecodeGenerator>(reader: &mut BytecodeReader<G>) -> IonResult<Value> {
    let ion_type = reader
        .ion_type()
        .ok_or_else(|| IonResult::<()>::decoding_error("no current value").unwrap_err())?;

    // Handle nulls
    if reader.is_null() {
        return Ok(Value::Null(ion_type));
    }

    match ion_type {
        IonType::Null => Ok(Value::Null(IonType::Null)),
        IonType::Bool => Ok(Value::Bool(reader.bool_value()?)),
        IonType::Int => Ok(Value::Int(reader.int_value()?)),
        IonType::Float => Ok(Value::Float(reader.f64_value()?)),
        IonType::Decimal => Ok(Value::Decimal(reader.decimal_value()?)),
        IonType::Timestamp => Ok(Value::Timestamp(reader.timestamp_value()?)),
        IonType::Symbol => {
            let symbol = materialize_symbol_value(reader)?;
            Ok(Value::Symbol(symbol))
        }
        IonType::String => {
            let text = reader.string_value()?;
            Ok(Value::String(Str::from(text.as_ref())))
        }
        IonType::Clob => {
            let bytes = reader.lob_value()?;
            Ok(Value::Clob(Bytes::from(bytes.as_ref())))
        }
        IonType::Blob => {
            let bytes = reader.lob_value()?;
            Ok(Value::Blob(Bytes::from(bytes.as_ref())))
        }
        IonType::List => {
            let children = materialize_sequence(reader)?;
            Ok(Value::List(children))
        }
        IonType::SExp => {
            let children = materialize_sequence(reader)?;
            Ok(Value::SExp(children))
        }
        IonType::Struct => {
            let s = materialize_struct(reader)?;
            Ok(Value::Struct(s))
        }
    }
}

/// Reads the current symbol value from the reader and resolves it.
fn materialize_symbol_value<G: BytecodeGenerator>(reader: &BytecodeReader<G>) -> IonResult<Symbol> {
    let instruction = reader.instruction();
    let data = instruction.data();

    match instruction.operation() {
        op::SYMBOL_SID => {
            let sid = data as usize;
            if sid == 0 {
                Ok(Symbol::unknown_text())
            } else {
                let index = sid - 1;
                match reader.symbol_table().get(index) {
                    Some(Some(arc)) => Ok(Symbol::shared(Arc::clone(arc))),
                    Some(None) | None => Ok(Symbol::unknown_text()),
                }
            }
        }
        op::SYMBOL_CP => match reader.constant_pool().get(data) {
            Constant::String(rc) => Ok(Symbol::from(rc.as_ref())),
            _ => IonResult::decoding_error("symbol CP entry is not a string"),
        },
        op::SYMBOL_CHAR => {
            let ch = char::from_u32(data)
                .ok_or_else(|| IonResult::<()>::decoding_error("invalid char code").unwrap_err())?;
            let mut buf = [0u8; 4];
            let s = ch.encode_utf8(&mut buf);
            Ok(Symbol::from(&*s))
        }
        op::SYMBOL_REF => {
            // STRING_REF-style: data is length, operand at reader.i is offset.
            // We need to use the string_value pattern but for symbols. Since
            // the reader's string_value() requires STRING_REF operation, we use
            // the generator's read_text_ref directly is not available via public
            // API. Instead, we'll adapt: the symbol reader is positioned on
            // SYMBOL_REF which shares the same layout as STRING_REF.
            // We can't call string_value() because it checks op::STRING_REF.
            // For now, treat this as unresolved.
            IonResult::decoding_error("SYMBOL_REF resolution not yet implemented")
        }
        _ => IonResult::decoding_error("not positioned on a symbol value"),
    }
}

/// Steps into a container and materializes all children as a `Sequence`.
fn materialize_sequence<G: BytecodeGenerator>(
    reader: &mut BytecodeReader<G>,
) -> IonResult<Sequence> {
    reader.step_in()?;
    let mut elements = Vec::new();
    while reader.next()?.is_some() {
        elements.push(materialize_element(reader)?);
    }
    reader.step_out()?;
    Ok(Sequence::from(elements))
}

/// Steps into a struct and materializes all field name/value pairs.
fn materialize_struct<G: BytecodeGenerator>(reader: &mut BytecodeReader<G>) -> IonResult<Struct> {
    reader.step_in()?;
    let mut fields: Vec<(Symbol, Element)> = Vec::new();
    while reader.next()?.is_some() {
        let field_name = match reader.field_name()? {
            Some(token) => resolve_symbol_token(&token, reader.symbol_table()),
            None => Symbol::unknown_text(),
        };
        let element = materialize_element(reader)?;
        fields.push((field_name, element));
    }
    reader.step_out()?;
    Ok(Struct::from_iter(fields))
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

    #[test]
    fn read_one_v2_integer() -> IonResult<()> {
        let binary = encode_as_binary("5");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Int(5.into()));
        Ok(())
    }

    #[test]
    fn read_one_v2_negative_integer() -> IonResult<()> {
        let binary = encode_as_binary("-42");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Int((-42).into()));
        Ok(())
    }

    #[test]
    fn read_one_v2_bool() -> IonResult<()> {
        let binary = encode_as_binary("true");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Bool(true));
        Ok(())
    }

    #[test]
    fn read_one_v2_float() -> IonResult<()> {
        let binary = encode_as_binary("3.14e0");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Float(3.14));
        Ok(())
    }

    #[test]
    fn read_one_v2_string() -> IonResult<()> {
        let binary = encode_as_binary("\"hello\"");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::String(Str::from("hello")));
        Ok(())
    }

    #[test]
    fn read_one_v2_null() -> IonResult<()> {
        let binary = encode_as_binary("null");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Null(IonType::Null));
        Ok(())
    }

    #[test]
    fn read_one_v2_null_int() -> IonResult<()> {
        let binary = encode_as_binary("null.int");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Null(IonType::Int));
        Ok(())
    }

    #[test]
    fn read_one_v2_symbol() -> IonResult<()> {
        let binary = encode_as_binary("name");
        let element = read_one_v2(&binary)?;
        // "name" is system symbol SID 4
        assert_eq!(element.value(), &Value::Symbol(Symbol::from("name")));
        Ok(())
    }

    #[test]
    fn read_all_v2_multiple_values() -> IonResult<()> {
        let binary = encode_as_binary("1 2 3");
        let seq = read_all_v2(&binary)?;
        assert_eq!(seq.len(), 3);
        assert_eq!(seq.get(0).unwrap().value(), &Value::Int(1.into()));
        assert_eq!(seq.get(1).unwrap().value(), &Value::Int(2.into()));
        assert_eq!(seq.get(2).unwrap().value(), &Value::Int(3.into()));
        Ok(())
    }

    #[test]
    fn read_one_v2_list() -> IonResult<()> {
        let binary = encode_as_binary("[1, 2, 3]");
        let element = read_one_v2(&binary)?;
        if let Value::List(seq) = element.value() {
            assert_eq!(seq.len(), 3);
            assert_eq!(seq.get(0).unwrap().value(), &Value::Int(1.into()));
            assert_eq!(seq.get(1).unwrap().value(), &Value::Int(2.into()));
            assert_eq!(seq.get(2).unwrap().value(), &Value::Int(3.into()));
        } else {
            panic!("expected a list, got {:?}", element.value());
        }
        Ok(())
    }

    #[test]
    fn read_one_v2_sexp() -> IonResult<()> {
        let binary = encode_as_binary("(1 2 3)");
        let element = read_one_v2(&binary)?;
        if let Value::SExp(seq) = element.value() {
            assert_eq!(seq.len(), 3);
        } else {
            panic!("expected an sexp, got {:?}", element.value());
        }
        Ok(())
    }

    #[test]
    fn read_one_v2_struct_with_lst() -> IonResult<()> {
        let binary = encode_as_binary("{foo: 1}");
        let element = read_one_v2(&binary)?;
        if let Value::Struct(s) = element.value() {
            let field = s.get("foo");
            assert!(field.is_some(), "struct should have field 'foo'");
            assert_eq!(field.unwrap().value(), &Value::Int(1.into()));
        } else {
            panic!("expected a struct, got {:?}", element.value());
        }
        Ok(())
    }

    #[test]
    fn read_one_v2_annotations() -> IonResult<()> {
        let binary = encode_as_binary("foo::5");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Int(5.into()));
        let annotations: Vec<&Symbol> = element.annotations().iter().collect();
        assert_eq!(annotations.len(), 1);
        assert_eq!(annotations[0].text(), Some("foo"));
        Ok(())
    }

    #[test]
    fn read_one_v2_multiple_annotations() -> IonResult<()> {
        let binary = encode_as_binary("foo::bar::5");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Int(5.into()));
        let annotations: Vec<&Symbol> = element.annotations().iter().collect();
        assert_eq!(annotations.len(), 2);
        assert_eq!(annotations[0].text(), Some("foo"));
        assert_eq!(annotations[1].text(), Some("bar"));
        Ok(())
    }

    #[test]
    fn read_one_v2_nested_list() -> IonResult<()> {
        let binary = encode_as_binary("[[1, 2], [3]]");
        let element = read_one_v2(&binary)?;
        if let Value::List(outer) = element.value() {
            assert_eq!(outer.len(), 2);
            if let Value::List(inner1) = outer.get(0).unwrap().value() {
                assert_eq!(inner1.len(), 2);
            } else {
                panic!("expected inner list");
            }
            if let Value::List(inner2) = outer.get(1).unwrap().value() {
                assert_eq!(inner2.len(), 1);
            } else {
                panic!("expected inner list");
            }
        } else {
            panic!("expected a list");
        }
        Ok(())
    }

    #[test]
    fn read_one_v2_empty_input() {
        // Binary Ion with just the IVM and nothing else
        let binary: Vec<u8> = vec![0xE0, 0x01, 0x00, 0xEA];
        let result = read_one_v2(&binary);
        assert!(result.is_err());
    }

    #[test]
    fn read_one_v2_matches_existing_reader() -> IonResult<()> {
        let test_cases = &[
            "5",
            "-100",
            "true",
            "false",
            "null",
            "null.bool",
            "null.int",
            "null.string",
            "\"hello world\"",
            "[1, 2, 3]",
            "{foo: 1, bar: 2}",
            "foo::bar::5",
            "[[[]]]",
            "(1 2 (3 4))",
            "1.23",
            "-0.",
            "123d2",
            "2024T",
            "2024-01T",
            "2024-01-15",
            "2024-01-15T10:30Z",
            "2024-01-15T10:30:00Z",
            "2024-01-15T10:30:00.123Z",
            "2024-01-15T10:30:00-00:00",
            "2024-01-15T10:30:00+05:30",
        ];

        for text in test_cases {
            let binary = encode_as_binary(text);
            let expected = Element::read_one(&binary)?;
            let actual = read_one_v2(&binary)?;
            assert_eq!(
                expected, actual,
                "mismatch for input: {text}\nexpected: {expected:?}\nactual: {actual:?}"
            );
        }
        Ok(())
    }

    #[test]
    fn read_all_v2_matches_existing_reader() -> IonResult<()> {
        let text = "1 true \"hello\" [1, 2] {a: 1}";
        let binary = encode_as_binary(text);
        let expected = Element::read_all(&binary)?;
        let actual = read_all_v2(&binary)?;
        assert_eq!(expected, actual);
        Ok(())
    }

    #[test]
    fn read_one_v2_user_symbol() -> IonResult<()> {
        // "hello" is not a system symbol, so it must go through an LST
        let binary = encode_as_binary("hello");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Symbol(Symbol::from("hello")));
        Ok(())
    }

    #[test]
    fn read_one_v2_struct_multiple_fields() -> IonResult<()> {
        let binary = encode_as_binary("{a: 1, b: 2, c: 3}");
        let element = read_one_v2(&binary)?;
        if let Value::Struct(s) = element.value() {
            assert_eq!(s.get("a").unwrap().value(), &Value::Int(1.into()));
            assert_eq!(s.get("b").unwrap().value(), &Value::Int(2.into()));
            assert_eq!(s.get("c").unwrap().value(), &Value::Int(3.into()));
        } else {
            panic!("expected a struct");
        }
        Ok(())
    }

    #[test]
    fn read_all_v2_many_short_strings() -> IonResult<()> {
        // Generate a stream of 20 short strings
        let mut text_values = Vec::new();
        for i in 0..20 {
            text_values.push(format!("\"str{i}\""));
        }
        let text = text_values.join(" ");
        let binary = encode_as_binary(&text);
        let expected = Element::read_all(&binary)?;
        let actual = read_all_v2(&binary)?;
        assert_eq!(expected.len(), actual.len());
        for (i, (e, a)) in expected.iter().zip(actual.iter()).enumerate() {
            assert_eq!(e, a, "mismatch at index {i}");
        }
        Ok(())
    }

    #[test]
    fn read_all_v2_long_strings() -> IonResult<()> {
        // Generate strings that exceed 13 bytes (VarUInt length in Ion 1.0)
        let mut text_values = Vec::new();
        for i in 0..20 {
            let long_str = format!("\"this_is_a_longer_string_value_number_{i}\"");
            text_values.push(long_str);
        }
        let text = text_values.join(" ");
        let binary = encode_as_binary(&text);
        let expected = Element::read_all(&binary)?;
        let actual = read_all_v2(&binary)?;
        assert_eq!(expected.len(), actual.len());
        for (i, (e, a)) in expected.iter().zip(actual.iter()).enumerate() {
            assert_eq!(e, a, "mismatch at index {i}");
        }
        Ok(())
    }

    #[test]
    fn read_all_v2_100_strings() -> IonResult<()> {
        // Generate 100 strings - this tests that the generator correctly
        // handles VarUInt-encoded lengths >= 15 (the old null sentinel).
        let mut text_values = Vec::new();
        for i in 0..100 {
            text_values.push(format!("\"string_value_{i}\""));
        }
        let text = text_values.join(" ");
        let binary = encode_as_binary(&text);
        let expected = Element::read_all(&binary)?;
        let actual = read_all_v2(&binary)?;
        assert_eq!(expected.len(), actual.len());
        for (i, (e, a)) in expected.iter().zip(actual.iter()).enumerate() {
            assert_eq!(e, a, "mismatch at index {i}");
        }
        Ok(())
    }

    #[test]
    fn read_all_v2_200_strings() -> IonResult<()> {
        // Stress test with 200 strings to ensure no hang or panic
        let mut text_values = Vec::new();
        for i in 0..200 {
            text_values.push(format!("\"string_value_{i}\""));
        }
        let text = text_values.join(" ");
        let binary = encode_as_binary(&text);
        let expected = Element::read_all(&binary)?;
        let actual = read_all_v2(&binary)?;
        assert_eq!(expected.len(), actual.len());
        for (i, (e, a)) in expected.iter().zip(actual.iter()).enumerate() {
            assert_eq!(e, a, "mismatch at index {i}");
        }
        Ok(())
    }

    #[test]
    fn read_one_v2_blob() -> IonResult<()> {
        // {{aGVsbG8=}} is base64 for "hello"
        let binary = encode_as_binary("{{aGVsbG8=}}");
        let expected = Element::read_one(&binary)?;
        let actual = read_one_v2(&binary)?;
        assert_eq!(expected, actual);
        assert_eq!(
            actual.value(),
            &Value::Blob(Bytes::from(b"hello".as_slice()))
        );
        Ok(())
    }

    #[test]
    fn read_one_v2_clob() -> IonResult<()> {
        let binary = encode_as_binary("{{\"hello\"}}");
        let expected = Element::read_one(&binary)?;
        let actual = read_one_v2(&binary)?;
        assert_eq!(expected, actual);
        assert_eq!(
            actual.value(),
            &Value::Clob(Bytes::from(b"hello".as_slice()))
        );
        Ok(())
    }

    #[test]
    fn read_one_v2_null_blob() -> IonResult<()> {
        let binary = encode_as_binary("null.blob");
        let expected = Element::read_one(&binary)?;
        let actual = read_one_v2(&binary)?;
        assert_eq!(expected, actual);
        assert_eq!(actual.value(), &Value::Null(IonType::Blob));
        Ok(())
    }

    #[test]
    fn read_one_v2_null_clob() -> IonResult<()> {
        let binary = encode_as_binary("null.clob");
        let expected = Element::read_one(&binary)?;
        let actual = read_one_v2(&binary)?;
        assert_eq!(expected, actual);
        assert_eq!(actual.value(), &Value::Null(IonType::Clob));
        Ok(())
    }

    // --- read_all_v3 tests ---

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
    fn v3_matches_element_read_all(#[case] text: &str) -> IonResult<()> {
        let binary = encode_as_binary(text);
        let expected = Element::read_all(&binary)?;
        let v3 = read_all_v3(&binary)?;
        assert_eq!(
            expected, v3,
            "mismatch for input: {text}\nexpected: {expected:?}\nv3: {v3:?}"
        );
        Ok(())
    }

    #[test]
    fn v3_200_strings() -> IonResult<()> {
        let mut text_values = Vec::new();
        for i in 0..200 {
            text_values.push(format!("\"string_value_{i}\""));
        }
        let text = text_values.join(" ");
        let binary = encode_as_binary(&text);
        let v2 = read_all_v2(&binary)?;
        let v3 = read_all_v3(&binary)?;
        assert_eq!(v2.len(), v3.len());
        for (i, (e2, e3)) in v2.iter().zip(v3.iter()).enumerate() {
            assert_eq!(e2, e3, "mismatch at index {i}");
        }
        Ok(())
    }

    #[test]
    fn all_text_benchmarks_pass() {
        let cases: Vec<(&str, String)> = vec![
            (
                "integers",
                (0..100).map(|i| format!("{} ", i * 7 - 50)).collect(),
            ),
            (
                "floats",
                (0..100)
                    .map(|i| format!("{}e0 ", (i as f64) * 1.7 - 85.0))
                    .collect(),
            ),
            (
                "bools",
                (0..100)
                    .map(|i| if i % 2 == 0 { "true " } else { "false " }.to_string())
                    .collect(),
            ),
            ("nulls", (0..100).map(|_| "null ".to_string()).collect()),
            ("symbols", (0..100).map(|i| format!("sym_{} ", i)).collect()),
            (
                "strings",
                (0..100).map(|i| format!("\"str_{}\" ", i)).collect(),
            ),
            (
                "decimals",
                (0..100)
                    .map(|i| format!("{}.{}d{} ", i, i % 10, (i % 3) as i32 - 1))
                    .collect(),
            ),
            (
                "timestamps",
                (0..100)
                    .map(|i| {
                        let year = 2000 + (i % 25);
                        let month = (i % 12) + 1;
                        let day = (i % 28) + 1;
                        format!("{year}-{month:02}-{day:02}T10:30:00Z ")
                    })
                    .collect(),
            ),
            (
                "lists",
                (0..50)
                    .map(|i| {
                        format!(
                            "[[{}, {}], [{}, {}]] ",
                            i * 4,
                            i * 4 + 1,
                            i * 4 + 2,
                            i * 4 + 3
                        )
                    })
                    .collect(),
            ),
            (
                "nested_structs",
                (0..50)
                    .map(|i| format!("{{name: \"item_{i}\", value: {i}, tags: [\"a\", \"b\"]}} "))
                    .collect(),
            ),
            (
                "mixed",
                (0..50)
                    .map(|i| {
                        format!(
                            "{{id: {i}, name: \"u_{i}\", ok: true, v: [{}, {}]}} ",
                            i * 2,
                            i * 2 + 1
                        )
                    })
                    .collect(),
            ),
        ];

        for (name, text) in &cases {
            let expected = Element::read_all(text.as_bytes())
                .unwrap_or_else(|e| panic!("{name}: Element::read_all failed: {e}"));
            let actual = read_all_v3(text.as_bytes())
                .unwrap_or_else(|e| panic!("{name}: read_all_v3 failed: {e}"));
            assert_eq!(expected.len(), actual.len(), "{name}: length mismatch");
        }
    }
}
