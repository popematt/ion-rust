use std::sync::Arc;

use crate::bytecode::constant_pool::{Constant, ConstantPool};
use crate::bytecode::generator::BytecodeGenerator;
use crate::bytecode::instruction::{instr, op, operation_kind, Instruction};
use crate::result::IonFailure;
use crate::{Decimal, Int, IonResult, IonType, Timestamp};

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

/// Represents a resolved or unresolved symbol token from the bytecode.
///
/// Annotations and field names in the bytecode may be stored as either
/// a symbol ID (SID) or as text from the constant pool. This enum
/// captures both forms without requiring a full symbol table lookup.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum SymbolToken {
    /// A symbol ID. The text can be resolved via the symbol table.
    Sid(usize),
    /// Text resolved from the constant pool.
    Text(Arc<str>),
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct ContainerInfo {
    end_index: usize,
}

pub struct BytecodeReader<G: BytecodeGenerator = Box<dyn BytecodeGenerator>> {
    bytecode: Vec<u32>,
    i: usize,
    instruction: Instruction,
    field_name_index: i32,
    annotations_index: i32,
    annotation_count: u8,
    label_index: i32,
    container_stack: Vec<ContainerInfo>,
    constant_pool: ConstantPool,
    /// The number of constants owned by compiled macro templates. After
    /// each refill, the pool is truncated to this length to discard
    /// ephemeral user constants while retaining macro-owned constants.
    first_local_constant: usize,
    /// The bytecode generator that produces instructions on demand.
    generator: Option<G>,
    /// The current local symbol table. Initialized with system symbols
    /// (SIDs 1-9). Updated when DIRECTIVE_SET_SYMBOLS or
    /// DIRECTIVE_ADD_SYMBOLS instructions are encountered.
    symbol_table: Vec<Option<Arc<str>>>,
}

impl BytecodeReader<Box<dyn BytecodeGenerator>> {
    /// Creates a reader from a pre-built bytecode buffer with no generator.
    ///
    /// Encountering a REFILL instruction will panic. This constructor is
    /// intended for tests that supply complete bytecode sequences.
    pub fn new(bytecode: Vec<u32>) -> Self {
        let symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
        Self {
            bytecode,
            i: 0,
            instruction: Instruction::from_raw(0),
            field_name_index: -1,
            annotations_index: -1,
            annotation_count: 0,
            label_index: -1,
            container_stack: Vec::with_capacity(10),
            constant_pool: ConstantPool::new(),
            first_local_constant: 0,
            generator: None,
            symbol_table,
        }
    }
}

impl<G: BytecodeGenerator> BytecodeReader<G> {
    /// Creates a reader backed by a generator that produces bytecode on
    /// demand. The initial bytecode buffer contains only a REFILL
    /// instruction, so the first call to `next()` will trigger a refill.
    pub fn with_generator(generator: G) -> Self {
        let symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
        Self {
            bytecode: vec![instr::REFILL],
            i: 0,
            instruction: Instruction::from_raw(0),
            field_name_index: -1,
            annotations_index: -1,
            annotation_count: 0,
            label_index: -1,
            container_stack: Vec::with_capacity(10),
            constant_pool: ConstantPool::new(),
            first_local_constant: 0,
            generator: Some(generator),
            symbol_table,
        }
    }

    pub fn next(&mut self) -> IonResult<Option<IonType>> {
        self.field_name_index = -1;
        let mut i = self.i;
        let mut instruction = self.instruction;

        let mut annotation_start: i32 = 0;
        let mut annotation_flag: i32 = -1;
        let mut annotation_count: u8 = 0;
        let mut label_index = self.label_index;

        loop {
            let data = instruction.data();
            // Branchless skip: when oc_bits < 3, (oc_bits - 3) wraps negative,
            // arithmetic right-shift fills with 1s → use_oc = all-ones → selects
            // oc_bits as the skip count. When oc_bits == 3, subtraction gives 0,
            // shift gives 0 → !use_oc = all-ones → selects `data` (container length).
            let oc_bits = instruction.operand_count_bits();
            let use_oc = ((oc_bits as i32 - 3) >> 2) as u32;
            i += ((oc_bits as u32 & use_oc) | (data & !use_oc)) as usize;

            let raw = self.bytecode[i];
            i += 1;
            instruction = Instruction::from_raw(raw);

            let kind = instruction.operation_kind();

            match kind {
                operation_kind::NULL
                | operation_kind::BOOL
                | operation_kind::INT
                | operation_kind::FLOAT
                | operation_kind::DECIMAL
                | operation_kind::TIMESTAMP
                | operation_kind::STRING
                | operation_kind::SYMBOL
                | operation_kind::BLOB
                | operation_kind::CLOB
                | operation_kind::LIST
                | operation_kind::SEXP
                | operation_kind::STRUCT => break,

                operation_kind::END => {
                    // Don't update state — repeated next() returns None stably.
                    return Ok(None);
                }

                operation_kind::FIELD_NAME => {
                    self.field_name_index = (i - 1) as i32;
                }

                // Branchless first-annotation capture: annotation_flag starts as -1
                // (all bits set), so the first time `(i as i32) & annotation_flag`
                // captures i. Then annotation_flag is set to 0, making subsequent
                // ORs no-ops — only the first annotation's position is recorded.
                operation_kind::ANNOTATIONS => {
                    annotation_start = annotation_start | ((i as i32) & annotation_flag);
                    annotation_count += 1;
                    annotation_flag = 0;
                }

                operation_kind::IVM => {
                    self.i = i;
                    self.handle_ivm(instruction);
                    i = self.i;
                }

                operation_kind::REFILL => {
                    self.refill_bytecode();
                    i = 0;
                    instruction = Instruction::from_raw(0);
                    continue;
                }

                operation_kind::DIRECTIVE => {
                    self.i = i;
                    self.handle_directive(instruction);
                    i = self.i;
                }

                operation_kind::ARGUMENT => {
                    annotation_start = 0;
                    annotation_flag = -1;
                    annotation_count = 0;
                }

                operation_kind::METADATA => {
                    label_index = (i - 1) as i32;
                    continue;
                }

                _ => {
                    return IonResult::decoding_error(format!(
                        "unexpected operation kind {} at position {}",
                        kind,
                        i - 1
                    ));
                }
            }
        }

        self.i = i;
        self.instruction = instruction;
        self.annotations_index = annotation_start - 1;
        self.annotation_count = annotation_count;
        if label_index != -1 {
            self.label_index = label_index;
        }

        Ok(operation_kind::ion_type_of(instruction.operation_kind()))
    }

    pub fn ion_type(&self) -> Option<IonType> {
        operation_kind::ion_type_of(self.instruction.operation_kind())
    }

    pub fn is_null(&self) -> bool {
        self.instruction.is_null()
    }

    pub fn bool_value(&self) -> IonResult<bool> {
        if self.instruction.operation() != op::BOOL {
            return IonResult::decoding_error("not positioned on a boolean");
        }
        Ok((self.instruction.data() & 1) == 1)
    }

    pub fn i64_value(&self) -> IonResult<i64> {
        let instruction = self.instruction;
        let i = self.i;
        match instruction.operation() {
            op::INT_I16 => Ok(instruction.data_as_i16() as i64),
            op::INT_I32 => Ok(self.bytecode[i] as i32 as i64),
            op::INT_I64 => {
                let hi = self.bytecode[i] as u64;
                let lo = self.bytecode[i + 1] as u64;
                Ok(((hi << 32) | lo) as i64)
            }
            op::INT_CP => {
                let index = instruction.data();
                match self.constant_pool.get(index) {
                    Constant::BigInt(rc) => {
                        // Attempt to extract as i64; fail if value doesn't fit.
                        rc.expect_i64()
                    }
                    _ => IonResult::decoding_error("CP entry is not a BigInt"),
                }
            }
            op::INT_REF => {
                let length = instruction.data();
                let position = self.bytecode[i];
                let int_value = self.generator()?.read_int_ref(position, length)?;
                int_value.expect_i64()
            }
            _ => IonResult::decoding_error("not positioned on an integer"),
        }
    }

    /// Returns the current value as an arbitrary-precision integer.
    ///
    /// Handles inline encodings (i16, i32, i64) as well as constant pool
    /// entries (INT_CP) and source references (INT_REF).
    pub fn int_value(&self) -> IonResult<Int> {
        let instruction = self.instruction;
        let i = self.i;
        match instruction.operation() {
            op::INT_I16 => Ok(Int::from(instruction.data_as_i16() as i64)),
            op::INT_I32 => Ok(Int::from(self.bytecode[i] as i32 as i64)),
            op::INT_I64 => {
                let hi = self.bytecode[i] as u64;
                let lo = self.bytecode[i + 1] as u64;
                Ok(Int::from(((hi << 32) | lo) as i64))
            }
            op::INT_CP => {
                let index = instruction.data();
                match self.constant_pool.get(index) {
                    Constant::BigInt(rc) => Ok(rc.as_ref().clone()),
                    _ => IonResult::decoding_error("CP entry is not a BigInt"),
                }
            }
            op::INT_REF => {
                let length = instruction.data();
                let position = self.bytecode[i];
                self.generator()?.read_int_ref(position, length)
            }
            _ => IonResult::decoding_error("not positioned on an integer"),
        }
    }

    /// Returns the current value as a `Decimal`.
    pub fn decimal_value(&self) -> IonResult<Decimal> {
        let instruction = self.instruction;
        match instruction.operation() {
            op::DECIMAL_CP => {
                let index = instruction.data();
                match self.constant_pool.get(index) {
                    Constant::Decimal(rc) => Ok(rc.as_ref().clone()),
                    _ => IonResult::decoding_error("CP entry is not a Decimal"),
                }
            }
            op::DECIMAL_REF => {
                let length = instruction.data();
                let position = self.bytecode[self.i];
                self.generator()?.read_decimal_ref(position, length)
            }
            _ => IonResult::decoding_error("not positioned on a decimal"),
        }
    }

    /// Returns the current value as a `Timestamp`.
    pub fn timestamp_value(&self) -> IonResult<Timestamp> {
        let instruction = self.instruction;
        match instruction.operation() {
            op::TIMESTAMP_CP => {
                let index = instruction.data();
                match self.constant_pool.get(index) {
                    Constant::Timestamp(rc) => Ok(rc.as_ref().clone()),
                    _ => IonResult::decoding_error("CP entry is not a Timestamp"),
                }
            }
            op::SHORT_TIMESTAMP_REF | op::TIMESTAMP_REF => {
                let length = instruction.data();
                let position = self.bytecode[self.i];
                self.generator()?.read_timestamp_ref(position, length)
            }
            _ => IonResult::decoding_error("not positioned on a timestamp"),
        }
    }

    /// Returns the current value as a string reference.
    pub fn string_value(&self) -> IonResult<Arc<str>> {
        let instruction = self.instruction;
        match instruction.operation() {
            op::STRING_CP => {
                let index = instruction.data();
                match self.constant_pool.get(index) {
                    Constant::String(rc) => Ok(Arc::clone(rc)),
                    _ => IonResult::decoding_error("CP entry is not a String"),
                }
            }
            op::STRING_REF => {
                let length = instruction.data();
                let position = self.bytecode[self.i];
                let text: &str = self.generator()?.read_text_ref(position, length)?;
                Ok(Arc::from(text))
            }
            _ => IonResult::decoding_error("not positioned on a string"),
        }
    }

    /// Returns the current value as a byte slice reference.
    pub fn lob_value(&self) -> IonResult<Arc<[u8]>> {
        let instruction = self.instruction;
        match instruction.operation() {
            op::BLOB_CP | op::CLOB_CP => {
                let index = instruction.data();
                match self.constant_pool.get(index) {
                    Constant::Bytes(rc) => Ok(Arc::clone(rc)),
                    _ => IonResult::decoding_error("CP entry is not Bytes"),
                }
            }
            op::BLOB_REF | op::CLOB_REF => {
                let length = instruction.data();
                let position = self.bytecode[self.i];
                let bytes: &[u8] = self.generator()?.read_bytes_ref(position, length)?;
                Ok(Arc::from(bytes))
            }
            _ => IonResult::decoding_error("not positioned on a lob"),
        }
    }

    /// Returns a reference to the constant pool.
    pub fn constant_pool(&self) -> &ConstantPool {
        &self.constant_pool
    }

    /// Returns a mutable reference to the constant pool.
    pub fn constant_pool_mut(&mut self) -> &mut ConstantPool {
        &mut self.constant_pool
    }

    /// Returns the first_local_constant index.
    pub fn first_local_constant(&self) -> usize {
        self.first_local_constant
    }

    /// Sets the first_local_constant index.
    pub fn set_first_local_constant(&mut self, index: usize) {
        self.first_local_constant = index;
    }

    pub fn f64_value(&self) -> IonResult<f64> {
        let instruction = self.instruction;
        let i = self.i;
        match instruction.operation() {
            op::FLOAT_F32 => {
                let bits = self.bytecode[i];
                Ok(f32::from_bits(bits) as f64)
            }
            op::FLOAT_F64 => {
                let hi = self.bytecode[i] as u64;
                let lo = self.bytecode[i + 1] as u64;
                Ok(f64::from_bits((hi << 32) | lo))
            }
            _ => IonResult::decoding_error("not positioned on a float"),
        }
    }

    /// Steps into the current container (list, sexp, or struct).
    /// After calling this, `next()` will iterate the container's children.
    pub fn step_in(&mut self) -> IonResult<()> {
        let instruction = self.instruction;
        let o = instruction.operation();

        if !matches!(o, op::LIST_START | op::SEXP_START | op::STRUCT_START) {
            return IonResult::decoding_error("cannot step into a non-container value");
        }

        let bytecode_length = instruction.data() as usize;

        self.container_stack.push(ContainerInfo {
            end_index: self.i + bytecode_length,
        });

        // Reset instruction so the next() branchless skip starts at 0.
        self.instruction = Instruction::from_raw(0);

        Ok(())
    }

    /// Steps out of the current container. Remaining children are skipped
    /// in O(1) via the length prefix.
    pub fn step_out(&mut self) -> IonResult<()> {
        let info = self.container_stack.pop().ok_or_else(|| {
            IonResult::<()>::decoding_error("cannot step out: not inside a container").unwrap_err()
        })?;

        self.i = info.end_index;
        // Reset instruction so the next() branchless skip starts at 0.
        self.instruction = Instruction::from_raw(0);

        Ok(())
    }

    /// Returns the current container nesting depth. At the top level,
    /// depth is 0.
    pub fn depth(&self) -> usize {
        self.container_stack.len()
    }

    pub fn instruction(&self) -> Instruction {
        self.instruction
    }

    pub fn annotations_index(&self) -> i32 {
        self.annotations_index
    }

    pub fn annotation_count(&self) -> u8 {
        self.annotation_count
    }

    /// Returns true if the current value has any annotations.
    pub fn has_annotations(&self) -> bool {
        self.annotation_count > 0
    }

    /// Returns an iterator over the annotations of the current value.
    ///
    /// Each annotation is yielded as a `SymbolToken` — either a SID or
    /// text from the constant pool. REF variants are not yet supported
    /// and will produce an error.
    pub fn annotations(&self) -> AnnotationIterator<'_> {
        AnnotationIterator {
            bytecode: &self.bytecode,
            constant_pool: &self.constant_pool,
            index: if self.annotations_index >= 0 {
                self.annotations_index as usize
            } else {
                0
            },
            remaining: self.annotation_count,
        }
    }

    /// Returns the field name of the current value, or `None` if not
    /// inside a struct (i.e., no field name instruction preceded this
    /// value).
    ///
    /// REF variants are not yet supported and will produce an error.
    pub fn field_name(&self) -> IonResult<Option<SymbolToken>> {
        let idx = self.field_name_index;
        if idx < 0 {
            return Ok(None);
        }

        let instruction = Instruction::from_raw(self.bytecode[idx as usize]);
        let data = instruction.data();

        match instruction.operation() {
            op::FIELD_NAME_SID => Ok(Some(SymbolToken::Sid(data as usize))),
            op::FIELD_NAME_CP => match self.constant_pool.get(data) {
                Constant::String(rc) => Ok(Some(SymbolToken::Text(Arc::clone(rc)))),
                _ => IonResult::decoding_error("field name CP entry is not a string"),
            },
            op::FIELD_NAME_REF => {
                let length = data;
                let position = self.bytecode[idx as usize + 1];
                let text: &str = self.generator()?.read_text_ref(position, length)?;
                Ok(Some(SymbolToken::Text(Arc::from(text))))
            }
            _ => IonResult::decoding_error(
                "field_name_index does not point to a field name instruction",
            ),
        }
    }

    pub fn field_name_index(&self) -> i32 {
        self.field_name_index
    }

    /// Returns a reference to the attached generator, or an error if none.
    fn generator(&self) -> IonResult<&G> {
        self.generator.as_ref().ok_or_else(|| {
            IonResult::<()>::decoding_error(
                "REF instruction encountered but no BytecodeGenerator is attached",
            )
            .unwrap_err()
        })
    }

    fn refill_bytecode(&mut self) {
        let generator = self
            .generator
            .as_mut()
            .expect("REFILL encountered but no BytecodeGenerator is attached");

        // Discard ephemeral user constants from the previous refill cycle
        // while retaining macro-owned constants.
        self.constant_pool.truncate(self.first_local_constant);

        // Clear the bytecode buffer and ask the generator to fill it.
        self.bytecode.clear();
        generator.refill(&mut self.bytecode, &mut self.constant_pool);
    }

    /// Returns a reference to the reader's symbol table.
    pub fn symbol_table(&self) -> &[Option<Arc<str>>] {
        &self.symbol_table
    }

    /// Returns a mutable reference to the reader's symbol table.
    pub fn symbol_table_mut(&mut self) -> &mut Vec<Option<Arc<str>>> {
        &mut self.symbol_table
    }

    /// Handles an IVM instruction. Resets the symbol table to system
    /// symbols only.
    fn handle_ivm(&mut self, _instruction: Instruction) {
        // Reset symbol table to system symbols (Ion 1.0)
        self.symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
    }

    /// Handles a directive instruction. Reads the directive content
    /// (symbol entries until END_CONTAINER) and updates the symbol table.
    fn handle_directive(&mut self, instruction: Instruction) {
        let op = instruction.operation();
        match op {
            op::DIRECTIVE_SET_SYMBOLS | op::DIRECTIVE_ADD_SYMBOLS => {
                let is_set = op == op::DIRECTIVE_SET_SYMBOLS;
                if is_set {
                    // Reset to system symbols only
                    self.symbol_table =
                        SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
                }

                // Read directive content until END_CONTAINER
                let mut i = self.i;
                loop {
                    let raw = self.bytecode[i];
                    let instr = Instruction::from_raw(raw);
                    i += 1;

                    match instr.operation() {
                        op::END_CONTAINER => break,
                        op::STRING_REF => {
                            let length = instr.data();
                            let position = self.bytecode[i];
                            i += 1;
                            // Resolve text from the generator
                            if let Some(gen) = &self.generator {
                                match gen.read_text_ref(position, length) {
                                    Ok(text) => {
                                        self.symbol_table.push(Some(Arc::from(text)));
                                    }
                                    Err(_) => self.symbol_table.push(None),
                                }
                            } else {
                                self.symbol_table.push(None);
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
                            // Advance past operands based on operand count.
                            let oc = instr.operand_count_bits();
                            if oc < 3 {
                                i += oc as usize;
                            }
                        }
                    }
                }
                self.i = i;
            }
            _ => {
                // For DIRECTIVE_SET_MACROS, DIRECTIVE_ADD_MACROS,
                // DIRECTIVE_USE: skip until END_CONTAINER (not yet
                // implemented).
                let mut i = self.i;
                loop {
                    let raw = self.bytecode[i];
                    let instr = Instruction::from_raw(raw);
                    i += 1;
                    if instr.operation() == op::END_CONTAINER {
                        break;
                    }
                    let oc = instr.operand_count_bits();
                    if oc < 3 {
                        i += oc as usize;
                    }
                }
                self.i = i;
            }
        }
    }
}

/// Iterator over annotation instructions in the bytecode.
///
/// Created by [`BytecodeReader::annotations()`]. Yields one
/// `SymbolToken` per annotation.
pub(crate) struct AnnotationIterator<'a> {
    bytecode: &'a [u32],
    constant_pool: &'a ConstantPool,
    index: usize,
    remaining: u8,
}

impl<'a> Iterator for AnnotationIterator<'a> {
    type Item = IonResult<SymbolToken>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;

        let raw = self.bytecode[self.index];
        let instruction = Instruction::from_raw(raw);
        self.index += 1;

        let data = instruction.data();

        let result = match instruction.operation() {
            op::ANNOTATION_SID => Ok(SymbolToken::Sid(data as usize)),
            op::ANNOTATION_CP => match self.constant_pool.get(data) {
                Constant::String(rc) => Ok(SymbolToken::Text(Arc::clone(rc))),
                _ => IonResult::decoding_error("annotation CP entry is not a string"),
            },
            op::ANNOTATION_REF => {
                // REF has one operand word following the instruction.
                self.index += 1;
                // The iterator does not hold a reference to the generator,
                // so REF resolution requires a design change (e.g., passing
                // the generator to the iterator or pre-resolving during
                // refill). For now this remains unimplemented.
                todo!("ANNOTATION_REF resolution in AnnotationIterator")
            }
            _ => IonResult::decoding_error("expected annotation instruction"),
        };
        Some(result)
    }
}

impl ExactSizeIterator for AnnotationIterator<'_> {
    fn len(&self) -> usize {
        self.remaining as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::builder::BytecodeBuilder;
    use crate::IonType;

    fn reader_from(builder: BytecodeBuilder) -> BytecodeReader {
        let bytecode: Vec<u32> = builder.build().iter().map(|i| i.raw()).collect();
        BytecodeReader::new(bytecode)
    }

    #[test]
    fn next_returns_correct_types() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .bool(true)
                .int_i16(42)
                .float_f64(3.14)
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::Bool));
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.next()?, Some(IonType::Float));
        assert_eq!(reader.next()?, None);
        Ok(())
    }

    #[test]
    fn next_inline_scalars() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .bool(true)
                .bool(false)
                .int_i16(-7)
                .int_i32(100_000)
                .int_i64(i64::MAX)
                .float_f32(2.5)
                .float_f64(std::f64::consts::PI)
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::Bool));
        assert_eq!(reader.bool_value()?, true);

        assert_eq!(reader.next()?, Some(IonType::Bool));
        assert_eq!(reader.bool_value()?, false);

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, -7);

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 100_000);

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, i64::MAX);

        assert_eq!(reader.next()?, Some(IonType::Float));
        assert_eq!(reader.f64_value()?, 2.5);

        assert_eq!(reader.next()?, Some(IonType::Float));
        assert_eq!(reader.f64_value()?, std::f64::consts::PI);

        Ok(())
    }

    #[test]
    fn next_null_values() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .null_null()
                .null_bool()
                .null_int()
                .null_list()
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::Null));
        assert!(reader.is_null());

        assert_eq!(reader.next()?, Some(IonType::Bool));
        assert!(reader.is_null());

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert!(reader.is_null());

        assert_eq!(reader.next()?, Some(IonType::List));
        assert!(reader.is_null());

        Ok(())
    }

    #[test]
    fn end_of_input_returns_none() -> IonResult<()> {
        let mut reader = reader_from(BytecodeBuilder::new().int_i16(1).end_of_input());

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.next()?, None);

        Ok(())
    }

    #[test]
    fn end_container_returns_none_repeatedly() -> IonResult<()> {
        // Test END_CONTAINER directly (step-in not available until pt003)
        let inner: Vec<u32> = vec![instr::INT_I16 | 1, instr::END_CONTAINER];
        let mut reader = BytecodeReader::new(inner);

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.next()?, None);
        assert_eq!(reader.next()?, None); // stable
        Ok(())
    }

    #[test]
    fn skips_containers_at_same_depth() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .list(|b| b.int_i16(1).int_i16(2).int_i16(3))
                .int_i16(42)
                .end_of_input(),
        );

        // First next() lands on the list
        assert_eq!(reader.next()?, Some(IonType::List));
        // Second next() should skip the list entirely and land on 42
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 42);

        Ok(())
    }

    #[test]
    fn annotation_tracking() -> IonResult<()> {
        let bytecode: Vec<u32> = vec![
            instr::ANNOTATION_SID | 4, // annotation $4
            instr::ANNOTATION_SID | 5, // annotation $5
            instr::INT_I16 | 42,       // value
            instr::END_OF_INPUT,
        ];
        let mut reader = BytecodeReader::new(bytecode);

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.annotation_count(), 2);
        assert_eq!(reader.annotations_index(), 0); // first annotation at index 0

        Ok(())
    }

    #[test]
    fn field_name_tracking() -> IonResult<()> {
        let bytecode: Vec<u32> = vec![
            instr::FIELD_NAME_SID | 4, // field name $4
            instr::INT_I16 | 99,       // value
            instr::END_OF_INPUT,
        ];
        let mut reader = BytecodeReader::new(bytecode);

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.field_name_index(), 0); // field name at index 0

        Ok(())
    }

    #[test]
    fn metadata_tracking() -> IonResult<()> {
        let bytecode: Vec<u32> = vec![
            instr::META_OFFSET,
            42, // operand: offset value
            instr::INT_I16 | 7,
            instr::END_OF_INPUT,
        ];
        let mut reader = BytecodeReader::new(bytecode);

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 7);

        Ok(())
    }

    // --- pt003: Container navigation tests ---

    #[test]
    fn step_in_and_iterate_list() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .list(|b| b.int_i16(1).int_i16(2).int_i16(3))
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::List));
        assert_eq!(reader.depth(), 0);

        reader.step_in()?;
        assert_eq!(reader.depth(), 1);

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 1);
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 2);
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 3);
        assert_eq!(reader.next()?, None); // END_CONTAINER

        reader.step_out()?;
        assert_eq!(reader.depth(), 0);
        assert_eq!(reader.next()?, None); // END_OF_INPUT

        Ok(())
    }

    #[test]
    fn step_in_struct_with_fields() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .r#struct(|b| b.field_name_sid(4).int_i16(10).field_name_sid(5).bool(true))
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::Struct));
        reader.step_in()?;

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.field_name_index(), 1); // field_name at index 1 (after STRUCT_START)
        assert_eq!(reader.i64_value()?, 10);

        assert_eq!(reader.next()?, Some(IonType::Bool));
        assert_eq!(reader.bool_value()?, true);

        assert_eq!(reader.next()?, None);
        reader.step_out()?;

        Ok(())
    }

    #[test]
    fn early_step_out_skips_remaining() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .list(|b| b.int_i16(1).int_i16(2).int_i16(3).int_i16(4).int_i16(5))
                .int_i16(42)
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::List));
        reader.step_in()?;

        // Read only 2 of 5 children
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.next()?, Some(IonType::Int));

        // Step out early — remaining 3 children are skipped O(1)
        reader.step_out()?;

        // Should land on the value after the list
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 42);

        Ok(())
    }

    #[test]
    fn nested_containers() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .list(|b| b.list(|b| b.int_i16(1).int_i16(2)).int_i16(3))
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::List)); // outer
        reader.step_in()?;
        assert_eq!(reader.depth(), 1);

        assert_eq!(reader.next()?, Some(IonType::List)); // inner
        reader.step_in()?;
        assert_eq!(reader.depth(), 2);

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 1);
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 2);
        assert_eq!(reader.next()?, None); // inner END_CONTAINER

        reader.step_out()?; // out of inner
        assert_eq!(reader.depth(), 1);

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 3);
        assert_eq!(reader.next()?, None); // outer END_CONTAINER

        reader.step_out()?; // out of outer
        assert_eq!(reader.depth(), 0);

        Ok(())
    }

    #[test]
    fn skip_container_without_step_in() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .list(|b| b.int_i16(1).int_i16(2).int_i16(3))
                .int_i16(42)
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::List));
        // Don't step in — next() skips the entire container
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 42);

        Ok(())
    }

    #[test]
    fn empty_container() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .list(|b| b) // empty list
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::List));
        reader.step_in()?;
        assert_eq!(reader.next()?, None); // immediately END_CONTAINER
        reader.step_out()?;
        assert_eq!(reader.next()?, None); // END_OF_INPUT

        Ok(())
    }

    #[test]
    fn step_in_then_immediate_step_out() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .list(|b| b.int_i16(1).int_i16(2).int_i16(3))
                .int_i16(99)
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::List));
        reader.step_in()?;
        // Step out immediately without reading any children
        reader.step_out()?;

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 99);

        Ok(())
    }

    #[test]
    fn step_in_on_null_list_returns_error() -> IonResult<()> {
        let mut reader = reader_from(BytecodeBuilder::new().null_list().end_of_input());
        assert_eq!(reader.next()?, Some(IonType::List));
        assert!(reader.is_null());
        assert!(reader.step_in().is_err());
        Ok(())
    }

    #[test]
    fn step_in_on_null_sexp_returns_error() -> IonResult<()> {
        let mut reader = reader_from(BytecodeBuilder::new().null_sexp().end_of_input());
        assert_eq!(reader.next()?, Some(IonType::SExp));
        assert!(reader.is_null());
        assert!(reader.step_in().is_err());
        Ok(())
    }

    #[test]
    fn step_in_on_null_struct_returns_error() -> IonResult<()> {
        let mut reader = reader_from(BytecodeBuilder::new().null_struct().end_of_input());
        assert_eq!(reader.next()?, Some(IonType::Struct));
        assert!(reader.is_null());
        assert!(reader.step_in().is_err());
        Ok(())
    }

    #[test]
    fn step_in_on_scalar_returns_error() -> IonResult<()> {
        let mut reader = reader_from(BytecodeBuilder::new().int_i16(5).end_of_input());

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert!(reader.step_in().is_err());

        Ok(())
    }

    #[test]
    fn step_out_at_top_level_returns_error() -> IonResult<()> {
        let mut reader = reader_from(BytecodeBuilder::new().int_i16(5).end_of_input());
        assert!(reader.step_out().is_err());
        Ok(())
    }

    #[test]
    fn sexp_navigation() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .sexp(|b| b.int_i16(1).int_i16(2))
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::SExp));
        reader.step_in()?;
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 1);
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 2);
        assert_eq!(reader.next()?, None);
        reader.step_out()?;

        Ok(())
    }

    // --- End pt003 tests ---

    #[test]
    fn empty_stream_returns_none() -> IonResult<()> {
        let mut reader = BytecodeReader::new(vec![instr::END_OF_INPUT]);
        assert_eq!(reader.next()?, None);
        Ok(())
    }

    #[test]
    fn end_of_input_is_stable_on_repeated_calls() -> IonResult<()> {
        let mut reader = reader_from(BytecodeBuilder::new().int_i16(1).end_of_input());
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.next()?, None);
        assert_eq!(reader.next()?, None); // no panic
        assert_eq!(reader.next()?, None); // still stable
        Ok(())
    }

    // --- pt004: Constant pool tests ---

    #[test]
    fn int_cp_via_i64_value() -> IonResult<()> {
        let mut reader = reader_from(BytecodeBuilder::new().int_cp(0).int_cp(1).end_of_input());
        // Pre-populate the constant pool.
        reader
            .constant_pool_mut()
            .add(Constant::BigInt(Arc::new(Int::from(123_456_789))));
        reader
            .constant_pool_mut()
            .add(Constant::BigInt(Arc::new(Int::from(-99))));

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 123_456_789);

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, -99);

        Ok(())
    }

    #[test]
    fn int_cp_via_int_value() -> IonResult<()> {
        let big = Int::from(i64::MAX as i128 + 1);
        let mut reader = reader_from(BytecodeBuilder::new().int_cp(0).end_of_input());
        reader
            .constant_pool_mut()
            .add(Constant::BigInt(Arc::new(big.clone())));

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.int_value()?, big);

        Ok(())
    }

    #[test]
    fn int_cp_i64_value_fails_for_big_value() -> IonResult<()> {
        let big = Int::from(i64::MAX as i128 + 1);
        let mut reader = reader_from(BytecodeBuilder::new().int_cp(0).end_of_input());
        reader
            .constant_pool_mut()
            .add(Constant::BigInt(Arc::new(big)));

        assert_eq!(reader.next()?, Some(IonType::Int));
        // i64_value should fail because the value doesn't fit in i64.
        assert!(reader.i64_value().is_err());

        Ok(())
    }

    #[test]
    fn decimal_cp_value() -> IonResult<()> {
        let decimal = Decimal::new(314, -2);
        let mut reader = reader_from(BytecodeBuilder::new().decimal_cp(0).end_of_input());
        reader
            .constant_pool_mut()
            .add(Constant::Decimal(Arc::new(decimal.clone())));

        assert_eq!(reader.next()?, Some(IonType::Decimal));
        assert_eq!(reader.decimal_value()?, decimal);

        Ok(())
    }

    #[test]
    fn timestamp_cp_value() -> IonResult<()> {
        let timestamp = Timestamp::with_year(2024)
            .with_month(6)
            .with_day(15)
            .build()?;
        let mut reader = reader_from(BytecodeBuilder::new().timestamp_cp(0).end_of_input());
        reader
            .constant_pool_mut()
            .add(Constant::Timestamp(Arc::new(timestamp.clone())));

        assert_eq!(reader.next()?, Some(IonType::Timestamp));
        assert_eq!(reader.timestamp_value()?, timestamp);

        Ok(())
    }

    #[test]
    fn string_cp_value() -> IonResult<()> {
        let mut reader = reader_from(BytecodeBuilder::new().string_cp(0).end_of_input());
        reader
            .constant_pool_mut()
            .add(Constant::String(Arc::from("hello, world!")));

        assert_eq!(reader.next()?, Some(IonType::String));
        let value = reader.string_value()?;
        assert_eq!(&*value, "hello, world!");

        Ok(())
    }

    #[test]
    fn blob_cp_value() -> IonResult<()> {
        let data: &[u8] = &[0xDE, 0xAD, 0xBE, 0xEF];
        let mut reader = reader_from(BytecodeBuilder::new().blob_cp(0).end_of_input());
        reader
            .constant_pool_mut()
            .add(Constant::Bytes(Arc::from(data)));

        assert_eq!(reader.next()?, Some(IonType::Blob));
        let value = reader.lob_value()?;
        assert_eq!(&*value, data);

        Ok(())
    }

    #[test]
    fn clob_cp_value() -> IonResult<()> {
        let data: &[u8] = b"some text";
        let mut reader = reader_from(BytecodeBuilder::new().clob_cp(0).end_of_input());
        reader
            .constant_pool_mut()
            .add(Constant::Bytes(Arc::from(data)));

        assert_eq!(reader.next()?, Some(IonType::Clob));
        let value = reader.lob_value()?;
        assert_eq!(&*value, data);

        Ok(())
    }

    #[test]
    fn int_cp_wrong_type_returns_error() -> IonResult<()> {
        // Put a String constant but try to read it as an integer.
        let mut reader = reader_from(BytecodeBuilder::new().int_cp(0).end_of_input());
        reader
            .constant_pool_mut()
            .add(Constant::String(Arc::from("not an int")));

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert!(reader.i64_value().is_err());
        assert!(reader.int_value().is_err());

        Ok(())
    }

    #[test]
    fn decimal_cp_wrong_type_returns_error() -> IonResult<()> {
        // Put an Int constant but try to read as decimal.
        let mut reader = reader_from(BytecodeBuilder::new().decimal_cp(0).end_of_input());
        reader
            .constant_pool_mut()
            .add(Constant::BigInt(Arc::new(Int::from(42))));

        assert_eq!(reader.next()?, Some(IonType::Decimal));
        assert!(reader.decimal_value().is_err());

        Ok(())
    }

    #[test]
    fn timestamp_cp_wrong_type_returns_error() -> IonResult<()> {
        // Put a String constant but try to read as timestamp.
        let mut reader = reader_from(BytecodeBuilder::new().timestamp_cp(0).end_of_input());
        reader
            .constant_pool_mut()
            .add(Constant::String(Arc::from("2024-01-01")));

        assert_eq!(reader.next()?, Some(IonType::Timestamp));
        assert!(reader.timestamp_value().is_err());

        Ok(())
    }

    #[test]
    fn string_cp_wrong_type_returns_error() -> IonResult<()> {
        // Put Bytes constant but try to read as string.
        let mut reader = reader_from(BytecodeBuilder::new().string_cp(0).end_of_input());
        reader
            .constant_pool_mut()
            .add(Constant::Bytes(Arc::from([0u8; 4].as_slice())));

        assert_eq!(reader.next()?, Some(IonType::String));
        assert!(reader.string_value().is_err());

        Ok(())
    }

    #[test]
    fn lob_cp_wrong_type_returns_error() -> IonResult<()> {
        // Put a String constant but try to read as blob.
        let mut reader = reader_from(BytecodeBuilder::new().blob_cp(0).end_of_input());
        reader
            .constant_pool_mut()
            .add(Constant::String(Arc::from("not bytes")));

        assert_eq!(reader.next()?, Some(IonType::Blob));
        assert!(reader.lob_value().is_err());

        Ok(())
    }

    #[test]
    fn value_accessor_on_wrong_instruction_returns_error() -> IonResult<()> {
        // Position on a bool, then try to read as decimal/timestamp/string/lob.
        let mut reader = reader_from(BytecodeBuilder::new().bool(true).end_of_input());
        assert_eq!(reader.next()?, Some(IonType::Bool));

        assert!(reader.decimal_value().is_err());
        assert!(reader.timestamp_value().is_err());
        assert!(reader.string_value().is_err());
        assert!(reader.lob_value().is_err());

        Ok(())
    }

    #[test]
    fn constant_pool_truncation_in_reader() -> IonResult<()> {
        let mut reader = reader_from(BytecodeBuilder::new().int_cp(0).int_cp(1).end_of_input());
        // Simulate macro constants (index 0) and user constants (index 1).
        reader
            .constant_pool_mut()
            .add(Constant::BigInt(Arc::new(Int::from(100))));
        reader.set_first_local_constant(1);
        reader
            .constant_pool_mut()
            .add(Constant::BigInt(Arc::new(Int::from(200))));

        // Both are accessible before truncation.
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 100);
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 200);

        // Truncate to first_local_constant — simulating what happens after
        // a refill.
        let first_local = reader.first_local_constant();
        reader.constant_pool_mut().truncate(first_local);
        assert_eq!(reader.constant_pool().len(), 1);

        Ok(())
    }

    // --- End pt004 tests ---

    // --- pt005: Annotation and field name access tests ---

    #[test]
    fn no_annotations_yields_empty_iterator() -> IonResult<()> {
        let mut reader = reader_from(BytecodeBuilder::new().int_i16(42).end_of_input());

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert!(!reader.has_annotations());
        assert_eq!(reader.annotation_count(), 0);
        assert_eq!(reader.annotations().len(), 0);
        assert!(reader.annotations().next().is_none());

        Ok(())
    }

    #[test]
    fn single_annotation_sid() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .annotation_sid(4)
                .int_i16(42)
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert!(reader.has_annotations());
        assert_eq!(reader.annotation_count(), 1);

        let mut iter = reader.annotations();
        assert_eq!(iter.len(), 1);
        assert_eq!(iter.next().unwrap()?, SymbolToken::Sid(4));
        assert!(iter.next().is_none());

        Ok(())
    }

    #[test]
    fn two_annotations_sid_and_cp() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .annotation_sid(4)
                .annotation_cp(0)
                .int_i16(42)
                .end_of_input(),
        );
        reader
            .constant_pool_mut()
            .add(Constant::String(Arc::from("my_annotation")));

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert!(reader.has_annotations());
        assert_eq!(reader.annotation_count(), 2);

        let annotations: Vec<SymbolToken> = reader.annotations().collect::<IonResult<Vec<_>>>()?;

        assert_eq!(annotations.len(), 2);
        assert_eq!(annotations[0], SymbolToken::Sid(4));
        assert_eq!(
            annotations[1],
            SymbolToken::Text(Arc::from("my_annotation"))
        );

        Ok(())
    }

    #[test]
    fn annotation_cp_only() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .annotation_cp(0)
                .int_i16(7)
                .end_of_input(),
        );
        reader
            .constant_pool_mut()
            .add(Constant::String(Arc::from("some_ann")));

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.annotation_count(), 1);

        let mut iter = reader.annotations();
        assert_eq!(
            iter.next().unwrap()?,
            SymbolToken::Text(Arc::from("some_ann"))
        );
        assert!(iter.next().is_none());

        Ok(())
    }

    #[test]
    fn field_name_sid_returns_sid() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .r#struct(|b| b.field_name_sid(10).int_i16(99))
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::Struct));
        reader.step_in()?;
        assert_eq!(reader.next()?, Some(IonType::Int));

        let field = reader.field_name()?;
        assert_eq!(field, Some(SymbolToken::Sid(10)));

        Ok(())
    }

    #[test]
    fn field_name_cp_returns_text() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .r#struct(|b| b.field_name_cp(0).int_i16(99))
                .end_of_input(),
        );
        reader
            .constant_pool_mut()
            .add(Constant::String(Arc::from("my_field")));

        assert_eq!(reader.next()?, Some(IonType::Struct));
        reader.step_in()?;
        assert_eq!(reader.next()?, Some(IonType::Int));

        let field = reader.field_name()?;
        assert_eq!(field, Some(SymbolToken::Text(Arc::from("my_field"))));

        Ok(())
    }

    #[test]
    fn no_field_name_outside_struct() -> IonResult<()> {
        let mut reader = reader_from(BytecodeBuilder::new().int_i16(42).end_of_input());

        assert_eq!(reader.next()?, Some(IonType::Int));
        let field = reader.field_name()?;
        assert_eq!(field, None);

        Ok(())
    }

    #[test]
    fn annotations_and_field_name_together() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .r#struct(|b| {
                    b.annotation_sid(1)
                        .annotation_sid(2)
                        .field_name_sid(10)
                        .int_i16(42)
                })
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::Struct));
        reader.step_in()?;
        assert_eq!(reader.next()?, Some(IonType::Int));

        // Annotations are accessible
        assert_eq!(reader.annotation_count(), 2);
        let annotations: Vec<SymbolToken> = reader.annotations().collect::<IonResult<Vec<_>>>()?;
        assert_eq!(annotations, vec![SymbolToken::Sid(1), SymbolToken::Sid(2)]);

        // Field name is accessible
        let field = reader.field_name()?;
        assert_eq!(field, Some(SymbolToken::Sid(10)));

        Ok(())
    }

    #[test]
    fn annotations_reset_between_values() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .annotation_sid(1)
                .int_i16(10)
                .int_i16(20)
                .end_of_input(),
        );

        // First value has one annotation
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.annotation_count(), 1);
        assert!(reader.has_annotations());

        // Second value has no annotations
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.annotation_count(), 0);
        assert!(!reader.has_annotations());

        Ok(())
    }

    // --- End pt005 tests ---

    #[test]
    fn three_annotations() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .annotation_sid(1)
                .annotation_sid(2)
                .annotation_sid(3)
                .int_i16(99)
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert!(reader.has_annotations());
        assert_eq!(reader.annotation_count(), 3);

        let annotations: Vec<SymbolToken> = reader.annotations().collect::<IonResult<Vec<_>>>()?;
        assert_eq!(
            annotations,
            vec![
                SymbolToken::Sid(1),
                SymbolToken::Sid(2),
                SymbolToken::Sid(3)
            ]
        );

        Ok(())
    }

    #[test]
    fn annotation_iterator_exact_size() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .annotation_sid(1)
                .annotation_sid(2)
                .int_i16(42)
                .end_of_input(),
        );

        assert_eq!(reader.next()?, Some(IonType::Int));

        let mut iter = reader.annotations();
        assert_eq!(iter.len(), 2);
        iter.next();
        assert_eq!(iter.len(), 1);
        iter.next();
        assert_eq!(iter.len(), 0);
        assert!(iter.next().is_none());

        Ok(())
    }

    #[test]
    fn annotation_cp_wrong_type_returns_error() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .annotation_cp(0)
                .int_i16(42)
                .end_of_input(),
        );
        // Put a non-String constant in the pool.
        reader
            .constant_pool_mut()
            .add(Constant::BigInt(Arc::new(Int::from(99))));

        assert_eq!(reader.next()?, Some(IonType::Int));

        let mut iter = reader.annotations();
        let result = iter.next().unwrap();
        assert!(result.is_err());

        Ok(())
    }

    #[test]
    fn field_name_cp_wrong_type_returns_error() -> IonResult<()> {
        let mut reader = reader_from(
            BytecodeBuilder::new()
                .r#struct(|b| b.field_name_cp(0).int_i16(42))
                .end_of_input(),
        );
        // Put a non-String constant in the pool.
        reader
            .constant_pool_mut()
            .add(Constant::BigInt(Arc::new(Int::from(99))));

        assert_eq!(reader.next()?, Some(IonType::Struct));
        reader.step_in()?;
        assert_eq!(reader.next()?, Some(IonType::Int));

        let result = reader.field_name();
        assert!(result.is_err());

        Ok(())
    }

    #[test]
    fn ref_without_generator_returns_error() -> IonResult<()> {
        // Construct a reader without a generator that has a STRING_REF
        // instruction. Attempting to read the value should return an error
        // (not panic).
        let bytecode: Vec<u32> = vec![
            instr::STRING_REF | 10, // length=10
            0x0000_1000,            // position operand
            instr::END_OF_INPUT,
        ];
        let mut reader = BytecodeReader::new(bytecode);

        assert_eq!(reader.next()?, Some(IonType::String));
        let result = reader.string_value();
        assert!(result.is_err());

        Ok(())
    }

    // --- End pt005 tests ---

    // --- pt006: Generator integration tests ---

    use crate::bytecode::generator::BytecodeGenerator;

    /// A mock generator that emits a pre-determined sequence of bytecode
    /// batches, one per refill call.
    struct MockGenerator {
        /// Each entry is a batch of raw u32 instructions to emit on refill.
        batches: Vec<Vec<u32>>,
        /// Tracks how many times refill has been called.
        call_count: usize,
    }

    impl MockGenerator {
        fn new(batches: Vec<Vec<u32>>) -> Self {
            Self {
                batches,
                call_count: 0,
            }
        }
    }

    impl BytecodeGenerator for MockGenerator {
        fn refill(&mut self, destination: &mut Vec<u32>, _constant_pool: &mut ConstantPool) {
            let idx = self.call_count;
            self.call_count += 1;
            if idx < self.batches.len() {
                destination.extend_from_slice(&self.batches[idx]);
            } else {
                destination.push(instr::END_OF_INPUT);
            }
        }

        fn read_int_ref(&self, _position: u32, _length: u32) -> IonResult<Int> {
            IonResult::decoding_error("MockGenerator does not support read_int_ref")
        }

        fn read_decimal_ref(&self, _position: u32, _length: u32) -> IonResult<Decimal> {
            IonResult::decoding_error("MockGenerator does not support read_decimal_ref")
        }

        fn read_timestamp_ref(&self, _position: u32, _length: u32) -> IonResult<Timestamp> {
            IonResult::decoding_error("MockGenerator does not support read_timestamp_ref")
        }

        fn read_text_ref(&self, _position: u32, _length: u32) -> IonResult<&str> {
            IonResult::decoding_error("MockGenerator does not support read_text_ref")
        }

        fn read_bytes_ref(&self, _position: u32, _length: u32) -> IonResult<&[u8]> {
            IonResult::decoding_error("MockGenerator does not support read_bytes_ref")
        }
    }

    #[test]
    fn generator_single_refill() -> IonResult<()> {
        let gen = MockGenerator::new(vec![vec![
            instr::INT_I16 | 1,
            instr::INT_I16 | 2,
            instr::END_OF_INPUT,
        ]]);
        let mut reader = BytecodeReader::with_generator(gen);

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 1);
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 2);
        assert_eq!(reader.next()?, None);

        Ok(())
    }

    #[test]
    fn generator_multiple_refills() -> IonResult<()> {
        // Two batches: each ends with REFILL to trigger the next.
        let gen = MockGenerator::new(vec![
            vec![instr::INT_I16 | 10, instr::REFILL],
            vec![instr::INT_I16 | 20, instr::REFILL],
            vec![instr::INT_I16 | 30, instr::END_OF_INPUT],
        ]);
        let mut reader = BytecodeReader::with_generator(gen);

        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 10);

        // This next() hits REFILL, triggers second batch
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 20);

        // This next() hits REFILL, triggers third batch
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 30);

        assert_eq!(reader.next()?, None);

        Ok(())
    }

    #[test]
    fn generator_refill_truncates_constant_pool() -> IonResult<()> {
        /// A generator that adds a constant on each refill call.
        struct ConstantAddingGenerator {
            call_count: usize,
        }

        impl BytecodeGenerator for ConstantAddingGenerator {
            fn refill(&mut self, destination: &mut Vec<u32>, constant_pool: &mut ConstantPool) {
                self.call_count += 1;
                match self.call_count {
                    1 => {
                        // First refill: add a user constant and reference it.
                        let idx = constant_pool.add(Constant::BigInt(Arc::new(Int::from(999))));
                        destination.push(instr::INT_CP | idx);
                        destination.push(instr::REFILL);
                    }
                    2 => {
                        // Second refill: the previous user constant should
                        // have been truncated. Add a new one.
                        let idx = constant_pool.add(Constant::BigInt(Arc::new(Int::from(777))));
                        destination.push(instr::INT_CP | idx);
                        destination.push(instr::END_OF_INPUT);
                    }
                    _ => {
                        destination.push(instr::END_OF_INPUT);
                    }
                }
            }

            fn read_int_ref(&self, _position: u32, _length: u32) -> IonResult<Int> {
                IonResult::decoding_error("not supported")
            }

            fn read_decimal_ref(&self, _position: u32, _length: u32) -> IonResult<Decimal> {
                IonResult::decoding_error("not supported")
            }

            fn read_timestamp_ref(&self, _position: u32, _length: u32) -> IonResult<Timestamp> {
                IonResult::decoding_error("not supported")
            }

            fn read_text_ref(&self, _position: u32, _length: u32) -> IonResult<&str> {
                IonResult::decoding_error("not supported")
            }

            fn read_bytes_ref(&self, _position: u32, _length: u32) -> IonResult<&[u8]> {
                IonResult::decoding_error("not supported")
            }
        }

        let gen = ConstantAddingGenerator { call_count: 0 };
        let mut reader = BytecodeReader::with_generator(gen);

        // Simulate one macro-owned constant at index 0.
        reader
            .constant_pool_mut()
            .add(Constant::BigInt(Arc::new(Int::from(42))));
        reader.set_first_local_constant(1);

        // First value comes from first refill
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 999);

        // The constant pool now has:
        // [macro_constant(42), user_constant(999)]
        assert_eq!(reader.constant_pool().len(), 2);

        // Second next() hits REFILL. The refill truncates user constants,
        // then the generator adds a new one.
        assert_eq!(reader.next()?, Some(IonType::Int));
        assert_eq!(reader.i64_value()?, 777);

        // After second refill:
        // [macro_constant(42), new_user_constant(777)]
        assert_eq!(reader.constant_pool().len(), 2);

        assert_eq!(reader.next()?, None);

        Ok(())
    }

    #[test]
    fn generator_exhausted_returns_end_of_input() -> IonResult<()> {
        // Generator with one batch followed by exhaustion.
        let gen = MockGenerator::new(vec![vec![instr::BOOL | 1, instr::END_OF_INPUT]]);
        let mut reader = BytecodeReader::with_generator(gen);

        assert_eq!(reader.next()?, Some(IonType::Bool));
        assert_eq!(reader.bool_value()?, true);
        assert_eq!(reader.next()?, None);
        // Repeated calls remain stable
        assert_eq!(reader.next()?, None);

        Ok(())
    }

    // --- End pt006 tests ---
}
