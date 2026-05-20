use super::instruction::{instr, op, Instruction};

pub(crate) struct BytecodeBuilder {
    buffer: Vec<Instruction>,
}

impl BytecodeBuilder {
    pub fn new() -> Self {
        Self { buffer: Vec::new() }
    }

    pub fn build(self) -> Vec<Instruction> {
        self.buffer
    }

    pub fn null_null(mut self) -> Self {
        self.buffer.push(Instruction::from_raw(instr::NULL_NULL));
        self
    }

    pub fn null_bool(mut self) -> Self {
        self.buffer.push(Instruction::from_raw(instr::NULL_BOOL));
        self
    }

    pub fn null_int(mut self) -> Self {
        self.buffer.push(Instruction::from_raw(instr::NULL_INT));
        self
    }

    pub fn null_float(mut self) -> Self {
        self.buffer.push(Instruction::from_raw(instr::NULL_FLOAT));
        self
    }

    pub fn null_decimal(mut self) -> Self {
        self.buffer.push(Instruction::from_raw(instr::NULL_DECIMAL));
        self
    }

    pub fn null_timestamp(mut self) -> Self {
        self.buffer
            .push(Instruction::from_raw(instr::NULL_TIMESTAMP));
        self
    }

    pub fn null_string(mut self) -> Self {
        self.buffer.push(Instruction::from_raw(instr::NULL_STRING));
        self
    }

    pub fn null_symbol(mut self) -> Self {
        self.buffer.push(Instruction::from_raw(instr::NULL_SYMBOL));
        self
    }

    pub fn null_clob(mut self) -> Self {
        self.buffer.push(Instruction::from_raw(instr::NULL_CLOB));
        self
    }

    pub fn null_blob(mut self) -> Self {
        self.buffer.push(Instruction::from_raw(instr::NULL_BLOB));
        self
    }

    pub fn null_list(mut self) -> Self {
        self.buffer.push(Instruction::from_raw(instr::NULL_LIST));
        self
    }

    pub fn null_sexp(mut self) -> Self {
        self.buffer.push(Instruction::from_raw(instr::NULL_SEXP));
        self
    }

    pub fn null_struct(mut self) -> Self {
        self.buffer.push(Instruction::from_raw(instr::NULL_STRUCT));
        self
    }

    pub fn bool(mut self, value: bool) -> Self {
        self.buffer
            .push(Instruction::from_raw(instr::BOOL | value as u32));
        self
    }

    pub fn int_i16(mut self, value: i16) -> Self {
        self.buffer.push(Instruction::from_raw(
            instr::INT_I16 | (value as u16 as u32),
        ));
        self
    }

    pub fn int_i32(mut self, value: i32) -> Self {
        self.buffer.push(Instruction::from_raw(instr::INT_I32));
        self.buffer.push(Instruction::from_raw(value as u32));
        self
    }

    pub fn int_i64(mut self, value: i64) -> Self {
        self.buffer.push(Instruction::from_raw(instr::INT_I64));
        self.buffer
            .push(Instruction::from_raw((value >> 32) as u32));
        self.buffer.push(Instruction::from_raw(value as u32));
        self
    }

    pub fn float_f32(mut self, value: f32) -> Self {
        self.buffer.push(Instruction::from_raw(instr::FLOAT_F32));
        self.buffer.push(Instruction::from_raw(value.to_bits()));
        self
    }

    pub fn float_f64(mut self, value: f64) -> Self {
        self.buffer.push(Instruction::from_raw(instr::FLOAT_F64));
        let bits = value.to_bits();
        self.buffer.push(Instruction::from_raw((bits >> 32) as u32));
        self.buffer.push(Instruction::from_raw(bits as u32));
        self
    }

    pub fn symbol_sid(mut self, sid: u32) -> Self {
        self.buffer
            .push(Instruction::with_data_from(instr::SYMBOL_SID, sid));
        self
    }

    pub fn symbol_char(mut self, ch: char) -> Self {
        self.buffer
            .push(Instruction::with_data_from(instr::SYMBOL_CHAR, ch as u32));
        self
    }

    pub fn annotation_sid(mut self, sid: u32) -> Self {
        self.buffer
            .push(Instruction::with_data_from(instr::ANNOTATION_SID, sid));
        self
    }

    pub fn field_name_sid(mut self, sid: u32) -> Self {
        self.buffer
            .push(Instruction::with_data_from(instr::FIELD_NAME_SID, sid));
        self
    }

    pub fn list(self, children: impl FnOnce(Self) -> Self) -> Self {
        self.container(instr::LIST_START, children)
    }

    pub fn sexp(self, children: impl FnOnce(Self) -> Self) -> Self {
        self.container(instr::SEXP_START, children)
    }

    pub fn r#struct(self, children: impl FnOnce(Self) -> Self) -> Self {
        self.container(instr::STRUCT_START, children)
    }

    fn container(mut self, start_instr: u32, children: impl FnOnce(Self) -> Self) -> Self {
        let start = self.buffer.len();
        self.buffer.push(Instruction::from_raw(0));
        self = children(self);
        self.buffer
            .push(Instruction::from_raw(instr::END_CONTAINER));
        let len = self.buffer.len() - start - 1;
        debug_assert!(
            len <= 0x003F_FFFF,
            "container bytecode length exceeds 22-bit data field"
        );
        self.buffer[start] = Instruction::from_raw(start_instr | len as u32);
        self
    }

    pub fn end_of_input(mut self) -> Self {
        self.buffer.push(Instruction::from_raw(instr::END_OF_INPUT));
        self
    }

    pub fn refill(mut self) -> Self {
        self.buffer.push(Instruction::from_raw(instr::REFILL));
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::instruction::{op, operation_kind, render_bytecode};

    #[test]
    fn builder_scalars() {
        let bytecode = BytecodeBuilder::new()
            .bool(true)
            .int_i16(42)
            .int_i32(100_000)
            .float_f64(3.14)
            .end_of_input()
            .build();

        assert_eq!(bytecode.len(), 8);
        assert_eq!(bytecode[0].operation(), op::BOOL);
        assert_eq!(bytecode[0].data() & 1, 1);
        assert_eq!(bytecode[1].operation(), op::INT_I16);
        assert_eq!(bytecode[1].data_as_i16(), 42);
        assert_eq!(bytecode[2].operation(), op::INT_I32);
        assert_eq!(bytecode[3].raw(), 100_000u32);
        assert_eq!(bytecode[4].operation(), op::FLOAT_F64);
    }

    #[test]
    fn builder_list_auto_length() {
        let bytecode = BytecodeBuilder::new()
            .list(|b| b.int_i16(1).int_i16(2).int_i16(3))
            .end_of_input()
            .build();

        // LIST_START, 3x INT_I16, END_CONTAINER, END_OF_INPUT
        assert_eq!(bytecode.len(), 6);
        assert_eq!(bytecode[0].operation(), op::LIST_START);
        assert_eq!(bytecode[0].data(), 4); // 3 children + END_CONTAINER
        assert_eq!(bytecode[4].operation(), op::END_CONTAINER);
    }

    #[test]
    fn builder_nested_containers() {
        let bytecode = BytecodeBuilder::new()
            .list(|b| b.list(|b| b.int_i16(1).int_i16(2)).int_i16(3))
            .end_of_input()
            .build();

        // Structure:
        //   [0] LIST_START (len=6)  -- outer
        //   [1]   LIST_START (len=3)  -- inner
        //   [2]     INT_I16 1
        //   [3]     INT_I16 2
        //   [4]   END_CONTAINER       -- inner end
        //   [5]   INT_I16 3
        //   [6] END_CONTAINER         -- outer end
        //   [7] END_OF_INPUT
        assert_eq!(bytecode.len(), 8);
        assert_eq!(bytecode[0].operation(), op::LIST_START);
        assert_eq!(bytecode[0].data(), 6); // inner(4) + int(1) + END(1)
        assert_eq!(bytecode[1].operation(), op::LIST_START);
        assert_eq!(bytecode[1].data(), 3); // 2 ints + END_CONTAINER
        assert_eq!(bytecode[4].operation(), op::END_CONTAINER);
        assert_eq!(bytecode[6].operation(), op::END_CONTAINER);
        assert_eq!(bytecode[7].operation(), op::END_OF_INPUT);
    }

    #[test]
    fn builder_struct_with_fields() {
        let bytecode = BytecodeBuilder::new()
            .r#struct(|b| b.field_name_sid(4).int_i16(42).field_name_sid(5).bool(true))
            .end_of_input()
            .build();

        assert_eq!(bytecode[0].operation(), op::STRUCT_START);
        assert_eq!(bytecode[1].operation(), op::FIELD_NAME_SID);
        assert_eq!(bytecode[1].data(), 4);
        assert_eq!(bytecode[2].operation(), op::INT_I16);
        assert_eq!(bytecode[3].operation(), op::FIELD_NAME_SID);
        assert_eq!(bytecode[3].data(), 5);
        assert_eq!(bytecode[4].operation(), op::BOOL);
    }

    #[test]
    fn builder_render_output() {
        let bytecode = BytecodeBuilder::new()
            .list(|b| b.int_i16(1).bool(true))
            .end_of_input()
            .build();

        let rendered = render_bytecode(&bytecode);
        assert!(rendered.contains("LIST_START"));
        assert!(rendered.contains("INT_I16 1"));
        assert!(rendered.contains("BOOL true"));
        assert!(rendered.contains("END_CONTAINER"));
    }
}
