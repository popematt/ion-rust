//! Bytecode instruction set for the Ion bytecode reader.
//!
//! # Instruction Format
//!
//! Each instruction is a packed 32-bit integer:
//!
//! ```text
//!      ┌─ Kind (5 bits)
//!      │    ┌─ Variant (3 bits)
//!      │    │    ┌─ Operand Count (2 bits)
//!      │    │    │         ┌─ Data (22 bits)
//!      │    │    │         │
//!   ┌──┴──┐┌┴┐   ├┐ ┌──────┴──────────────────┐
//!    00000 000   00 000000  00000000  00000000
//! ```
//!
//! - **Kind** (5 bits): General category. Kinds 1–13 map to IonType.
//! - **Variant** (3 bits): Specific representation. Variant 7 = typed null.
//! - **Operand Count** (2 bits): 0–2 = literal count of following u32 words.
//!   3 = data field holds the count (for containers).
//! - **Data** (22 bits): Operation-specific payload.
//!
//! # Operation Reference
//!
//! | Operation             | Code   | Kind      | V | OC | Data              | Operand(s) |
//! |-----------------------|--------|-----------|---|----|-------------------|------------|
//! | `NULL_NULL`           | `0x0F` | Null      | 7 | 0  | —                 | —          |
//! | `BOOL`                | `0x10` | Bool      | 0 | 0  | 0=false, 1=true   | —          |
//! | `NULL_BOOL`           | `0x17` | Bool      | 7 | 0  | —                 | —          |
//! | `INT_I16`             | `0x18` | Int       | 0 | 0  | i16 value         | —          |
//! | `INT_I32`             | `0x19` | Int       | 1 | 1  | —                 | i32        |
//! | `INT_I64`             | `0x1A` | Int       | 2 | 2  | —                 | i64 (hi, lo) |
//! | `INT_CP`              | `0x1B` | Int       | 3 | 0  | CP index          | —          |
//! | `INT_REF`             | `0x1C` | Int       | 4 | 1  | length            | offset     |
//! | `NULL_INT`            | `0x1F` | Int       | 7 | 0  | —                 | —          |
//! | `FLOAT_F32`           | `0x20` | Float     | 0 | 1  | —                 | f32 bits   |
//! | `FLOAT_F64`           | `0x21` | Float     | 1 | 2  | —                 | f64 (hi, lo) |
//! | `NULL_FLOAT`          | `0x27` | Float     | 7 | 0  | —                 | —          |
//! | `DECIMAL_CP`          | `0x28` | Decimal   | 0 | 0  | CP index          | —          |
//! | `DECIMAL_REF`         | `0x29` | Decimal   | 1 | 1  | length            | offset     |
//! | `NULL_DECIMAL`        | `0x2F` | Decimal   | 7 | 0  | —                 | —          |
//! | `TIMESTAMP_CP`        | `0x30` | Timestamp | 0 | 0  | CP index          | —          |
//! | `SHORT_TIMESTAMP_REF` | `0x31` | Timestamp | 1 | 1  | opcode            | offset     |
//! | `TIMESTAMP_REF`       | `0x32` | Timestamp | 2 | 1  | length            | offset     |
//! | `NULL_TIMESTAMP`      | `0x37` | Timestamp | 7 | 0  | —                 | —          |
//! | `STRING_CP`           | `0x38` | String    | 0 | 0  | CP index          | —          |
//! | `STRING_REF`          | `0x39` | String    | 1 | 1  | length            | offset     |
//! | `NULL_STRING`         | `0x3F` | String    | 7 | 0  | —                 | —          |
//! | `SYMBOL_CP`           | `0x40` | Symbol    | 0 | 0  | CP index          | —          |
//! | `SYMBOL_REF`          | `0x41` | Symbol    | 1 | 1  | length            | offset     |
//! | `SYMBOL_SID`          | `0x42` | Symbol    | 2 | 0  | SID               | —          |
//! | `SYMBOL_CHAR`         | `0x43` | Symbol    | 3 | 0  | char code         | —          |
//! | `NULL_SYMBOL`         | `0x47` | Symbol    | 7 | 0  | —                 | —          |
//! | `CLOB_CP`             | `0x48` | Clob      | 0 | 0  | CP index          | —          |
//! | `CLOB_REF`            | `0x49` | Clob      | 1 | 1  | length            | offset     |
//! | `NULL_CLOB`           | `0x4F` | Clob      | 7 | 0  | —                 | —          |
//! | `BLOB_CP`             | `0x50` | Blob      | 0 | 0  | CP index          | —          |
//! | `BLOB_REF`            | `0x51` | Blob      | 1 | 1  | length            | offset     |
//! | `NULL_BLOB`           | `0x57` | Blob      | 7 | 0  | —                 | —          |
//! | `LIST_START`          | `0x58` | List      | 0 | 3  | bytecode length   | —          |
//! | `NULL_LIST`           | `0x5F` | List      | 7 | 0  | —                 | —          |
//! | `SEXP_START`          | `0x60` | SExp      | 0 | 3  | bytecode length   | —          |
//! | `NULL_SEXP`           | `0x67` | SExp      | 7 | 0  | —                 | —          |
//! | `STRUCT_START`        | `0x68` | Struct    | 0 | 3  | bytecode length   | —          |
//! | `NULL_STRUCT`         | `0x6F` | Struct    | 7 | 0  | —                 | —          |
//! | `ANNOTATION_CP`       | `0x70` | Annot.    | 0 | 0  | CP index          | —          |
//! | `ANNOTATION_REF`      | `0x71` | Annot.    | 1 | 1  | length            | offset     |
//! | `ANNOTATION_SID`      | `0x72` | Annot.    | 2 | 0  | SID               | —          |
//! | `FIELD_NAME_CP`       | `0x78` | Field     | 0 | 0  | CP index          | —          |
//! | `FIELD_NAME_REF`      | `0x79` | Field     | 1 | 1  | length            | offset     |
//! | `FIELD_NAME_SID`      | `0x7A` | Field     | 2 | 0  | SID               | —          |
//! | `IVM`                 | `0x80` | IVM       | 0 | 0  | major, minor (u8) | —          |
//! | `DIRECTIVE_SET_SYMBOLS`| `0x88`| Directive | 0 | 0  | —                 | —          |
//! | `DIRECTIVE_ADD_SYMBOLS`| `0x89`| Directive | 1 | 0  | —                 | —          |
//! | `DIRECTIVE_SET_MACROS`| `0x8A` | Directive | 2 | 0  | —                 | —          |
//! | `DIRECTIVE_ADD_MACROS`| `0x8B` | Directive | 3 | 0  | —                 | —          |
//! | `DIRECTIVE_USE`       | `0x8C` | Directive | 4 | 0  | —                 | —          |
//! | `PLACEHOLDER_TAGGED`  | `0x90` | Placeholder| 0| 3  | bytecode length   | —          |
//! | `PLACEHOLDER_TAGLESS` | `0x91` | Placeholder| 1| 0  | opcode            | —          |
//! | `ARGUMENT_NONE`       | `0x98` | Argument  | 0 | 0  | —                 | —          |
//! | `INVOKE`              | `0xA0` | Invoke    | 0 | 0  | macro ID          | —          |
//! | `REFILL`              | `0xA8` | Refill    | 0 | 0  | —                 | —          |
//! | `END_TEMPLATE`        | `0xB0` | End       | 0 | 0  | —                 | —          |
//! | `END_OF_INPUT`        | `0xB1` | End       | 1 | 0  | —                 | —          |
//! | `END_CONTAINER`       | `0xB2` | End       | 2 | 0  | —                 | —          |
//! | `META_OFFSET`         | `0xB8` | Metadata  | 0 | 1  | high bits (u16)   | low bits (u32) |
//! | `META_ROWCOL`         | `0xB9` | Metadata  | 1 | 1  | column            | row        |
//! | `META_COMMENT`        | `0xBA` | Metadata  | 2 | 1  | length            | offset     |
//!
//! # Containers
//!
//! Container instructions (`LIST_START`, `SEXP_START`, `STRUCT_START`) use
//! operand count 3, meaning the data field holds the **bytecode length** —
//! the number of instruction/operand words that follow, including the
//! `END_CONTAINER` delimiter. This enables O(1) skipping.
//!
//! # Directives
//!
//! Directive instructions have operand count 0 because they cannot be
//! skipped. Their content is delimited by `END_CONTAINER`.

use std::fmt;

use crate::IonType;

/// A single bytecode instruction, packed into a 32-bit integer.
///
/// Layout:
/// ```text
///      ┌─ Type (5 bits)
///      │    ┌─ Variant (3 bits)
///      │    │    ┌─ Operand Count (2 bits)
///      │    │    │         ┌─ Data (22 bits)
///      │    │    │         │
///   ┌──┴──┐ ┌┴┐ ├┐ ┌──────┴──────────────────┐
///   00000  000  00  0000000000000000000000
/// ```
#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub(crate) struct Instruction(u32);

impl Instruction {
    /// Constructs an instruction from a raw packed u32.
    pub const fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    /// Returns the raw packed u32 value.
    pub const fn raw(self) -> u32 {
        self.0
    }

    /// The 5-bit operation kind (bits 27–31). Maps directly to IonType
    /// for data model types (kinds 1–13).
    pub const fn operation_kind(self) -> u8 {
        (self.0 >> 27) as u8
    }

    /// The 3-bit variant (bits 24–26). Selects the encoding
    /// representation within an operation kind. Variant 7 indicates a
    /// typed null.
    pub const fn variant(self) -> u8 {
        ((self.0 >> 24) & 0x7) as u8
    }

    /// The full 8-bit operation (bits 24–31): kind and variant combined.
    pub const fn operation(self) -> u8 {
        (self.0 >> 24) as u8
    }

    /// Returns true if this instruction represents a typed null
    /// (variant == 0b111).
    pub const fn is_null(self) -> bool {
        self.variant() == 7
    }

    /// The 2-bit operand count field (bits 22–23). Values 0–2 are
    /// literal counts of following operand words. Value 3 means the data
    /// field holds the count (used for containers).
    pub const fn operand_count_bits(self) -> u8 {
        ((self.0 >> 22) & 0x3) as u8
    }

    /// The 22-bit data field (bits 0–21). Interpretation is
    /// operation-specific.
    pub const fn data(self) -> u32 {
        self.0 & 0x003F_FFFF
    }

    /// The data field truncated to a signed 16-bit integer. Only
    /// meaningful for `INT_I16` instructions where the generator stored
    /// a sign-extended i16 value.
    pub const fn data_as_i16(self) -> i16 {
        self.data() as i16
    }

    /// Returns a new instruction with the data field replaced. The
    /// operation and operand count bits are preserved.
    pub const fn with_data(self, data: u32) -> Self {
        Self((self.0 & !0x003F_FFFF) | (data & 0x003F_FFFF))
    }

    /// Constructs an instruction from a pre-computed base constant
    /// (which has operation and operand count set) combined with a data
    /// value. The data is masked to 22 bits.
    pub const fn with_data_from(base: u32, data: u32) -> Self {
        Self(base | (data & 0x003F_FFFF))
    }
}

impl fmt::Debug for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Instruction({:#010X})", self.0)
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = op_name(self.operation());
        let data = self.data();
        let oc = self.operand_count_bits();

        match self.operation() {
            op::BOOL => write!(f, "{name} {}", data & 1 == 1),
            op::INT_I16 => write!(f, "{name} {}", self.data_as_i16()),
            op::INT_I32 | op::INT_I64 | op::INT_CP | op::INT_REF => {
                write!(f, "{name} (data={data})")
            }
            op::FLOAT_F32 | op::FLOAT_F64 => {
                write!(f, "{name} (data={data})")
            }
            op::SYMBOL_SID | op::ANNOTATION_SID | op::FIELD_NAME_SID => {
                write!(f, "{name} ${data}")
            }
            op::SYMBOL_CHAR => {
                let ch = char::from_u32(data).unwrap_or('?');
                write!(f, "{name} '{ch}'")
            }
            _ if oc == 3 => write!(f, "{name} (len={data})"),
            _ if data != 0 => write!(f, "{name} (data={data})"),
            _ => write!(f, "{name}"),
        }
    }
}

pub(crate) fn render_bytecode(bytecode: &[Instruction]) -> String {
    use std::fmt::Write;

    let mut out = String::new();
    let mut indent: usize = 0;
    let mut i = 0;
    while i < bytecode.len() {
        let instr = bytecode[i];
        let oc = instr.operand_count_bits();

        if instr.operation() == op::END_CONTAINER || instr.operation() == op::END_TEMPLATE {
            indent = indent.saturating_sub(1);
        }

        for _ in 0..indent {
            out.push_str("  ");
        }

        // Render the instruction with operand values when present
        match oc {
            1 => {
                let operand = bytecode[i + 1].raw();
                match instr.operation() {
                    op::INT_I32 => {
                        let value = operand as i32;
                        write!(out, "INT_I32 {value}").unwrap();
                    }
                    op::FLOAT_F32 => {
                        let value = f32::from_bits(operand);
                        write!(out, "FLOAT_F32 {value}").unwrap();
                    }
                    _ => {
                        write!(out, "{instr} @{operand:#010X}").unwrap();
                    }
                }
                i += 2;
            }
            2 => {
                let hi = bytecode[i + 1].raw();
                let lo = bytecode[i + 2].raw();
                match instr.operation() {
                    op::INT_I64 => {
                        let value = ((hi as u64) << 32) | (lo as u64);
                        write!(out, "INT_I64 {}", value as i64).unwrap();
                    }
                    op::FLOAT_F64 => {
                        let bits = ((hi as u64) << 32) | (lo as u64);
                        let value = f64::from_bits(bits);
                        write!(out, "FLOAT_F64 {value}").unwrap();
                    }
                    _ => {
                        write!(out, "{instr} @{hi:#010X}:{lo:#010X}").unwrap();
                    }
                }
                i += 3;
            }
            _ => {
                // oc == 0 or oc == 3 (container start / variable-length)
                write!(out, "{instr}").unwrap();
                i += 1;
            }
        }
        out.push('\n');

        let is_container_start = matches!(
            instr.operation(),
            op::LIST_START | op::SEXP_START | op::STRUCT_START
        );
        if is_container_start {
            indent += 1;
        }
    }
    out
}

pub(crate) mod operation_kind {
    use crate::IonType;

    pub const UNSET: u8 = 0;
    pub const NULL: u8 = 1;
    pub const BOOL: u8 = 2;
    pub const INT: u8 = 3;
    pub const FLOAT: u8 = 4;
    pub const DECIMAL: u8 = 5;
    pub const TIMESTAMP: u8 = 6;
    pub const STRING: u8 = 7;
    pub const SYMBOL: u8 = 8;
    pub const CLOB: u8 = 9;
    pub const BLOB: u8 = 10;
    pub const LIST: u8 = 11;
    pub const SEXP: u8 = 12;
    pub const STRUCT: u8 = 13;
    pub const ANNOTATIONS: u8 = 14;
    pub const FIELD_NAME: u8 = 15;
    pub const IVM: u8 = 16;
    pub const DIRECTIVE: u8 = 17;
    pub const PLACEHOLDER: u8 = 18;
    pub const ARGUMENT: u8 = 19;
    pub const INVOKE_TEMPLATE: u8 = 20;
    pub const REFILL: u8 = 21;
    pub const END: u8 = 22;
    pub const METADATA: u8 = 23;

    const ION_TYPE_TABLE: [Option<IonType>; 24] = [
        None,                     // UNSET
        Some(IonType::Null),      // NULL
        Some(IonType::Bool),      // BOOL
        Some(IonType::Int),       // INT
        Some(IonType::Float),     // FLOAT
        Some(IonType::Decimal),   // DECIMAL
        Some(IonType::Timestamp), // TIMESTAMP
        Some(IonType::String),    // STRING
        Some(IonType::Symbol),    // SYMBOL
        Some(IonType::Clob),      // CLOB
        Some(IonType::Blob),      // BLOB
        Some(IonType::List),      // LIST
        Some(IonType::SExp),      // SEXP
        Some(IonType::Struct),    // STRUCT
        None,                     // ANNOTATIONS
        None,                     // FIELD_NAME
        None,                     // IVM
        None,                     // DIRECTIVE
        None,                     // PLACEHOLDER
        None,                     // ARGUMENT
        None,                     // INVOKE_TEMPLATE
        None,                     // REFILL
        None,                     // END
        None,                     // METADATA
    ];

    pub fn ion_type_of(kind: u8) -> Option<IonType> {
        ION_TYPE_TABLE.get(kind as usize).copied().flatten()
    }
}

pub(crate) mod op {
    use super::operation_kind as kind;

    const fn make(kind: u8, variant: u8) -> u8 {
        (kind << 3) | variant
    }

    pub const NULL_NULL: u8 = make(kind::NULL, 7);

    pub const BOOL: u8 = make(kind::BOOL, 0);
    pub const NULL_BOOL: u8 = make(kind::BOOL, 7);

    pub const INT_I16: u8 = make(kind::INT, 0);
    pub const INT_I32: u8 = make(kind::INT, 1);
    pub const INT_I64: u8 = make(kind::INT, 2);
    pub const INT_CP: u8 = make(kind::INT, 3);
    pub const INT_REF: u8 = make(kind::INT, 4);
    pub const NULL_INT: u8 = make(kind::INT, 7);

    pub const FLOAT_F32: u8 = make(kind::FLOAT, 0);
    pub const FLOAT_F64: u8 = make(kind::FLOAT, 1);
    pub const NULL_FLOAT: u8 = make(kind::FLOAT, 7);

    pub const DECIMAL_CP: u8 = make(kind::DECIMAL, 0);
    pub const DECIMAL_REF: u8 = make(kind::DECIMAL, 1);
    pub const NULL_DECIMAL: u8 = make(kind::DECIMAL, 7);

    pub const TIMESTAMP_CP: u8 = make(kind::TIMESTAMP, 0);
    pub const SHORT_TIMESTAMP_REF: u8 = make(kind::TIMESTAMP, 1);
    pub const TIMESTAMP_REF: u8 = make(kind::TIMESTAMP, 2);
    pub const NULL_TIMESTAMP: u8 = make(kind::TIMESTAMP, 7);

    pub const STRING_CP: u8 = make(kind::STRING, 0);
    pub const STRING_REF: u8 = make(kind::STRING, 1);
    pub const NULL_STRING: u8 = make(kind::STRING, 7);

    pub const SYMBOL_CP: u8 = make(kind::SYMBOL, 0);
    pub const SYMBOL_REF: u8 = make(kind::SYMBOL, 1);
    pub const SYMBOL_SID: u8 = make(kind::SYMBOL, 2);
    pub const SYMBOL_CHAR: u8 = make(kind::SYMBOL, 3);
    pub const NULL_SYMBOL: u8 = make(kind::SYMBOL, 7);

    pub const CLOB_CP: u8 = make(kind::CLOB, 0);
    pub const CLOB_REF: u8 = make(kind::CLOB, 1);
    pub const NULL_CLOB: u8 = make(kind::CLOB, 7);

    pub const BLOB_CP: u8 = make(kind::BLOB, 0);
    pub const BLOB_REF: u8 = make(kind::BLOB, 1);
    pub const NULL_BLOB: u8 = make(kind::BLOB, 7);

    pub const LIST_START: u8 = make(kind::LIST, 0);
    pub const NULL_LIST: u8 = make(kind::LIST, 7);

    pub const SEXP_START: u8 = make(kind::SEXP, 0);
    pub const NULL_SEXP: u8 = make(kind::SEXP, 7);

    pub const STRUCT_START: u8 = make(kind::STRUCT, 0);
    pub const NULL_STRUCT: u8 = make(kind::STRUCT, 7);

    pub const ANNOTATION_CP: u8 = make(kind::ANNOTATIONS, 0);
    pub const ANNOTATION_REF: u8 = make(kind::ANNOTATIONS, 1);
    pub const ANNOTATION_SID: u8 = make(kind::ANNOTATIONS, 2);

    pub const FIELD_NAME_CP: u8 = make(kind::FIELD_NAME, 0);
    pub const FIELD_NAME_REF: u8 = make(kind::FIELD_NAME, 1);
    pub const FIELD_NAME_SID: u8 = make(kind::FIELD_NAME, 2);

    pub const IVM: u8 = make(kind::IVM, 0);

    pub const DIRECTIVE_SET_SYMBOLS: u8 = make(kind::DIRECTIVE, 0);
    pub const DIRECTIVE_ADD_SYMBOLS: u8 = make(kind::DIRECTIVE, 1);
    pub const DIRECTIVE_SET_MACROS: u8 = make(kind::DIRECTIVE, 2);
    pub const DIRECTIVE_ADD_MACROS: u8 = make(kind::DIRECTIVE, 3);
    pub const DIRECTIVE_USE: u8 = make(kind::DIRECTIVE, 4);

    pub const PLACEHOLDER_TAGGED: u8 = make(kind::PLACEHOLDER, 0);
    pub const PLACEHOLDER_TAGLESS: u8 = make(kind::PLACEHOLDER, 1);

    pub const ARGUMENT_NONE: u8 = make(kind::ARGUMENT, 0);

    pub const INVOKE: u8 = make(kind::INVOKE_TEMPLATE, 0);

    pub const REFILL: u8 = make(kind::REFILL, 0);

    pub const END_TEMPLATE: u8 = make(kind::END, 0);
    pub const END_OF_INPUT: u8 = make(kind::END, 1);
    pub const END_CONTAINER: u8 = make(kind::END, 2);

    pub const META_OFFSET: u8 = make(kind::METADATA, 0);
    pub const META_ROWCOL: u8 = make(kind::METADATA, 1);
    pub const META_COMMENT: u8 = make(kind::METADATA, 2);
}

pub(crate) mod instr {
    use super::op;

    const fn make(operation: u8, operand_count: u8) -> u32 {
        ((operation as u32) << 24) | ((operand_count as u32) << 22)
    }

    const O0: u8 = 0;
    const O1: u8 = 1;
    const O2: u8 = 2;
    const ON: u8 = 3;

    pub const NULL_NULL: u32 = make(op::NULL_NULL, O0);
    pub const BOOL: u32 = make(op::BOOL, O0);
    pub const NULL_BOOL: u32 = make(op::NULL_BOOL, O0);
    pub const INT_I16: u32 = make(op::INT_I16, O0);
    pub const INT_I32: u32 = make(op::INT_I32, O1);
    pub const INT_I64: u32 = make(op::INT_I64, O2);
    pub const INT_CP: u32 = make(op::INT_CP, O0);
    pub const INT_REF: u32 = make(op::INT_REF, O1);
    pub const NULL_INT: u32 = make(op::NULL_INT, O0);
    pub const FLOAT_F32: u32 = make(op::FLOAT_F32, O1);
    pub const FLOAT_F64: u32 = make(op::FLOAT_F64, O2);
    pub const NULL_FLOAT: u32 = make(op::NULL_FLOAT, O0);
    pub const DECIMAL_CP: u32 = make(op::DECIMAL_CP, O0);
    pub const DECIMAL_REF: u32 = make(op::DECIMAL_REF, O1);
    pub const NULL_DECIMAL: u32 = make(op::NULL_DECIMAL, O0);
    pub const TIMESTAMP_CP: u32 = make(op::TIMESTAMP_CP, O0);
    pub const SHORT_TIMESTAMP_REF: u32 = make(op::SHORT_TIMESTAMP_REF, O1);
    pub const TIMESTAMP_REF: u32 = make(op::TIMESTAMP_REF, O1);
    pub const NULL_TIMESTAMP: u32 = make(op::NULL_TIMESTAMP, O0);
    pub const STRING_CP: u32 = make(op::STRING_CP, O0);
    pub const STRING_REF: u32 = make(op::STRING_REF, O1);
    pub const NULL_STRING: u32 = make(op::NULL_STRING, O0);
    pub const SYMBOL_CP: u32 = make(op::SYMBOL_CP, O0);
    pub const SYMBOL_REF: u32 = make(op::SYMBOL_REF, O1);
    pub const SYMBOL_SID: u32 = make(op::SYMBOL_SID, O0);
    pub const SYMBOL_CHAR: u32 = make(op::SYMBOL_CHAR, O0);
    pub const NULL_SYMBOL: u32 = make(op::NULL_SYMBOL, O0);
    pub const CLOB_CP: u32 = make(op::CLOB_CP, O0);
    pub const CLOB_REF: u32 = make(op::CLOB_REF, O1);
    pub const NULL_CLOB: u32 = make(op::NULL_CLOB, O0);
    pub const BLOB_CP: u32 = make(op::BLOB_CP, O0);
    pub const BLOB_REF: u32 = make(op::BLOB_REF, O1);
    pub const NULL_BLOB: u32 = make(op::NULL_BLOB, O0);
    pub const LIST_START: u32 = make(op::LIST_START, ON);
    pub const NULL_LIST: u32 = make(op::NULL_LIST, O0);
    pub const SEXP_START: u32 = make(op::SEXP_START, ON);
    pub const NULL_SEXP: u32 = make(op::NULL_SEXP, O0);
    pub const STRUCT_START: u32 = make(op::STRUCT_START, ON);
    pub const NULL_STRUCT: u32 = make(op::NULL_STRUCT, O0);
    pub const ANNOTATION_CP: u32 = make(op::ANNOTATION_CP, O0);
    pub const ANNOTATION_REF: u32 = make(op::ANNOTATION_REF, O1);
    pub const ANNOTATION_SID: u32 = make(op::ANNOTATION_SID, O0);
    pub const FIELD_NAME_CP: u32 = make(op::FIELD_NAME_CP, O0);
    pub const FIELD_NAME_REF: u32 = make(op::FIELD_NAME_REF, O1);
    pub const FIELD_NAME_SID: u32 = make(op::FIELD_NAME_SID, O0);
    pub const IVM: u32 = make(op::IVM, O0);
    pub const DIRECTIVE_SET_SYMBOLS: u32 = make(op::DIRECTIVE_SET_SYMBOLS, O0);
    pub const DIRECTIVE_ADD_SYMBOLS: u32 = make(op::DIRECTIVE_ADD_SYMBOLS, O0);
    pub const DIRECTIVE_SET_MACROS: u32 = make(op::DIRECTIVE_SET_MACROS, O0);
    pub const DIRECTIVE_ADD_MACROS: u32 = make(op::DIRECTIVE_ADD_MACROS, O0);
    pub const DIRECTIVE_USE: u32 = make(op::DIRECTIVE_USE, O0);
    pub const PLACEHOLDER_TAGGED: u32 = make(op::PLACEHOLDER_TAGGED, ON);
    pub const PLACEHOLDER_TAGLESS: u32 = make(op::PLACEHOLDER_TAGLESS, O0);
    pub const ARGUMENT_NONE: u32 = make(op::ARGUMENT_NONE, O0);
    pub const INVOKE: u32 = make(op::INVOKE, O0);
    pub const REFILL: u32 = make(op::REFILL, O0);
    pub const END_TEMPLATE: u32 = make(op::END_TEMPLATE, O0);
    pub const END_OF_INPUT: u32 = make(op::END_OF_INPUT, O0);
    pub const END_CONTAINER: u32 = make(op::END_CONTAINER, O0);
    pub const META_OFFSET: u32 = make(op::META_OFFSET, O1);
    pub const META_ROWCOL: u32 = make(op::META_ROWCOL, O1);
    pub const META_COMMENT: u32 = make(op::META_COMMENT, O1);
}

fn op_name(operation: u8) -> &'static str {
    match operation {
        op::NULL_NULL => "NULL_NULL",
        op::BOOL => "BOOL",
        op::NULL_BOOL => "NULL_BOOL",
        op::INT_I16 => "INT_I16",
        op::INT_I32 => "INT_I32",
        op::INT_I64 => "INT_I64",
        op::INT_CP => "INT_CP",
        op::INT_REF => "INT_REF",
        op::NULL_INT => "NULL_INT",
        op::FLOAT_F32 => "FLOAT_F32",
        op::FLOAT_F64 => "FLOAT_F64",
        op::NULL_FLOAT => "NULL_FLOAT",
        op::DECIMAL_CP => "DECIMAL_CP",
        op::DECIMAL_REF => "DECIMAL_REF",
        op::NULL_DECIMAL => "NULL_DECIMAL",
        op::TIMESTAMP_CP => "TIMESTAMP_CP",
        op::SHORT_TIMESTAMP_REF => "SHORT_TIMESTAMP_REF",
        op::TIMESTAMP_REF => "TIMESTAMP_REF",
        op::NULL_TIMESTAMP => "NULL_TIMESTAMP",
        op::STRING_CP => "STRING_CP",
        op::STRING_REF => "STRING_REF",
        op::NULL_STRING => "NULL_STRING",
        op::SYMBOL_CP => "SYMBOL_CP",
        op::SYMBOL_REF => "SYMBOL_REF",
        op::SYMBOL_SID => "SYMBOL_SID",
        op::SYMBOL_CHAR => "SYMBOL_CHAR",
        op::NULL_SYMBOL => "NULL_SYMBOL",
        op::CLOB_CP => "CLOB_CP",
        op::CLOB_REF => "CLOB_REF",
        op::NULL_CLOB => "NULL_CLOB",
        op::BLOB_CP => "BLOB_CP",
        op::BLOB_REF => "BLOB_REF",
        op::NULL_BLOB => "NULL_BLOB",
        op::LIST_START => "LIST_START",
        op::NULL_LIST => "NULL_LIST",
        op::SEXP_START => "SEXP_START",
        op::NULL_SEXP => "NULL_SEXP",
        op::STRUCT_START => "STRUCT_START",
        op::NULL_STRUCT => "NULL_STRUCT",
        op::ANNOTATION_CP => "ANNOTATION_CP",
        op::ANNOTATION_REF => "ANNOTATION_REF",
        op::ANNOTATION_SID => "ANNOTATION_SID",
        op::FIELD_NAME_CP => "FIELD_NAME_CP",
        op::FIELD_NAME_REF => "FIELD_NAME_REF",
        op::FIELD_NAME_SID => "FIELD_NAME_SID",
        op::IVM => "IVM",
        op::DIRECTIVE_SET_SYMBOLS => "DIRECTIVE_SET_SYMBOLS",
        op::DIRECTIVE_ADD_SYMBOLS => "DIRECTIVE_ADD_SYMBOLS",
        op::DIRECTIVE_SET_MACROS => "DIRECTIVE_SET_MACROS",
        op::DIRECTIVE_ADD_MACROS => "DIRECTIVE_ADD_MACROS",
        op::DIRECTIVE_USE => "DIRECTIVE_USE",
        op::PLACEHOLDER_TAGGED => "PLACEHOLDER_TAGGED",
        op::PLACEHOLDER_TAGLESS => "PLACEHOLDER_TAGLESS",
        op::ARGUMENT_NONE => "ARGUMENT_NONE",
        op::INVOKE => "INVOKE",
        op::REFILL => "REFILL",
        op::END_TEMPLATE => "END_TEMPLATE",
        op::END_OF_INPUT => "END_OF_INPUT",
        op::END_CONTAINER => "END_CONTAINER",
        op::META_OFFSET => "META_OFFSET",
        op::META_ROWCOL => "META_ROWCOL",
        op::META_COMMENT => "META_COMMENT",
        _ => "UNKNOWN",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[test]
    fn instruction_field_extraction() {
        let i = Instruction::from_raw(instr::INT_I16).with_data(42);
        assert_eq!(i.operation_kind(), operation_kind::INT);
        assert_eq!(i.variant(), 0);
        assert_eq!(i.operation(), op::INT_I16);
        assert_eq!(i.operand_count_bits(), 0);
        assert_eq!(i.data(), 42);
        assert_eq!(i.data_as_i16(), 42);
        assert!(!i.is_null());
    }

    #[test]
    fn instruction_negative_i16() {
        let i = Instruction::from_raw(instr::INT_I16 | (-7i16 as u16 as u32));
        assert_eq!(i.data_as_i16(), -7);
    }

    #[test]
    fn instruction_null_variant() {
        let i = Instruction::from_raw(instr::NULL_INT);
        assert!(i.is_null());
        assert_eq!(i.operation_kind(), operation_kind::INT);
    }

    #[test]
    fn instruction_container_operand_count() {
        let i = Instruction::from_raw(instr::LIST_START | 10);
        assert_eq!(i.operand_count_bits(), 3);
        assert_eq!(i.data(), 10);
        assert_eq!(i.operation_kind(), operation_kind::LIST);
    }

    #[rstest]
    #[case(instr::INT_I32, 1)]
    #[case(instr::INT_I64, 2)]
    #[case(instr::FLOAT_F32, 1)]
    #[case(instr::FLOAT_F64, 2)]
    #[case(instr::BOOL, 0)]
    #[case(instr::SYMBOL_SID, 0)]
    #[case(instr::LIST_START, 3)]
    fn operand_count(#[case] raw: u32, #[case] expected: u8) {
        let i = Instruction::from_raw(raw);
        assert_eq!(i.operand_count_bits(), expected);
    }

    #[rstest]
    #[case(instr::NULL_NULL)]
    #[case(instr::NULL_BOOL)]
    #[case(instr::NULL_INT)]
    #[case(instr::NULL_FLOAT)]
    #[case(instr::NULL_DECIMAL)]
    #[case(instr::NULL_TIMESTAMP)]
    #[case(instr::NULL_STRING)]
    #[case(instr::NULL_SYMBOL)]
    #[case(instr::NULL_CLOB)]
    #[case(instr::NULL_BLOB)]
    #[case(instr::NULL_LIST)]
    #[case(instr::NULL_SEXP)]
    #[case(instr::NULL_STRUCT)]
    fn null_operations_are_null(#[case] raw: u32) {
        assert!(Instruction::from_raw(raw).is_null());
    }

    #[rstest]
    #[case(instr::BOOL)]
    #[case(instr::INT_I16)]
    #[case(instr::INT_I32)]
    #[case(instr::INT_I64)]
    #[case(instr::FLOAT_F32)]
    #[case(instr::FLOAT_F64)]
    #[case(instr::LIST_START)]
    #[case(instr::SEXP_START)]
    #[case(instr::STRUCT_START)]
    #[case(instr::SYMBOL_SID)]
    #[case(instr::STRING_REF)]
    #[case(instr::END_CONTAINER)]
    #[case(instr::REFILL)]
    fn non_null_operations_are_not_null(#[case] raw: u32) {
        assert!(!Instruction::from_raw(raw).is_null());
    }

    #[rstest]
    #[case(operation_kind::NULL, Some(IonType::Null))]
    #[case(operation_kind::BOOL, Some(IonType::Bool))]
    #[case(operation_kind::INT, Some(IonType::Int))]
    #[case(operation_kind::FLOAT, Some(IonType::Float))]
    #[case(operation_kind::DECIMAL, Some(IonType::Decimal))]
    #[case(operation_kind::TIMESTAMP, Some(IonType::Timestamp))]
    #[case(operation_kind::STRING, Some(IonType::String))]
    #[case(operation_kind::SYMBOL, Some(IonType::Symbol))]
    #[case(operation_kind::CLOB, Some(IonType::Clob))]
    #[case(operation_kind::BLOB, Some(IonType::Blob))]
    #[case(operation_kind::LIST, Some(IonType::List))]
    #[case(operation_kind::SEXP, Some(IonType::SExp))]
    #[case(operation_kind::STRUCT, Some(IonType::Struct))]
    #[case(operation_kind::ANNOTATIONS, None)]
    #[case(operation_kind::FIELD_NAME, None)]
    #[case(operation_kind::END, None)]
    #[case(operation_kind::REFILL, None)]
    fn ion_type_mapping(#[case] kind: u8, #[case] expected: Option<IonType>) {
        assert_eq!(operation_kind::ion_type_of(kind), expected);
    }

    #[test]
    fn with_data_preserves_operation() {
        let base = Instruction::from_raw(instr::SYMBOL_SID);
        let with_data = base.with_data(123);
        assert_eq!(with_data.operation(), op::SYMBOL_SID);
        assert_eq!(with_data.data(), 123);
        assert_eq!(with_data.operand_count_bits(), 0);
    }

    #[test]
    fn with_data_from_works() {
        let i = Instruction::with_data_from(instr::INT_I16, 0x003F_FFFF);
        assert_eq!(i.operation(), op::INT_I16);
        assert_eq!(i.data(), 0x003F_FFFF);
    }

    #[rstest]
    #[case(instr::BOOL | 1, "BOOL true")]
    #[case(instr::BOOL, "BOOL false")]
    #[case(instr::INT_I16 | (-3i16 as u16 as u32), "INT_I16 -3")]
    #[case(instr::LIST_START | 5, "LIST_START (len=5)")]
    #[case(instr::SYMBOL_SID | 7, "SYMBOL_SID $7")]
    #[case(instr::SYMBOL_CHAR | ('A' as u32), "SYMBOL_CHAR 'A'")]
    #[case(instr::END_CONTAINER, "END_CONTAINER")]
    #[case(instr::NULL_INT, "NULL_INT")]
    fn display_formatting(#[case] raw: u32, #[case] expected: &str) {
        assert_eq!(format!("{}", Instruction::from_raw(raw)), expected);
    }

    #[test]
    fn op_name_covers_all_operations() {
        let all_ops: &[u8] = &[
            op::NULL_NULL,
            op::BOOL,
            op::NULL_BOOL,
            op::INT_I16,
            op::INT_I32,
            op::INT_I64,
            op::INT_CP,
            op::INT_REF,
            op::NULL_INT,
            op::FLOAT_F32,
            op::FLOAT_F64,
            op::NULL_FLOAT,
            op::DECIMAL_CP,
            op::DECIMAL_REF,
            op::NULL_DECIMAL,
            op::TIMESTAMP_CP,
            op::SHORT_TIMESTAMP_REF,
            op::TIMESTAMP_REF,
            op::NULL_TIMESTAMP,
            op::STRING_CP,
            op::STRING_REF,
            op::NULL_STRING,
            op::SYMBOL_CP,
            op::SYMBOL_REF,
            op::SYMBOL_SID,
            op::SYMBOL_CHAR,
            op::NULL_SYMBOL,
            op::CLOB_CP,
            op::CLOB_REF,
            op::NULL_CLOB,
            op::BLOB_CP,
            op::BLOB_REF,
            op::NULL_BLOB,
            op::LIST_START,
            op::NULL_LIST,
            op::SEXP_START,
            op::NULL_SEXP,
            op::STRUCT_START,
            op::NULL_STRUCT,
            op::ANNOTATION_CP,
            op::ANNOTATION_REF,
            op::ANNOTATION_SID,
            op::FIELD_NAME_CP,
            op::FIELD_NAME_REF,
            op::FIELD_NAME_SID,
            op::IVM,
            op::DIRECTIVE_SET_SYMBOLS,
            op::DIRECTIVE_ADD_SYMBOLS,
            op::DIRECTIVE_SET_MACROS,
            op::DIRECTIVE_ADD_MACROS,
            op::DIRECTIVE_USE,
            op::PLACEHOLDER_TAGGED,
            op::PLACEHOLDER_TAGLESS,
            op::ARGUMENT_NONE,
            op::INVOKE,
            op::REFILL,
            op::END_TEMPLATE,
            op::END_OF_INPUT,
            op::END_CONTAINER,
            op::META_OFFSET,
            op::META_ROWCOL,
            op::META_COMMENT,
        ];
        for &operation in all_ops {
            assert_ne!(
                op_name(operation),
                "UNKNOWN",
                "op_name does not cover operation code {operation:#04X}"
            );
        }
    }
}
