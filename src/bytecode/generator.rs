use crate::bytecode::constant_pool::ConstantPool;
use crate::{Decimal, Int, IonResult, Timestamp};

/// A source of bytecode instructions for the reader.
///
/// Implementations translate some underlying representation (e.g., Ion binary
/// bytes, Ion text, macro expansion) into bytecode instructions that the
/// reader can consume. The reader calls [`refill`](BytecodeGenerator::refill)
/// when it encounters a REFILL instruction, signaling that the current
/// bytecode buffer is exhausted and more instructions are needed.
///
/// The `read_*_ref` methods allow lazy resolution of scalars that were
/// encoded as source-position references (REF instructions) rather than
/// being eagerly materialized into the constant pool.
pub(crate) trait BytecodeGenerator {
    /// Fills the bytecode buffer with instructions for one or more
    /// top-level values. Appends `END_OF_INPUT` if the source is exhausted.
    ///
    /// The implementation should clear the destination before writing, or
    /// append to it -- the reader handles clearing before calling this method.
    fn refill(&mut self, destination: &mut Vec<u32>, constant_pool: &mut ConstantPool);

    /// Reads a big integer from the source at the given position/length.
    fn read_int_ref(&self, position: u32, length: u32) -> IonResult<Int>;

    /// Reads a decimal from the source.
    fn read_decimal_ref(&self, position: u32, length: u32) -> IonResult<Decimal>;

    /// Reads a timestamp from the source.
    fn read_timestamp_ref(&self, position: u32, length: u32) -> IonResult<Timestamp>;

    /// Reads UTF-8 text from the source.
    fn read_text_ref(&self, position: u32, length: u32) -> IonResult<String>;

    /// Reads raw bytes from the source.
    fn read_bytes_ref(&self, position: u32, length: u32) -> IonResult<Vec<u8>>;
}
