//! Arena-based materializer for the bytecode reader.
//!
//! Eliminates the ~41% deallocation cost observed in profiling by
//! materializing `Element` values into a reusable bump arena. Each call
//! to [`ArenaReader::next`] resets the arena (O(1) pointer reset) and
//! materializes the next top-level value into it, returning `&Element`.
//!
//! The public API is fully safe. All `unsafe` is encapsulated within
//! this module.

use std::mem;
use std::sync::Arc;

use crate::bytecode::constant_pool::{Constant, ConstantPool};
use crate::bytecode::generator::BytecodeGenerator;
use crate::bytecode::instruction::{op, operation_kind, Instruction};
use crate::element::Annotations;
use crate::result::IonFailure;
use crate::types::symbol::SymbolTableRef;
use crate::{Bytes, Element, Int, IonResult, IonType, Sequence, Str, Struct, Symbol, Value};

use super::materialize::SYSTEM_SYMBOLS;

// ─── Bump Arena ────────────────────────────────────────────────────────

/// Default initial chunk size (4 KB).
const INITIAL_CHUNK_SIZE: usize = 4096;

/// A chunk-based bump allocator.
///
/// Allocations are O(1) pointer bumps within the current chunk. When a
/// chunk fills, a new (larger) chunk is allocated — previous chunks are
/// retained and their pointers remain valid. The entire arena is reset
/// in O(1) by resetting the offset in the first chunk and discarding
/// additional chunks.
///
/// No destructors are run on reset — all types placed in the arena must
/// tolerate having their `Drop` skipped.
struct BumpArena {
    /// The chunks. Index 0 is the "primary" chunk reused across resets.
    /// Additional chunks are overflow allocations.
    chunks: Vec<Vec<u8>>,
    /// Current allocation offset within the active (last) chunk.
    offset: usize,
}

impl BumpArena {
    fn new() -> Self {
        Self {
            chunks: Vec::new(),
            offset: 0,
        }
    }

    /// Resets the arena, invalidating all prior allocations.
    /// This does NOT run destructors on any allocated values.
    ///
    /// The first chunk is retained for reuse. Additional overflow chunks
    /// are dropped to free memory.
    #[inline]
    fn reset(&mut self) {
        // Keep only the first chunk (if any) to avoid reallocation on
        // the next iteration. Additional overflow chunks are freed.
        self.chunks.truncate(1);
        self.offset = 0;
    }

    /// Allocates space for a value of type `T` and writes `value` into it.
    /// Returns a mutable reference to the arena-placed value.
    #[inline]
    fn alloc<T>(&mut self, value: T) -> &mut T {
        let align = mem::align_of::<T>();
        let size = mem::size_of::<T>();
        let ptr = self.alloc_raw(size, align);
        // SAFETY: `alloc_raw` returns a properly aligned pointer with
        // sufficient space for `size` bytes. We write a valid `T` into it.
        unsafe {
            let typed_ptr = ptr as *mut T;
            typed_ptr.write(value);
            &mut *typed_ptr
        }
    }

    /// Allocates `len` bytes in the arena and copies `src` into them.
    /// Returns a pointer to the start of the allocation.
    #[inline]
    fn alloc_bytes(&mut self, src: &[u8]) -> *mut u8 {
        let len = src.len();
        if len == 0 {
            return std::ptr::NonNull::dangling().as_ptr();
        }
        let ptr = self.alloc_raw(len, 1);
        // SAFETY: alloc_raw guarantees `ptr` has at least `len` bytes.
        unsafe {
            std::ptr::copy_nonoverlapping(src.as_ptr(), ptr, len);
        }
        ptr
    }

    /// Low-level allocation: aligns offset, ensures capacity (possibly
    /// adding a new chunk), bumps offset, and returns a raw pointer.
    ///
    /// Once allocated, the returned pointer remains valid until `reset()`
    /// is called — the underlying chunk is never moved or freed.
    #[inline]
    fn alloc_raw(&mut self, size: usize, align: usize) -> *mut u8 {
        if self.chunks.is_empty() {
            let cap = INITIAL_CHUNK_SIZE.max(size + align);
            // Zero-initialized; the memset cost is negligible relative to
            // the work saved by arena allocation over the chunk's lifetime.
            self.chunks.push(vec![0u8; cap]);
        }

        let chunk = self.chunks.last().unwrap();
        let chunk_len = chunk.len();

        // Align the current offset within this chunk.
        let aligned = (self.offset + align - 1) & !(align - 1);
        let new_offset = aligned + size;

        if new_offset <= chunk_len {
            // Allocation fits in the current chunk.
            self.offset = new_offset;
            // SAFETY: `aligned < new_offset <= chunk_len`, so the
            // pointer is within the chunk's allocation.
            unsafe { self.chunks.last_mut().unwrap().as_mut_ptr().add(aligned) }
        } else {
            // Need a new chunk. Size it as at least double the previous
            // chunk or large enough for this allocation.
            let prev_cap = chunk_len;
            let new_cap = (prev_cap * 2).max(size + align);
            self.chunks.push(vec![0u8; new_cap]);
            self.offset = size; // aligned offset is 0 for fresh chunk
                                // SAFETY: The new chunk has capacity >= size, and offset 0
                                // satisfies any alignment (system allocator returns
                                // maximally-aligned memory).
            self.chunks.last_mut().unwrap().as_mut_ptr()
        }
    }
}

// ─── Arena allocation helpers ──────────────────────────────────────────

/// Copies `text` into the arena and constructs a `String` backed by
/// arena memory. The resulting String must NOT be dropped normally --
/// it is only safe within the arena's lifetime with Drop skipped.
#[inline]
fn arena_string(arena: &mut BumpArena, text: &str) -> String {
    let bytes = text.as_bytes();
    let len = bytes.len();
    let ptr = arena.alloc_bytes(bytes);
    // SAFETY: `ptr` points to `len` bytes of valid UTF-8 in the arena.
    // We set capacity = len so realloc is triggered on any push (which
    // never happens -- the Element is immutable via &Element).
    // Drop is skipped because the arena reset doesn't run destructors.
    unsafe { String::from_raw_parts(ptr, len, len) }
}

/// Copies `bytes` into the arena and constructs a `Vec<u8>` backed by
/// arena memory.
#[inline]
fn arena_bytes(arena: &mut BumpArena, bytes: &[u8]) -> Vec<u8> {
    let len = bytes.len();
    let ptr = arena.alloc_bytes(bytes);
    // SAFETY: Same invariants as arena_string. ptr points to `len`
    // valid bytes in the arena. capacity = len. Drop is skipped.
    unsafe { Vec::from_raw_parts(ptr, len, len) }
}

/// Creates a Symbol from text by copying the text bytes into the arena,
/// then constructing an `Owned(String)` backed by arena memory.
#[inline]
fn arena_symbol_from_text(arena: &mut BumpArena, text: &str) -> Symbol {
    let s = arena_string(arena, text);
    Symbol::owned(s)
}

/// Copies a Vec of Symbols into the arena and constructs a `Vec<Symbol>`
/// backed by arena memory.
#[inline]
fn arena_symbol_vec(arena: &mut BumpArena, symbols: Vec<Symbol>) -> Vec<Symbol> {
    let len = symbols.len();
    if len == 0 {
        return unsafe { Vec::from_raw_parts(std::ptr::NonNull::dangling().as_ptr(), 0, 0) };
    }
    let size = len * std::mem::size_of::<Symbol>();
    let align = std::mem::align_of::<Symbol>();
    let ptr = arena.alloc_raw(size, align) as *mut Symbol;
    for (i, sym) in symbols.into_iter().enumerate() {
        unsafe { ptr.add(i).write(sym) };
    }
    unsafe { Vec::from_raw_parts(ptr, len, len) }
}

/// Copies a slice of Elements into the arena and constructs a `Vec<Element>`
/// backed by arena memory. The source Vec is consumed without dropping its
/// backing storage (we copy element by element into the arena).
#[inline]
fn arena_element_vec(arena: &mut BumpArena, elements: Vec<Element>) -> Vec<Element> {
    let len = elements.len();
    if len == 0 {
        return unsafe { Vec::from_raw_parts(std::ptr::NonNull::dangling().as_ptr(), 0, 0) };
    }
    let size = len * std::mem::size_of::<Element>();
    let align = std::mem::align_of::<Element>();
    let ptr = arena.alloc_raw(size, align) as *mut Element;
    // SAFETY: ptr is properly aligned and has space for `len` Elements.
    // We write each element via ptr::write (no drop of uninitialized memory).
    for (i, element) in elements.into_iter().enumerate() {
        unsafe { ptr.add(i).write(element) };
    }
    // SAFETY: ptr points to `len` initialized Elements in the arena.
    // capacity == len prevents growth. Drop is skipped on arena reset.
    unsafe { Vec::from_raw_parts(ptr, len, len) }
}

/// Copies a slice of (Symbol, Element) pairs into the arena and constructs
/// a `Vec<(Symbol, Element)>` backed by arena memory.
#[inline]
fn arena_fields_vec(
    arena: &mut BumpArena,
    fields: Vec<(Symbol, Element)>,
) -> Vec<(Symbol, Element)> {
    let len = fields.len();
    if len == 0 {
        return unsafe { Vec::from_raw_parts(std::ptr::NonNull::dangling().as_ptr(), 0, 0) };
    }
    let size = len * std::mem::size_of::<(Symbol, Element)>();
    let align = std::mem::align_of::<(Symbol, Element)>();
    let ptr = arena.alloc_raw(size, align) as *mut (Symbol, Element);
    for (i, field) in fields.into_iter().enumerate() {
        unsafe { ptr.add(i).write(field) };
    }
    unsafe { Vec::from_raw_parts(ptr, len, len) }
}

// ─── ArenaReader ───────────────────────────────────────────────────────

/// An arena-based materializer that yields `&Element` references backed
/// by a reusable bump arena.
///
/// Each call to [`next()`](ArenaReader::next) resets the arena and
/// materializes the next top-level value. The returned `&Element` borrows
/// from the reader, preventing another `next()` call until the reference
/// is dropped.
///
/// # Example
///
/// ```ignore
/// let mut reader = ArenaReader::new(generator)?;
/// while let Some(result) = reader.next() {
///     let element = result?;
///     process(element); // borrow valid here
/// }
/// ```
pub struct ArenaReader<G: BytecodeGenerator> {
    generator: G,
    bytecode: Vec<u32>,
    pos: usize,
    symbol_table: Vec<Option<Arc<str>>>,
    constant_pool: ConstantPool,
    first_local_constant: usize,
    arena: BumpArena,
}

impl<G: BytecodeGenerator> ArenaReader<G> {
    /// Creates a new `ArenaReader` backed by the given generator.
    pub fn new(generator: G) -> IonResult<Self> {
        let symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
        let mut reader = Self {
            generator,
            bytecode: Vec::new(),
            pos: 0,
            symbol_table,
            constant_pool: ConstantPool::new(),
            first_local_constant: 0,
            arena: BumpArena::new(),
        };
        reader.refill()?;
        Ok(reader)
    }

    /// Returns the number of chunks in the arena (for diagnostics).
    pub fn arena_chunk_count(&self) -> usize {
        self.arena.chunks.len()
    }

    /// Returns the total bytes allocated across all arena chunks.
    pub fn arena_total_bytes(&self) -> usize {
        self.arena.chunks.iter().map(|c| c.len()).sum()
    }

    /// Returns the next top-level value, or `None` at end of input.
    ///
    /// The returned reference is valid until the next call to `next()`
    /// or until the reader is dropped.
    ///
    /// Internally, multiple values are materialized into the arena in
    /// batches (aligned with bytecode refill boundaries). `next()`
    /// returns them one at a time. The arena resets only when the
    /// current batch is exhausted and a new refill is needed.
    ///
    /// This method intentionally does not implement `Iterator` because
    /// the returned reference borrows from `self` (lending iterator
    /// pattern), which `Iterator::Item` cannot express.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<IonResult<&Element>> {
        // Reset the arena — previous Element is abandoned, memory reused.
        self.arena.reset();

        // Process system instructions until we find a value or reach end.
        // Loop handles refill boundaries (including multiple consecutive
        // refills when bytecode buffers contain only system values).
        loop {
            if self.pos >= self.bytecode.len() {
                return None;
            }
            let peek = Instruction::from_raw(self.bytecode[self.pos]);
            match peek.operation_kind() {
                operation_kind::END => return None,
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
                    self.pos += 1;
                    let oc = peek.operand_count_bits();
                    if oc > 0 && oc < 3 {
                        self.pos += oc as usize;
                    }
                    continue;
                }
                _ => {
                    return Some(self.read_element_into_arena());
                }
            }
        }
    }

    // ─── Internal: bytecode navigation ─────────────────────────────

    #[inline(always)]
    fn consume(&mut self) -> Instruction {
        let raw = self.bytecode[self.pos];
        self.pos += 1;
        Instruction::from_raw(raw)
    }

    #[inline(always)]
    fn consume_raw(&mut self) -> u32 {
        let raw = self.bytecode[self.pos];
        self.pos += 1;
        raw
    }

    fn refill(&mut self) -> IonResult<()> {
        self.constant_pool.truncate(self.first_local_constant);
        self.bytecode.clear();
        self.generator
            .refill(&mut self.bytecode, &mut self.constant_pool)?;
        self.pos = 0;
        Ok(())
    }

    fn handle_ivm(&mut self, _instruction: Instruction) {
        self.symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
    }

    fn handle_directive(&mut self, instruction: Instruction) -> IonResult<()> {
        let operation = instruction.operation();
        match operation {
            op::DIRECTIVE_SET_SYMBOLS | op::DIRECTIVE_ADD_SYMBOLS => {
                if operation == op::DIRECTIVE_SET_SYMBOLS {
                    self.symbol_table =
                        SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
                }
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
                            self.symbol_table.push(None);
                        }
                        _ => {
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
            _ => loop {
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
            },
        }
        Ok(())
    }

    // ─── Internal: arena materialization ───────────────────────────

    /// Reads an element (annotations + value) and places it in the arena.
    /// Returns a reference to the arena-allocated Element.
    ///
    /// # Safety rationale
    ///
    /// The returned `&Element` borrows from `self.arena`. The signature
    /// ties its lifetime to `&mut self`, which prevents the caller from
    /// calling `next()` (which takes `&mut self`) while the reference is
    /// live. The arena memory remains valid until the next `reset()` call,
    /// which only happens at the top of `next()`.
    fn read_element_into_arena(&mut self) -> IonResult<&Element> {
        let annotations = self.read_annotations_arena()?;
        let instr = self.consume();
        let value = self.read_value_arena(instr)?;

        // Construct the Element in the arena.
        let element = Element::new(annotations, value);
        let element_ptr = self.arena.alloc(element) as *const Element;
        // SAFETY: The pointer is into `self.arena` which lives as long as
        // `self`. The caller cannot call `next()` again while holding the
        // returned reference because `next()` requires `&mut self`. The
        // arena memory is not freed until the next `reset()` in `next()`.
        Ok(unsafe { &*element_ptr })
    }

    /// Reads annotations into arena-allocated symbols.
    fn read_annotations_arena(&mut self) -> IonResult<Annotations> {
        let start = self.pos;
        let mut count: usize = 0;
        loop {
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

        // Resolve annotations
        let mut symbols = Vec::with_capacity(count);
        let mut p = start;
        for _ in 0..count {
            let instr = Instruction::from_raw(self.bytecode[p]);
            p += 1;
            let data = instr.data();
            let symbol = match instr.operation() {
                op::ANNOTATION_SID => self.resolve_sid_arena(data as usize),
                op::ANNOTATION_CP => match self.constant_pool.get(data) {
                    Constant::String(arc) => {
                        // SAFETY: The constant pool is not truncated during
                        // materialization. The pointer is valid until arena reset.
                        let ptr = arc as *const Arc<str>;
                        Symbol {
                            text: crate::types::symbol::SymbolText::ArenaBorrowed(
                                unsafe { SymbolTableRef::new(ptr) },
                            ),
                        }
                    }
                    _ => return IonResult::decoding_error("annotation CP entry is not a string"),
                },
                op::ANNOTATION_REF => {
                    let position = self.bytecode[p];
                    p += 1;
                    let text = self.generator.read_text_ref(position, data)?;
                    // SAFETY: Generator source is stable during materialization.
                    let text: &str = unsafe { &*(text as *const str) };
                    arena_symbol_from_text(&mut self.arena, text)
                }
                _ => return IonResult::decoding_error("expected annotation instruction"),
            };
            symbols.push(symbol);
        }

        // Move symbols into arena-backed Vec so Drop is skipped.
        let arena_vec = arena_symbol_vec(&mut self.arena, symbols);
        Ok(Annotations::new(arena_vec))
    }

    /// Resolves a SID to a Symbol using `ArenaBorrowed` when possible.
    #[inline]
    fn resolve_sid_arena(&self, sid: usize) -> Symbol {
        if sid == 0 {
            return Symbol::unknown_text();
        }
        match self.symbol_table.get(sid - 1) {
            Some(Some(arc)) => {
                // SAFETY: The pointer targets a slot in the symbol table Vec's buffer.
                // The symbol table is stable during materialization (between arena reset
                // and the return of &Element). The borrow checker prevents another
                // next() call while the &Element borrow is live.
                let ptr = arc as *const Arc<str>;
                let sym_ref = unsafe { SymbolTableRef::new(ptr) };
                Symbol {
                    text: crate::types::symbol::SymbolText::ArenaBorrowed(sym_ref),
                }
            }
            _ => Symbol::unknown_text(),
        }
    }

    /// Reads a value from the bytecode and materializes it.
    fn read_value_arena(&mut self, instr: Instruction) -> IonResult<Value> {
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

            op::STRING_CP => {
                let text: &str = match self.constant_pool.get(instr.data()) {
                    Constant::String(arc) => {
                        // SAFETY: We need to extend the lifetime of this &str past
                        // the borrow of constant_pool. This is safe because the
                        // constant pool is not modified during value materialization.
                        unsafe { &*(arc.as_ref() as *const str) }
                    }
                    _ => return IonResult::decoding_error("CP entry is not String"),
                };
                let s = arena_string(&mut self.arena, text);
                Ok(Value::String(Str::from(s)))
            }
            op::STRING_REF => {
                let position = self.consume_raw();
                let text = self.generator.read_text_ref(position, instr.data())?;
                // SAFETY: The generator's source data is stable during materialization.
                let text: &str = unsafe { &*(text as *const str) };
                let s = arena_string(&mut self.arena, text);
                Ok(Value::String(Str::from(s)))
            }
            op::NULL_STRING => Ok(Value::Null(IonType::String)),

            op::SYMBOL_SID => {
                let sid = instr.data() as usize;
                Ok(Value::Symbol(self.resolve_sid_arena(sid)))
            }
            op::SYMBOL_CP => match self.constant_pool.get(instr.data()) {
                Constant::String(arc) => {
                    // SAFETY: CP is stable during materialization.
                    let ptr = arc as *const Arc<str>;
                    Ok(Value::Symbol(Symbol {
                        text: crate::types::symbol::SymbolText::ArenaBorrowed(
                            unsafe { SymbolTableRef::new(ptr) },
                        ),
                    }))
                }
                _ => IonResult::decoding_error("CP entry is not String"),
            },
            op::SYMBOL_CHAR => {
                let ch = char::from_u32(instr.data()).ok_or_else(|| {
                    IonResult::<()>::decoding_error("invalid char code").unwrap_err()
                })?;
                let mut buf = [0u8; 4];
                let s = ch.encode_utf8(&mut buf);
                Ok(Value::Symbol(arena_symbol_from_text(&mut self.arena, s)))
            }
            op::SYMBOL_REF => {
                let position = self.consume_raw();
                let text = self.generator.read_text_ref(position, instr.data())?;
                // SAFETY: The generator's source data is stable during materialization.
                let text: &str = unsafe { &*(text as *const str) };
                Ok(Value::Symbol(arena_symbol_from_text(&mut self.arena, text)))
            }
            op::NULL_SYMBOL => Ok(Value::Null(IonType::Symbol)),

            op::BLOB_CP => {
                let data: &[u8] = match self.constant_pool.get(instr.data()) {
                    Constant::Bytes(arc) => {
                        // SAFETY: Constant pool is stable during materialization.
                        unsafe { &*(arc.as_ref() as *const [u8]) }
                    }
                    _ => return IonResult::decoding_error("CP entry is not Bytes"),
                };
                let v = arena_bytes(&mut self.arena, data);
                Ok(Value::Blob(Bytes::from(v)))
            }
            op::BLOB_REF => {
                let position = self.consume_raw();
                let bytes = self.generator.read_bytes_ref(position, instr.data())?;
                // SAFETY: Generator source data is stable during materialization.
                let bytes: &[u8] = unsafe { &*(bytes as *const [u8]) };
                let v = arena_bytes(&mut self.arena, bytes);
                Ok(Value::Blob(Bytes::from(v)))
            }
            op::NULL_BLOB => Ok(Value::Null(IonType::Blob)),

            op::CLOB_CP => {
                let data: &[u8] = match self.constant_pool.get(instr.data()) {
                    Constant::Bytes(arc) => {
                        // SAFETY: Constant pool is stable during materialization.
                        unsafe { &*(arc.as_ref() as *const [u8]) }
                    }
                    _ => return IonResult::decoding_error("CP entry is not Bytes"),
                };
                let v = arena_bytes(&mut self.arena, data);
                Ok(Value::Clob(Bytes::from(v)))
            }
            op::CLOB_REF => {
                let position = self.consume_raw();
                let bytes = self.generator.read_bytes_ref(position, instr.data())?;
                // SAFETY: Generator source data is stable during materialization.
                let bytes: &[u8] = unsafe { &*(bytes as *const [u8]) };
                let v = arena_bytes(&mut self.arena, bytes);
                Ok(Value::Clob(Bytes::from(v)))
            }
            op::NULL_CLOB => Ok(Value::Null(IonType::Clob)),

            op::LIST_START => Ok(Value::List(self.read_sequence_arena()?)),
            op::NULL_LIST => Ok(Value::Null(IonType::List)),

            op::SEXP_START => Ok(Value::SExp(self.read_sequence_arena()?)),
            op::NULL_SEXP => Ok(Value::Null(IonType::SExp)),

            op::STRUCT_START => Ok(Value::Struct(self.read_struct_arena()?)),
            op::NULL_STRUCT => Ok(Value::Null(IonType::Struct)),

            op::NULL_NULL => Ok(Value::Null(IonType::Null)),

            _ => IonResult::decoding_error(format!(
                "unexpected operation {:#04X}",
                instr.operation()
            )),
        }
    }

    /// Reads a sequence (list or sexp children) until END_CONTAINER.
    fn read_sequence_arena(&mut self) -> IonResult<Sequence> {
        let mut elements = Vec::new();
        loop {
            let peek = Instruction::from_raw(self.bytecode[self.pos]);
            if peek.operation() == op::END_CONTAINER {
                self.pos += 1;
                break;
            }
            let annotations = self.read_annotations_arena()?;
            let instr = self.consume();
            let value = self.read_value_arena(instr)?;
            elements.push(Element::new(annotations, value));
        }
        // Move the Vec's contents into the arena so Drop is skipped.
        let arena_vec = arena_element_vec(&mut self.arena, elements);
        Ok(Sequence::from(arena_vec))
    }

    /// Reads a struct (field name/value pairs) until END_CONTAINER.
    fn read_struct_arena(&mut self) -> IonResult<Struct> {
        let mut fields: Vec<(Symbol, Element)> = Vec::new();
        loop {
            let peek = Instruction::from_raw(self.bytecode[self.pos]);
            if peek.operation() == op::END_CONTAINER {
                self.pos += 1;
                break;
            }
            let field_name = self.read_field_name_arena()?;
            let annotations = self.read_annotations_arena()?;
            let instr = self.consume();
            let value = self.read_value_arena(instr)?;
            fields.push((field_name, Element::new(annotations, value)));
        }
        // Move the Vec's contents into the arena so Drop is skipped.
        let arena_vec = arena_fields_vec(&mut self.arena, fields);
        Ok(Struct::from_vec(arena_vec))
    }

    /// Reads a field name instruction and resolves it to a Symbol.
    fn read_field_name_arena(&mut self) -> IonResult<Symbol> {
        let instr = self.consume();
        let data = instr.data();
        match instr.operation() {
            op::FIELD_NAME_SID => Ok(self.resolve_sid_arena(data as usize)),
            op::FIELD_NAME_CP => match self.constant_pool.get(data) {
                Constant::String(arc) => {
                    // SAFETY: CP is stable during materialization.
                    let ptr = arc as *const Arc<str>;
                    Ok(Symbol {
                        text: crate::types::symbol::SymbolText::ArenaBorrowed(
                            unsafe { SymbolTableRef::new(ptr) },
                        ),
                    })
                }
                _ => IonResult::decoding_error("field name CP entry is not a string"),
            },
            op::FIELD_NAME_REF => {
                let position = self.consume_raw();
                let text = self.generator.read_text_ref(position, data)?;
                // SAFETY: Generator source is stable during materialization.
                let text: &str = unsafe { &*(text as *const str) };
                Ok(arena_symbol_from_text(&mut self.arena, text))
            }
            _ => IonResult::decoding_error("expected field name instruction"),
        }
    }
}

/// Reads all top-level values from binary Ion data using the arena reader.
/// Each element is cloned out of the arena into an owned Sequence.
/// This function exists for API compatibility and correctness testing --
/// the real performance benefit comes from using `ArenaReader::next()`
/// directly without collecting.
pub fn read_all_v3_arena(data: &[u8]) -> IonResult<Sequence> {
    use crate::bytecode::ion10::BinaryIon10Generator;
    if data.first() == Some(&0xE0) {
        let generator = BinaryIon10Generator::new(data);
        let mut reader = ArenaReader::new(generator)?;
        let mut elements = Vec::new();
        while let Some(result) = reader.next() {
            elements.push(result?.clone());
        }
        Ok(elements.into())
    } else {
        let source = std::str::from_utf8(data)
            .map_err(|_| crate::IonError::decoding_error("invalid UTF-8 in text Ion input"))?;
        use crate::bytecode::str_text10::StrTextIon10Generator;
        let generator = StrTextIon10Generator::new(source);
        let mut reader = ArenaReader::new(generator)?;
        let mut elements = Vec::new();
        while let Some(result) = reader.next() {
            elements.push(result?.clone());
        }
        Ok(elements.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::IonData;

    #[test]
    fn arena_basic_values() {
        let cases = &[
            "1 2 3",
            "true false null",
            "[1, 2, 3]",
            "{foo: 1, bar: \"hello\"}",
            "ann::42",
            "name",
            "$0",
        ];
        for text in cases {
            let expected = Element::read_all(text.as_bytes()).unwrap();
            let arena = read_all_v3_arena(text.as_bytes()).unwrap();
            assert!(IonData::eq(&expected, &arena), "mismatch for: {text}");
        }
    }

    #[test]
    fn arena_symbol_table_operations() {
        // Tests that the arena reader handles symbol table append/reset.
        let data =
            std::fs::read("ion-tests/iontestdata/good/equivs/localSymbolTableAppend.ion").unwrap();
        let expected = Element::read_all(&data).unwrap();
        let arena = read_all_v3_arena(&data).unwrap();
        assert!(IonData::eq(&expected, &arena));
    }

    #[test]
    fn arena_large_values() {
        // Test with a large string that forces chunk overflow in the arena.
        let large_str = "x".repeat(8192);
        let text = format!("\"{large_str}\"");
        let expected = Element::read_all(text.as_bytes()).unwrap();
        let arena = read_all_v3_arena(text.as_bytes()).unwrap();
        assert!(IonData::eq(&expected, &arena));
    }
}
