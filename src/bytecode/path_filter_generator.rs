//! Path-filtering bytecode generator for Ion 1.0 binary data.
//!
//! `PathFilterGenerator` parses Ion 1.0 binary data and selectively emits
//! bytecode only for values matching a registered set of path filters.
//! Non-matching values are skipped at the source level in O(1) via Ion 1.0
//! length prefixes.

use std::ops::Neg;
use std::sync::Arc;

use crate::bytecode::constant_pool::{Constant, ConstantPool};
use crate::bytecode::generator::BytecodeGenerator;
use crate::bytecode::instruction::instr;
#[allow(deprecated)]
use crate::bytecode::path_filter::{FilterFsm, PathFilter, PathQuery, Predicate};
use crate::result::IonFailure;
use crate::{Decimal, Int, IonResult, IonType, Timestamp, UInt};

// ─── Ion 1.0 constants (duplicated from ion10.rs) ─────────────────────

const IVM_BYTES: [u8; 4] = [0xE0, 0x01, 0x00, 0xEA];
const VARINT_STOP_BIT: u8 = 0x80;
const VARINT_SIGN_BIT: u8 = 0x40;
const VARINT_FIRST_BYTE_DATA_MASK: u8 = 0x3F;
const VARUINT_DATA_MASK: u8 = 0x7F;
const NULL_SENTINEL: usize = usize::MAX;

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

mod system_symbol {
    pub const ION_SYMBOL_TABLE: u32 = 3;
    pub const SYMBOLS: u32 = 7;
}

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

// ─── Generator ────────────────────────────────────────────────────────

/// A standalone bytecode generator that parses Ion 1.0 binary data and
/// selectively emits bytecode only for values matching a set of
/// registered path filters. Non-matching values are skipped at the source
/// level in O(1) via length prefixes.
pub struct PathFilterGenerator<S: AsRef<[u8]>> {
    source: S,
    position: usize,
    fsm: FilterFsm,
    /// Whether intermediate structs should be collapsed.
    flatten: bool,
    /// Resolved symbol table (built from LSTs).
    /// Maps SID-1 -> text (zero-indexed; SID 1 = index 0).
    symbols: Vec<Option<String>>,
}

impl<S: AsRef<[u8]>> PathFilterGenerator<S> {
    /// Create a new generator from v2 PathQuery types.
    pub fn new_v2(source: S, queries: &[PathQuery], flatten: bool) -> Self {
        let symbols = SYSTEM_SYMBOLS.iter().map(|s| Some(s.to_string())).collect();
        Self {
            source,
            position: 0,
            fsm: FilterFsm::compile(queries),
            flatten,
            symbols,
        }
    }

    /// Create a new generator from v1 PathFilter types (legacy API).
    #[allow(deprecated)]
    pub fn new(source: S, filters: &[PathFilter]) -> Self {
        let symbols = SYSTEM_SYMBOLS.iter().map(|s| Some(s.to_string())).collect();
        Self {
            source,
            position: 0,
            fsm: FilterFsm::compile_legacy(filters),
            flatten: false,
            symbols,
        }
    }

    // ─── Low-level parsing utilities ──────────────────────────────────

    #[inline(always)]
    fn source(&self) -> &[u8] {
        self.source.as_ref()
    }

    fn is_exhausted(&self) -> bool {
        self.position >= self.source().len()
    }

    fn read_var_uint(&mut self) -> usize {
        let mut result: usize = 0;
        loop {
            let byte = self.source()[self.position];
            self.position += 1;
            result = (result << 7) | (byte & VARUINT_DATA_MASK) as usize;
            if byte & VARINT_STOP_BIT != 0 {
                return result;
            }
        }
    }

    fn read_uint(&mut self, length: usize) -> u64 {
        let mut result: u64 = 0;
        for i in 0..length {
            result = (result << 8) | self.source()[self.position + i] as u64;
        }
        self.position += length;
        result
    }

    fn read_type_descriptor(&mut self) -> (u8, usize) {
        let td = self.source()[self.position];
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

    fn is_at_ivm(&self) -> bool {
        self.position + 4 <= self.source().len()
            && self.source()[self.position..self.position + 4] == IVM_BYTES
    }

    // ─── Symbol table resolution ─────────────────────────────────────

    /// Resolve a SID to field name text for FSM matching.
    fn resolve_sid(&self, sid: usize) -> Option<&str> {
        if sid == 0 {
            return None;
        }
        self.symbols.get(sid - 1).and_then(|opt| opt.as_deref())
    }

    // ─── Predicate evaluation ─────────────────────────────────────────

    /// Evaluate all predicates on the given FSM node against the current
    /// value's type code, null status, and annotations. Returns true if
    /// all predicates pass.
    fn check_predicates(
        &self,
        fsm_node: usize,
        tc: u8,
        length: usize,
        annotation_sids: &[u32],
    ) -> bool {
        let predicates = self.fsm.predicates(fsm_node);
        if predicates.is_empty() {
            return true;
        }

        for (predicate, negated) in predicates {
            let result = self.evaluate_predicate(predicate, tc, length, annotation_sids);
            if *negated {
                if result {
                    return false;
                }
            } else if !result {
                return false;
            }
        }
        true
    }

    /// Evaluate a single predicate against the given value metadata.
    fn evaluate_predicate(
        &self,
        predicate: &Predicate,
        tc: u8,
        length: usize,
        annotation_sids: &[u32],
    ) -> bool {
        match predicate {
            Predicate::Type(ion_type) => tc_matches_ion_type(tc, *ion_type),
            Predicate::IsNull => length == NULL_SENTINEL,
            Predicate::IsAnnotated => !annotation_sids.is_empty(),
            Predicate::HasAnnotation(text) => annotation_sids.iter().any(|&sid| {
                self.resolve_sid(sid as usize)
                    .map_or(false, |resolved| resolved == text)
            }),
        }
    }

    // ─── Value emission (full, unfiltered) ────────────────────────────

    /// Emits a complete value (scalar or container) without filtering.
    /// Used when the FSM has reached a terminal state.
    fn emit_value_full(&mut self, destination: &mut Vec<u32>, constant_pool: &mut ConstantPool) {
        let (tc, length) = self.read_type_descriptor();
        self.emit_value_body_full(tc, length, destination, constant_pool);
    }

    fn emit_value_body_full(
        &mut self,
        tc: u8,
        length: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) {
        if length == NULL_SENTINEL && tc <= type_code::STRUCT {
            self.emit_null(tc, destination);
            return;
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
            type_code::CLOB => self.emit_lob_ref(instr::CLOB_REF, length, destination),
            type_code::BLOB => self.emit_lob_ref(instr::BLOB_REF, length, destination),
            type_code::LIST => {
                self.emit_container_full(
                    instr::LIST_START,
                    length,
                    false,
                    destination,
                    constant_pool,
                );
            }
            type_code::SEXP => {
                self.emit_container_full(
                    instr::SEXP_START,
                    length,
                    false,
                    destination,
                    constant_pool,
                );
            }
            type_code::STRUCT => {
                self.emit_container_full(
                    instr::STRUCT_START,
                    length,
                    true,
                    destination,
                    constant_pool,
                );
            }
            type_code::ANNOTATION => {
                self.emit_annotation_wrapper_full(length, destination, constant_pool);
            }
            _ => {
                self.position += length;
            }
        }
    }

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

    fn emit_bool(&self, low_nibble: usize, destination: &mut Vec<u32>) {
        let value = if low_nibble == 0 { 0u32 } else { 1u32 };
        destination.push(instr::BOOL | value);
    }

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

    fn emit_big_int(
        &mut self,
        length: usize,
        is_negative: bool,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) {
        let bytes = &self.source()[self.position..self.position + length];
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

    fn emit_decimal(&mut self, length: usize, destination: &mut Vec<u32>) {
        if length == 0 {
            destination.push(instr::DECIMAL_REF);
            destination.push(self.position as u32);
            return;
        }
        let offset = self.position as u32;
        destination.push(instr::DECIMAL_REF | (length as u32 & 0x003F_FFFF));
        destination.push(offset);
        self.position += length;
    }

    fn emit_timestamp_ref(&mut self, length: usize, destination: &mut Vec<u32>) {
        let offset = self.position as u32;
        destination.push(instr::TIMESTAMP_REF | (length as u32 & 0x003F_FFFF));
        destination.push(offset);
        self.position += length;
    }

    fn emit_symbol(&mut self, length: usize, destination: &mut Vec<u32>) {
        if length == 0 {
            destination.push(instr::SYMBOL_SID);
            return;
        }
        let sid = self.read_uint(length) as u32;
        destination.push(instr::SYMBOL_SID | (sid & 0x003F_FFFF));
    }

    fn emit_string(&mut self, length: usize, destination: &mut Vec<u32>) {
        let offset = self.position as u32;
        destination.push(instr::STRING_REF | (length as u32 & 0x003F_FFFF));
        destination.push(offset);
        self.position += length;
    }

    fn emit_lob_ref(&mut self, instr_base: u32, length: usize, destination: &mut Vec<u32>) {
        let offset = self.position as u32;
        destination.push(instr_base | (length as u32 & 0x003F_FFFF));
        destination.push(offset);
        self.position += length;
    }

    fn emit_container_full(
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
                let peek_td = self.source()[self.position];
                let peek_tc = peek_td >> 4;
                let peek_low = peek_td & 0x0F;
                if peek_tc == type_code::NOP && peek_low != 0x0F {
                    let (_nop_tc, nop_length) = self.read_type_descriptor();
                    self.position += nop_length;
                    continue;
                }

                destination.push(instr::FIELD_NAME_SID | (field_sid & 0x003F_FFFF));
            }
            self.emit_value_full(destination, constant_pool);
        }

        destination.push(instr::END_CONTAINER);
        let bytecode_length = destination.len() - start_index - 1;
        destination[start_index] = start_instr | (bytecode_length as u32 & 0x003F_FFFF);
    }

    fn emit_annotation_wrapper_full(
        &mut self,
        wrapper_length: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) {
        let wrapper_end = self.position + wrapper_length;

        let annot_length = self.read_var_uint();
        let annot_end = self.position + annot_length;

        while self.position < annot_end {
            let sid = self.read_var_uint() as u32;
            destination.push(instr::ANNOTATION_SID | (sid & 0x003F_FFFF));
        }

        self.emit_value_full(destination, constant_pool);
        self.position = wrapper_end;
    }

    // ─── Filtered processing ──────────────────────────────────────────

    /// Process a top-level annotation wrapper with filtering.
    /// Returns `true` if this was a local symbol table.
    fn process_annotation_wrapper(
        &mut self,
        wrapper_length: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> bool {
        let wrapper_end = self.position + wrapper_length;

        // Read annotation SIDs
        let annot_length = self.read_var_uint();
        let annot_end = self.position + annot_length;

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
            let peek_td = self.source()[self.position];
            let peek_tc = peek_td >> 4;
            if peek_tc == type_code::STRUCT {
                self.parse_local_symbol_table(wrapper_end, destination);
                return true;
            }
        }

        // Not an LST — process as filtered annotated value.
        // Save rewind point (before annotations in bytecode).
        let rewind_point = destination.len();

        // Emit annotation SIDs
        for sid in &annotation_sids {
            destination.push(instr::ANNOTATION_SID | (*sid & 0x003F_FFFF));
        }

        // Now process the wrapped value with filtering at root FSM node.
        let emitted = self.process_value_filtered(0, &annotation_sids, destination, constant_pool);

        if !emitted {
            // Nothing matched — rewind annotations too.
            destination.truncate(rewind_point);
        }

        self.position = wrapper_end;
        false
    }

    /// Process a value with filtering. Returns `true` if any bytecode was
    /// emitted for this value (directly or for matched children).
    fn process_value_filtered(
        &mut self,
        fsm_node: usize,
        annotation_sids: &[u32],
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> bool {
        let (tc, length) = self.read_type_descriptor();

        // Handle nulls
        if length == NULL_SENTINEL && tc <= type_code::STRUCT {
            // A null at a terminal node: check predicates, then emit.
            if self.fsm.is_terminal(fsm_node) {
                if self.check_predicates(fsm_node, tc, length, annotation_sids) {
                    self.emit_null(tc, destination);
                    return true;
                }
            }
            return false;
        }

        // Handle annotation wrappers
        if tc == type_code::ANNOTATION {
            return self.process_annotation_value_filtered(
                fsm_node,
                length,
                destination,
                constant_pool,
            );
        }

        // Handle NOP
        if tc == type_code::NOP {
            self.position += length;
            return false;
        }

        // If the current node is terminal, check predicates and emit.
        if self.fsm.is_terminal(fsm_node) {
            if self.check_predicates(fsm_node, tc, length, annotation_sids) {
                self.emit_value_body_full(tc, length, destination, constant_pool);
                return true;
            }
            // Predicates failed — skip the value.
            self.position += length;
            return false;
        }

        // Non-terminal node: check leading predicates before
        // transitioning.
        if !self.check_predicates(fsm_node, tc, length, annotation_sids) {
            self.position += length;
            return false;
        }

        // If it's a scalar at a non-terminal node, no match.
        if !is_container(tc) {
            self.position += length;
            return false;
        }

        // Container at a non-terminal node — check if transitions exist.
        if !self.fsm.has_transitions(fsm_node) {
            self.position += length;
            return false;
        }

        // Step into the container and process children with filtering.
        self.process_container_filtered(fsm_node, tc, length, destination, constant_pool)
    }

    /// Process an annotated value at a filtered level.
    fn process_annotation_value_filtered(
        &mut self,
        fsm_node: usize,
        wrapper_length: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> bool {
        let wrapper_end = self.position + wrapper_length;

        // Read annotation SIDs
        let annot_length = self.read_var_uint();
        let annot_end = self.position + annot_length;

        let rewind_point = destination.len();

        let mut annotation_sids = Vec::new();
        while self.position < annot_end {
            let sid = self.read_var_uint() as u32;
            annotation_sids.push(sid);
        }

        // Emit annotations speculatively
        for sid in &annotation_sids {
            destination.push(instr::ANNOTATION_SID | (*sid & 0x003F_FFFF));
        }

        // Process the inner value at the same FSM node, passing
        // annotations for predicate evaluation.
        let emitted =
            self.process_value_filtered(fsm_node, &annotation_sids, destination, constant_pool);

        if !emitted {
            destination.truncate(rewind_point);
        }

        self.position = wrapper_end;
        emitted
    }

    /// Process a container's children with filtering. Emits the
    /// container start/end if any children match. Returns true if any
    /// children were emitted.
    fn process_container_filtered(
        &mut self,
        fsm_node: usize,
        tc: u8,
        content_length: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> bool {
        let is_struct = tc == type_code::STRUCT;
        let start_instr = match tc {
            type_code::STRUCT => instr::STRUCT_START,
            type_code::SEXP => instr::SEXP_START,
            _ => instr::LIST_START,
        };

        // Determine if this struct is "intermediate" for flatten purposes.
        // An intermediate struct is one navigated through but not terminal.
        // The top-level container (fsm_node == 0) is never suppressed.
        // For flatten=true, suppress intermediate struct containers.
        let suppress_container = self.flatten && is_struct && fsm_node != 0;

        // Record rewind point before container start
        let rewind_point = destination.len();
        let start_index = destination.len();
        if !suppress_container {
            destination.push(0); // placeholder for container start
        }

        let end_position = self.position + content_length;
        let mut child_index: usize = 0;
        let mut any_emitted = false;

        while self.position < end_position {
            if is_struct {
                let field_sid = self.read_var_uint() as u32;

                // Check for NOP padding
                let peek_td = self.source()[self.position];
                let peek_tc = peek_td >> 4;
                let peek_low = peek_td & 0x0F;
                if peek_tc == type_code::NOP && peek_low != 0x0F {
                    let (_nop_tc, nop_length) = self.read_type_descriptor();
                    self.position += nop_length;
                    continue;
                }

                // Attempt FSM transition on field name
                let child_node = self.transition_on_field(fsm_node, field_sid as usize);

                match child_node {
                    None => {
                        // No match — skip the value
                        self.skip_value();
                    }
                    Some(child) => {
                        // When flatten is active and the child is a
                        // non-terminal node with FIELD transitions, this
                        // child navigates through a struct (flattenable).
                        // Don't emit its field name (the child's children
                        // will emit their own field names directly).
                        // Only suppress for struct navigation (field
                        // transitions), not sequence navigation (index).
                        let child_is_intermediate = self.flatten
                            && !self.fsm.is_terminal(child)
                            && self.fsm.has_field_transitions(child);

                        let field_rewind = destination.len();
                        if !child_is_intermediate {
                            destination.push(instr::FIELD_NAME_SID | (field_sid & 0x003F_FFFF));
                        }

                        let emitted = self.process_value_filtered(
                            child,
                            &[], // no annotations known yet
                            destination,
                            constant_pool,
                        );
                        if emitted {
                            any_emitted = true;
                        } else {
                            // Rewind (field name if emitted, or nothing)
                            destination.truncate(field_rewind);
                        }
                    }
                }
            } else {
                // Sequence (list or sexp)
                let child_node = self.fsm.transition_index(fsm_node, child_index);

                match child_node {
                    None => {
                        self.skip_value();
                    }
                    Some(child) => {
                        let emitted = self.process_value_filtered(
                            child,
                            &[], // no annotations known yet
                            destination,
                            constant_pool,
                        );
                        if emitted {
                            any_emitted = true;
                        }
                    }
                }
                child_index += 1;
            }
        }

        if any_emitted {
            if !suppress_container {
                destination.push(instr::END_CONTAINER);
                let bytecode_length = destination.len() - start_index - 1;
                destination[start_index] = start_instr | (bytecode_length as u32 & 0x003F_FFFF);
            }
            true
        } else {
            // No children matched — rewind the container.
            destination.truncate(rewind_point);
            false
        }
    }

    /// Attempt an FSM transition on a struct field name. Tries text
    /// resolution first, then falls back to SID matching.
    fn transition_on_field(&self, fsm_node: usize, field_sid: usize) -> Option<usize> {
        // Try text-based matching first
        if let Some(text) = self.resolve_sid(field_sid) {
            if let Some(child) = self.fsm.transition_field(fsm_node, text) {
                return Some(child);
            }
        }
        // Try direct SID matching
        self.fsm.transition_sid(fsm_node, field_sid)
    }

    /// Skip a value in the source by reading its type descriptor and
    /// advancing past its content.
    fn skip_value(&mut self) {
        let (tc, length) = self.read_type_descriptor();
        if length == NULL_SENTINEL {
            return; // typed null — no body bytes
        }
        if tc == type_code::ANNOTATION {
            // Annotation wrapper — skip entire wrapper content
            self.position += length;
        } else {
            self.position += length;
        }
    }

    // ─── LST parsing ──────────────────────────────────────────────────

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
            } else if value_length != NULL_SENTINEL {
                self.position += value_length;
            }
        }

        // Update internal symbol table
        self.symbols = SYSTEM_SYMBOLS.iter().map(|s| Some(s.to_string())).collect();
        for entry in &new_symbols {
            match entry {
                Some((offset, length)) => {
                    let bytes = &self.source()[*offset..*offset + *length];
                    match std::str::from_utf8(bytes) {
                        Ok(text) => self.symbols.push(Some(text.to_owned())),
                        Err(_) => self.symbols.push(None),
                    }
                }
                None => self.symbols.push(None),
            }
        }

        // Emit the directive bytecode
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

/// Maps a binary type code to an IonType for predicate evaluation.
fn tc_matches_ion_type(tc: u8, ion_type: IonType) -> bool {
    match ion_type {
        IonType::Null => tc == type_code::NOP, // NOP with 0x0F is null.null
        IonType::Bool => tc == type_code::BOOL,
        IonType::Int => tc == type_code::POS_INT || tc == type_code::NEG_INT,
        IonType::Float => tc == type_code::FLOAT,
        IonType::Decimal => tc == type_code::DECIMAL,
        IonType::Timestamp => tc == type_code::TIMESTAMP,
        IonType::Symbol => tc == type_code::SYMBOL,
        IonType::String => tc == type_code::STRING,
        IonType::Clob => tc == type_code::CLOB,
        IonType::Blob => tc == type_code::BLOB,
        IonType::List => tc == type_code::LIST,
        IonType::SExp => tc == type_code::SEXP,
        IonType::Struct => tc == type_code::STRUCT,
    }
}

fn is_container(tc: u8) -> bool {
    matches!(tc, type_code::LIST | type_code::SEXP | type_code::STRUCT)
}

// ─── BytecodeGenerator impl ──────────────────────────────────────────

impl<S: AsRef<[u8]>> BytecodeGenerator for PathFilterGenerator<S> {
    fn refill(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        if self.is_exhausted() {
            destination.push(instr::END_OF_INPUT);
            return Ok(());
        }

        loop {
            if self.is_exhausted() {
                destination.push(instr::END_OF_INPUT);
                return Ok(());
            }

            // Check for IVM
            if self.is_at_ivm() {
                self.position += 4;
                let version_data = 1u32 << 8;
                destination.push(instr::IVM | version_data);

                // Reset symbol table on IVM
                self.symbols = SYSTEM_SYMBOLS.iter().map(|s| Some(s.to_string())).collect();

                destination.push(instr::REFILL);
                return Ok(());
            }

            // Peek for NOP
            let td = self.source()[self.position];
            let tc = td >> 4;
            let low = td & 0x0F;

            if tc == type_code::NOP && low != 0x0F {
                self.position += 1;
                if low == 0x0E {
                    let pad_len = self.read_var_uint();
                    self.position += pad_len;
                } else {
                    self.position += low as usize;
                }
                continue;
            }

            // Check for annotation wrapper (potential LST or filtered value)
            if tc == type_code::ANNOTATION {
                self.position += 1;
                let length = if low == 0x0E {
                    self.read_var_uint()
                } else {
                    low as usize
                };

                let is_lst = self.process_annotation_wrapper(length, destination, constant_pool);
                if is_lst {
                    destination.push(instr::REFILL);
                    return Ok(());
                }
                // If not LST and not matched, continue to next value.
                continue;
            }

            // Non-annotation top-level value — process with filtering at
            // root FSM node.
            self.process_value_filtered(0, &[], destination, constant_pool);
            // Continue processing more top-level values in the same refill
            // batch.
        }
    }

    fn read_int_ref(&self, position: u32, length: u32) -> IonResult<Int> {
        let start = position as usize;
        let end = start + length as usize;
        let bytes = &self.source()[start..end];
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
        if end > self.source().len() {
            return IonResult::decoding_error("decimal reference out of bounds");
        }
        let bytes = &self.source()[start..end];

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
        if end > self.source().len() {
            return IonResult::decoding_error("timestamp reference out of bounds");
        }
        let bytes = &self.source()[start..end];

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
            return if is_known_offset {
                builder.build_utc_fields_at_offset(offset_minutes)
            } else {
                builder.build()
            };
        }

        let second = read_var_uint_from_slice(bytes, &mut pos)?;
        let builder = builder.with_second(second);
        if pos >= bytes.len() {
            return if is_known_offset {
                builder.build_utc_fields_at_offset(offset_minutes)
            } else {
                builder.build()
            };
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
                        "timestamp fractional seconds coefficient must not be negative",
                    );
                }
            } else {
                Decimal::new(magnitude as i128, frac_exponent)
            }
        };

        let builder = builder.with_fractional_seconds(fractional_seconds);
        if is_known_offset {
            builder.build_utc_fields_at_offset(offset_minutes)
        } else {
            builder.build()
        }
    }

    fn read_text_ref(&self, position: u32, length: u32) -> IonResult<&str> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.source().len() {
            return IonResult::decoding_error("text reference out of bounds");
        }
        let bytes = &self.source()[start..end];
        std::str::from_utf8(bytes).map_err(|e| {
            crate::IonError::decoding_error(format!(
                "invalid UTF-8 in string at offset {position}: {e}"
            ))
        })
    }

    fn read_bytes_ref(&self, position: u32, length: u32) -> IonResult<&[u8]> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.source().len() {
            return IonResult::decoding_error("bytes reference out of bounds");
        }
        Ok(&self.source()[start..end])
    }
}

// ─── Shared helpers (duplicated from ion10.rs) ────────────────────────

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

// ─── Tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::materialize::BytecodeElementIterator;
    use crate::bytecode::path_filter::{PathQuerySet, Select, Step};
    use crate::lazy::encoding::Encoding;
    use crate::{v1_0, Element, IonResult, Sequence, Value};

    /// Helper: encodes Ion text as binary Ion 1.0.
    fn encode_as_binary(text: &str) -> Vec<u8> {
        let elements = Element::read_all(text).unwrap();
        v1_0::Binary::encode_all(elements.iter()).unwrap()
    }

    /// Helper: read all values from binary data through the path filter
    /// generator using v2 queries.
    fn read_filtered_v2(data: &[u8], queries: &[PathQuery], flatten: bool) -> IonResult<Sequence> {
        let generator = PathFilterGenerator::new_v2(data, queries, flatten);
        let mut iter = BytecodeElementIterator::new(generator)?;
        let mut elements = Vec::new();
        for result in &mut iter {
            elements.push(result?);
        }
        Ok(elements.into())
    }

    /// Helper: read all values using v1 API (for backwards compatibility
    /// tests).
    #[allow(deprecated)]
    fn read_filtered(data: &[u8], filters: &[PathFilter]) -> IonResult<Sequence> {
        let generator = PathFilterGenerator::new(data, filters);
        let mut iter = BytecodeElementIterator::new(generator)?;
        let mut elements = Vec::new();
        for result in &mut iter {
            elements.push(result?);
        }
        Ok(elements.into())
    }

    // ─── v1 backwards compatibility tests ─────────────────────────────

    #[allow(deprecated)]
    #[test]
    fn single_field_filter() -> IonResult<()> {
        let binary = encode_as_binary("{foo: 1, bar: 2}");
        let result = read_filtered(&binary, &[PathFilter::field("foo")])?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            assert_eq!(st.len(), 1);
            assert_eq!(st.get("foo").unwrap().value(), &Value::Int(1.into()));
            assert!(st.get("bar").is_none());
        } else {
            panic!("expected a struct, got {:?}", s.value());
        }
        Ok(())
    }

    #[allow(deprecated)]
    #[test]
    fn nested_path_filter() -> IonResult<()> {
        let binary = encode_as_binary("{foo: {bar: 1, baz: 2}}");
        let result = read_filtered(&binary, &[PathFilter::fields(&["foo", "bar"])])?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(outer) = s.value() {
            let foo_val = outer.get("foo").unwrap();
            if let Value::Struct(inner) = foo_val.value() {
                assert_eq!(inner.len(), 1);
                assert_eq!(inner.get("bar").unwrap().value(), &Value::Int(1.into()));
                assert!(inner.get("baz").is_none());
            } else {
                panic!("expected inner struct");
            }
        } else {
            panic!("expected outer struct");
        }
        Ok(())
    }

    #[allow(deprecated)]
    #[test]
    fn wildcard_filter() -> IonResult<()> {
        use crate::bytecode::path_filter::PathStep;
        let binary = encode_as_binary("{a: {name: 1}, b: {name: 2}}");
        let filters = [PathFilter::new(vec![
            PathStep::Wildcard,
            PathStep::Field("name".into()),
        ])];
        let result = read_filtered(&binary, &filters)?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(outer) = s.value() {
            let a = outer.get("a").unwrap();
            if let Value::Struct(inner) = a.value() {
                assert_eq!(inner.get("name").unwrap().value(), &Value::Int(1.into()));
            } else {
                panic!("expected inner struct for 'a'");
            }
            let b = outer.get("b").unwrap();
            if let Value::Struct(inner) = b.value() {
                assert_eq!(inner.get("name").unwrap().value(), &Value::Int(2.into()));
            } else {
                panic!("expected inner struct for 'b'");
            }
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[allow(deprecated)]
    #[test]
    fn index_filter() -> IonResult<()> {
        use crate::bytecode::path_filter::PathStep;
        let binary = encode_as_binary("{items: [10, 20, 30]}");
        let filters = [PathFilter::new(vec![
            PathStep::Field("items".into()),
            PathStep::Index(0),
        ])];
        let result = read_filtered(&binary, &filters)?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(outer) = s.value() {
            let items = outer.get("items").unwrap();
            if let Value::List(seq) = items.value() {
                assert_eq!(seq.len(), 1);
                assert_eq!(seq.get(0).unwrap().value(), &Value::Int(10.into()));
            } else {
                panic!("expected list");
            }
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[allow(deprecated)]
    #[test]
    fn multiple_registered_paths() -> IonResult<()> {
        let binary = encode_as_binary("{foo: 1, bar: 2, baz: 3}");
        let filters = [PathFilter::field("foo"), PathFilter::field("bar")];
        let result = read_filtered(&binary, &filters)?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            assert_eq!(st.len(), 2);
            assert_eq!(st.get("foo").unwrap().value(), &Value::Int(1.into()));
            assert_eq!(st.get("bar").unwrap().value(), &Value::Int(2.into()));
            assert!(st.get("baz").is_none());
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[allow(deprecated)]
    #[test]
    fn no_match_empty_result() -> IonResult<()> {
        let binary = encode_as_binary("{foo: 1}");
        let result = read_filtered(&binary, &[PathFilter::field("missing")])?;
        assert_eq!(result.len(), 0);
        Ok(())
    }

    #[allow(deprecated)]
    #[test]
    fn symbol_table_interaction() -> IonResult<()> {
        let binary = encode_as_binary("{custom_field: 42}");
        let result = read_filtered(&binary, &[PathFilter::field("custom_field")])?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            assert_eq!(
                st.get("custom_field").unwrap().value(),
                &Value::Int(42.into())
            );
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[allow(deprecated)]
    #[test]
    fn deep_nesting_with_skip() -> IonResult<()> {
        let binary = encode_as_binary("{a: 1, b: {deeply: {nested: {large: \"blob\"}}}}");
        let result = read_filtered(&binary, &[PathFilter::field("a")])?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            assert_eq!(st.len(), 1);
            assert_eq!(st.get("a").unwrap().value(), &Value::Int(1.into()));
            assert!(st.get("b").is_none());
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[allow(deprecated)]
    #[test]
    fn empty_container_rewind() -> IonResult<()> {
        let binary = encode_as_binary("{foo: {baz: 1}}");
        let result = read_filtered(&binary, &[PathFilter::fields(&["foo", "bar"])])?;
        assert_eq!(result.len(), 0);
        Ok(())
    }

    #[allow(deprecated)]
    #[test]
    fn top_level_scalar() -> IonResult<()> {
        let binary = encode_as_binary("42");
        let result = read_filtered(&binary, &[PathFilter::field("foo")])?;
        assert_eq!(result.len(), 0);
        Ok(())
    }

    #[allow(deprecated)]
    #[test]
    fn matched_container_value() -> IonResult<()> {
        let binary = encode_as_binary("{foo: [1, 2, 3]}");
        let result = read_filtered(&binary, &[PathFilter::field("foo")])?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            let foo = st.get("foo").unwrap();
            if let Value::List(seq) = foo.value() {
                assert_eq!(seq.len(), 3);
            } else {
                panic!("expected list");
            }
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[allow(deprecated)]
    #[test]
    fn duplicate_fields() -> IonResult<()> {
        let binary = encode_as_binary("{foo: 1, foo: 2}");
        let result = read_filtered(&binary, &[PathFilter::field("foo")])?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            let foo_values: Vec<_> = st.get_all("foo").collect();
            assert_eq!(foo_values.len(), 2);
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[allow(deprecated)]
    #[test]
    fn empty_input() -> IonResult<()> {
        let binary: Vec<u8> = vec![0xE0, 0x01, 0x00, 0xEA]; // just IVM
        let result = read_filtered(&binary, &[PathFilter::field("foo")])?;
        assert_eq!(result.len(), 0);
        Ok(())
    }

    // ─── v2 API tests ────────────────────────────────────────────────

    #[test]
    fn v2_single_field() -> IonResult<()> {
        let binary = encode_as_binary("{foo: 1, bar: 2}");
        let result = read_filtered_v2(&binary, &[PathQuery::field("foo")], false)?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            assert_eq!(st.len(), 1);
            assert_eq!(st.get("foo").unwrap().value(), &Value::Int(1.into()));
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[test]
    fn v2_all_matches_everything() -> IonResult<()> {
        let binary = encode_as_binary("1 \"hello\" true [1,2] {a:1}");
        let result = read_filtered_v2(&binary, &[PathQuery::all()], false)?;
        assert_eq!(result.len(), 5);
        Ok(())
    }

    #[test]
    fn v2_all_matches_top_level_scalars() -> IonResult<()> {
        let binary = encode_as_binary("42");
        let result = read_filtered_v2(&binary, &[PathQuery::all()], false)?;
        assert_eq!(result.len(), 1);
        assert_eq!(result.get(0).unwrap().value(), &Value::Int(42.into()));
        Ok(())
    }

    #[test]
    fn v2_type_predicate_int() -> IonResult<()> {
        let binary = encode_as_binary("{foo: 1, bar: \"hello\"}");
        let queries = [PathQuery::new(vec![
            Step::Select(Select::Field("foo".into())),
            Step::Match(Predicate::Type(IonType::Int)),
        ])];
        let result = read_filtered_v2(&binary, &queries, false)?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            assert_eq!(st.get("foo").unwrap().value(), &Value::Int(1.into()));
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[test]
    fn v2_type_predicate_rejects_wrong_type() -> IonResult<()> {
        let binary = encode_as_binary("{foo: \"hello\"}");
        let queries = [PathQuery::new(vec![
            Step::Select(Select::Field("foo".into())),
            Step::Match(Predicate::Type(IonType::Int)),
        ])];
        let result = read_filtered_v2(&binary, &queries, false)?;
        // No match since "hello" is a string, not an int
        assert_eq!(result.len(), 0);
        Ok(())
    }

    #[test]
    fn v2_not_match_is_null() -> IonResult<()> {
        let binary = encode_as_binary("{foo: null.int, bar: 1}");
        let queries = [PathQuery::new(vec![
            Step::Select(Select::AnyField),
            Step::NotMatch(Predicate::IsNull),
        ])];
        let result = read_filtered_v2(&binary, &queries, false)?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            assert_eq!(st.len(), 1);
            assert_eq!(st.get("bar").unwrap().value(), &Value::Int(1.into()));
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[test]
    fn v2_match_is_null() -> IonResult<()> {
        let binary = encode_as_binary("{foo: null.int, bar: 1}");
        let queries = [PathQuery::new(vec![
            Step::Select(Select::AnyField),
            Step::Match(Predicate::IsNull),
        ])];
        let result = read_filtered_v2(&binary, &queries, false)?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            assert_eq!(st.len(), 1);
            assert_eq!(st.get("foo").unwrap().value(), &Value::Null(IonType::Int));
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[test]
    fn v2_has_annotation_predicate() -> IonResult<()> {
        let binary = encode_as_binary("{foo: abc::1, bar: 2}");
        let queries = [PathQuery::new(vec![
            Step::Select(Select::AnyField),
            Step::Match(Predicate::HasAnnotation("abc".into())),
        ])];
        let result = read_filtered_v2(&binary, &queries, false)?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            assert_eq!(st.len(), 1);
            let foo = st.get("foo").unwrap();
            assert_eq!(foo.value(), &Value::Int(1.into()));
            let annotations: Vec<_> = foo.annotations().iter().collect();
            assert_eq!(annotations[0].text(), Some("abc"));
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[test]
    fn v2_is_annotated_predicate() -> IonResult<()> {
        let binary = encode_as_binary("abc::1 2 def::3");
        let queries = [PathQuery::new(vec![Step::Match(Predicate::IsAnnotated)])];
        let result = read_filtered_v2(&binary, &queries, false)?;

        assert_eq!(result.len(), 2);
        assert_eq!(result.get(0).unwrap().value(), &Value::Int(1.into()));
        assert_eq!(result.get(1).unwrap().value(), &Value::Int(3.into()));
        Ok(())
    }

    #[test]
    fn v2_not_match_is_annotated() -> IonResult<()> {
        let binary = encode_as_binary("abc::1 2 def::3");
        let queries = [PathQuery::new(vec![Step::NotMatch(Predicate::IsAnnotated)])];
        let result = read_filtered_v2(&binary, &queries, false)?;

        assert_eq!(result.len(), 1);
        assert_eq!(result.get(0).unwrap().value(), &Value::Int(2.into()));
        Ok(())
    }

    #[test]
    fn v2_any_index_selects_all_elements() -> IonResult<()> {
        let binary = encode_as_binary("{items: [10, 20, 30]}");
        let queries = [PathQuery::new(vec![
            Step::Select(Select::Field("items".into())),
            Step::Select(Select::AnyIndex),
        ])];
        let result = read_filtered_v2(&binary, &queries, false)?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            let items = st.get("items").unwrap();
            if let Value::List(seq) = items.value() {
                assert_eq!(seq.len(), 3);
                assert_eq!(seq.get(0).unwrap().value(), &Value::Int(10.into()));
                assert_eq!(seq.get(1).unwrap().value(), &Value::Int(20.into()));
                assert_eq!(seq.get(2).unwrap().value(), &Value::Int(30.into()));
            } else {
                panic!("expected list");
            }
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[test]
    fn v2_any_field_selects_all_struct_fields() -> IonResult<()> {
        let binary = encode_as_binary("{a: 1, b: 2, c: 3}");
        let queries = [PathQuery::new(vec![Step::Select(Select::AnyField)])];
        let result = read_filtered_v2(&binary, &queries, false)?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            assert_eq!(st.len(), 3);
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[test]
    fn v2_conjunction_predicates() -> IonResult<()> {
        let binary = encode_as_binary("{a: 1, b: null.int, c: \"hi\"}");
        let queries = [PathQuery::new(vec![
            Step::Select(Select::AnyField),
            Step::Match(Predicate::Type(IonType::Int)),
            Step::NotMatch(Predicate::IsNull),
        ])];
        let result = read_filtered_v2(&binary, &queries, false)?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            assert_eq!(st.len(), 1);
            assert_eq!(st.get("a").unwrap().value(), &Value::Int(1.into()));
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[test]
    fn v2_leading_predicate() -> IonResult<()> {
        // Leading predicate: only descend into annotated top-level values
        let binary = encode_as_binary("abc::{x: 1} {x: 2}");
        let queries = [PathQuery::new(vec![
            Step::Match(Predicate::HasAnnotation("abc".into())),
            Step::Select(Select::Field("x".into())),
        ])];
        let result = read_filtered_v2(&binary, &queries, false)?;

        // Only the first struct (annotated "abc") should produce a match
        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            assert_eq!(st.get("x").unwrap().value(), &Value::Int(1.into()));
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[test]
    fn v2_flatten_basic() -> IonResult<()> {
        let binary = encode_as_binary("{a: {b: 1, c: 2}}");
        let queries = [PathQuery::fields(&["a", "b"])];
        let result = read_filtered_v2(&binary, &queries, true)?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            // With flatten, intermediate struct 'a' is collapsed.
            // 'b: 1' is emitted directly.
            assert_eq!(st.len(), 1);
            assert_eq!(st.get("b").unwrap().value(), &Value::Int(1.into()));
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[test]
    fn v2_flatten_deep() -> IonResult<()> {
        let binary = encode_as_binary("{a: {b: {c: 42}}}");
        let queries = [PathQuery::fields(&["a", "b", "c"])];
        let result = read_filtered_v2(&binary, &queries, true)?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            assert_eq!(st.len(), 1);
            assert_eq!(st.get("c").unwrap().value(), &Value::Int(42.into()));
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[test]
    fn v2_flatten_no_intermediate() -> IonResult<()> {
        let binary = encode_as_binary("{foo: 99}");
        let queries = [PathQuery::field("foo")];
        let result_flat = read_filtered_v2(&binary, &queries, true)?;
        let result_noflat = read_filtered_v2(&binary, &queries, false)?;

        // No intermediate struct to collapse — output should be same
        assert_eq!(result_flat, result_noflat);
        Ok(())
    }

    #[test]
    fn v2_flatten_sequences_unchanged() -> IonResult<()> {
        let binary = encode_as_binary("{items: [1, 2, 3]}");
        let queries = [PathQuery::new(vec![
            Step::Select(Select::Field("items".into())),
            Step::Select(Select::AnyIndex),
        ])];
        let result_flat = read_filtered_v2(&binary, &queries, true)?;
        let result_noflat = read_filtered_v2(&binary, &queries, false)?;

        // Sequences cannot be flattened
        assert_eq!(result_flat, result_noflat);
        Ok(())
    }

    #[test]
    fn v2_flatten_multi_depth() -> IonResult<()> {
        let binary = encode_as_binary("{x: 1, a: {b: 2, c: {d: 3}}}");
        let queries = [
            PathQuery::field("x"),
            PathQuery::fields(&["a", "b"]),
            PathQuery::fields(&["a", "c", "d"]),
        ];
        let result = read_filtered_v2(&binary, &queries, true)?;

        assert_eq!(result.len(), 1);
        let s = result.get(0).unwrap();
        if let Value::Struct(st) = s.value() {
            // All terminal values placed directly in top-level struct
            assert_eq!(st.get("x").unwrap().value(), &Value::Int(1.into()));
            assert_eq!(st.get("b").unwrap().value(), &Value::Int(2.into()));
            assert_eq!(st.get("d").unwrap().value(), &Value::Int(3.into()));
        } else {
            panic!("expected struct");
        }
        Ok(())
    }

    #[test]
    fn v2_validation_errors() {
        // Select after scalar type predicate
        let result = PathQuerySet::compile(
            vec![PathQuery::new(vec![
                Step::Match(Predicate::Type(IonType::Int)),
                Step::Select(Select::Field("foo".into())),
            ])],
            false,
        );
        assert!(result.is_err());

        // Struct navigation after List type predicate
        let result = PathQuerySet::compile(
            vec![PathQuery::new(vec![
                Step::Match(Predicate::Type(IonType::List)),
                Step::Select(Select::Field("foo".into())),
            ])],
            false,
        );
        assert!(result.is_err());
    }

    #[test]
    fn v2_empty_query_set_matches_nothing() -> IonResult<()> {
        let binary = encode_as_binary("1 2 3");
        let result = read_filtered_v2(&binary, &[], false)?;
        assert_eq!(result.len(), 0);
        Ok(())
    }
}
