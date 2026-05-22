//! In-memory `&str` Ion 1.0 text bytecode generator.
//!
//! Optimized for in-memory text input that is already valid UTF-8.
//! Key advantages over the streaming generator:
//!
//! - **No scan phase** — single-pass parsing (entire input is available)
//! - **`memchr`-accelerated scanning** — uses `memchr`/`memchr2` for
//!   finding string boundaries and delimiters
//! - **Zero-cost `read_text_ref`** — returns `&self.source[start..end]`
//!   directly (source is guaranteed UTF-8, no validation needed)
//! - **No buffering overhead** — no `Vec<u8>` buffer, no `Read` trait,
//!   no incomplete-value handling

use std::sync::Arc;

use memchr::memchr;
use memchr::memchr2;

use crate::bytecode::constant_pool::{Constant, ConstantPool};
use crate::bytecode::generator::BytecodeGenerator;
use crate::bytecode::instruction::instr;
use crate::result::IonFailure;
use crate::{Decimal, Int, IonResult, Timestamp, UInt};

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

/// Result of parsing a symbol-like token (identifier or quoted symbol)
/// that may be a SID reference (`$N`) or a text symbol.
enum SymbolToken {
    /// A text symbol (regular identifier or quoted symbol).
    Text(Arc<str>),
    /// A SID reference (`$N` where N is all digits).
    Sid(u32),
}

/// A bytecode generator optimized for in-memory UTF-8 Ion 1.0 text.
///
/// Accepts `&str` input and exploits the UTF-8 guarantee to:
/// - Skip UTF-8 validation for STRING_REF/SYMBOL_REF
/// - Use SIMD-accelerated `memchr` for delimiter search
/// - Parse in a single pass (no scan phase)
pub struct StrTextIon10Generator<'a> {
    source: &'a str,
    position: usize,
    symbol_table: Vec<Option<Arc<str>>>,
    /// Whether we have already emitted all bytecode (and END_OF_INPUT).
    done: bool,
}

impl<'a> StrTextIon10Generator<'a> {
    /// Creates a new in-memory text generator from the given string.
    pub fn new(source: &'a str) -> Self {
        let symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
        Self {
            source,
            position: 0,
            symbol_table,
            done: false,
        }
    }

    /// Skips only whitespace characters (no comments). Returns true if there
    /// are remaining bytes, false if EOF. Used inside lob literals where
    /// `//` is valid base64 rather than a comment delimiter.
    fn skip_whitespace_only(&mut self) -> bool {
        let bytes = self.source.as_bytes();
        while self.position < bytes.len() {
            match bytes[self.position] {
                b' ' | b'\t' | b'\r' | b'\n' | b'\x0B' | b'\x0C' => self.position += 1,
                _ => return true,
            }
        }
        false
    }

    /// Skips whitespace and comments. Returns true if there is more
    /// content to parse.
    fn skip_whitespace_and_comments(&mut self) -> bool {
        let bytes = self.source.as_bytes();
        loop {
            if self.position >= bytes.len() {
                return false;
            }
            match bytes[self.position] {
                b' ' | b'\t' | b'\r' | b'\n' | b'\x0B' | b'\x0C' => {
                    self.position += 1;
                }
                b'/' => {
                    if self.position + 1 >= bytes.len() {
                        return true;
                    }
                    match bytes[self.position + 1] {
                        b'/' => {
                            // Line comment: use memchr2 to find \r or \n
                            self.position += 2;
                            let remaining = &bytes[self.position..];
                            match memchr2(b'\r', b'\n', remaining) {
                                Some(offset) => {
                                    self.position += offset + 1;
                                    // If we stopped at \r and next is \n, consume it too
                                    if remaining[offset] == b'\r'
                                        && self.position < bytes.len()
                                        && bytes[self.position] == b'\n'
                                    {
                                        self.position += 1;
                                    }
                                }
                                None => self.position = bytes.len(),
                            }
                        }
                        b'*' => {
                            // Block comment: find */
                            self.position += 2;
                            loop {
                                let remaining = &bytes[self.position..];
                                match memchr(b'*', remaining) {
                                    Some(offset) => {
                                        self.position += offset + 1;
                                        if self.position < bytes.len()
                                            && bytes[self.position] == b'/'
                                        {
                                            self.position += 1;
                                            break;
                                        }
                                    }
                                    None => {
                                        self.position = bytes.len();
                                        break;
                                    }
                                }
                            }
                        }
                        _ => return true,
                    }
                }
                _ => return true,
            }
        }
    }

    /// Emits all top-level values into the destination buffer.
    fn emit_all(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        loop {
            if !self.skip_whitespace_and_comments() {
                destination.push(instr::END_OF_INPUT);
                return Ok(());
            }
            self.emit_top_level_value(destination, constant_pool)?;
        }
    }

    /// Emits a top-level value (with possible IVM/LST detection).
    fn emit_top_level_value(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();

        // Collect annotations
        let mut annotations: Vec<SymbolToken> = Vec::new();
        loop {
            if !self.skip_whitespace_and_comments() {
                return IonResult::decoding_error("expected value after annotations");
            }
            if let Some((token, after_colons)) = self.try_parse_annotation()? {
                annotations.push(token);
                self.position = after_colons;
            } else {
                break;
            }
        }

        // Check for IVM: `$ion_1_0` at top-level with no annotations
        if annotations.is_empty() {
            let pos = self.position;
            if pos + 8 <= bytes.len() && &bytes[pos..pos + 8] == b"$ion_1_0" {
                let after = pos + 8;
                if after >= bytes.len() || is_value_terminator(bytes[after]) {
                    self.position = after;
                    let version_data = 1u32 << 8;
                    destination.push(instr::IVM | version_data);
                    // Reset symbol table
                    self.symbol_table =
                        SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
                    return Ok(());
                }
            }
        }

        // Check for LST: `$ion_symbol_table::{ ... }`
        if annotations.len() == 1
            && matches!(&annotations[0], SymbolToken::Text(t) if t.as_ref() == "$ion_symbol_table")
            && self.position < bytes.len()
            && bytes[self.position] == b'{'
        {
            self.parse_lst(destination, constant_pool)?;
            return Ok(());
        }

        // Emit annotations
        for ann in &annotations {
            match ann {
                SymbolToken::Text(text) => {
                    let idx = constant_pool.add(Constant::String(Arc::clone(text)));
                    destination.push(instr::ANNOTATION_CP | idx);
                }
                SymbolToken::Sid(sid) => {
                    destination.push(instr::ANNOTATION_SID | sid);
                }
            }
        }

        // Parse the value
        self.emit_value(destination, constant_pool)
    }

    /// Tries to parse an annotation at the current position.
    /// Returns `Some((token, position_after_colons))` if found.
    fn try_parse_annotation(&self) -> IonResult<Option<(SymbolToken, usize)>> {
        let bytes = self.source.as_bytes();
        let start = self.position;
        if start >= bytes.len() {
            return Ok(None);
        }
        let b = bytes[start];

        let (token, token_end) = if b == b'\'' {
            // Quoted symbol — but NOT long string (''')
            if start + 2 < bytes.len() && bytes[start + 1] == b'\'' && bytes[start + 2] == b'\'' {
                return Ok(None); // Long string, not annotation
            }
            let mut i = start + 1;
            let mut has_escapes = false;
            while i < bytes.len() && bytes[i] != b'\'' {
                if bytes[i] == b'\\' {
                    has_escapes = true;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            if i >= bytes.len() {
                return Ok(None);
            }
            let text_end = i;
            i += 1; // skip closing '
            let text = if has_escapes {
                let decoded = decode_escape_sequences(&bytes[start + 1..text_end])?;
                Arc::from(decoded.as_str())
            } else {
                Arc::from(&self.source[start + 1..text_end])
            };
            (SymbolToken::Text(text), i)
        } else if is_identifier_start(b) {
            let mut i = start + 1;
            while i < bytes.len() && is_identifier_continue(bytes[i]) {
                i += 1;
            }
            let text = &self.source[start..i];
            let token = if let Some(sid) = try_parse_sid_from_text(text) {
                SymbolToken::Sid(sid)
            } else {
                SymbolToken::Text(Arc::from(text))
            };
            (token, i)
        } else {
            return Ok(None);
        };

        // Check for :: after the token (with possible whitespace)
        let mut i = token_end;
        while i < bytes.len()
            && matches!(bytes[i], b' ' | b'\t' | b'\r' | b'\n' | b'\x0B' | b'\x0C')
        {
            i += 1;
        }
        if i + 1 < bytes.len() && bytes[i] == b':' && bytes[i + 1] == b':' {
            let mut after = i + 2;
            // Skip whitespace and comments after ::
            while after < bytes.len()
                && matches!(
                    bytes[after],
                    b' ' | b'\t' | b'\r' | b'\n' | b'\x0B' | b'\x0C'
                )
            {
                after += 1;
            }
            // Also skip comments after ::
            while after < bytes.len() && bytes[after] == b'/' {
                if after + 1 < bytes.len() && bytes[after + 1] == b'/' {
                    after += 2;
                    while after < bytes.len() && bytes[after] != b'\n' && bytes[after] != b'\r' {
                        after += 1;
                    }
                    if after < bytes.len() {
                        if bytes[after] == b'\r' {
                            after += 1;
                            if after < bytes.len() && bytes[after] == b'\n' {
                                after += 1;
                            }
                        } else {
                            after += 1;
                        }
                    }
                } else if after + 1 < bytes.len() && bytes[after + 1] == b'*' {
                    after += 2;
                    while after + 1 < bytes.len() {
                        if bytes[after] == b'*' && bytes[after + 1] == b'/' {
                            after += 2;
                            break;
                        }
                        after += 1;
                    }
                } else {
                    break;
                }
                while after < bytes.len()
                    && matches!(
                        bytes[after],
                        b' ' | b'\t' | b'\r' | b'\n' | b'\x0B' | b'\x0C'
                    )
                {
                    after += 1;
                }
            }
            Ok(Some((token, after)))
        } else {
            Ok(None)
        }
    }

    /// Emits bytecode for a value at the current position.
    fn emit_value(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        if self.position >= bytes.len() {
            return IonResult::decoding_error("expected value but found end of input");
        }

        let b = bytes[self.position];
        match b {
            b'n' => self.parse_null_or_identifier(destination, constant_pool),
            b't' => self.parse_true(destination, constant_pool),
            b'f' => self.parse_false(destination, constant_pool),
            b'"' => self.parse_string(destination, constant_pool),
            b'\'' => self.parse_quoted_symbol_or_long_string(destination, constant_pool),
            b'[' => self.parse_list(destination, constant_pool),
            b'(' => self.parse_sexp(destination, constant_pool),
            b'{' => self.parse_struct_or_lob(destination, constant_pool),
            b'+' | b'-' => self.parse_signed_number(destination, constant_pool),
            b'0'..=b'9' => self.parse_number(destination, constant_pool),
            _ if is_identifier_start(b) => self.parse_symbol_value(destination, constant_pool),
            _ => IonResult::decoding_error(format!(
                "unexpected character '{}' at position {}",
                b as char, self.position
            )),
        }
    }

    /// Emits an annotated value (annotations + value).
    fn emit_annotated_value(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        loop {
            if !self.skip_whitespace_and_comments() {
                return IonResult::decoding_error("expected value");
            }
            if let Some((token, after)) = self.try_parse_annotation()? {
                match token {
                    SymbolToken::Text(text) => {
                        let idx = constant_pool.add(Constant::String(text));
                        destination.push(instr::ANNOTATION_CP | idx);
                    }
                    SymbolToken::Sid(sid) => {
                        destination.push(instr::ANNOTATION_SID | sid);
                    }
                }
                self.position = after;
            } else {
                break;
            }
        }
        self.emit_value(destination, constant_pool)
    }

    // ─── Scalar Parsing ──────────────────────────────────────────────

    fn parse_null_or_identifier(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        let start = self.position;
        let mut i = start;
        while i < bytes.len() && is_identifier_continue(bytes[i]) {
            i += 1;
        }
        let word = &bytes[start..i];

        if word == b"null" {
            // Check for null.type
            if i < bytes.len() && bytes[i] == b'.' {
                i += 1;
                let type_start = i;
                while i < bytes.len() && is_identifier_continue(bytes[i]) {
                    i += 1;
                }
                let type_name = &bytes[type_start..i];
                self.position = i;
                let null_instr = match type_name {
                    b"null" => instr::NULL_NULL,
                    b"bool" => instr::NULL_BOOL,
                    b"int" => instr::NULL_INT,
                    b"float" => instr::NULL_FLOAT,
                    b"decimal" => instr::NULL_DECIMAL,
                    b"timestamp" => instr::NULL_TIMESTAMP,
                    b"symbol" => instr::NULL_SYMBOL,
                    b"string" => instr::NULL_STRING,
                    b"clob" => instr::NULL_CLOB,
                    b"blob" => instr::NULL_BLOB,
                    b"list" => instr::NULL_LIST,
                    b"sexp" => instr::NULL_SEXP,
                    b"struct" => instr::NULL_STRUCT,
                    _ => {
                        return IonResult::decoding_error(format!(
                            "unknown null type: null.{}",
                            String::from_utf8_lossy(type_name)
                        ));
                    }
                };
                destination.push(null_instr);
                return Ok(());
            }
            self.position = i;
            destination.push(instr::NULL_NULL);
            Ok(())
        } else if word == b"nan" {
            self.position = i;
            let bits = f64::NAN.to_bits();
            destination.push(instr::FLOAT_F64);
            destination.push((bits >> 32) as u32);
            destination.push(bits as u32);
            Ok(())
        } else {
            // It's an identifier (symbol value)
            self.position = i;
            let text = &self.source[start..i];
            let idx = constant_pool.add(Constant::String(Arc::from(text)));
            destination.push(instr::SYMBOL_CP | idx);
            Ok(())
        }
    }

    fn parse_true(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        let start = self.position;
        let mut i = start;
        while i < bytes.len() && is_identifier_continue(bytes[i]) {
            i += 1;
        }
        let word = &bytes[start..i];
        if word == b"true" {
            self.position = i;
            destination.push(instr::BOOL | 1);
            Ok(())
        } else {
            self.parse_symbol_value(destination, constant_pool)
        }
    }

    fn parse_false(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        let start = self.position;
        let mut i = start;
        while i < bytes.len() && is_identifier_continue(bytes[i]) {
            i += 1;
        }
        let word = &bytes[start..i];
        if word == b"false" {
            self.position = i;
            destination.push(instr::BOOL);
            Ok(())
        } else {
            self.parse_symbol_value(destination, constant_pool)
        }
    }

    fn parse_symbol_value(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        let start = self.position;
        let mut i = start;
        while i < bytes.len() && is_identifier_continue(bytes[i]) {
            i += 1;
        }
        self.position = i;
        let text = &self.source[start..i];
        if let Some(sid) = try_parse_sid_from_text(text) {
            destination.push(instr::SYMBOL_SID | sid);
        } else {
            let idx = constant_pool.add(Constant::String(Arc::from(text)));
            destination.push(instr::SYMBOL_CP | idx);
        }
        Ok(())
    }

    /// Parses a short string using memchr2 for fast delimiter finding.
    fn parse_string(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        let start = self.position + 1; // skip opening "

        // Use memchr2 to find either closing " or first escape \
        let search_slice = &bytes[start..];
        match memchr2(b'"', b'\\', search_slice) {
            Some(offset) => {
                if search_slice[offset] == b'"' {
                    // No escapes — check for \r that needs normalization
                    let content_end = start + offset;
                    if memchr(b'\r', &bytes[start..content_end]).is_some() {
                        // Contains \r — must normalize through CP path
                        self.parse_string_with_escapes(start, destination, constant_pool)
                    } else {
                        // No escapes, no \r — fast path: emit STRING_REF
                        self.position = content_end + 1; // skip closing "
                        let length = offset as u32;
                        destination.push(instr::STRING_REF | (length & 0x003F_FFFF));
                        destination.push(start as u32);
                        Ok(())
                    }
                } else {
                    // Has escapes — decode to CP
                    self.parse_string_with_escapes(start, destination, constant_pool)
                }
            }
            None => IonResult::decoding_error("unterminated string"),
        }
    }

    /// Handles a string that contains escape sequences or CR characters
    /// that need normalization.
    fn parse_string_with_escapes(
        &mut self,
        start: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        let mut i = start;
        while i < bytes.len() {
            match bytes[i] {
                b'"' => break,
                b'\\' => i += 2,
                _ => i += 1,
            }
        }
        if i >= bytes.len() {
            return IonResult::decoding_error("unterminated string");
        }
        let content_end = i;
        self.position = i + 1; // skip closing "

        let decoded = decode_string_content(&bytes[start..content_end])?;
        let idx = constant_pool.add(Constant::String(Arc::from(decoded.as_str())));
        destination.push(instr::STRING_CP | idx);
        Ok(())
    }

    fn parse_quoted_symbol_or_long_string(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        if self.position + 2 < bytes.len()
            && bytes[self.position + 1] == b'\''
            && bytes[self.position + 2] == b'\''
        {
            // Long string
            self.parse_long_string(destination, constant_pool)
        } else {
            // Quoted symbol
            let start = self.position + 1; // skip opening '
            let search_slice = &bytes[start..];
            match memchr2(b'\'', b'\\', search_slice) {
                Some(offset) => {
                    if search_slice[offset] == b'\'' {
                        // No escapes
                        let content_end = start + offset;
                        self.position = content_end + 1;
                        let text = &self.source[start..content_end];
                        let idx = constant_pool.add(Constant::String(Arc::from(text)));
                        destination.push(instr::SYMBOL_CP | idx);
                        Ok(())
                    } else {
                        // Has escapes
                        let mut i = start;
                        while i < bytes.len() && bytes[i] != b'\'' {
                            if bytes[i] == b'\\' {
                                i += 2;
                            } else {
                                i += 1;
                            }
                        }
                        if i >= bytes.len() {
                            return IonResult::decoding_error("unterminated quoted symbol");
                        }
                        let content_end = i;
                        self.position = i + 1;
                        let decoded = decode_escape_sequences(&bytes[start..content_end])?;
                        let idx = constant_pool.add(Constant::String(Arc::from(decoded.as_str())));
                        destination.push(instr::SYMBOL_CP | idx);
                        Ok(())
                    }
                }
                None => IonResult::decoding_error("unterminated quoted symbol"),
            }
        }
    }

    fn parse_long_string(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        let mut result = String::new();
        loop {
            // Expect ''' at self.position
            if self.position + 2 >= bytes.len()
                || bytes[self.position] != b'\''
                || bytes[self.position + 1] != b'\''
                || bytes[self.position + 2] != b'\''
            {
                break;
            }
            self.position += 3; // skip '''
            let seg_start = self.position;
            let mut i = seg_start;
            while i + 2 < bytes.len() {
                if bytes[i] == b'\'' && bytes[i + 1] == b'\'' && bytes[i + 2] == b'\'' {
                    break;
                }
                if bytes[i] == b'\\' {
                    i += 2;
                } else {
                    i += 1;
                }
            }
            let seg_end = i;
            self.position = i + 3; // skip closing '''

            let segment = &bytes[seg_start..seg_end];
            if segment.contains(&b'\\') || segment.contains(&b'\r') {
                result.push_str(&decode_string_content(segment)?);
            } else {
                result.push_str(&self.source[seg_start..seg_end]);
            }

            // Skip whitespace/comments between segments, check for another '''
            let saved = self.position;
            if !self.skip_whitespace_and_comments() {
                break;
            }
            if self.position + 2 < bytes.len()
                && bytes[self.position] == b'\''
                && bytes[self.position + 1] == b'\''
                && bytes[self.position + 2] == b'\''
            {
                // Another segment follows
            } else {
                self.position = saved;
                self.skip_whitespace_and_comments();
                break;
            }
        }

        let idx = constant_pool.add(Constant::String(Arc::from(result.as_str())));
        destination.push(instr::STRING_CP | idx);
        Ok(())
    }

    /// Parses a triple-quoted string (`'''...'''`) and returns its content.
    /// Used for field names in triple-quoted form.
    fn parse_long_string_content(&mut self) -> IonResult<String> {
        let bytes = self.source.as_bytes();
        let mut result = String::new();
        loop {
            // Expect ''' at self.position
            if self.position + 2 >= bytes.len()
                || bytes[self.position] != b'\''
                || bytes[self.position + 1] != b'\''
                || bytes[self.position + 2] != b'\''
            {
                break;
            }
            self.position += 3; // skip '''
            let seg_start = self.position;
            let mut i = seg_start;
            while i + 2 < bytes.len() {
                if bytes[i] == b'\'' && bytes[i + 1] == b'\'' && bytes[i + 2] == b'\'' {
                    break;
                }
                if bytes[i] == b'\\' {
                    i += 2;
                } else {
                    i += 1;
                }
            }
            let seg_end = i;
            self.position = i + 3; // skip closing '''

            let segment = &bytes[seg_start..seg_end];
            if segment.contains(&b'\\') || segment.contains(&b'\r') {
                result.push_str(&decode_string_content(segment)?);
            } else {
                result.push_str(&self.source[seg_start..seg_end]);
            }

            // Skip whitespace/comments between segments, check for another '''
            let saved = self.position;
            if !self.skip_whitespace_and_comments() {
                break;
            }
            if self.position + 2 < bytes.len()
                && bytes[self.position] == b'\''
                && bytes[self.position + 1] == b'\''
                && bytes[self.position + 2] == b'\''
            {
                // Another segment follows
            } else {
                self.position = saved;
                self.skip_whitespace_and_comments();
                break;
            }
        }
        Ok(result)
    }

    // ─── Number Parsing ──────────────────────────────────────────────

    fn parse_signed_number(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        let sign_byte = bytes[self.position];

        // Check for +inf / -inf
        if self.position + 4 <= bytes.len() {
            let candidate = &bytes[self.position..self.position + 4];
            if candidate == b"+inf" || candidate == b"-inf" {
                let after = self.position + 4;
                if after >= bytes.len() || is_value_terminator(bytes[after]) {
                    let value = if sign_byte == b'+' {
                        f64::INFINITY
                    } else {
                        f64::NEG_INFINITY
                    };
                    self.position = after;
                    let bits = value.to_bits();
                    destination.push(instr::FLOAT_F64);
                    destination.push((bits >> 32) as u32);
                    destination.push(bits as u32);
                    return Ok(());
                }
            }
        }

        self.position += 1; // skip sign
        let is_negative = sign_byte == b'-';
        self.parse_number_with_sign(is_negative, destination, constant_pool)
    }

    fn parse_number(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        self.parse_number_with_sign(false, destination, constant_pool)
    }

    fn parse_number_with_sign(
        &mut self,
        is_negative: bool,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        let start = self.position;

        // Check for 0x (hex) or 0b (binary) prefix
        if start + 1 < bytes.len() && bytes[start] == b'0' {
            match bytes[start + 1] {
                b'x' | b'X' => return self.parse_hex_int(is_negative, destination, constant_pool),
                b'b' | b'B' => {
                    return self.parse_binary_int(is_negative, destination, constant_pool)
                }
                _ => {}
            }
        }

        // Scan to determine type: integer, float, decimal, or timestamp
        let mut i = start;
        let mut has_dot = false;
        let mut has_exp = false;
        let mut has_d_exp = false;
        let mut has_dash_after_4digits = false;
        let mut has_t = false;

        // Count initial digits
        let mut digit_count = 0;
        while i < bytes.len() && (bytes[i].is_ascii_digit() || bytes[i] == b'_') {
            if bytes[i] != b'_' {
                digit_count += 1;
            }
            i += 1;
        }

        if i < bytes.len() {
            match bytes[i] {
                b'.' => {
                    has_dot = true;
                    i += 1;
                    while i < bytes.len() && (bytes[i].is_ascii_digit() || bytes[i] == b'_') {
                        i += 1;
                    }
                    if i < bytes.len() {
                        match bytes[i] {
                            b'e' | b'E' => {
                                has_exp = true;
                                i += 1;
                                if i < bytes.len() && (bytes[i] == b'+' || bytes[i] == b'-') {
                                    i += 1;
                                }
                                while i < bytes.len() && bytes[i].is_ascii_digit() {
                                    i += 1;
                                }
                            }
                            b'd' | b'D' => {
                                has_d_exp = true;
                                i += 1;
                                if i < bytes.len() && (bytes[i] == b'+' || bytes[i] == b'-') {
                                    i += 1;
                                }
                                while i < bytes.len() && bytes[i].is_ascii_digit() {
                                    i += 1;
                                }
                            }
                            _ => {}
                        }
                    }
                }
                b'e' | b'E' => {
                    has_exp = true;
                    i += 1;
                    if i < bytes.len() && (bytes[i] == b'+' || bytes[i] == b'-') {
                        i += 1;
                    }
                    while i < bytes.len() && bytes[i].is_ascii_digit() {
                        i += 1;
                    }
                }
                b'd' | b'D' => {
                    has_d_exp = true;
                    i += 1;
                    if i < bytes.len() && (bytes[i] == b'+' || bytes[i] == b'-') {
                        i += 1;
                    }
                    while i < bytes.len() && bytes[i].is_ascii_digit() {
                        i += 1;
                    }
                }
                b'-' if digit_count == 4 => {
                    has_dash_after_4digits = true;
                }
                b'T' if digit_count == 4 => {
                    has_t = true;
                }
                _ => {}
            }
        }

        // Determine if this is a timestamp
        if has_dash_after_4digits || has_t {
            let ts_end = self.scan_timestamp_end(start);
            self.position = ts_end;
            // Parse directly from source bytes without allocation
            let ts_bytes = self.source[start..ts_end].as_bytes();
            let ts = parse_timestamp_direct(ts_bytes)?;
            let idx = constant_pool.add(Constant::Timestamp(Arc::new(ts)));
            destination.push(instr::TIMESTAMP_CP | idx);
            return Ok(());
        }

        self.position = i;

        if has_exp {
            // Float
            let slice = &self.source[start..i];
            if !slice.contains('_') {
                // Fast path: parse directly without allocation
                let value: f64 = if is_negative {
                    // Negative floats: the sign was already consumed, so we
                    // need to negate the parsed positive value.
                    let positive: f64 = slice.parse().map_err(|e| {
                        crate::IonError::decoding_error(format!("invalid float: {e}"))
                    })?;
                    -positive
                } else {
                    slice.parse().map_err(|e| {
                        crate::IonError::decoding_error(format!("invalid float: {e}"))
                    })?
                };
                let bits = value.to_bits();
                destination.push(instr::FLOAT_F64);
                destination.push((bits >> 32) as u32);
                destination.push(bits as u32);
            } else {
                let text = self.collect_number_text(start, i, is_negative);
                let value: f64 = text
                    .parse()
                    .map_err(|e| crate::IonError::decoding_error(format!("invalid float: {e}")))?;
                let bits = value.to_bits();
                destination.push(instr::FLOAT_F64);
                destination.push((bits >> 32) as u32);
                destination.push(bits as u32);
            }
        } else if has_dot || has_d_exp {
            // Decimal
            let slice = &self.source[start..i];
            if !slice.contains('_') {
                // Fast path: parse directly without allocation
                let dec = if is_negative {
                    let mut buf = String::with_capacity(slice.len() + 1);
                    buf.push('-');
                    buf.push_str(slice);
                    parse_text_decimal(&buf)?
                } else {
                    parse_text_decimal(slice)?
                };
                let idx = constant_pool.add(Constant::Decimal(Arc::new(dec)));
                destination.push(instr::DECIMAL_CP | idx);
            } else {
                let text = self.collect_number_text(start, i, is_negative);
                let dec = parse_text_decimal(&text)?;
                let idx = constant_pool.add(Constant::Decimal(Arc::new(dec)));
                destination.push(instr::DECIMAL_CP | idx);
            }
        } else {
            // Integer — try direct parse fast path
            let slice = &self.source[start..i];
            if !slice.contains('_') {
                // Fast path: no underscores, parse directly without allocation
                self.emit_int_from_slice(slice, is_negative, destination, constant_pool)?;
            } else {
                let text = self.collect_number_text(start, i, is_negative);
                self.emit_parsed_int(&text, destination, constant_pool)?;
            }
        }
        Ok(())
    }

    fn scan_timestamp_end(&self, start: usize) -> usize {
        let bytes = self.source.as_bytes();
        let mut i = start;
        while i < bytes.len() {
            match bytes[i] {
                b'0'..=b'9' | b'-' | b'+' | b':' | b'.' | b'T' | b'Z' | b't' | b'z' => {
                    i += 1;
                }
                _ => break,
            }
        }
        i
    }

    fn collect_number_text(&self, start: usize, end: usize, is_negative: bool) -> String {
        let raw = &self.source.as_bytes()[start..end];
        let mut text = String::with_capacity(raw.len() + 1);
        if is_negative {
            text.push('-');
        }
        for &b in raw {
            if b != b'_' {
                text.push(b as char);
            }
        }
        text
    }

    fn parse_hex_int(
        &mut self,
        is_negative: bool,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        self.position += 2; // skip 0x
        let start = self.position;
        while self.position < bytes.len()
            && (bytes[self.position].is_ascii_hexdigit() || bytes[self.position] == b'_')
        {
            self.position += 1;
        }
        let hex_slice = &bytes[start..self.position];
        let mut text = String::with_capacity(hex_slice.len() + 3);
        if is_negative {
            text.push('-');
        }
        text.push_str("0x");
        for &b in hex_slice {
            if b != b'_' {
                text.push(b as char);
            }
        }
        self.emit_parsed_int(&text, destination, constant_pool)
    }

    fn parse_binary_int(
        &mut self,
        is_negative: bool,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        self.position += 2; // skip 0b
        let start = self.position;
        while self.position < bytes.len()
            && (bytes[self.position] == b'0'
                || bytes[self.position] == b'1'
                || bytes[self.position] == b'_')
        {
            self.position += 1;
        }
        let bin_slice = &bytes[start..self.position];
        let mut magnitude: u128 = 0;
        for &b in bin_slice {
            if b != b'_' {
                magnitude = magnitude
                    .checked_shl(1)
                    .ok_or_else(|| crate::IonError::decoding_error("binary integer overflow"))?
                    | (b - b'0') as u128;
            }
        }
        let value: i128 = if is_negative {
            -(magnitude as i128)
        } else {
            magnitude as i128
        };
        emit_i128_int(value, destination, constant_pool);
        Ok(())
    }

    /// Emits an integer from a `&str` slice (no underscores) and a sign flag,
    /// avoiding String allocation by parsing directly.
    fn emit_int_from_slice(
        &self,
        slice: &str,
        is_negative: bool,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        // Try to parse as i64 using manual accumulation to avoid allocation
        if let Some(v) = parse_i64_no_alloc(slice, is_negative) {
            emit_i64_int(v, destination);
            return Ok(());
        }
        // Fallback: need to build a string for i128/BigInt parsing
        let text = if is_negative {
            let mut s = String::with_capacity(slice.len() + 1);
            s.push('-');
            s.push_str(slice);
            s
        } else {
            slice.to_string()
        };
        self.emit_parsed_int(&text, destination, constant_pool)
    }

    fn emit_parsed_int(
        &self,
        text: &str,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        if let Ok(v) = text.parse::<i64>() {
            emit_i64_int(v, destination);
            return Ok(());
        }
        if let Ok(v) = parse_i128(text) {
            emit_i128_int(v, destination, constant_pool);
            return Ok(());
        }
        // Arbitrary-precision fallback for integers exceeding i128
        let big_int = parse_big_int(text)?;
        let idx = constant_pool.add(Constant::BigInt(Arc::new(big_int)));
        destination.push(instr::INT_CP | idx);
        Ok(())
    }

    // ─── Container Parsing ───────────────────────────────────────────

    fn parse_list(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        self.position += 1; // skip '['
        let start_index = destination.len();
        destination.push(0); // placeholder for LIST_START

        loop {
            if !self.skip_whitespace_and_comments() {
                return IonResult::decoding_error("unterminated list");
            }
            if bytes[self.position] == b']' {
                self.position += 1;
                break;
            }
            if bytes[self.position] == b',' {
                self.position += 1;
                continue;
            }
            self.emit_annotated_value(destination, constant_pool)?;
        }

        destination.push(instr::END_CONTAINER);
        let bytecode_length = destination.len() - start_index - 1;
        destination[start_index] = instr::LIST_START | (bytecode_length as u32 & 0x003F_FFFF);
        Ok(())
    }

    fn parse_sexp(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        self.position += 1; // skip '('
        let start_index = destination.len();
        destination.push(0); // placeholder for SEXP_START

        loop {
            if !self.skip_whitespace_and_comments() {
                return IonResult::decoding_error("unterminated sexp");
            }
            if bytes[self.position] == b')' {
                self.position += 1;
                break;
            }
            self.emit_sexp_annotated_value(destination, constant_pool)?;
        }

        destination.push(instr::END_CONTAINER);
        let bytecode_length = destination.len() - start_index - 1;
        destination[start_index] = instr::SEXP_START | (bytecode_length as u32 & 0x003F_FFFF);
        Ok(())
    }

    /// Emits an annotated value within an s-expression context.
    /// After handling annotations, tries normal value parsing first;
    /// if the current byte is an operator character that doesn't start
    /// a number, parses it as an operator symbol.
    fn emit_sexp_annotated_value(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        // Handle annotations (same logic as emit_annotated_value)
        loop {
            if !self.skip_whitespace_and_comments() {
                return IonResult::decoding_error("expected value");
            }
            if let Some((token, after)) = self.try_parse_annotation()? {
                match token {
                    SymbolToken::Text(text) => {
                        let idx = constant_pool.add(Constant::String(text));
                        destination.push(instr::ANNOTATION_CP | idx);
                    }
                    SymbolToken::Sid(sid) => {
                        destination.push(instr::ANNOTATION_SID | sid);
                    }
                }
                self.position = after;
            } else {
                break;
            }
        }
        self.emit_sexp_value(destination, constant_pool)
    }

    /// Emits a value in s-expression context. Tries normal value parsing
    /// first; falls back to operator symbol parsing for operator characters.
    ///
    /// Ion rules for sign characters in s-expressions:
    /// - `-` followed by a digit -> negative number (e.g., `-3` is int -3)
    /// - `-` followed by `i` -> `-inf` (negative infinity float)
    /// - `+` followed by `i` -> `+inf` (positive infinity float)
    /// - `+` followed by a digit -> operator `+` then int (e.g., `+1` is symbol `+`, int 1)
    /// - Any sign not followed by digit/`i` -> operator symbol
    fn emit_sexp_value(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        if self.position >= bytes.len() {
            return IonResult::decoding_error("expected value but found end of input");
        }

        let b = bytes[self.position];

        if is_operator_char(b) {
            if b == b'-' {
                let next_pos = self.position + 1;
                if next_pos < bytes.len() {
                    let next = bytes[next_pos];
                    if next.is_ascii_digit() || next == b'i' {
                        // `-3` is negative int, `-inf` is negative infinity
                        return self.emit_value(destination, constant_pool);
                    }
                }
            } else if b == b'+' {
                let next_pos = self.position + 1;
                if next_pos < bytes.len() && bytes[next_pos] == b'i' {
                    // `+inf` is positive infinity
                    return self.emit_value(destination, constant_pool);
                }
            }
            // All other operator chars, or sign not followed by valid number start
            return self.parse_operator_symbol(destination, constant_pool);
        }

        self.emit_value(destination, constant_pool)
    }

    /// Parses an operator symbol (one or more operator characters) and emits
    /// a SYMBOL_CP instruction.
    fn parse_operator_symbol(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        let start = self.position;
        while self.position < bytes.len() && is_operator_char(bytes[self.position]) {
            self.position += 1;
        }
        let text = &self.source[start..self.position];
        let idx = constant_pool.add(Constant::String(Arc::from(text)));
        destination.push(instr::SYMBOL_CP | idx);
        Ok(())
    }

    fn parse_struct_or_lob(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        if self.position + 1 < bytes.len() && bytes[self.position + 1] == b'{' {
            return self.parse_lob(destination, constant_pool);
        }
        self.parse_struct(destination, constant_pool)
    }

    fn parse_struct(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        self.position += 1; // skip '{'
        let start_index = destination.len();
        destination.push(0); // placeholder for STRUCT_START

        loop {
            if !self.skip_whitespace_and_comments() {
                return IonResult::decoding_error("unterminated struct");
            }
            if bytes[self.position] == b'}' {
                self.position += 1;
                break;
            }
            if bytes[self.position] == b',' {
                self.position += 1;
                continue;
            }

            // Parse and emit field name instruction
            self.emit_field_name(destination, constant_pool)?;

            // Skip colon
            if !self.skip_whitespace_and_comments() {
                return IonResult::decoding_error("expected ':' after field name");
            }
            if self.position >= bytes.len() || bytes[self.position] != b':' {
                return IonResult::decoding_error("expected ':' after field name");
            }
            self.position += 1;

            // Parse field value
            self.emit_annotated_value(destination, constant_pool)?;
        }

        destination.push(instr::END_CONTAINER);
        let bytecode_length = destination.len() - start_index - 1;
        destination[start_index] = instr::STRUCT_START | (bytecode_length as u32 & 0x003F_FFFF);
        Ok(())
    }

    /// Parses a field name and emits a `FIELD_NAME_REF` (for unescaped names)
    /// or `FIELD_NAME_CP` (for names with escape sequences) instruction.
    fn emit_field_name(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        if !self.skip_whitespace_and_comments() {
            return IonResult::decoding_error("expected field name");
        }
        let b = bytes[self.position];
        if b == b'\'' {
            // Check for triple-quoted string ('''...''')
            if self.position + 2 < bytes.len()
                && bytes[self.position + 1] == b'\''
                && bytes[self.position + 2] == b'\''
            {
                // Triple-quoted field name — parse like long string
                let text = self.parse_long_string_content()?;
                let arc = Arc::from(text.as_str());
                let idx = constant_pool.add(Constant::String(arc));
                destination.push(instr::FIELD_NAME_CP | idx);
            } else {
                // Quoted symbol
                self.position += 1;
                let start = self.position;
                let search_slice = &bytes[start..];
                match memchr2(b'\'', b'\\', search_slice) {
                    Some(offset) => {
                        if search_slice[offset] == b'\'' {
                            // No escapes — emit FIELD_NAME_REF
                            let content_end = start + offset;
                            self.position = content_end + 1;
                            let length = (content_end - start) as u32;
                            debug_assert!(length <= 0x003F_FFFF);
                            destination.push(instr::FIELD_NAME_REF | length);
                            destination.push(start as u32);
                        } else {
                            // Has escapes — decode and emit FIELD_NAME_CP
                            let mut i = start;
                            while i < bytes.len() && bytes[i] != b'\'' {
                                if bytes[i] == b'\\' {
                                    i += 2;
                                } else {
                                    i += 1;
                                }
                            }
                            let content_end = i;
                            self.position = i + 1;
                            let decoded = decode_escape_sequences(&bytes[start..content_end])?;
                            let arc = Arc::from(decoded.as_str());
                            let idx = constant_pool.add(Constant::String(arc));
                            destination.push(instr::FIELD_NAME_CP | idx);
                        }
                    }
                    None => return IonResult::decoding_error("unterminated quoted field name"),
                }
            }
        } else if b == b'"' {
            // Double-quoted field name
            self.position += 1;
            let start = self.position;
            let search_slice = &bytes[start..];
            match memchr2(b'"', b'\\', search_slice) {
                Some(offset) => {
                    if search_slice[offset] == b'"' {
                        // No escapes — emit FIELD_NAME_REF
                        let content_end = start + offset;
                        self.position = content_end + 1;
                        let length = (content_end - start) as u32;
                        debug_assert!(length <= 0x003F_FFFF);
                        destination.push(instr::FIELD_NAME_REF | length);
                        destination.push(start as u32);
                    } else {
                        // Has escapes — decode and emit FIELD_NAME_CP
                        let mut i = start;
                        while i < bytes.len() && bytes[i] != b'"' {
                            if bytes[i] == b'\\' {
                                i += 2;
                            } else {
                                i += 1;
                            }
                        }
                        let content_end = i;
                        self.position = i + 1;
                        let decoded = decode_escape_sequences(&bytes[start..content_end])?;
                        let arc = Arc::from(decoded.as_str());
                        let idx = constant_pool.add(Constant::String(arc));
                        destination.push(instr::FIELD_NAME_CP | idx);
                    }
                }
                None => return IonResult::decoding_error("unterminated double-quoted field name"),
            }
        } else if is_identifier_start(b) {
            // Unquoted identifier — check for SID reference
            let start = self.position;
            self.position += 1;
            while self.position < bytes.len() && is_identifier_continue(bytes[self.position]) {
                self.position += 1;
            }
            let text = &self.source[start..self.position];
            if let Some(sid) = try_parse_sid_from_text(text) {
                destination.push(instr::FIELD_NAME_SID | sid);
            } else {
                let length = (self.position - start) as u32;
                debug_assert!(length <= 0x003F_FFFF);
                destination.push(instr::FIELD_NAME_REF | length);
                destination.push(start as u32);
            }
        } else {
            return IonResult::decoding_error(format!(
                "unexpected character in field name position: '{}'",
                b as char
            ));
        }
        Ok(())
    }

    /// Parses a field name and returns it as an `Arc<str>`.
    /// Used only for system-level processing (e.g., LST parsing) where the
    /// field name text is needed for comparison.
    fn parse_field_name(&mut self) -> IonResult<Arc<str>> {
        let bytes = self.source.as_bytes();
        if !self.skip_whitespace_and_comments() {
            return IonResult::decoding_error("expected field name");
        }
        let b = bytes[self.position];
        if b == b'\'' {
            // Check for triple-quoted string ('''...''')
            if self.position + 2 < bytes.len()
                && bytes[self.position + 1] == b'\''
                && bytes[self.position + 2] == b'\''
            {
                let text = self.parse_long_string_content()?;
                return Ok(Arc::from(text.as_str()));
            }
            // Quoted symbol
            self.position += 1;
            let start = self.position;
            let search_slice = &bytes[start..];
            match memchr2(b'\'', b'\\', search_slice) {
                Some(offset) => {
                    if search_slice[offset] == b'\'' {
                        // No escapes
                        let content_end = start + offset;
                        self.position = content_end + 1;
                        Ok(Arc::from(&self.source[start..content_end]))
                    } else {
                        // Has escapes
                        let mut i = start;
                        while i < bytes.len() && bytes[i] != b'\'' {
                            if bytes[i] == b'\\' {
                                i += 2;
                            } else {
                                i += 1;
                            }
                        }
                        let content_end = i;
                        self.position = i + 1;
                        let decoded = decode_escape_sequences(&bytes[start..content_end])?;
                        Ok(Arc::from(decoded.as_str()))
                    }
                }
                None => IonResult::decoding_error("unterminated quoted field name"),
            }
        } else if b == b'"' {
            // Double-quoted field name
            self.position += 1;
            let start = self.position;
            let search_slice = &bytes[start..];
            match memchr2(b'"', b'\\', search_slice) {
                Some(offset) => {
                    if search_slice[offset] == b'"' {
                        let content_end = start + offset;
                        self.position = content_end + 1;
                        Ok(Arc::from(&self.source[start..content_end]))
                    } else {
                        let mut i = start;
                        while i < bytes.len() && bytes[i] != b'"' {
                            if bytes[i] == b'\\' {
                                i += 2;
                            } else {
                                i += 1;
                            }
                        }
                        let content_end = i;
                        self.position = i + 1;
                        let decoded = decode_escape_sequences(&bytes[start..content_end])?;
                        Ok(Arc::from(decoded.as_str()))
                    }
                }
                None => IonResult::decoding_error("unterminated double-quoted field name"),
            }
        } else if is_identifier_start(b) {
            let start = self.position;
            self.position += 1;
            while self.position < bytes.len() && is_identifier_continue(bytes[self.position]) {
                self.position += 1;
            }
            Ok(Arc::from(&self.source[start..self.position]))
        } else {
            IonResult::decoding_error(format!(
                "unexpected character in field name position: '{}'",
                b as char
            ))
        }
    }

    fn parse_lob(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        self.position += 2; // skip {{
                            // Only skip whitespace inside lobs — `//` is valid base64, not a comment.
        if !self.skip_whitespace_only() {
            return IonResult::decoding_error("unterminated lob");
        }

        if bytes[self.position] == b'"' {
            // Short clob (double-quoted)
            self.position += 1;
            let start = self.position;
            let mut has_escapes = false;
            while self.position < bytes.len() && bytes[self.position] != b'"' {
                if bytes[self.position] == b'\\' {
                    has_escapes = true;
                    self.position += 2;
                } else {
                    self.position += 1;
                }
            }
            let content_end = self.position;
            if self.position < bytes.len() {
                self.position += 1; // skip "
            }
            // Skip whitespace to }}
            if !self.skip_whitespace_only() {
                return IonResult::decoding_error("unterminated clob");
            }
            if self.position + 1 < bytes.len()
                && bytes[self.position] == b'}'
                && bytes[self.position + 1] == b'}'
            {
                self.position += 2;
            }

            if has_escapes {
                let decoded_bytes = decode_clob_escape_sequences(&bytes[start..content_end])?;
                let idx = constant_pool.add(Constant::Bytes(Arc::from(decoded_bytes)));
                destination.push(instr::CLOB_CP | idx);
            } else {
                let data = &bytes[start..content_end];
                let idx = constant_pool.add(Constant::Bytes(Arc::from(data)));
                destination.push(instr::CLOB_CP | idx);
            }
        } else if bytes[self.position] == b'\''
            && self.position + 2 < bytes.len()
            && bytes[self.position + 1] == b'\''
            && bytes[self.position + 2] == b'\''
        {
            // Long clob (triple-quoted)
            let mut result = Vec::new();
            loop {
                // Expect ''' at self.position
                if self.position + 2 >= bytes.len()
                    || bytes[self.position] != b'\''
                    || bytes[self.position + 1] != b'\''
                    || bytes[self.position + 2] != b'\''
                {
                    break;
                }
                self.position += 3; // skip opening '''
                let seg_start = self.position;
                while self.position + 2 < bytes.len() {
                    if bytes[self.position] == b'\''
                        && bytes[self.position + 1] == b'\''
                        && bytes[self.position + 2] == b'\''
                    {
                        break;
                    }
                    if bytes[self.position] == b'\\' {
                        self.position += 2;
                    } else {
                        self.position += 1;
                    }
                }
                let seg_end = self.position;
                self.position += 3; // skip closing '''

                // Always process long-clob content for newline normalization
                // (bare CR and CR LF are normalized to LF).
                let decoded = decode_long_clob_content(&bytes[seg_start..seg_end])?;
                result.extend_from_slice(&decoded);

                // Skip whitespace between segments
                if !self.skip_whitespace_only() {
                    break;
                }
                // Check for another ''' segment or }}
                if self.position + 2 < bytes.len()
                    && bytes[self.position] == b'\''
                    && bytes[self.position + 1] == b'\''
                    && bytes[self.position + 2] == b'\''
                {
                    // Another segment follows — continue loop
                } else {
                    break;
                }
            }
            // Expect }}
            if self.position + 1 < bytes.len()
                && bytes[self.position] == b'}'
                && bytes[self.position + 1] == b'}'
            {
                self.position += 2;
            }
            let idx = constant_pool.add(Constant::Bytes(Arc::from(result)));
            destination.push(instr::CLOB_CP | idx);
        } else {
            // Blob (base64)
            let start = self.position;
            while self.position < bytes.len() && bytes[self.position] != b'}' {
                self.position += 1;
            }
            let b64_end = self.position;
            // Skip }}
            if self.position + 1 < bytes.len()
                && bytes[self.position] == b'}'
                && bytes[self.position + 1] == b'}'
            {
                self.position += 2;
            }

            let b64_text: String = bytes[start..b64_end]
                .iter()
                .filter(|&&b| !b.is_ascii_whitespace())
                .map(|&b| b as char)
                .collect();
            let decoded = base64_decode(&b64_text)?;
            let idx = constant_pool.add(Constant::Bytes(Arc::from(decoded)));
            destination.push(instr::BLOB_CP | idx);
        }
        Ok(())
    }

    // ─── LST Parsing ─────────────────────────────────────────────────

    fn parse_lst(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        self.position += 1; // skip {
        let mut symbols: Vec<Option<Arc<str>>> = Vec::new();

        loop {
            if !self.skip_whitespace_and_comments() {
                return IonResult::decoding_error("unterminated LST struct");
            }
            if bytes[self.position] == b'}' {
                self.position += 1;
                break;
            }
            if bytes[self.position] == b',' {
                self.position += 1;
                continue;
            }

            // Parse field name
            let field_name = self.parse_field_name()?;
            if !self.skip_whitespace_and_comments() {
                return IonResult::decoding_error("expected ':' in LST field");
            }
            if bytes[self.position] != b':' {
                return IonResult::decoding_error("expected ':' in LST field");
            }
            self.position += 1;
            if !self.skip_whitespace_and_comments() {
                return IonResult::decoding_error("expected value in LST field");
            }

            if field_name.as_ref() == "symbols" {
                if bytes[self.position] == b'[' {
                    self.position += 1; // skip [
                    loop {
                        if !self.skip_whitespace_and_comments() {
                            return IonResult::decoding_error("unterminated symbols list");
                        }
                        if bytes[self.position] == b']' {
                            self.position += 1;
                            break;
                        }
                        if bytes[self.position] == b',' {
                            self.position += 1;
                            continue;
                        }
                        if bytes[self.position] == b'"' {
                            let s = self.parse_string_content()?;
                            symbols.push(Some(Arc::from(s.as_str())));
                        } else if bytes[self.position] == b'n' {
                            self.skip_identifier();
                            symbols.push(None);
                        } else {
                            self.skip_value()?;
                            symbols.push(None);
                        }
                    }
                } else {
                    self.skip_value()?;
                }
            } else {
                self.skip_value()?;
            }
        }

        // Emit the DIRECTIVE_SET_SYMBOLS bytecode
        destination.push(instr::DIRECTIVE_SET_SYMBOLS);
        for entry in &symbols {
            match entry {
                Some(text) => {
                    let idx = constant_pool.add(Constant::String(Arc::clone(text)));
                    destination.push(instr::STRING_CP | idx);
                }
                None => {
                    destination.push(instr::SYMBOL_SID);
                }
            }
        }
        destination.push(instr::END_CONTAINER);

        // Update the generator's internal symbol table
        self.symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
        for sym in &symbols {
            self.symbol_table.push(sym.clone());
        }

        Ok(())
    }

    fn parse_string_content(&mut self) -> IonResult<String> {
        let bytes = self.source.as_bytes();
        self.position += 1; // skip "
        let start = self.position;
        let search_slice = &bytes[start..];
        match memchr2(b'"', b'\\', search_slice) {
            Some(offset) => {
                if search_slice[offset] == b'"' {
                    // No escapes
                    let content_end = start + offset;
                    self.position = content_end + 1;
                    Ok(self.source[start..content_end].to_string())
                } else {
                    // Has escapes
                    let mut i = start;
                    while i < bytes.len() && bytes[i] != b'"' {
                        if bytes[i] == b'\\' {
                            i += 2;
                        } else {
                            i += 1;
                        }
                    }
                    let content_end = i;
                    self.position = i + 1;
                    decode_escape_sequences(&bytes[start..content_end])
                }
            }
            None => IonResult::decoding_error("unterminated string in LST"),
        }
    }

    fn skip_identifier(&mut self) {
        let bytes = self.source.as_bytes();
        while self.position < bytes.len() && is_identifier_continue(bytes[self.position]) {
            self.position += 1;
        }
        // Skip .type for null.type
        if self.position < bytes.len() && bytes[self.position] == b'.' {
            self.position += 1;
            while self.position < bytes.len() && is_identifier_continue(bytes[self.position]) {
                self.position += 1;
            }
        }
    }

    fn skip_value(&mut self) -> IonResult<()> {
        let bytes = self.source.as_bytes();
        if self.position >= bytes.len() {
            return Ok(());
        }
        match bytes[self.position] {
            b'"' => {
                self.position += 1;
                while self.position < bytes.len() && bytes[self.position] != b'"' {
                    if bytes[self.position] == b'\\' {
                        self.position += 2;
                    } else {
                        self.position += 1;
                    }
                }
                if self.position < bytes.len() {
                    self.position += 1;
                }
            }
            b'\'' => {
                if self.position + 2 < bytes.len()
                    && bytes[self.position + 1] == b'\''
                    && bytes[self.position + 2] == b'\''
                {
                    // Long string
                    self.position += 3;
                    loop {
                        if self.position + 2 >= bytes.len() {
                            break;
                        }
                        if bytes[self.position] == b'\''
                            && bytes[self.position + 1] == b'\''
                            && bytes[self.position + 2] == b'\''
                        {
                            self.position += 3;
                            break;
                        }
                        if bytes[self.position] == b'\\' {
                            self.position += 2;
                        } else {
                            self.position += 1;
                        }
                    }
                } else {
                    self.position += 1;
                    while self.position < bytes.len() && bytes[self.position] != b'\'' {
                        if bytes[self.position] == b'\\' {
                            self.position += 2;
                        } else {
                            self.position += 1;
                        }
                    }
                    if self.position < bytes.len() {
                        self.position += 1;
                    }
                }
            }
            b'[' | b'(' => {
                let close = if bytes[self.position] == b'[' {
                    b']'
                } else {
                    b')'
                };
                let open = bytes[self.position];
                self.position += 1;
                let mut depth = 1u32;
                while self.position < bytes.len() && depth > 0 {
                    match bytes[self.position] {
                        c if c == close => depth -= 1,
                        c if c == open => depth += 1,
                        b'"' => {
                            self.position += 1;
                            while self.position < bytes.len() && bytes[self.position] != b'"' {
                                if bytes[self.position] == b'\\' {
                                    self.position += 1;
                                }
                                self.position += 1;
                            }
                        }
                        _ => {}
                    }
                    self.position += 1;
                }
            }
            b'{' => {
                self.position += 1;
                if self.position < bytes.len() && bytes[self.position] == b'{' {
                    // Lob
                    self.position += 1;
                    while self.position + 1 < bytes.len() {
                        if bytes[self.position] == b'}' && bytes[self.position + 1] == b'}' {
                            self.position += 2;
                            return Ok(());
                        }
                        self.position += 1;
                    }
                } else {
                    let mut depth = 1u32;
                    while self.position < bytes.len() && depth > 0 {
                        match bytes[self.position] {
                            b'}' => depth -= 1,
                            b'{' => depth += 1,
                            b'"' => {
                                self.position += 1;
                                while self.position < bytes.len() && bytes[self.position] != b'"' {
                                    if bytes[self.position] == b'\\' {
                                        self.position += 1;
                                    }
                                    self.position += 1;
                                }
                            }
                            _ => {}
                        }
                        self.position += 1;
                    }
                }
            }
            _ => {
                while self.position < bytes.len() && !is_value_terminator(bytes[self.position]) {
                    self.position += 1;
                }
            }
        }
        Ok(())
    }
}

impl<'a> BytecodeGenerator for StrTextIon10Generator<'a> {
    fn refill(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        if self.done {
            destination.push(instr::END_OF_INPUT);
            return Ok(());
        }
        self.emit_all(destination, constant_pool)?;
        self.done = true;
        Ok(())
    }

    fn read_int_ref(&self, _position: u32, _length: u32) -> IonResult<Int> {
        // Text integers are parsed eagerly
        IonResult::decoding_error("read_int_ref not supported for str text generator")
    }

    fn read_decimal_ref(&self, _position: u32, _length: u32) -> IonResult<Decimal> {
        IonResult::decoding_error("read_decimal_ref not supported for str text generator")
    }

    fn read_timestamp_ref(&self, _position: u32, _length: u32) -> IonResult<Timestamp> {
        IonResult::decoding_error("read_timestamp_ref not supported for str text generator")
    }

    fn read_text_ref(&self, position: u32, length: u32) -> IonResult<&str> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.source.len() {
            return IonResult::decoding_error("text reference out of bounds");
        }
        // Zero-cost: source is already valid UTF-8
        Ok(&self.source[start..end])
    }

    fn read_bytes_ref(&self, position: u32, length: u32) -> IonResult<&[u8]> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.source.len() {
            return IonResult::decoding_error("bytes reference out of bounds");
        }
        Ok(&self.source.as_bytes()[start..end])
    }
}

// ─── Helper Functions ────────────────────────────────────────────────

/// Returns true if the byte terminates an undelimited value.
fn is_value_terminator(b: u8) -> bool {
    matches!(
        b,
        b' ' | b'\t' | b'\r' | b'\n' | b'\x0B' | b'\x0C' | b',' | b']' | b')' | b'}' | b'/'
    )
}

/// Returns true if the byte can start an identifier.
fn is_identifier_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_' || b == b'$'
}

/// Returns true if the byte can continue an identifier.
fn is_identifier_continue(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'$'
}

/// Returns true if the byte is an Ion operator character (valid unquoted
/// in s-expression context only).
fn try_parse_sid_from_text(text: &str) -> Option<u32> {
    let bytes = text.as_bytes();
    if bytes.len() < 2 || bytes[0] != b'$' {
        return None;
    }
    let digits = &bytes[1..];
    if digits.is_empty() {
        return None;
    }
    let mut value: u32 = 0;
    for &b in digits {
        if !b.is_ascii_digit() {
            return None;
        }
        value = value.checked_mul(10)?.checked_add((b - b'0') as u32)?;
    }
    Some(value)
}

fn is_operator_char(b: u8) -> bool {
    matches!(
        b,
        b'!' | b'#'
            | b'%'
            | b'&'
            | b'*'
            | b'+'
            | b'-'
            | b'.'
            | b'/'
            | b';'
            | b'<'
            | b'='
            | b'>'
            | b'?'
            | b'@'
            | b'^'
            | b'`'
            | b'|'
            | b'~'
    )
}

/// Emits an i64 value as the appropriate int instruction.
fn emit_i64_int(v: i64, destination: &mut Vec<u32>) {
    if v >= i16::MIN as i64 && v <= i16::MAX as i64 {
        destination.push(instr::INT_I16 | (v as i16 as u16 as u32));
    } else if v >= i32::MIN as i64 && v <= i32::MAX as i64 {
        destination.push(instr::INT_I32);
        destination.push(v as i32 as u32);
    } else {
        destination.push(instr::INT_I64);
        destination.push((v >> 32) as u32);
        destination.push(v as u32);
    }
}

/// Emits an i128 value as the appropriate int instruction.
fn emit_i128_int(v: i128, destination: &mut Vec<u32>, constant_pool: &mut ConstantPool) {
    if v >= i64::MIN as i128 && v <= i64::MAX as i128 {
        emit_i64_int(v as i64, destination);
    } else {
        let int_value = Int::from(v);
        let idx = constant_pool.add(Constant::BigInt(Arc::new(int_value)));
        destination.push(instr::INT_CP | idx);
    }
}

/// Parses an integer from a digit-only `&str` slice (no underscores) with an
/// external sign flag. Returns `None` if the value overflows i64.
fn parse_i64_no_alloc(slice: &str, is_negative: bool) -> Option<i64> {
    // Avoid allocation by accumulating digits manually.
    let mut result: i64 = 0;
    for &b in slice.as_bytes() {
        if !b.is_ascii_digit() {
            return None;
        }
        result = result.checked_mul(10)?;
        let digit = (b - b'0') as i64;
        if is_negative {
            result = result.checked_sub(digit)?;
        } else {
            result = result.checked_add(digit)?;
        }
    }
    Some(result)
}

/// Parses an integer string that may have 0x prefix.
fn parse_i128(text: &str) -> Result<i128, std::num::ParseIntError> {
    if let Some(hex) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        i128::from_str_radix(hex, 16)
    } else if let Some(hex) = text
        .strip_prefix("-0x")
        .or_else(|| text.strip_prefix("-0X"))
    {
        let magnitude =
            u128::from_str_radix(hex, 16).map_err(|_| "x".parse::<i128>().unwrap_err())?;
        Ok(-(magnitude as i128))
    } else {
        text.parse::<i128>()
    }
}

/// Parses an arbitrary-precision integer string that may have a sign and/or 0x prefix.
/// Used as a fallback when the value exceeds i128.
fn parse_big_int(text: &str) -> IonResult<Int> {
    let (is_negative, magnitude_str, radix) =
        if let Some(hex) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
            (false, hex, 16)
        } else if let Some(hex) = text
            .strip_prefix("-0x")
            .or_else(|| text.strip_prefix("-0X"))
        {
            (true, hex, 16)
        } else if let Some(digits) = text.strip_prefix('-') {
            (true, digits, 10)
        } else {
            (false, text, 10)
        };
    let uint = UInt::from_str_radix(magnitude_str, radix)?;
    let int_value = Int::from(&uint);
    if is_negative {
        Ok(-int_value)
    } else {
        Ok(int_value)
    }
}

/// Decodes escape sequences AND normalizes newlines in a string body.
/// Per the Ion spec, `\r\n` and bare `\r` in string content are normalized to `\n`.
fn decode_string_content(input: &[u8]) -> IonResult<String> {
    let mut result = String::with_capacity(input.len());
    let mut i = 0;
    while i < input.len() {
        match input[i] {
            b'\\' => {
                i += 1;
                if i >= input.len() {
                    return IonResult::decoding_error("trailing backslash");
                }
                match input[i] {
                    b'n' => {
                        result.push('\n');
                        i += 1;
                    }
                    b'r' => {
                        result.push('\r');
                        i += 1;
                    }
                    b't' => {
                        result.push('\t');
                        i += 1;
                    }
                    b'\\' => {
                        result.push('\\');
                        i += 1;
                    }
                    b'"' => {
                        result.push('"');
                        i += 1;
                    }
                    b'\'' => {
                        result.push('\'');
                        i += 1;
                    }
                    b'/' => {
                        result.push('/');
                        i += 1;
                    }
                    b'?' => {
                        result.push('?');
                        i += 1;
                    }
                    b'0' => {
                        result.push('\0');
                        i += 1;
                    }
                    b'a' => {
                        result.push('\x07');
                        i += 1;
                    }
                    b'b' => {
                        result.push('\x08');
                        i += 1;
                    }
                    b'f' => {
                        result.push('\x0C');
                        i += 1;
                    }
                    b'v' => {
                        result.push('\x0B');
                        i += 1;
                    }
                    b'x' => {
                        if i + 2 >= input.len() {
                            return IonResult::decoding_error("incomplete \\x escape");
                        }
                        let hex = std::str::from_utf8(&input[i + 1..i + 3]).map_err(|_| {
                            crate::IonError::decoding_error("invalid hex in \\x escape")
                        })?;
                        let code = u8::from_str_radix(hex, 16).map_err(|_| {
                            crate::IonError::decoding_error("invalid hex in \\x escape")
                        })?;
                        result.push(code as char);
                        i += 3;
                    }
                    b'u' => {
                        if i + 4 >= input.len() {
                            return IonResult::decoding_error("incomplete \\u escape");
                        }
                        let hex = std::str::from_utf8(&input[i + 1..i + 5]).map_err(|_| {
                            crate::IonError::decoding_error("invalid hex in \\u escape")
                        })?;
                        let code = u32::from_str_radix(hex, 16).map_err(|_| {
                            crate::IonError::decoding_error("invalid hex in \\u escape")
                        })?;
                        i += 5;
                        // Handle surrogate pairs
                        if (0xD800..=0xDBFF).contains(&code) {
                            // High surrogate — expect \uXXXX low surrogate
                            // `i` is currently past the 4 hex digits; we need
                            // `\u` followed by 4 more hex digits
                            if i + 5 < input.len() && input[i] == b'\\' && input[i + 1] == b'u' {
                                let hex2 =
                                    std::str::from_utf8(&input[i + 2..i + 6]).map_err(|_| {
                                        crate::IonError::decoding_error(
                                            "invalid hex in \\u surrogate pair",
                                        )
                                    })?;
                                let low = u32::from_str_radix(hex2, 16).map_err(|_| {
                                    crate::IonError::decoding_error(
                                        "invalid hex in \\u surrogate pair",
                                    )
                                })?;
                                if !(0xDC00..=0xDFFF).contains(&low) {
                                    return IonResult::decoding_error(
                                        "high surrogate not followed by low surrogate in \\u escape",
                                    );
                                }
                                let combined = 0x10000 + ((code - 0xD800) << 10) + (low - 0xDC00);
                                let ch = char::from_u32(combined).ok_or_else(|| {
                                    crate::IonError::decoding_error(
                                        "invalid unicode code point from surrogate pair",
                                    )
                                })?;
                                result.push(ch);
                                i += 6; // skip \uXXXX
                            } else {
                                return IonResult::decoding_error(
                                    "high surrogate not followed by low surrogate in \\u escape",
                                );
                            }
                        } else if (0xDC00..=0xDFFF).contains(&code) {
                            return IonResult::decoding_error(
                                "unexpected low surrogate in \\u escape",
                            );
                        } else {
                            let ch = char::from_u32(code).ok_or_else(|| {
                                crate::IonError::decoding_error(
                                    "invalid unicode code point in \\u escape",
                                )
                            })?;
                            result.push(ch);
                        }
                    }
                    b'U' => {
                        if i + 8 >= input.len() {
                            return IonResult::decoding_error("incomplete \\U escape");
                        }
                        let hex = std::str::from_utf8(&input[i + 1..i + 9]).map_err(|_| {
                            crate::IonError::decoding_error("invalid hex in \\U escape")
                        })?;
                        let code = u32::from_str_radix(hex, 16).map_err(|_| {
                            crate::IonError::decoding_error("invalid hex in \\U escape")
                        })?;
                        let ch = char::from_u32(code).ok_or_else(|| {
                            crate::IonError::decoding_error(
                                "invalid unicode code point in \\U escape",
                            )
                        })?;
                        result.push(ch);
                        i += 9;
                    }
                    b'\n' => {
                        // Escaped newline (line continuation) — skip
                        i += 1;
                    }
                    b'\r' => {
                        // Escaped CR (line continuation) — skip, also consume \n if present
                        i += 1;
                        if i < input.len() && input[i] == b'\n' {
                            i += 1;
                        }
                    }
                    other => {
                        return IonResult::decoding_error(format!(
                            "unknown escape sequence: \\{}",
                            other as char
                        ));
                    }
                }
            }
            b'\r' => {
                // Normalize \r\n or bare \r to \n
                i += 1;
                if i < input.len() && input[i] == b'\n' {
                    i += 1;
                }
                result.push('\n');
            }
            _ => {
                result.push(input[i] as char);
                i += 1;
            }
        }
    }
    Ok(result)
}

/// Decodes escape sequences in a string/symbol body (between quotes).
fn decode_escape_sequences(input: &[u8]) -> IonResult<String> {
    let mut result = String::with_capacity(input.len());
    let mut i = 0;
    while i < input.len() {
        if input[i] == b'\\' {
            i += 1;
            if i >= input.len() {
                return IonResult::decoding_error("trailing backslash");
            }
            match input[i] {
                b'n' => {
                    result.push('\n');
                    i += 1;
                }
                b'r' => {
                    result.push('\r');
                    i += 1;
                }
                b't' => {
                    result.push('\t');
                    i += 1;
                }
                b'\\' => {
                    result.push('\\');
                    i += 1;
                }
                b'"' => {
                    result.push('"');
                    i += 1;
                }
                b'\'' => {
                    result.push('\'');
                    i += 1;
                }
                b'/' => {
                    result.push('/');
                    i += 1;
                }
                b'?' => {
                    result.push('?');
                    i += 1;
                }
                b'0' => {
                    result.push('\0');
                    i += 1;
                }
                b'a' => {
                    result.push('\x07');
                    i += 1;
                }
                b'b' => {
                    result.push('\x08');
                    i += 1;
                }
                b'f' => {
                    result.push('\x0C');
                    i += 1;
                }
                b'v' => {
                    result.push('\x0B');
                    i += 1;
                }
                b'x' => {
                    if i + 2 >= input.len() {
                        return IonResult::decoding_error("incomplete \\x escape");
                    }
                    let hex = std::str::from_utf8(&input[i + 1..i + 3]).map_err(|_| {
                        crate::IonError::decoding_error("invalid hex in \\x escape")
                    })?;
                    let code = u8::from_str_radix(hex, 16).map_err(|_| {
                        crate::IonError::decoding_error("invalid hex in \\x escape")
                    })?;
                    result.push(code as char);
                    i += 3;
                }
                b'u' => {
                    if i + 4 >= input.len() {
                        return IonResult::decoding_error("incomplete \\u escape");
                    }
                    let hex = std::str::from_utf8(&input[i + 1..i + 5]).map_err(|_| {
                        crate::IonError::decoding_error("invalid hex in \\u escape")
                    })?;
                    let code = u32::from_str_radix(hex, 16).map_err(|_| {
                        crate::IonError::decoding_error("invalid hex in \\u escape")
                    })?;
                    i += 5;
                    // Handle surrogate pairs
                    if (0xD800..=0xDBFF).contains(&code) {
                        // High surrogate — expect \uXXXX low surrogate
                        if i + 5 < input.len() && input[i] == b'\\' && input[i + 1] == b'u' {
                            let hex2 = std::str::from_utf8(&input[i + 2..i + 6]).map_err(|_| {
                                crate::IonError::decoding_error("invalid hex in \\u surrogate pair")
                            })?;
                            let low = u32::from_str_radix(hex2, 16).map_err(|_| {
                                crate::IonError::decoding_error("invalid hex in \\u surrogate pair")
                            })?;
                            if !(0xDC00..=0xDFFF).contains(&low) {
                                return IonResult::decoding_error(
                                    "high surrogate not followed by low surrogate in \\u escape",
                                );
                            }
                            let combined = 0x10000 + ((code - 0xD800) << 10) + (low - 0xDC00);
                            let ch = char::from_u32(combined).ok_or_else(|| {
                                crate::IonError::decoding_error(
                                    "invalid unicode code point from surrogate pair",
                                )
                            })?;
                            result.push(ch);
                            i += 6; // skip \uXXXX
                        } else {
                            return IonResult::decoding_error(
                                "high surrogate not followed by low surrogate in \\u escape",
                            );
                        }
                    } else if (0xDC00..=0xDFFF).contains(&code) {
                        return IonResult::decoding_error("unexpected low surrogate in \\u escape");
                    } else {
                        let ch = char::from_u32(code).ok_or_else(|| {
                            crate::IonError::decoding_error(
                                "invalid unicode code point in \\u escape",
                            )
                        })?;
                        result.push(ch);
                    }
                }
                b'U' => {
                    if i + 8 >= input.len() {
                        return IonResult::decoding_error("incomplete \\U escape");
                    }
                    let hex = std::str::from_utf8(&input[i + 1..i + 9]).map_err(|_| {
                        crate::IonError::decoding_error("invalid hex in \\U escape")
                    })?;
                    let code = u32::from_str_radix(hex, 16).map_err(|_| {
                        crate::IonError::decoding_error("invalid hex in \\U escape")
                    })?;
                    let ch = char::from_u32(code).ok_or_else(|| {
                        crate::IonError::decoding_error("invalid unicode code point in \\U escape")
                    })?;
                    result.push(ch);
                    i += 9;
                }
                b'\n' => {
                    i += 1;
                }
                b'\r' => {
                    i += 1;
                    if i < input.len() && input[i] == b'\n' {
                        i += 1;
                    }
                }
                other => {
                    return IonResult::decoding_error(format!(
                        "unknown escape sequence: \\{}",
                        other as char
                    ));
                }
            }
        } else {
            result.push(input[i] as char);
            i += 1;
        }
    }
    Ok(result)
}

/// Decodes escape sequences for clob content (produces raw bytes).
fn decode_clob_escape_sequences(input: &[u8]) -> IonResult<Vec<u8>> {
    let mut result = Vec::with_capacity(input.len());
    let mut i = 0;
    while i < input.len() {
        if input[i] == b'\\' {
            i += 1;
            if i >= input.len() {
                return IonResult::decoding_error("trailing backslash in clob");
            }
            match input[i] {
                b'n' => {
                    result.push(b'\n');
                    i += 1;
                }
                b'r' => {
                    result.push(b'\r');
                    i += 1;
                }
                b't' => {
                    result.push(b'\t');
                    i += 1;
                }
                b'\\' => {
                    result.push(b'\\');
                    i += 1;
                }
                b'"' => {
                    result.push(b'"');
                    i += 1;
                }
                b'\'' => {
                    result.push(b'\'');
                    i += 1;
                }
                b'/' => {
                    result.push(b'/');
                    i += 1;
                }
                b'?' => {
                    result.push(b'?');
                    i += 1;
                }
                b'0' => {
                    result.push(0);
                    i += 1;
                }
                b'a' => {
                    result.push(0x07);
                    i += 1;
                }
                b'b' => {
                    result.push(0x08);
                    i += 1;
                }
                b'f' => {
                    result.push(0x0C);
                    i += 1;
                }
                b'v' => {
                    result.push(0x0B);
                    i += 1;
                }
                b'x' => {
                    if i + 2 >= input.len() {
                        return IonResult::decoding_error("incomplete \\x escape in clob");
                    }
                    let hex = std::str::from_utf8(&input[i + 1..i + 3]).map_err(|_| {
                        crate::IonError::decoding_error("invalid hex in clob \\x escape")
                    })?;
                    let code = u8::from_str_radix(hex, 16).map_err(|_| {
                        crate::IonError::decoding_error("invalid hex in clob \\x escape")
                    })?;
                    result.push(code);
                    i += 3;
                }
                b'\n' => i += 1,
                b'\r' => {
                    i += 1;
                    if i < input.len() && input[i] == b'\n' {
                        i += 1;
                    }
                }
                other => {
                    return IonResult::decoding_error(format!(
                        "unknown escape in clob: \\{}",
                        other as char
                    ));
                }
            }
        } else {
            result.push(input[i]);
            i += 1;
        }
    }
    Ok(result)
}

/// Decodes escape sequences for long-clob content (triple-quoted) with
/// newline normalization: bare CR LF and bare CR are normalized to LF.
fn decode_long_clob_content(input: &[u8]) -> IonResult<Vec<u8>> {
    let mut result = Vec::with_capacity(input.len());
    let mut i = 0;
    while i < input.len() {
        if input[i] == b'\\' {
            i += 1;
            if i >= input.len() {
                return IonResult::decoding_error("trailing backslash in clob");
            }
            match input[i] {
                b'n' => {
                    result.push(b'\n');
                    i += 1;
                }
                b'r' => {
                    result.push(b'\r');
                    i += 1;
                }
                b't' => {
                    result.push(b'\t');
                    i += 1;
                }
                b'\\' => {
                    result.push(b'\\');
                    i += 1;
                }
                b'"' => {
                    result.push(b'"');
                    i += 1;
                }
                b'\'' => {
                    result.push(b'\'');
                    i += 1;
                }
                b'/' => {
                    result.push(b'/');
                    i += 1;
                }
                b'?' => {
                    result.push(b'?');
                    i += 1;
                }
                b'0' => {
                    result.push(0);
                    i += 1;
                }
                b'a' => {
                    result.push(0x07);
                    i += 1;
                }
                b'b' => {
                    result.push(0x08);
                    i += 1;
                }
                b'f' => {
                    result.push(0x0C);
                    i += 1;
                }
                b'v' => {
                    result.push(0x0B);
                    i += 1;
                }
                b'x' => {
                    if i + 2 >= input.len() {
                        return IonResult::decoding_error("incomplete \\x escape in clob");
                    }
                    let hex = std::str::from_utf8(&input[i + 1..i + 3]).map_err(|_| {
                        crate::IonError::decoding_error("invalid hex in clob \\x escape")
                    })?;
                    let code = u8::from_str_radix(hex, 16).map_err(|_| {
                        crate::IonError::decoding_error("invalid hex in clob \\x escape")
                    })?;
                    result.push(code);
                    i += 3;
                }
                // Escaped newline (line continuation) — produces no bytes
                b'\n' => i += 1,
                b'\r' => {
                    i += 1;
                    if i < input.len() && input[i] == b'\n' {
                        i += 1;
                    }
                }
                other => {
                    return IonResult::decoding_error(format!(
                        "unknown escape in clob: \\{}",
                        other as char
                    ));
                }
            }
        } else if input[i] == b'\r' {
            // Normalize bare CR LF or bare CR to LF
            result.push(b'\n');
            i += 1;
            if i < input.len() && input[i] == b'\n' {
                i += 1;
            }
        } else {
            result.push(input[i]);
            i += 1;
        }
    }
    Ok(result)
}

/// Simple base64 decoder.
fn base64_decode(input: &str) -> IonResult<Vec<u8>> {
    let mut result = Vec::with_capacity(input.len() * 3 / 4);
    let mut buf: u32 = 0;
    let mut bits: u32 = 0;

    for c in input.chars() {
        let val = match c {
            'A'..='Z' => c as u32 - b'A' as u32,
            'a'..='z' => c as u32 - b'a' as u32 + 26,
            '0'..='9' => c as u32 - b'0' as u32 + 52,
            '+' => 62,
            '/' => 63,
            '=' => break,
            _ => {
                return IonResult::decoding_error(format!("invalid base64 character: '{c}'"));
            }
        };
        buf = (buf << 6) | val;
        bits += 6;
        if bits >= 8 {
            bits -= 8;
            result.push((buf >> bits) as u8);
            buf &= (1 << bits) - 1;
        }
    }
    Ok(result)
}

/// Parses a text decimal string into a `Decimal`.
fn parse_text_decimal(text: &str) -> IonResult<Decimal> {
    let text = text.trim();

    let (coeff_str, exp) = if let Some(d_pos) = text.find(['d', 'D']) {
        let coeff_part = &text[..d_pos];
        let exp_part = &text[d_pos + 1..];
        let explicit_exp: i64 = if exp_part.is_empty() {
            0
        } else {
            exp_part.parse().map_err(|e| {
                crate::IonError::decoding_error(format!("invalid decimal exponent: {e}"))
            })?
        };
        (coeff_part, explicit_exp)
    } else {
        (text, 0i64)
    };

    let (integer_part, frac_part) = if let Some(dot_pos) = coeff_str.find('.') {
        (&coeff_str[..dot_pos], &coeff_str[dot_pos + 1..])
    } else {
        (coeff_str, "")
    };

    let frac_digits = frac_part.len() as i64;
    let full_coeff_str = format!("{integer_part}{frac_part}");
    let total_exp = exp - frac_digits;

    if full_coeff_str.is_empty() || full_coeff_str == "-" || full_coeff_str == "+" {
        return Ok(Decimal::new(0i32, total_exp));
    }

    // Check for negative zero
    if let Some(after_sign) = full_coeff_str.strip_prefix('-') {
        if after_sign.chars().all(|c| c == '0') {
            return Ok(Decimal::negative_zero_with_exponent(total_exp));
        }
    }

    // Try i128 first (fast path), fall back to arbitrary-precision Int
    if let Ok(coefficient) = full_coeff_str.parse::<i128>() {
        return Ok(Decimal::new(coefficient, total_exp));
    }
    let coefficient = parse_big_int(&full_coeff_str)?;
    Ok(Decimal::new(coefficient, total_exp))
}

// ─── Timestamp Parsing ────────────────────────────────────────────────

/// Parses exactly 4 ASCII decimal digits starting at `pos`.
#[inline(always)]
fn parse_4_digits(text: &[u8], pos: &mut usize) -> IonResult<u32> {
    let p = *pos;
    if p + 4 > text.len() {
        return IonResult::decoding_error("unexpected end of timestamp (expected 4 digits)");
    }
    let d0 = text[p].wrapping_sub(b'0') as u32;
    let d1 = text[p + 1].wrapping_sub(b'0') as u32;
    let d2 = text[p + 2].wrapping_sub(b'0') as u32;
    let d3 = text[p + 3].wrapping_sub(b'0') as u32;
    if d0 > 9 || d1 > 9 || d2 > 9 || d3 > 9 {
        return IonResult::decoding_error("non-digit in timestamp year");
    }
    *pos = p + 4;
    Ok(d0 * 1000 + d1 * 100 + d2 * 10 + d3)
}

/// Parses exactly 2 ASCII decimal digits starting at `pos`.
#[inline(always)]
fn parse_2_digits(text: &[u8], pos: &mut usize) -> IonResult<u32> {
    let p = *pos;
    if p + 2 > text.len() {
        return IonResult::decoding_error("unexpected end of timestamp (expected 2 digits)");
    }
    let d0 = text[p].wrapping_sub(b'0') as u32;
    let d1 = text[p + 1].wrapping_sub(b'0') as u32;
    if d0 > 9 || d1 > 9 {
        return IonResult::decoding_error("non-digit in timestamp field");
    }
    *pos = p + 2;
    Ok(d0 * 10 + d1)
}

/// Expects a specific byte at `pos` and advances past it.
#[inline(always)]
fn expect_byte(text: &[u8], pos: &mut usize, expected: u8) -> IonResult<()> {
    let p = *pos;
    if p >= text.len() || text[p] != expected {
        return IonResult::decoding_error(format!(
            "expected '{}' in timestamp at position {p}",
            expected as char
        ));
    }
    *pos = p + 1;
    Ok(())
}

/// Parses the timezone offset from the current position.
#[inline]
fn parse_offset(text: &[u8], pos: &mut usize) -> IonResult<Option<i32>> {
    let p = *pos;
    if p >= text.len() {
        return Ok(None);
    }
    match text[p] {
        b'Z' | b'z' => {
            *pos = p + 1;
            Ok(Some(0))
        }
        b'+' => {
            *pos = p + 1;
            let hours = parse_2_digits(text, pos)? as i32;
            expect_byte(text, pos, b':')?;
            let minutes = parse_2_digits(text, pos)? as i32;
            Ok(Some(hours * 60 + minutes))
        }
        b'-' => {
            *pos = p + 1;
            let hours = parse_2_digits(text, pos)? as i32;
            expect_byte(text, pos, b':')?;
            let minutes = parse_2_digits(text, pos)? as i32;
            if hours == 0 && minutes == 0 {
                Ok(None)
            } else {
                Ok(Some(-(hours * 60 + minutes)))
            }
        }
        _ => IonResult::decoding_error(format!(
            "expected offset (Z, +hh:mm, or -hh:mm) at position {p}"
        )),
    }
}

/// Directly parses an Ion 1.0 text timestamp from raw bytes.
fn parse_timestamp_direct(text: &[u8]) -> IonResult<Timestamp> {
    let mut pos = 0;

    let year = parse_4_digits(text, &mut pos)?;

    if pos >= text.len() || text[pos] == b'T' {
        return Timestamp::with_year(year).build();
    }

    expect_byte(text, &mut pos, b'-')?;
    let month = parse_2_digits(text, &mut pos)?;

    if pos >= text.len() || text[pos] == b'T' {
        return Timestamp::with_year(year).with_month(month).build();
    }

    expect_byte(text, &mut pos, b'-')?;
    let day = parse_2_digits(text, &mut pos)?;

    if pos >= text.len() || text[pos] != b'T' {
        return Timestamp::with_year(year)
            .with_month(month)
            .with_day(day)
            .build();
    }
    pos += 1; // skip 'T'

    if pos >= text.len() {
        return Timestamp::with_year(year)
            .with_month(month)
            .with_day(day)
            .build();
    }

    let hour = parse_2_digits(text, &mut pos)?;
    expect_byte(text, &mut pos, b':')?;
    let minute = parse_2_digits(text, &mut pos)?;

    if pos >= text.len()
        || text[pos] == b'Z'
        || text[pos] == b'z'
        || text[pos] == b'+'
        || text[pos] == b'-'
    {
        let offset = parse_offset(text, &mut pos)?;
        let ts = Timestamp::with_year(year)
            .with_month(month)
            .with_day(day)
            .with_hour_and_minute(hour, minute);
        return if let Some(off) = offset {
            ts.with_offset(off).build()
        } else {
            ts.build()
        };
    }

    expect_byte(text, &mut pos, b':')?;
    let second = parse_2_digits(text, &mut pos)?;

    if pos < text.len() && text[pos] == b'.' {
        pos += 1;
        let frac_start = pos;
        while pos < text.len() && text[pos].is_ascii_digit() {
            pos += 1;
        }
        let frac_len = pos - frac_start;

        if frac_len == 0 {
            return IonResult::decoding_error("expected digits after '.' in timestamp");
        }

        let offset = parse_offset(text, &mut pos)?;

        let ts_base = Timestamp::with_year(year)
            .with_month(month)
            .with_day(day)
            .with_hour_and_minute(hour, minute)
            .with_second(second);

        let ts = if frac_len <= 9 {
            let frac_digits = &text[frac_start..frac_start + frac_len];
            let mut frac_value: u32 = 0;
            for &d in frac_digits {
                frac_value = frac_value * 10 + (d - b'0') as u32;
            }
            let multiplier = 10u32.pow(9 - frac_len as u32);
            let nanoseconds = frac_value * multiplier;
            ts_base.with_nanoseconds_and_precision(nanoseconds, frac_len as u32)
        } else if frac_len <= 38 {
            let frac_digits = &text[frac_start..frac_start + frac_len];
            let mut frac_value: u128 = 0;
            for &d in frac_digits {
                frac_value = frac_value * 10 + (d - b'0') as u128;
            }
            let le_bytes = frac_value.to_le_bytes();
            let significant_len = le_bytes
                .iter()
                .rposition(|&b| b != 0)
                .map(|i| i + 1)
                .unwrap_or(1);
            let mut signed_le = le_bytes[..significant_len].to_vec();
            if signed_le.last().is_some_and(|&b| b & 0x80 != 0) {
                signed_le.push(0);
            }
            let coefficient = Int::from_le_signed_bytes(&signed_le);
            let decimal = Decimal::new(coefficient, -(frac_len as i64));
            ts_base.with_fractional_seconds(decimal)
        } else {
            let frac_digits = &text[frac_start..frac_start + frac_len];
            let big = num_bigint::BigUint::parse_bytes(frac_digits, 10).ok_or_else(|| {
                crate::IonError::decoding_error("invalid fractional seconds digits")
            })?;
            let mut le = big.to_bytes_le();
            le.push(0);
            let coefficient = Int::from_le_signed_bytes(&le);
            let decimal = Decimal::new(coefficient, -(frac_len as i64));
            ts_base.with_fractional_seconds(decimal)
        };

        return if let Some(off) = offset {
            ts.with_offset(off).build()
        } else {
            ts.build()
        };
    }

    let offset = parse_offset(text, &mut pos)?;
    let ts = Timestamp::with_year(year)
        .with_month(month)
        .with_day(day)
        .with_hour_and_minute(hour, minute)
        .with_second(second);
    if let Some(off) = offset {
        ts.with_offset(off).build()
    } else {
        ts.build()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::instruction::{op, Instruction};
    use crate::bytecode::materialize::read_all_v3;
    use crate::ion_data::IonEq;
    use crate::Element;

    /// Helper: generate all bytecode from text Ion input using the str generator.
    fn generate_all(text: &str) -> (Vec<u32>, ConstantPool) {
        let mut gen = StrTextIon10Generator::new(text);
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();
        gen.refill(&mut dest, &mut cp).unwrap();
        (dest, cp)
    }

    #[test]
    fn empty_input() {
        let (dest, _cp) = generate_all("");
        assert_eq!(*dest.last().unwrap(), instr::END_OF_INPUT);
    }

    #[test]
    fn whitespace_only() {
        let (dest, _cp) = generate_all("   \n\t  ");
        assert_eq!(*dest.last().unwrap(), instr::END_OF_INPUT);
    }

    #[test]
    fn null_value() {
        let (dest, _cp) = generate_all("null");
        let instr_val = Instruction::from_raw(dest[0]);
        assert_eq!(instr_val.operation(), op::NULL_NULL);
    }

    #[test]
    fn typed_nulls() {
        let cases = [
            ("null.bool", op::NULL_BOOL),
            ("null.int", op::NULL_INT),
            ("null.float", op::NULL_FLOAT),
            ("null.decimal", op::NULL_DECIMAL),
            ("null.timestamp", op::NULL_TIMESTAMP),
            ("null.symbol", op::NULL_SYMBOL),
            ("null.string", op::NULL_STRING),
            ("null.clob", op::NULL_CLOB),
            ("null.blob", op::NULL_BLOB),
            ("null.list", op::NULL_LIST),
            ("null.sexp", op::NULL_SEXP),
            ("null.struct", op::NULL_STRUCT),
        ];
        for (text, expected_op) in cases {
            let (dest, _cp) = generate_all(text);
            let instr_val = Instruction::from_raw(dest[0]);
            assert_eq!(instr_val.operation(), expected_op, "failed for: {text}");
        }
    }

    #[test]
    fn bool_values() {
        let (dest, _cp) = generate_all("true");
        let instr_val = Instruction::from_raw(dest[0]);
        assert_eq!(instr_val.operation(), op::BOOL);
        assert_eq!(instr_val.data() & 1, 1);

        let (dest, _cp) = generate_all("false");
        let instr_val = Instruction::from_raw(dest[0]);
        assert_eq!(instr_val.operation(), op::BOOL);
        assert_eq!(instr_val.data() & 1, 0);
    }

    #[test]
    fn integers() {
        let (dest, _cp) = generate_all("0");
        let instr_val = Instruction::from_raw(dest[0]);
        assert_eq!(instr_val.operation(), op::INT_I16);
        assert_eq!(instr_val.data_as_i16(), 0);

        let (dest, _cp) = generate_all("42");
        let instr_val = Instruction::from_raw(dest[0]);
        assert_eq!(instr_val.operation(), op::INT_I16);
        assert_eq!(instr_val.data_as_i16(), 42);

        let (dest, _cp) = generate_all("-7");
        let instr_val = Instruction::from_raw(dest[0]);
        assert_eq!(instr_val.operation(), op::INT_I16);
        assert_eq!(instr_val.data_as_i16(), -7);

        let (dest, _cp) = generate_all("100000");
        let instr_val = Instruction::from_raw(dest[0]);
        assert_eq!(instr_val.operation(), op::INT_I32);
        assert_eq!(dest[1] as i32, 100000);
    }

    #[test]
    fn simple_string_ref() {
        let text = r#""hello""#;
        let (dest, _cp) = generate_all(text);
        let instr_val = Instruction::from_raw(dest[0]);
        assert_eq!(instr_val.operation(), op::STRING_REF);
        assert_eq!(instr_val.data(), 5); // "hello" is 5 bytes
    }

    #[test]
    fn string_with_escape() {
        let text = r#""hello\nworld""#;
        let (dest, cp) = generate_all(text);
        let instr_val = Instruction::from_raw(dest[0]);
        assert_eq!(instr_val.operation(), op::STRING_CP);
        match cp.get(instr_val.data()) {
            Constant::String(s) => assert_eq!(s.as_ref(), "hello\nworld"),
            _ => panic!("expected String constant"),
        }
    }

    #[test]
    fn simple_list() {
        let (dest, _cp) = generate_all("[1, 2, 3]");
        let list_instr = Instruction::from_raw(dest[0]);
        assert_eq!(list_instr.operation(), op::LIST_START);
    }

    #[test]
    fn simple_struct() {
        let (dest, _cp) = generate_all("{a: 1, b: 2}");
        let struct_instr = Instruction::from_raw(dest[0]);
        assert_eq!(struct_instr.operation(), op::STRUCT_START);
    }

    #[test]
    fn str_generator_all_benchmarks_pass() {
        // Helper to compare read_all_v3 (which now uses StrTextIon10Generator
        // for text) against Element::read_all.
        fn verify(input: &str) {
            let v3_result = read_all_v3(input.as_bytes());
            let expected = Element::read_all(input);
            match (&v3_result, &expected) {
                (Ok(v3_seq), Ok(exp_seq)) => {
                    let v3_elems: Vec<_> = v3_seq.iter().collect();
                    let exp_elems: Vec<_> = exp_seq.iter().collect();
                    assert_eq!(
                        v3_elems.len(),
                        exp_elems.len(),
                        "different element count for input \
                         (first 100 bytes): {:?}",
                        &input[..input.len().min(100)]
                    );
                    for (i, (v3, exp)) in v3_elems.iter().zip(exp_elems.iter()).enumerate() {
                        assert!(
                            v3.ion_eq(exp),
                            "element {i} differs.\n  v3:  {v3:?}\n  exp: {exp:?}\n  \
                             input (first 100 bytes): {:?}",
                            &input[..input.len().min(100)]
                        );
                    }
                }
                (Err(e), _) => {
                    panic!(
                        "v3 failed: {e}\n  input (first 100 bytes): {:?}",
                        &input[..input.len().min(100)]
                    );
                }
                (_, Err(e)) => {
                    panic!(
                        "Element::read_all failed: {e}\n  \
                         input (first 100 bytes): {:?}",
                        &input[..input.len().min(100)]
                    );
                }
            }
        }

        // integers
        let integers: String = (0..4000).map(|i| format!("{} ", i * 7 - 2000)).collect();
        verify(&integers);

        // floats
        let floats: String = (0..4000)
            .map(|i| format!("{}e0 ", (i as f64) * 1.7 - 3400.0))
            .collect();
        verify(&floats);

        // bools
        let bools: String = (0..4000)
            .map(|i| if i % 2 == 0 { "true " } else { "false " })
            .collect();
        verify(&bools);

        // nulls
        let nulls = "null null.bool null.int null.float null.decimal \
                     null.timestamp null.symbol null.string null.clob \
                     null.blob null.list null.sexp null.struct ";
        verify(nulls);

        // symbols
        let symbols: String = (0..1500).map(|i| format!("sym_{} ", i)).collect();
        verify(&symbols);

        // strings
        let strings: String = (0..3000)
            .map(|i| format!("\"string_value_{}\" ", i))
            .collect();
        verify(&strings);

        // decimals
        let decimals: String = (0..2500)
            .map(|i| format!("{}.{}d{} ", i, i % 100, (i % 5) as i32 - 2))
            .collect();
        verify(&decimals);

        // timestamps
        let timestamps = "2000-01-01T00:00:00Z 2023-06-15T12:30:45.123Z \
                          2024-12-31T23:59:59-05:00 2000-01T ";
        verify(timestamps);

        // lists
        let lists: String = (0..500)
            .map(|i| format!("[{}, {}] ", i * 2, i * 2 + 1))
            .collect();
        verify(&lists);

        // nested_structs
        let nested_structs: String = (0..200)
            .map(|i| format!("{{name: \"item_{i}\", value: {i}, tags: [\"a\", \"b\", \"c\"]}} "))
            .collect();
        verify(&nested_structs);

        // mixed
        let mixed: String = (0..200)
            .map(|i| {
                format!(
                    "{{id: {i}, name: \"user_{i}\", active: true, \
                     scores: [{}, {}, {}]}} ",
                    i * 10,
                    i * 20,
                    i * 30
                )
            })
            .collect();
        verify(&mixed);
    }
}
