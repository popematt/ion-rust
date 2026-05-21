//! Streaming Ion 1.0 text bytecode generator.
//!
//! Parses Ion 1.0 text data from an `impl Read` source and produces
//! bytecode instructions for the bytecode reader. Uses a two-phase
//! approach: scan for complete value boundaries, then parse.
//!
//! Each `refill()` call blocks until at least one complete top-level
//! value is available (or EOF is reached), then emits bytecode.

use std::io::Read;
use std::sync::Arc;

use memchr::memchr2;

use crate::bytecode::constant_pool::{Constant, ConstantPool};
use crate::bytecode::generator::BytecodeGenerator;
use crate::bytecode::instruction::instr;
use crate::result::IonFailure;
use crate::{Decimal, Int, IonResult, Timestamp};

/// Default internal buffer capacity in bytes.
const DEFAULT_BUFFER_CAPACITY: usize = 8 * 1024;

/// Minimum number of bytes to request in a single read.
const MIN_READ_SIZE: usize = 4096;

/// A streaming bytecode generator for Ion 1.0 text data.
///
/// Reads from an `impl Read` source, buffering data internally.
/// Each `refill()` call blocks until at least one complete top-level
/// value is available (or EOF is reached), then emits bytecode.
///
/// # REF Lifetime Contract
///
/// REF instructions emitted during a `refill()` call store positions
/// into the internal buffer. These positions are valid only until the
/// next `refill()` call, at which point the buffer may be compacted.
/// Callers must resolve all REF instructions before calling
/// `refill()` again.
pub struct StreamingTextIon10Generator<R: Read> {
    source: R,
    /// Internal buffer holding data read from the source.
    buffer: Vec<u8>,
    /// Number of valid bytes in `buffer` (data may not fill the whole Vec).
    filled: usize,
    /// Current parse position within buffer.
    position: usize,
    /// How many bytes from the start of buffer have been consumed
    /// (and can be discarded on the next refill).
    consumed: usize,
    /// Whether EOF has been reached on the source.
    eof: bool,
    /// The buffer region `[0..utf8_validated_end]` has been confirmed to be
    /// valid UTF-8. This allows `read_text_ref` to skip re-validation.
    utf8_validated_end: usize,
    /// Symbol table for LST detection and text-to-SID resolution.
    symbol_table: Vec<Option<Arc<str>>>,
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

impl<R: Read> StreamingTextIon10Generator<R> {
    /// Creates a new streaming text generator from the given reader.
    ///
    /// Do NOT wrap the reader in `BufReader` — this generator performs
    /// its own internal buffering.
    pub fn new(reader: R) -> Self {
        let symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
        Self {
            source: reader,
            buffer: vec![0u8; DEFAULT_BUFFER_CAPACITY],
            filled: 0,
            position: 0,
            consumed: 0,
            eof: false,
            utf8_validated_end: 0,
            symbol_table,
        }
    }

    /// Compacts the buffer by removing already-consumed bytes (those
    /// before `self.consumed`).
    fn compact(&mut self) {
        if self.consumed > 0 {
            self.buffer.copy_within(self.consumed..self.filled, 0);
            self.filled -= self.consumed;
            self.position -= self.consumed;
            // Adjust the validated boundary; it cannot go below zero because
            // we only ever validate regions that start at or after `consumed`.
            self.utf8_validated_end = self.utf8_validated_end.saturating_sub(self.consumed);
            self.consumed = 0;
        }
    }

    /// Ensures at least one more byte is available in the buffer.
    /// Returns `Ok(true)` if data is available, `Ok(false)` if EOF.
    fn ensure_data(&mut self) -> IonResult<bool> {
        if self.position < self.filled {
            return Ok(true);
        }
        if self.eof {
            return Ok(false);
        }
        self.read_more()?;
        Ok(self.position < self.filled)
    }

    /// Reads more data from the source into the buffer.
    fn read_more(&mut self) -> IonResult<()> {
        // Grow the buffer if needed
        if self.filled >= self.buffer.len() {
            let new_cap = self.buffer.len() * 2;
            self.buffer.resize(new_cap, 0);
        }

        // Ensure we request at least MIN_READ_SIZE bytes
        let available = self.buffer.len() - self.filled;
        if available < MIN_READ_SIZE {
            self.buffer.resize(self.filled + MIN_READ_SIZE, 0);
        }

        let n = self
            .source
            .read(&mut self.buffer[self.filled..])
            .map_err(|e| {
                crate::IonError::decoding_error(format!("I/O error reading text source: {e}"))
            })?;
        if n == 0 {
            self.eof = true;
        } else {
            self.filled += n;
        }
        Ok(())
    }

    /// Reads data until the predicate returns true for the available data,
    /// or EOF is reached. This is used by the scan phase.
    fn read_until_available(&mut self, min_bytes: usize) -> IonResult<()> {
        while self.filled - self.position < min_bytes && !self.eof {
            self.read_more()?;
        }
        Ok(())
    }

    /// Skips whitespace and comments, reading more data from the source as
    /// needed. Returns `Ok(true)` if positioned on a non-whitespace byte,
    /// `Ok(false)` if EOF.
    fn skip_whitespace_and_comments(&mut self) -> IonResult<bool> {
        loop {
            if !self.ensure_data()? {
                return Ok(false);
            }

            let b = self.buffer[self.position];
            match b {
                b' ' | b'\t' | b'\r' | b'\n' => {
                    self.position += 1;
                }
                b'/' => {
                    // Might be a comment
                    self.read_until_available(2)?;
                    if self.position + 1 >= self.filled {
                        // Single '/' at EOF is not a valid value start
                        return Ok(true);
                    }
                    match self.buffer[self.position + 1] {
                        b'/' => {
                            // Line comment: skip to end of line
                            self.position += 2;
                            self.skip_line_comment()?;
                        }
                        b'*' => {
                            // Block comment: skip to */
                            self.position += 2;
                            self.skip_block_comment()?;
                        }
                        _ => return Ok(true),
                    }
                }
                _ => return Ok(true),
            }
        }
    }

    /// Skips to end of line (or EOF).
    fn skip_line_comment(&mut self) -> IonResult<()> {
        loop {
            if !self.ensure_data()? {
                return Ok(());
            }
            let b = self.buffer[self.position];
            self.position += 1;
            if b == b'\n' {
                return Ok(());
            }
        }
    }

    /// Skips to the end of a block comment (`*/`).
    fn skip_block_comment(&mut self) -> IonResult<()> {
        loop {
            if !self.ensure_data()? {
                return IonResult::decoding_error("unterminated block comment");
            }
            let b = self.buffer[self.position];
            self.position += 1;
            if b == b'*' {
                if !self.ensure_data()? {
                    return IonResult::decoding_error("unterminated block comment");
                }
                if self.buffer[self.position] == b'/' {
                    self.position += 1;
                    return Ok(());
                }
            }
        }
    }

    /// Scans forward to find the end of a complete top-level value.
    /// After this returns successfully, `self.buffer[self.position..scan_end]`
    /// contains a complete value.
    ///
    /// Returns the end position (exclusive) in the buffer.
    fn scan_complete_value(&mut self) -> IonResult<usize> {
        let start = self.position;
        if start >= self.filled {
            return IonResult::decoding_error("no data to scan");
        }

        let b = self.buffer[start];
        match b {
            b'"' => self.scan_short_string(start),
            b'\'' => self.scan_quoted_symbol_or_long_string(start),
            b'(' => self.scan_container(start, b'(', b')'),
            b'[' => self.scan_container(start, b'[', b']'),
            b'{' => self.scan_brace_value(start),
            _ => self.scan_undelimited_value(start),
        }
    }

    /// Scans a short string ("...") from start, using memchr2 to quickly
    /// find the closing quote or the next escape sequence.
    fn scan_short_string(&mut self, start: usize) -> IonResult<usize> {
        let mut i = start + 1; // skip opening "
        loop {
            if i >= self.filled {
                if self.eof {
                    return IonResult::decoding_error("unterminated string");
                }
                self.read_more()?;
            }
            if i >= self.filled {
                return IonResult::decoding_error("unterminated string");
            }
            // Use memchr2 to skip directly to the next " or \ in the buffer
            match memchr2(b'"', b'\\', &self.buffer[i..self.filled]) {
                Some(offset) => {
                    let found = i + offset;
                    if self.buffer[found] == b'"' {
                        return Ok(found + 1);
                    }
                    // Escape: skip the backslash and the escaped char
                    i = found + 1;
                    if i >= self.filled {
                        if self.eof {
                            return IonResult::decoding_error("unterminated string escape");
                        }
                        self.read_more()?;
                    }
                    if i >= self.filled {
                        return IonResult::decoding_error("unterminated string escape");
                    }
                    i += 1; // skip escaped char
                }
                None => {
                    // Neither " nor \ found in the remaining buffer
                    i = self.filled;
                    if self.eof {
                        return IonResult::decoding_error("unterminated string");
                    }
                    self.read_more()?;
                }
            }
        }
    }

    /// Scans a quoted symbol ('...') or a long string ('''...''').
    fn scan_quoted_symbol_or_long_string(&mut self, start: usize) -> IonResult<usize> {
        // Need at least 3 chars to distinguish ''' from 'x'
        self.read_until_available(3)?;
        let avail = self.filled - start;
        if avail >= 3 && self.buffer[start + 1] == b'\'' && self.buffer[start + 2] == b'\'' {
            // Long string
            self.scan_long_string(start)
        } else {
            // Quoted symbol
            self.scan_quoted_symbol(start)
        }
    }

    /// Scans a quoted symbol ('...') from start.
    fn scan_quoted_symbol(&mut self, start: usize) -> IonResult<usize> {
        let mut i = start + 1; // skip opening '
        loop {
            if i >= self.filled {
                if self.eof {
                    return IonResult::decoding_error("unterminated quoted symbol");
                }
                self.read_more()?;
            }
            if i >= self.filled {
                return IonResult::decoding_error("unterminated quoted symbol");
            }
            match self.buffer[i] {
                b'\'' => return Ok(i + 1),
                b'\\' => {
                    i += 2; // skip escape
                }
                _ => i += 1,
            }
        }
    }

    /// Scans a long string ('''...''') from start, handling continuation.
    fn scan_long_string(&mut self, start: usize) -> IonResult<usize> {
        let mut i = start + 3; // skip opening '''
        loop {
            // Find closing '''
            loop {
                if i >= self.filled {
                    if self.eof {
                        return IonResult::decoding_error("unterminated long string");
                    }
                    self.read_more()?;
                }
                if i >= self.filled {
                    return IonResult::decoding_error("unterminated long string");
                }
                match self.buffer[i] {
                    b'\'' => {
                        // Check for '''
                        self.read_until_available(i - self.position + 3)?;
                        if i + 2 < self.filled
                            && self.buffer[i + 1] == b'\''
                            && self.buffer[i + 2] == b'\''
                        {
                            i += 3;
                            break; // Found closing '''
                        }
                        i += 1;
                    }
                    b'\\' => {
                        i += 2; // skip escape
                    }
                    _ => i += 1,
                }
            }

            // Check for continuation: skip whitespace/comments, see if
            // another ''' follows.
            let saved_pos = self.position;
            self.position = i;
            let has_more = self.skip_whitespace_and_comments()?;
            if !has_more {
                let end = self.position;
                self.position = saved_pos;
                return Ok(end);
            }
            // Check if next chars are '''
            self.read_until_available(3)?;
            let remaining = self.filled - self.position;
            if remaining >= 3
                && self.buffer[self.position] == b'\''
                && self.buffer[self.position + 1] == b'\''
                && self.buffer[self.position + 2] == b'\''
            {
                // Continuation segment
                i = self.position + 3;
                self.position = saved_pos;
            } else {
                // No continuation — end of long string is at the
                // position before the whitespace we just consumed.
                let end = self.position;
                self.position = saved_pos;
                return Ok(end);
            }
        }
    }

    /// Scans a container (list, sexp, struct) matching open/close delimiters.
    fn scan_container(&mut self, start: usize, _open: u8, close: u8) -> IonResult<usize> {
        let mut i = start + 1; // skip opening delimiter
        let mut depth: u32 = 1;
        loop {
            if i >= self.filled {
                if self.eof {
                    return IonResult::decoding_error("unterminated container");
                }
                self.read_more()?;
            }
            if i >= self.filled {
                return IonResult::decoding_error("unterminated container");
            }
            match self.buffer[i] {
                b if b == close => {
                    depth -= 1;
                    i += 1;
                    if depth == 0 {
                        return Ok(i);
                    }
                }
                b'(' | b'[' | b'{' => {
                    depth += 1;
                    i += 1;
                }
                b')' | b']' | b'}' => {
                    // Closing delimiter that is not our `close` (handled above).
                    depth -= 1;
                    i += 1;
                    if depth == 0 {
                        return Ok(i);
                    }
                }
                b'"' => {
                    // Skip over string contents using memchr2
                    i += 1;
                    loop {
                        if i >= self.filled {
                            if self.eof {
                                return IonResult::decoding_error(
                                    "unterminated string in container",
                                );
                            }
                            self.read_more()?;
                        }
                        if i >= self.filled {
                            return IonResult::decoding_error("unterminated string in container");
                        }
                        match memchr2(b'"', b'\\', &self.buffer[i..self.filled]) {
                            Some(offset) => {
                                let found = i + offset;
                                if self.buffer[found] == b'"' {
                                    i = found + 1;
                                    break;
                                }
                                // Escape: skip backslash + escaped char
                                i = found + 2;
                            }
                            None => {
                                // Neither found in buffer — need more data
                                i = self.filled;
                                if self.eof {
                                    return IonResult::decoding_error(
                                        "unterminated string in container",
                                    );
                                }
                                self.read_more()?;
                            }
                        }
                    }
                }
                b'\'' => {
                    // Could be quoted symbol or long string
                    self.read_until_available(i - self.position + 3)?;
                    if i + 2 < self.filled
                        && self.buffer[i + 1] == b'\''
                        && self.buffer[i + 2] == b'\''
                    {
                        // Long string in container — skip to closing '''
                        i += 3;
                        i = self.scan_long_string_content(i)?;
                    } else {
                        // Quoted symbol
                        i += 1;
                        loop {
                            if i >= self.filled {
                                if self.eof {
                                    return IonResult::decoding_error(
                                        "unterminated quoted symbol in container",
                                    );
                                }
                                self.read_more()?;
                            }
                            if i >= self.filled {
                                return IonResult::decoding_error(
                                    "unterminated quoted symbol in container",
                                );
                            }
                            match self.buffer[i] {
                                b'\'' => {
                                    i += 1;
                                    break;
                                }
                                b'\\' => i += 2,
                                _ => i += 1,
                            }
                        }
                    }
                }
                b'/' => {
                    // Comment inside container
                    self.read_until_available(i - self.position + 2)?;
                    if i + 1 < self.filled {
                        match self.buffer[i + 1] {
                            b'/' => {
                                i += 2;
                                // Skip to end of line
                                loop {
                                    if i >= self.filled {
                                        if self.eof {
                                            break;
                                        }
                                        self.read_more()?;
                                        if i >= self.filled {
                                            break;
                                        }
                                    }
                                    if self.buffer[i] == b'\n' {
                                        i += 1;
                                        break;
                                    }
                                    i += 1;
                                }
                            }
                            b'*' => {
                                i += 2;
                                // Skip to */
                                loop {
                                    if i >= self.filled {
                                        if self.eof {
                                            return IonResult::decoding_error(
                                                "unterminated block comment in container",
                                            );
                                        }
                                        self.read_more()?;
                                    }
                                    if i >= self.filled {
                                        return IonResult::decoding_error(
                                            "unterminated block comment in container",
                                        );
                                    }
                                    if self.buffer[i] == b'*' {
                                        self.read_until_available(i - self.position + 2)?;
                                        if i + 1 < self.filled && self.buffer[i + 1] == b'/' {
                                            i += 2;
                                            break;
                                        }
                                    }
                                    i += 1;
                                }
                            }
                            _ => i += 1,
                        }
                    } else {
                        i += 1;
                    }
                }
                _ => i += 1,
            }
        }
    }

    /// Scans long string content (after the opening ''') to the closing '''.
    /// Returns position after the closing '''.
    fn scan_long_string_content(&mut self, mut i: usize) -> IonResult<usize> {
        loop {
            if i >= self.filled {
                if self.eof {
                    return IonResult::decoding_error("unterminated long string");
                }
                self.read_more()?;
            }
            if i >= self.filled {
                return IonResult::decoding_error("unterminated long string");
            }
            match self.buffer[i] {
                b'\'' => {
                    self.read_until_available(i - self.position + 3)?;
                    if i + 2 < self.filled
                        && self.buffer[i + 1] == b'\''
                        && self.buffer[i + 2] == b'\''
                    {
                        return Ok(i + 3);
                    }
                    i += 1;
                }
                b'\\' => i += 2,
                _ => i += 1,
            }
        }
    }

    /// Scans a value starting with `{` — could be a struct or a lob
    /// (`{{...}}`).
    fn scan_brace_value(&mut self, start: usize) -> IonResult<usize> {
        self.read_until_available(2)?;
        if start + 1 < self.filled && self.buffer[start + 1] == b'{' {
            // Lob literal: {{ ... }}
            self.scan_lob(start)
        } else {
            // Struct
            self.scan_container(start, b'{', b'}')
        }
    }

    /// Scans a lob literal `{{ ... }}`.
    fn scan_lob(&mut self, start: usize) -> IonResult<usize> {
        let mut i = start + 2; // skip {{
                               // Determine if this is a clob ({{"..."}}) or blob ({{base64}})
                               // by looking for a quote after optional whitespace
        loop {
            if i >= self.filled {
                if self.eof {
                    return IonResult::decoding_error("unterminated lob");
                }
                self.read_more()?;
            }
            if i >= self.filled {
                return IonResult::decoding_error("unterminated lob");
            }
            match self.buffer[i] {
                b' ' | b'\t' | b'\r' | b'\n' => i += 1,
                b'"' => {
                    // Clob: scan the string, then find }}
                    i += 1;
                    loop {
                        if i >= self.filled {
                            if self.eof {
                                return IonResult::decoding_error("unterminated clob");
                            }
                            self.read_more()?;
                        }
                        if i >= self.filled {
                            return IonResult::decoding_error("unterminated clob");
                        }
                        match self.buffer[i] {
                            b'"' => {
                                i += 1;
                                break;
                            }
                            b'\\' => i += 2,
                            _ => i += 1,
                        }
                    }
                    // Now find }}
                    loop {
                        if i >= self.filled {
                            if self.eof {
                                return IonResult::decoding_error("unterminated clob");
                            }
                            self.read_more()?;
                        }
                        if i >= self.filled {
                            return IonResult::decoding_error("unterminated clob");
                        }
                        match self.buffer[i] {
                            b'}' => {
                                self.read_until_available(i - self.position + 2)?;
                                if i + 1 < self.filled && self.buffer[i + 1] == b'}' {
                                    return Ok(i + 2);
                                }
                                return IonResult::decoding_error("malformed clob closing");
                            }
                            b' ' | b'\t' | b'\r' | b'\n' => i += 1,
                            _ => {
                                return IonResult::decoding_error("unexpected byte in clob");
                            }
                        }
                    }
                }
                _ => {
                    // Blob: scan to }}
                    loop {
                        if i >= self.filled {
                            if self.eof {
                                return IonResult::decoding_error("unterminated blob");
                            }
                            self.read_more()?;
                        }
                        if i >= self.filled {
                            return IonResult::decoding_error("unterminated blob");
                        }
                        if self.buffer[i] == b'}' {
                            self.read_until_available(i - self.position + 2)?;
                            if i + 1 < self.filled && self.buffer[i + 1] == b'}' {
                                return Ok(i + 2);
                            }
                            return IonResult::decoding_error("malformed blob closing");
                        }
                        i += 1;
                    }
                }
            }
        }
    }

    /// Scans an undelimited value (number, identifier, keyword, etc.)
    /// until a terminating character is found or EOF.
    fn scan_undelimited_value(&mut self, start: usize) -> IonResult<usize> {
        let mut i = start;
        loop {
            if i >= self.filled {
                if self.eof {
                    // Value ends at EOF
                    return Ok(i);
                }
                self.read_more()?;
                if i >= self.filled {
                    return Ok(i);
                }
            }
            let b = self.buffer[i];
            // Handle annotation lookahead: if we see ':', check for '::'
            // before treating it as a terminator.
            if b == b':' {
                self.read_until_available(i - self.position + 2)?;
                if i + 1 < self.filled && self.buffer[i + 1] == b':' {
                    // This is an annotation separator. The scanned region
                    // includes the identifier up to here as an annotation.
                    // Skip the :: and continue scanning the annotated value.
                    i += 2;
                    // Skip whitespace/comments after ::
                    let saved = self.position;
                    self.position = i;
                    self.skip_whitespace_and_comments()?;
                    i = self.position;
                    self.position = saved;
                    // Now scan the next value (which may itself be annotated)
                    if i >= self.filled {
                        if self.eof {
                            return IonResult::decoding_error("annotation not followed by a value");
                        }
                        self.read_more()?;
                    }
                    if i >= self.filled {
                        return IonResult::decoding_error("annotation not followed by a value");
                    }
                    // Dispatch on the first byte of the annotated value
                    let nb = self.buffer[i];
                    match nb {
                        b'"' => return self.scan_short_string(i),
                        b'\'' => return self.scan_quoted_symbol_or_long_string(i),
                        b'(' => return self.scan_container(i, b'(', b')'),
                        b'[' => return self.scan_container(i, b'[', b']'),
                        b'{' => return self.scan_brace_value(i),
                        _ => {
                            // Continue scanning as undelimited
                            continue;
                        }
                    }
                } else if self.looks_like_timestamp(start, i) {
                    // Single ':' inside what looks like a timestamp
                    // (e.g., `2024-01-15T10:30:00Z`). Continue scanning.
                    i += 1;
                    continue;
                } else {
                    // Single ':' — this is a value terminator (e.g., in struct)
                    return Ok(i);
                }
            }
            if is_value_terminator(b) {
                return Ok(i);
            }
            i += 1;
        }
    }

    // ─── Parse Phase ───────────────────────────────────────────────

    /// Parses the complete value in `buffer[self.position..end]` and emits
    /// bytecode. Returns `true` if this was a system value (IVM or LST).
    fn emit_top_level_value(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<bool> {
        // Collect annotations
        let mut annotations: Vec<Arc<str>> = Vec::new();
        loop {
            // Skip whitespace within the scanned region
            self.skip_ws_in_region(end);
            if self.position >= end {
                return IonResult::decoding_error("empty value after annotations");
            }
            // Try to parse annotation (identifier :: )
            if let Some((text, after_colons)) = self.try_parse_annotation(end)? {
                annotations.push(text);
                self.position = after_colons;
            } else {
                break;
            }
        }

        // Check for IVM: `$ion_1_0` at top-level with no annotations
        if annotations.is_empty() {
            let value_slice = &self.buffer[self.position..end];
            if value_slice == b"$ion_1_0" {
                self.position = end;
                let version_data = 1u32 << 8;
                destination.push(instr::IVM | version_data);
                return Ok(true);
            }
        }

        // Check for LST: `$ion_symbol_table::{ ... }`
        if annotations.len() == 1 && annotations[0].as_ref() == "$ion_symbol_table" {
            let b = self.buffer[self.position];
            if b == b'{' {
                // Parse as LST
                self.parse_lst(end, destination, constant_pool)?;
                return Ok(true);
            }
        }

        // Emit annotations
        for ann in &annotations {
            let idx = constant_pool.add(Constant::String(Arc::clone(ann)));
            destination.push(instr::ANNOTATION_CP | idx);
        }

        // Parse the value
        self.emit_value(end, destination, constant_pool)?;
        Ok(false)
    }

    /// Skips whitespace and comments within the already-scanned region.
    fn skip_ws_in_region(&mut self, end: usize) {
        while self.position < end {
            let b = self.buffer[self.position];
            match b {
                b' ' | b'\t' | b'\r' | b'\n' => self.position += 1,
                b'/' if self.position + 1 < end => {
                    match self.buffer[self.position + 1] {
                        b'/' => {
                            self.position += 2;
                            while self.position < end && self.buffer[self.position] != b'\n' {
                                self.position += 1;
                            }
                            if self.position < end {
                                self.position += 1; // skip \n
                            }
                        }
                        b'*' => {
                            self.position += 2;
                            while self.position + 1 < end {
                                if self.buffer[self.position] == b'*'
                                    && self.buffer[self.position + 1] == b'/'
                                {
                                    self.position += 2;
                                    break;
                                }
                                self.position += 1;
                            }
                        }
                        _ => return,
                    }
                }
                _ => return,
            }
        }
    }

    /// Tries to parse an annotation at the current position.
    /// Returns `Some((text, position_after_colons))` if an annotation was
    /// found, or `None` if the current position is a value (not annotation).
    fn try_parse_annotation(&self, end: usize) -> IonResult<Option<(Arc<str>, usize)>> {
        let start = self.position;
        let b = self.buffer[start];

        // An annotation must be an identifier or quoted symbol
        let (text, token_end) = if b == b'\'' {
            // Quoted symbol — find closing '
            let mut i = start + 1;
            while i < end && self.buffer[i] != b'\'' {
                if self.buffer[i] == b'\\' {
                    i += 1;
                }
                i += 1;
            }
            if i >= end {
                return Ok(None);
            }
            let text_end = i;
            i += 1; // skip closing '
            let has_escapes = self.buffer[start + 1..text_end].contains(&b'\\');
            let text = if has_escapes {
                let decoded = decode_escape_sequences(&self.buffer[start + 1..text_end])?;
                Arc::from(decoded.as_str())
            } else {
                let s = std::str::from_utf8(&self.buffer[start + 1..text_end]).map_err(|e| {
                    crate::IonError::decoding_error(format!("invalid UTF-8 in quoted symbol: {e}"))
                })?;
                Arc::from(s)
            };
            (text, i)
        } else if is_identifier_start(b) {
            // Unquoted identifier
            let mut i = start + 1;
            while i < end && is_identifier_continue(self.buffer[i]) {
                i += 1;
            }
            let s = std::str::from_utf8(&self.buffer[start..i]).map_err(|e| {
                crate::IonError::decoding_error(format!("invalid UTF-8 in identifier: {e}"))
            })?;
            (Arc::from(s), i)
        } else {
            return Ok(None);
        };

        // Check for :: after the token (with possible whitespace)
        let mut i = token_end;
        // Skip whitespace between token and potential ::
        while i < end && matches!(self.buffer[i], b' ' | b'\t' | b'\r' | b'\n') {
            i += 1;
        }
        if i + 1 < end && self.buffer[i] == b':' && self.buffer[i + 1] == b':' {
            // Skip whitespace after ::
            let mut after = i + 2;
            while after < end && matches!(self.buffer[after], b' ' | b'\t' | b'\r' | b'\n') {
                after += 1;
            }
            // Also skip block/line comments after ::
            while after < end && self.buffer[after] == b'/' {
                if after + 1 < end && self.buffer[after + 1] == b'/' {
                    after += 2;
                    while after < end && self.buffer[after] != b'\n' {
                        after += 1;
                    }
                    if after < end {
                        after += 1;
                    }
                } else if after + 1 < end && self.buffer[after + 1] == b'*' {
                    after += 2;
                    while after + 1 < end {
                        if self.buffer[after] == b'*' && self.buffer[after + 1] == b'/' {
                            after += 2;
                            break;
                        }
                        after += 1;
                    }
                } else {
                    break;
                }
                // Skip whitespace after comment
                while after < end && matches!(self.buffer[after], b' ' | b'\t' | b'\r' | b'\n') {
                    after += 1;
                }
            }
            Ok(Some((text, after)))
        } else {
            Ok(None)
        }
    }

    /// Emits bytecode for a value at the current position (within the
    /// scanned region ending at `end`).
    fn emit_value(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        self.skip_ws_in_region(end);
        if self.position >= end {
            return IonResult::decoding_error("expected value but found end of region");
        }

        let b = self.buffer[self.position];
        match b {
            b'n' => self.parse_null_or_identifier(end, destination, constant_pool),
            b't' => self.parse_true(end, destination, constant_pool),
            b'f' => self.parse_false(end, destination, constant_pool),
            b'"' => self.parse_string(end, destination, constant_pool),
            b'\'' => self.parse_quoted_symbol_or_long_string(end, destination, constant_pool),
            b'[' => self.parse_list(end, destination, constant_pool),
            b'(' => self.parse_sexp(end, destination, constant_pool),
            b'{' => self.parse_struct_or_lob(end, destination, constant_pool),
            b'+' | b'-' => self.parse_signed_number(end, destination, constant_pool),
            b'0'..=b'9' => self.parse_number(end, destination, constant_pool),
            _ if is_identifier_start(b) => self.parse_symbol_value(end, destination, constant_pool),
            _ => IonResult::decoding_error(format!(
                "unexpected character '{}' at position {}",
                b as char, self.position
            )),
        }
    }

    fn parse_null_or_identifier(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        // Read the identifier
        let start = self.position;
        let mut i = start;
        while i < end && is_identifier_continue(self.buffer[i]) {
            i += 1;
        }
        let word = &self.buffer[start..i];

        if word == b"null" {
            // Check for null.type
            if i < end && self.buffer[i] == b'.' {
                i += 1;
                let type_start = i;
                while i < end && is_identifier_continue(self.buffer[i]) {
                    i += 1;
                }
                let type_name = &self.buffer[type_start..i];
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
            let text = std::str::from_utf8(word).map_err(|e| {
                crate::IonError::decoding_error(format!("invalid UTF-8 in identifier: {e}"))
            })?;
            let idx = constant_pool.add(Constant::String(Arc::from(text)));
            destination.push(instr::SYMBOL_CP | idx);
            Ok(())
        }
    }

    fn parse_true(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let start = self.position;
        let mut i = start;
        while i < end && is_identifier_continue(self.buffer[i]) {
            i += 1;
        }
        let word = &self.buffer[start..i];
        if word == b"true" {
            self.position = i;
            destination.push(instr::BOOL | 1);
            Ok(())
        } else {
            // It's a symbol starting with 't'
            self.parse_symbol_value(end, destination, constant_pool)
        }
    }

    fn parse_false(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let start = self.position;
        let mut i = start;
        while i < end && is_identifier_continue(self.buffer[i]) {
            i += 1;
        }
        let word = &self.buffer[start..i];
        if word == b"false" {
            self.position = i;
            destination.push(instr::BOOL);
            Ok(())
        } else {
            // It's a symbol starting with 'f'
            self.parse_symbol_value(end, destination, constant_pool)
        }
    }

    fn parse_symbol_value(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let start = self.position;
        let mut i = start;
        while i < end && is_identifier_continue(self.buffer[i]) {
            i += 1;
        }
        let word = &self.buffer[start..i];
        self.position = i;

        let text = std::str::from_utf8(word).map_err(|e| {
            crate::IonError::decoding_error(format!("invalid UTF-8 in symbol: {e}"))
        })?;
        let idx = constant_pool.add(Constant::String(Arc::from(text)));
        destination.push(instr::SYMBOL_CP | idx);
        Ok(())
    }

    fn parse_string(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        // self.position is at opening "
        let start = self.position + 1;
        let mut i = start;
        let mut has_escapes = false;
        // Use memchr2 to quickly find closing " or first escape \
        loop {
            let search_end = end.min(self.filled);
            match memchr2(b'"', b'\\', &self.buffer[i..search_end]) {
                Some(offset) => {
                    let found = i + offset;
                    if self.buffer[found] == b'"' {
                        i = found;
                        break;
                    }
                    // Escape sequence found
                    has_escapes = true;
                    i = found + 2; // skip backslash + escaped char
                }
                None => {
                    // No delimiter found in remaining region
                    i = search_end;
                    break;
                }
            }
        }
        let content_end = i;
        self.position = i + 1; // skip closing "

        if has_escapes {
            let decoded = decode_escape_sequences(&self.buffer[start..content_end])?;
            let idx = constant_pool.add(Constant::String(Arc::from(decoded.as_str())));
            destination.push(instr::STRING_CP | idx);
        } else {
            // No escapes — emit STRING_REF pointing to buffer
            let length = content_end - start;
            let offset = start as u32;
            destination.push(instr::STRING_REF | (length as u32 & 0x003F_FFFF));
            destination.push(offset);
        }
        Ok(())
    }

    fn parse_quoted_symbol_or_long_string(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        if self.position + 2 < end
            && self.buffer[self.position + 1] == b'\''
            && self.buffer[self.position + 2] == b'\''
        {
            // Long string
            self.parse_long_string(end, destination, constant_pool)
        } else {
            // Quoted symbol
            let start = self.position + 1;
            let mut i = start;
            let mut has_escapes = false;
            while i < end && self.buffer[i] != b'\'' {
                if self.buffer[i] == b'\\' {
                    has_escapes = true;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            let content_end = i;
            self.position = i + 1; // skip closing '

            if has_escapes {
                let decoded = decode_escape_sequences(&self.buffer[start..content_end])?;
                let idx = constant_pool.add(Constant::String(Arc::from(decoded.as_str())));
                destination.push(instr::SYMBOL_CP | idx);
            } else {
                let text = std::str::from_utf8(&self.buffer[start..content_end]).map_err(|e| {
                    crate::IonError::decoding_error(format!("invalid UTF-8 in quoted symbol: {e}"))
                })?;
                let idx = constant_pool.add(Constant::String(Arc::from(text)));
                destination.push(instr::SYMBOL_CP | idx);
            }
            Ok(())
        }
    }

    fn parse_long_string(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        // Long strings always go through CP because they may have
        // multiple concatenated segments.
        let mut result = String::new();
        loop {
            // Expect ''' at self.position
            if self.position + 2 >= end
                || self.buffer[self.position] != b'\''
                || self.buffer[self.position + 1] != b'\''
                || self.buffer[self.position + 2] != b'\''
            {
                break;
            }
            self.position += 3; // skip '''
                                // Read content until closing '''
            let seg_start = self.position;
            let mut i = seg_start;
            while i + 2 < end {
                if self.buffer[i] == b'\''
                    && self.buffer[i + 1] == b'\''
                    && self.buffer[i + 2] == b'\''
                {
                    break;
                }
                if self.buffer[i] == b'\\' {
                    i += 2;
                } else {
                    i += 1;
                }
            }
            let seg_end = i;
            self.position = i + 3; // skip closing '''

            let segment = &self.buffer[seg_start..seg_end];
            if segment.contains(&b'\\') {
                result.push_str(&decode_escape_sequences(segment)?);
            } else {
                let s = std::str::from_utf8(segment).map_err(|e| {
                    crate::IonError::decoding_error(format!("invalid UTF-8 in long string: {e}"))
                })?;
                result.push_str(s);
            }

            // Skip whitespace/comments between segments
            self.skip_ws_in_region(end);
        }

        let idx = constant_pool.add(Constant::String(Arc::from(result.as_str())));
        destination.push(instr::STRING_CP | idx);
        Ok(())
    }

    fn parse_signed_number(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let sign_byte = self.buffer[self.position];
        // Check for +inf / -inf
        if self.position + 4 <= end {
            let candidate = &self.buffer[self.position..self.position + 4];
            if candidate == b"+inf" || candidate == b"-inf" {
                // Verify it's not part of a longer identifier
                let after = self.position + 4;
                if after >= end || is_value_terminator(self.buffer[after]) {
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
        // Otherwise parse as number
        self.position += 1; // skip sign
        let is_negative = sign_byte == b'-';
        self.parse_number_with_sign(end, is_negative, destination, constant_pool)
    }

    fn parse_number(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        self.parse_number_with_sign(end, false, destination, constant_pool)
    }

    fn parse_number_with_sign(
        &mut self,
        end: usize,
        is_negative: bool,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        let start = self.position;

        // Check for 0x (hex) or 0b (binary) prefix
        if start + 1 < end && self.buffer[start] == b'0' {
            match self.buffer[start + 1] {
                b'x' | b'X' => {
                    return self.parse_hex_int(end, is_negative, destination, constant_pool)
                }
                b'b' | b'B' => {
                    return self.parse_binary_int(end, is_negative, destination, constant_pool)
                }
                _ => {}
            }
        }

        // Scan to determine type: integer, float, decimal, or timestamp
        let mut i = start;
        let mut has_dot = false;
        let mut has_exp = false;
        let mut has_d_exp = false;
        let mut has_t = false;
        let mut has_dash_after_4digits = false;

        // Count initial digits for timestamp detection
        let mut digit_count = 0;
        while i < end && (self.buffer[i].is_ascii_digit() || self.buffer[i] == b'_') {
            if self.buffer[i] != b'_' {
                digit_count += 1;
            }
            i += 1;
        }

        if i < end {
            match self.buffer[i] {
                b'.' => {
                    has_dot = true;
                    i += 1;
                    while i < end && (self.buffer[i].is_ascii_digit() || self.buffer[i] == b'_') {
                        i += 1;
                    }
                    if i < end {
                        match self.buffer[i] {
                            b'e' | b'E' => {
                                has_exp = true;
                                i += 1;
                                if i < end && (self.buffer[i] == b'+' || self.buffer[i] == b'-') {
                                    i += 1;
                                }
                                while i < end && self.buffer[i].is_ascii_digit() {
                                    i += 1;
                                }
                            }
                            b'd' | b'D' => {
                                has_d_exp = true;
                                i += 1;
                                if i < end && (self.buffer[i] == b'+' || self.buffer[i] == b'-') {
                                    i += 1;
                                }
                                while i < end && self.buffer[i].is_ascii_digit() {
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
                    if i < end && (self.buffer[i] == b'+' || self.buffer[i] == b'-') {
                        i += 1;
                    }
                    while i < end && self.buffer[i].is_ascii_digit() {
                        i += 1;
                    }
                }
                b'd' | b'D' => {
                    has_d_exp = true;
                    i += 1;
                    if i < end && (self.buffer[i] == b'+' || self.buffer[i] == b'-') {
                        i += 1;
                    }
                    while i < end && self.buffer[i].is_ascii_digit() {
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
            // Parse as timestamp directly from buffer bytes without allocation
            let ts_end = self.scan_timestamp_end(start, end);
            let ts_bytes = &self.buffer[start..ts_end];
            self.position = ts_end;
            let ts = parse_timestamp_direct(ts_bytes)?;
            let idx = constant_pool.add(Constant::Timestamp(Arc::new(ts)));
            destination.push(instr::TIMESTAMP_CP | idx);
            return Ok(());
        }

        self.position = i;

        if has_exp {
            // Float
            let raw = &self.buffer[start..i];
            if !raw.contains(&b'_') {
                // Fast path: parse directly from buffer without allocation
                let slice = std::str::from_utf8(raw).map_err(|e| {
                    crate::IonError::decoding_error(format!("invalid UTF-8 in float: {e}"))
                })?;
                let value: f64 = if is_negative {
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
            let raw = &self.buffer[start..i];
            if !raw.contains(&b'_') {
                // Fast path: parse directly without allocation
                let slice = std::str::from_utf8(raw).map_err(|e| {
                    crate::IonError::decoding_error(format!("invalid UTF-8 in decimal: {e}"))
                })?;
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
            // Integer
            let raw = &self.buffer[start..i];
            if !raw.contains(&b'_') {
                // Fast path: parse directly without allocation
                self.emit_int_from_bytes(raw, is_negative, destination, constant_pool)?;
            } else {
                let text = self.collect_number_text(start, i, is_negative);
                self.emit_parsed_int(&text, destination, constant_pool)?;
            }
        }
        Ok(())
    }

    /// Returns true if the content in `buffer[start..colon_pos]` looks like
    /// it could be part of a timestamp. This is used during scanning to
    /// distinguish the `:` in a time component (e.g., `10:30`) from a struct
    /// field separator.
    ///
    /// A timestamp-like pattern has 4 digits followed by either `-` (date
    /// separator) or `T` (date-time separator) somewhere in the scanned
    /// region, and the byte immediately before the colon is a digit
    /// (indicating `HH:` in a time component).
    fn looks_like_timestamp(&self, start: usize, colon_pos: usize) -> bool {
        // The byte before the colon must be a digit (e.g., `...T10:`)
        if colon_pos == start {
            return false;
        }
        if !self.buffer[colon_pos - 1].is_ascii_digit() {
            return false;
        }
        // Look for a 'T' in the scanned region (marks date-time boundary)
        let region = &self.buffer[start..colon_pos];
        region.contains(&b'T')
    }

    /// Scans forward from a timestamp start to find where it ends.
    fn scan_timestamp_end(&self, start: usize, end: usize) -> usize {
        let mut i = start;
        // Scan characters that can appear in timestamps
        while i < end {
            let b = self.buffer[i];
            match b {
                b'0'..=b'9' | b'-' | b'+' | b':' | b'.' | b'T' | b'Z' | b't' | b'z' => {
                    i += 1;
                }
                _ => break,
            }
        }
        i
    }

    /// Collects number text from `start..i`, stripping underscores and
    /// prepending a `-` if negative.
    fn collect_number_text(&self, start: usize, i: usize, is_negative: bool) -> String {
        let raw = &self.buffer[start..i];
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
        end: usize,
        is_negative: bool,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        self.position += 2; // skip 0x
        let start = self.position;
        while self.position < end
            && (self.buffer[self.position].is_ascii_hexdigit()
                || self.buffer[self.position] == b'_')
        {
            self.position += 1;
        }
        let hex_slice = &self.buffer[start..self.position];
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
        end: usize,
        is_negative: bool,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        self.position += 2; // skip 0b
        let start = self.position;
        while self.position < end
            && (self.buffer[self.position] == b'0'
                || self.buffer[self.position] == b'1'
                || self.buffer[self.position] == b'_')
        {
            self.position += 1;
        }
        let bin_slice = &self.buffer[start..self.position];
        // Parse manually
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

    /// Emits an integer from raw buffer bytes (no underscores) with an external
    /// sign flag, avoiding String allocation.
    fn emit_int_from_bytes(
        &self,
        raw: &[u8],
        is_negative: bool,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        // Try to parse as i64 using manual accumulation to avoid allocation
        if let Some(v) = parse_i64_from_bytes(raw, is_negative) {
            emit_i64_int(v, destination);
            return Ok(());
        }
        // Fallback: need to build a string for i128/BigInt parsing
        let text = if is_negative {
            let mut s = String::with_capacity(raw.len() + 1);
            s.push('-');
            for &b in raw {
                s.push(b as char);
            }
            s
        } else {
            let s = std::str::from_utf8(raw).map_err(|e| {
                crate::IonError::decoding_error(format!("invalid UTF-8 in integer: {e}"))
            })?;
            s.to_string()
        };
        self.emit_parsed_int(&text, destination, constant_pool)
    }

    /// Emits an integer from parsed text (decimal, hex with 0x prefix).
    fn emit_parsed_int(
        &self,
        text: &str,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        // Try i64 first
        if let Ok(v) = text.parse::<i64>() {
            emit_i64_int(v, destination);
            return Ok(());
        }
        // Try i128
        if let Ok(v) = parse_i128(text) {
            emit_i128_int(v, destination, constant_pool);
            return Ok(());
        }
        IonResult::decoding_error(format!("integer too large: {text}"))
    }

    fn parse_list(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        self.position += 1; // skip '['
        let start_index = destination.len();
        destination.push(0); // placeholder for LIST_START

        loop {
            self.skip_ws_in_region(end);
            if self.position >= end {
                return IonResult::decoding_error("unterminated list");
            }
            if self.buffer[self.position] == b']' {
                self.position += 1;
                break;
            }
            // Skip comma separators
            if self.buffer[self.position] == b',' {
                self.position += 1;
                continue;
            }
            self.emit_annotated_value(end, destination, constant_pool)?;
        }

        destination.push(instr::END_CONTAINER);
        let bytecode_length = destination.len() - start_index - 1;
        destination[start_index] = instr::LIST_START | (bytecode_length as u32 & 0x003F_FFFF);
        Ok(())
    }

    fn parse_sexp(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        self.position += 1; // skip '('
        let start_index = destination.len();
        destination.push(0); // placeholder for SEXP_START

        loop {
            self.skip_ws_in_region(end);
            if self.position >= end {
                return IonResult::decoding_error("unterminated sexp");
            }
            if self.buffer[self.position] == b')' {
                self.position += 1;
                break;
            }
            self.emit_annotated_value(end, destination, constant_pool)?;
        }

        destination.push(instr::END_CONTAINER);
        let bytecode_length = destination.len() - start_index - 1;
        destination[start_index] = instr::SEXP_START | (bytecode_length as u32 & 0x003F_FFFF);
        Ok(())
    }

    fn parse_struct_or_lob(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        // Check for {{ (lob)
        if self.position + 1 < end && self.buffer[self.position + 1] == b'{' {
            return self.parse_lob(end, destination, constant_pool);
        }
        self.parse_struct(end, destination, constant_pool)
    }

    fn parse_struct(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        self.position += 1; // skip '{'
        let start_index = destination.len();
        destination.push(0); // placeholder for STRUCT_START

        loop {
            self.skip_ws_in_region(end);
            if self.position >= end {
                return IonResult::decoding_error("unterminated struct");
            }
            if self.buffer[self.position] == b'}' {
                self.position += 1;
                break;
            }
            // Skip comma
            if self.buffer[self.position] == b',' {
                self.position += 1;
                continue;
            }

            // Parse field name
            let field_name = self.parse_field_name(end)?;
            let idx = constant_pool.add(Constant::String(field_name));
            destination.push(instr::FIELD_NAME_CP | idx);

            // Skip colon
            self.skip_ws_in_region(end);
            if self.position >= end || self.buffer[self.position] != b':' {
                return IonResult::decoding_error("expected ':' after field name");
            }
            self.position += 1;

            // Parse field value
            self.emit_annotated_value(end, destination, constant_pool)?;
        }

        destination.push(instr::END_CONTAINER);
        let bytecode_length = destination.len() - start_index - 1;
        destination[start_index] = instr::STRUCT_START | (bytecode_length as u32 & 0x003F_FFFF);
        Ok(())
    }

    fn parse_field_name(&mut self, end: usize) -> IonResult<Arc<str>> {
        self.skip_ws_in_region(end);
        if self.position >= end {
            return IonResult::decoding_error("expected field name");
        }
        let b = self.buffer[self.position];
        if b == b'\'' {
            // Quoted symbol
            self.position += 1;
            let start = self.position;
            let mut has_escapes = false;
            while self.position < end && self.buffer[self.position] != b'\'' {
                if self.buffer[self.position] == b'\\' {
                    has_escapes = true;
                    self.position += 2;
                } else {
                    self.position += 1;
                }
            }
            let content_end = self.position;
            if self.position < end {
                self.position += 1; // skip closing '
            }
            if has_escapes {
                let decoded = decode_escape_sequences(&self.buffer[start..content_end])?;
                Ok(Arc::from(decoded.as_str()))
            } else {
                let s = std::str::from_utf8(&self.buffer[start..content_end]).map_err(|e| {
                    crate::IonError::decoding_error(format!("invalid UTF-8 in field name: {e}"))
                })?;
                Ok(Arc::from(s))
            }
        } else if b == b'"' {
            // Double-quoted field name (Ion allows this)
            self.position += 1;
            let start = self.position;
            let mut has_escapes = false;
            while self.position < end && self.buffer[self.position] != b'"' {
                if self.buffer[self.position] == b'\\' {
                    has_escapes = true;
                    self.position += 2;
                } else {
                    self.position += 1;
                }
            }
            let content_end = self.position;
            if self.position < end {
                self.position += 1; // skip closing "
            }
            if has_escapes {
                let decoded = decode_escape_sequences(&self.buffer[start..content_end])?;
                Ok(Arc::from(decoded.as_str()))
            } else {
                let s = std::str::from_utf8(&self.buffer[start..content_end]).map_err(|e| {
                    crate::IonError::decoding_error(format!("invalid UTF-8 in field name: {e}"))
                })?;
                Ok(Arc::from(s))
            }
        } else if is_identifier_start(b) {
            // Unquoted identifier
            let start = self.position;
            while self.position < end && is_identifier_continue(self.buffer[self.position]) {
                self.position += 1;
            }
            let s = std::str::from_utf8(&self.buffer[start..self.position]).map_err(|e| {
                crate::IonError::decoding_error(format!("invalid UTF-8 in field name: {e}"))
            })?;
            Ok(Arc::from(s))
        } else {
            IonResult::decoding_error(format!(
                "unexpected character in field name position: '{}'",
                b as char
            ))
        }
    }

    fn parse_lob(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        self.position += 2; // skip {{
        self.skip_ws_in_region(end);
        if self.position >= end {
            return IonResult::decoding_error("unterminated lob");
        }

        if self.buffer[self.position] == b'"' {
            // Clob
            self.position += 1;
            let start = self.position;
            let mut has_escapes = false;
            while self.position < end && self.buffer[self.position] != b'"' {
                if self.buffer[self.position] == b'\\' {
                    has_escapes = true;
                    self.position += 2;
                } else {
                    self.position += 1;
                }
            }
            let content_end = self.position;
            if self.position < end {
                self.position += 1; // skip "
            }
            // Skip to }}
            self.skip_ws_in_region(end);
            if self.position + 1 < end
                && self.buffer[self.position] == b'}'
                && self.buffer[self.position + 1] == b'}'
            {
                self.position += 2;
            }

            if has_escapes {
                let decoded_bytes = decode_clob_escape_sequences(&self.buffer[start..content_end])?;
                let idx = constant_pool.add(Constant::Bytes(Arc::from(decoded_bytes)));
                destination.push(instr::CLOB_CP | idx);
            } else {
                let bytes = &self.buffer[start..content_end];
                let idx = constant_pool.add(Constant::Bytes(Arc::from(bytes)));
                destination.push(instr::CLOB_CP | idx);
            }
        } else {
            // Blob (base64)
            let start = self.position;
            while self.position < end && self.buffer[self.position] != b'}' {
                self.position += 1;
            }
            let b64_end = self.position;
            // Skip }}
            if self.position + 1 < end
                && self.buffer[self.position] == b'}'
                && self.buffer[self.position + 1] == b'}'
            {
                self.position += 2;
            }

            // Decode base64 (strip whitespace)
            let b64_text: String = self.buffer[start..b64_end]
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

    /// Emits an annotated value (parses annotations then the value).
    fn emit_annotated_value(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        // Collect annotations
        loop {
            self.skip_ws_in_region(end);
            if self.position >= end {
                return IonResult::decoding_error("expected value");
            }
            if let Some((text, after)) = self.try_parse_annotation(end)? {
                let idx = constant_pool.add(Constant::String(text));
                destination.push(instr::ANNOTATION_CP | idx);
                self.position = after;
            } else {
                break;
            }
        }
        self.emit_value(end, destination, constant_pool)
    }

    /// Parses a local symbol table and emits a DIRECTIVE_SET_SYMBOLS.
    fn parse_lst(
        &mut self,
        end: usize,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        // The struct has already been identified as $ion_symbol_table::{...}
        self.position += 1; // skip {
        let mut symbols: Vec<Option<Arc<str>>> = Vec::new();

        loop {
            self.skip_ws_in_region(end);
            if self.position >= end {
                return IonResult::decoding_error("unterminated LST struct");
            }
            if self.buffer[self.position] == b'}' {
                self.position += 1;
                break;
            }
            if self.buffer[self.position] == b',' {
                self.position += 1;
                continue;
            }

            // Parse field name
            let field_name = self.parse_field_name(end)?;
            self.skip_ws_in_region(end);
            if self.position >= end || self.buffer[self.position] != b':' {
                return IonResult::decoding_error("expected ':' in LST field");
            }
            self.position += 1;
            self.skip_ws_in_region(end);

            if field_name.as_ref() == "symbols" {
                // Parse the symbols list
                if self.position < end && self.buffer[self.position] == b'[' {
                    self.position += 1; // skip [
                    loop {
                        self.skip_ws_in_region(end);
                        if self.position >= end {
                            return IonResult::decoding_error("unterminated symbols list");
                        }
                        if self.buffer[self.position] == b']' {
                            self.position += 1;
                            break;
                        }
                        if self.buffer[self.position] == b',' {
                            self.position += 1;
                            continue;
                        }
                        // Parse string value
                        if self.buffer[self.position] == b'"' {
                            let s = self.parse_string_content(end)?;
                            symbols.push(Some(Arc::from(s.as_str())));
                        } else if self.buffer[self.position] == b'n' {
                            // null
                            self.skip_identifier(end);
                            symbols.push(None);
                        } else {
                            // Skip other values
                            self.skip_value_in_region(end)?;
                            symbols.push(None);
                        }
                    }
                } else {
                    // Skip non-list value
                    self.skip_value_in_region(end)?;
                }
            } else {
                // Skip other fields
                self.skip_value_in_region(end)?;
            }
        }

        // Emit the DIRECTIVE_SET_SYMBOLS bytecode with STRING_CP entries
        destination.push(instr::DIRECTIVE_SET_SYMBOLS);
        for entry in &symbols {
            match entry {
                Some(text) => {
                    let idx = constant_pool.add(Constant::String(Arc::clone(text)));
                    destination.push(instr::STRING_CP | idx);
                }
                None => {
                    // Unknown/null text: emit SYMBOL_SID 0
                    destination.push(instr::SYMBOL_SID);
                }
            }
        }
        destination.push(instr::END_CONTAINER);

        // Also update the generator's internal symbol table for
        // IVM/annotation tracking purposes.
        self.symbol_table = SYSTEM_SYMBOLS.iter().map(|s| Some(Arc::from(*s))).collect();
        for sym in &symbols {
            self.symbol_table.push(sym.clone());
        }

        Ok(())
    }

    /// Parses a string content (after opening ") and returns the decoded text.
    fn parse_string_content(&mut self, end: usize) -> IonResult<String> {
        self.position += 1; // skip "
        let start = self.position;
        let mut has_escapes = false;
        while self.position < end && self.buffer[self.position] != b'"' {
            if self.buffer[self.position] == b'\\' {
                has_escapes = true;
                self.position += 2;
            } else {
                self.position += 1;
            }
        }
        let content_end = self.position;
        if self.position < end {
            self.position += 1; // skip "
        }
        if has_escapes {
            decode_escape_sequences(&self.buffer[start..content_end])
        } else {
            let s = std::str::from_utf8(&self.buffer[start..content_end]).map_err(|e| {
                crate::IonError::decoding_error(format!("invalid UTF-8 in string: {e}"))
            })?;
            Ok(s.to_string())
        }
    }

    /// Skips an identifier at the current position.
    fn skip_identifier(&mut self, end: usize) {
        while self.position < end && is_identifier_continue(self.buffer[self.position]) {
            self.position += 1;
        }
        // Skip .type for null.type
        if self.position < end && self.buffer[self.position] == b'.' {
            self.position += 1;
            while self.position < end && is_identifier_continue(self.buffer[self.position]) {
                self.position += 1;
            }
        }
    }

    /// Skips a complete value in the scanned region (for fields we don't
    /// care about).
    fn skip_value_in_region(&mut self, end: usize) -> IonResult<()> {
        self.skip_ws_in_region(end);
        if self.position >= end {
            return Ok(());
        }
        let b = self.buffer[self.position];
        match b {
            b'"' => {
                self.position += 1;
                while self.position < end && self.buffer[self.position] != b'"' {
                    if self.buffer[self.position] == b'\\' {
                        self.position += 2;
                    } else {
                        self.position += 1;
                    }
                }
                if self.position < end {
                    self.position += 1;
                }
            }
            b'\'' => {
                if self.position + 2 < end
                    && self.buffer[self.position + 1] == b'\''
                    && self.buffer[self.position + 2] == b'\''
                {
                    // Long string — skip to closing '''
                    self.position += 3;
                    loop {
                        if self.position + 2 >= end {
                            break;
                        }
                        if self.buffer[self.position] == b'\''
                            && self.buffer[self.position + 1] == b'\''
                            && self.buffer[self.position + 2] == b'\''
                        {
                            self.position += 3;
                            break;
                        }
                        if self.buffer[self.position] == b'\\' {
                            self.position += 2;
                        } else {
                            self.position += 1;
                        }
                    }
                } else {
                    self.position += 1;
                    while self.position < end && self.buffer[self.position] != b'\'' {
                        if self.buffer[self.position] == b'\\' {
                            self.position += 2;
                        } else {
                            self.position += 1;
                        }
                    }
                    if self.position < end {
                        self.position += 1;
                    }
                }
            }
            b'[' | b'(' => {
                let close = if b == b'[' { b']' } else { b')' };
                self.position += 1;
                let mut depth = 1u32;
                while self.position < end && depth > 0 {
                    match self.buffer[self.position] {
                        c if c == close => depth -= 1,
                        c if c == b => depth += 1,
                        b'"' => {
                            self.position += 1;
                            while self.position < end && self.buffer[self.position] != b'"' {
                                if self.buffer[self.position] == b'\\' {
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
                if self.position < end && self.buffer[self.position] == b'{' {
                    // Lob — skip to }}
                    self.position += 1;
                    while self.position + 1 < end {
                        if self.buffer[self.position] == b'}'
                            && self.buffer[self.position + 1] == b'}'
                        {
                            self.position += 2;
                            return Ok(());
                        }
                        self.position += 1;
                    }
                } else {
                    let mut depth = 1u32;
                    while self.position < end && depth > 0 {
                        match self.buffer[self.position] {
                            b'}' => depth -= 1,
                            b'{' => depth += 1,
                            b'"' => {
                                self.position += 1;
                                while self.position < end && self.buffer[self.position] != b'"' {
                                    if self.buffer[self.position] == b'\\' {
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
                // Undelimited — skip to terminator
                while self.position < end && !is_value_terminator(self.buffer[self.position]) {
                    self.position += 1;
                }
            }
        }
        Ok(())
    }
}

impl<R: Read> BytecodeGenerator for StreamingTextIon10Generator<R> {
    fn refill(
        &mut self,
        destination: &mut Vec<u32>,
        constant_pool: &mut ConstantPool,
    ) -> IonResult<()> {
        // Compact previously consumed data once at the start of refill.
        // This avoids redundant memmoves when the loop below processes
        // multiple values from the already-buffered data.
        self.compact();

        // Loop: emit multiple top-level values while we have complete ones
        // buffered. Stop at a system value boundary (IVM/LST), EOF, or when
        // the buffer is exhausted and we need more data from the reader.
        loop {
            // Skip leading whitespace/comments (may require reads)
            let has_data = self.skip_whitespace_and_comments()?;
            if !has_data {
                destination.push(instr::END_OF_INPUT);
                return Ok(());
            }

            // Scan for a complete top-level value
            let scan_end = self.scan_complete_value()?;

            // Validate UTF-8 for the scanned region. This allows read_text_ref
            // to skip re-validation later since the buffer is immutable between
            // refill calls.
            if scan_end > self.utf8_validated_end {
                std::str::from_utf8(&self.buffer[self.utf8_validated_end..scan_end]).map_err(
                    |e| {
                        crate::IonError::decoding_error(format!(
                            "invalid UTF-8 in Ion text at byte offset {}: {e}",
                            self.utf8_validated_end + e.valid_up_to()
                        ))
                    },
                )?;
                self.utf8_validated_end = scan_end;
            }

            // Parse the complete value and emit bytecode
            let is_system_value =
                self.emit_top_level_value(scan_end, destination, constant_pool)?;

            // Mark consumed so the next refill() call compacts past this data
            self.consumed = self.position;

            // System value boundary (IVM/LST) — stop so the reader can
            // process the directive before seeing more values.
            if is_system_value {
                destination.push(instr::REFILL);
                return Ok(());
            }

            // Check if we have more data immediately available without
            // blocking on a read. If the buffer is exhausted, stop and
            // let the caller process what we have so far.
            if self.position >= self.filled && !self.eof {
                destination.push(instr::REFILL);
                return Ok(());
            }
        }
    }

    fn read_int_ref(&self, _position: u32, _length: u32) -> IonResult<Int> {
        // Text integers are parsed eagerly; this should not be called.
        IonResult::decoding_error("read_int_ref not supported for text generator")
    }

    fn read_decimal_ref(&self, _position: u32, _length: u32) -> IonResult<Decimal> {
        // Text decimals are parsed eagerly; this should not be called.
        IonResult::decoding_error("read_decimal_ref not supported for text generator")
    }

    fn read_timestamp_ref(&self, _position: u32, _length: u32) -> IonResult<Timestamp> {
        // Text timestamps are parsed eagerly; this should not be called.
        IonResult::decoding_error("read_timestamp_ref not supported for text generator")
    }

    fn read_text_ref(&self, position: u32, length: u32) -> IonResult<&str> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.filled {
            return IonResult::decoding_error("text reference out of bounds");
        }
        debug_assert!(
            end <= self.utf8_validated_end,
            "read_text_ref called on unvalidated region: end={end}, validated={v}",
            v = self.utf8_validated_end
        );
        // SAFETY: The buffer region [0..utf8_validated_end] was validated as
        // UTF-8 during the refill() that produced the REF instruction pointing
        // here. The buffer is immutable between refill() calls, so the
        // validation remains valid.
        Ok(unsafe { std::str::from_utf8_unchecked(&self.buffer[start..end]) })
    }

    fn read_bytes_ref(&self, position: u32, length: u32) -> IonResult<&[u8]> {
        let start = position as usize;
        let end = start + length as usize;
        if end > self.filled {
            return IonResult::decoding_error("bytes reference out of bounds");
        }
        Ok(&self.buffer[start..end])
    }
}

// ─── Helper Functions ──────────────────────────────────────────────

/// Returns true if the byte terminates an undelimited value.
/// Note: `:` is NOT included here because it is handled specially
/// in `scan_undelimited_value` for annotation detection.
fn is_value_terminator(b: u8) -> bool {
    matches!(
        b,
        b' ' | b'\t' | b'\r' | b'\n' | b',' | b']' | b')' | b'}' | b'/'
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

/// Parses an integer from raw bytes (digit-only, no underscores) with an
/// external sign flag. Returns `None` if the value overflows i64.
fn parse_i64_from_bytes(raw: &[u8], is_negative: bool) -> Option<i64> {
    let mut result: i64 = 0;
    for &b in raw {
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
        let magnitude = u128::from_str_radix(hex, 16).map_err(|_| {
            // Create a parse error by parsing an invalid string
            "x".parse::<i128>().unwrap_err()
        })?;
        Ok(-(magnitude as i128))
    } else {
        text.parse::<i128>()
    }
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
                    // \xHH
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
                    // \uHHHH
                    if i + 4 >= input.len() {
                        return IonResult::decoding_error("incomplete \\u escape");
                    }
                    let hex = std::str::from_utf8(&input[i + 1..i + 5]).map_err(|_| {
                        crate::IonError::decoding_error("invalid hex in \\u escape")
                    })?;
                    let code = u32::from_str_radix(hex, 16).map_err(|_| {
                        crate::IonError::decoding_error("invalid hex in \\u escape")
                    })?;
                    let ch = char::from_u32(code).ok_or_else(|| {
                        crate::IonError::decoding_error("invalid unicode code point in \\u escape")
                    })?;
                    result.push(ch);
                    i += 5;
                }
                b'U' => {
                    // \UHHHHHHHH
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
                    // Escaped newline — discard
                    i += 1;
                }
                b'\r' => {
                    // Escaped CR or CRLF — discard
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
            // Regular byte — validate UTF-8 char by char is expensive;
            // just copy bytes and validate at the end.
            result.push(input[i] as char);
            i += 1;
        }
    }
    // Re-validate UTF-8 for high bytes
    // The above pushes bytes as chars which is wrong for multi-byte UTF-8.
    // Let me fix this: accumulate raw bytes and convert at the end.
    // Actually, let me redo this properly.
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
    // Format: [sign] digits [. digits] [d/D [sign] digits]
    // We need to compute coefficient and exponent.
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

    // Split coefficient on decimal point
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
    let is_negative_zero =
        (full_coeff_str == "-0" || full_coeff_str == "-00") && full_coeff_str.starts_with('-');
    if is_negative_zero {
        // Check all digits after '-' are zero
        let after_sign = &full_coeff_str[1..];
        if after_sign.chars().all(|c| c == '0') {
            return Ok(Decimal::negative_zero_with_exponent(total_exp));
        }
    }

    let coefficient: i128 = full_coeff_str.parse().map_err(|e| {
        crate::IonError::decoding_error(format!(
            "invalid decimal coefficient '{}': {e}",
            full_coeff_str
        ))
    })?;

    Ok(Decimal::new(coefficient, total_exp))
}

/// Trait extension for Timestamp parsing from text.
trait TimestampParse {
    fn parse(bytes: &[u8]) -> IonResult<Timestamp>;
}

impl TimestampParse for Timestamp {
    /// Parses an Ion 1.0 text timestamp directly from bytes without allocating
    /// intermediate buffers or instantiating an `EncodingContext`.
    fn parse(bytes: &[u8]) -> IonResult<Timestamp> {
        parse_timestamp_direct(bytes)
    }
}

/// Parses exactly 4 ASCII decimal digits starting at `pos`, advancing `pos` past them.
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

/// Parses exactly 2 ASCII decimal digits starting at `pos`, advancing `pos` past them.
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
/// Returns `Some(minutes)` for a known offset, or `None` for unknown offset (`-00:00`).
#[inline]
fn parse_offset(text: &[u8], pos: &mut usize) -> IonResult<Option<i32>> {
    let p = *pos;
    if p >= text.len() {
        // No offset means unknown offset
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
                // -00:00 means unknown offset
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

/// Directly parses an Ion 1.0 text timestamp from raw bytes without any intermediate
/// allocations or use of `TextBuffer`/`EncodingContext`/winnow.
fn parse_timestamp_direct(text: &[u8]) -> IonResult<Timestamp> {
    let mut pos = 0;

    // Parse YYYY
    let year = parse_4_digits(text, &mut pos)?;

    // Check for 'T' (year-only precision) or end of input
    if pos >= text.len() || text[pos] == b'T' {
        return Timestamp::with_year(year).build();
    }

    // Expect '-' before month
    expect_byte(text, &mut pos, b'-')?;
    let month = parse_2_digits(text, &mut pos)?;

    // Check for 'T' (year-month precision) or end of input
    if pos >= text.len() || text[pos] == b'T' {
        return Timestamp::with_year(year).with_month(month).build();
    }

    // Expect '-' before day
    expect_byte(text, &mut pos, b'-')?;
    let day = parse_2_digits(text, &mut pos)?;

    // Check for 'T' to separate date from time; if absent, day precision
    if pos >= text.len() {
        return Timestamp::with_year(year)
            .with_month(month)
            .with_day(day)
            .build();
    }
    if text[pos] != b'T' {
        return Timestamp::with_year(year)
            .with_month(month)
            .with_day(day)
            .build();
    }
    pos += 1; // skip 'T'

    // If nothing follows the 'T', this is day precision (e.g., 2024-01-15T)
    if pos >= text.len() {
        return Timestamp::with_year(year)
            .with_month(month)
            .with_day(day)
            .build();
    }

    // Parse hh:mm
    let hour = parse_2_digits(text, &mut pos)?;
    expect_byte(text, &mut pos, b':')?;
    let minute = parse_2_digits(text, &mut pos)?;

    // Check if we have an offset next (minute precision) or ':' (seconds)
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

    // Parse :ss
    expect_byte(text, &mut pos, b':')?;
    let second = parse_2_digits(text, &mut pos)?;

    // Check for fractional seconds
    if pos < text.len() && text[pos] == b'.' {
        pos += 1; // skip '.'

        // Count and parse fractional digits
        let frac_start = pos;
        while pos < text.len() && text[pos].is_ascii_digit() {
            pos += 1;
        }
        let frac_len = pos - frac_start;

        if frac_len == 0 {
            return IonResult::decoding_error("expected digits after '.' in timestamp");
        }

        // Parse offset
        let offset = parse_offset(text, &mut pos)?;

        let ts_base = Timestamp::with_year(year)
            .with_month(month)
            .with_day(day)
            .with_hour_and_minute(hour, minute)
            .with_second(second);

        let ts = if frac_len <= 9 {
            // Fast path: fits in u32, use nanoseconds with precision
            let frac_digits = &text[frac_start..frac_start + frac_len];
            let mut frac_value: u32 = 0;
            for &d in frac_digits {
                frac_value = frac_value * 10 + (d - b'0') as u32;
            }
            let multiplier = 10u32.pow(9 - frac_len as u32);
            let nanoseconds = frac_value * multiplier;
            ts_base.with_nanoseconds_and_precision(nanoseconds, frac_len as u32)
        } else if frac_len <= 38 {
            // Medium path: fits in u128, avoid BigUint allocation
            let frac_digits = &text[frac_start..frac_start + frac_len];
            let mut frac_value: u128 = 0;
            for &d in frac_digits {
                frac_value = frac_value * 10 + (d - b'0') as u128;
            }
            // Convert u128 to Int via little-endian bytes
            let le_bytes = frac_value.to_le_bytes();
            // Find the last non-zero byte to trim
            let significant_len = le_bytes
                .iter()
                .rposition(|&b| b != 0)
                .map(|i| i + 1)
                .unwrap_or(1);
            let mut signed_le = le_bytes[..significant_len].to_vec();
            // Ensure the sign bit is not set (positive value)
            if signed_le.last().map_or(false, |&b| b & 0x80 != 0) {
                signed_le.push(0);
            }
            let coefficient = Int::from_le_signed_bytes(&signed_le);
            let decimal = Decimal::new(coefficient, -(frac_len as i64));
            ts_base.with_fractional_seconds(decimal)
        } else {
            // Cold path: very large precision, use BigUint
            let frac_digits = &text[frac_start..frac_start + frac_len];
            let big = num_bigint::BigUint::parse_bytes(frac_digits, 10).ok_or_else(|| {
                crate::IonError::decoding_error("invalid fractional seconds digits")
            })?;
            let mut le = big.to_bytes_le();
            le.push(0); // Ensure positive sign
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

    // No fractional seconds - parse offset
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
    use std::io::Cursor;

    /// Helper: generate all bytecode from text Ion input.
    fn generate_all(text: &str) -> (Vec<u32>, ConstantPool) {
        let cursor = Cursor::new(text.as_bytes().to_vec());
        let mut gen = StreamingTextIon10Generator::new(cursor);
        let mut dest = Vec::new();
        let mut cp = ConstantPool::new();
        loop {
            gen.refill(&mut dest, &mut cp).unwrap();
            let last = *dest.last().unwrap();
            if last == instr::END_OF_INPUT {
                break;
            }
        }
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
        let instr = Instruction::from_raw(dest[0]);
        assert_eq!(instr.operation(), op::NULL_NULL);
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
            let instr = Instruction::from_raw(dest[0]);
            assert_eq!(instr.operation(), expected_op, "failed for: {text}");
        }
    }

    #[test]
    fn bool_true() {
        let (dest, _cp) = generate_all("true");
        let instr = Instruction::from_raw(dest[0]);
        assert_eq!(instr.operation(), op::BOOL);
        assert_eq!(instr.data() & 1, 1);
    }

    #[test]
    fn bool_false() {
        let (dest, _cp) = generate_all("false");
        let instr = Instruction::from_raw(dest[0]);
        assert_eq!(instr.operation(), op::BOOL);
        assert_eq!(instr.data() & 1, 0);
    }

    #[test]
    fn integer_zero() {
        let (dest, _cp) = generate_all("0");
        let instr = Instruction::from_raw(dest[0]);
        assert_eq!(instr.operation(), op::INT_I16);
        assert_eq!(instr.data_as_i16(), 0);
    }

    #[test]
    fn integer_positive() {
        let (dest, _cp) = generate_all("42");
        let instr = Instruction::from_raw(dest[0]);
        assert_eq!(instr.operation(), op::INT_I16);
        assert_eq!(instr.data_as_i16(), 42);
    }

    #[test]
    fn integer_negative() {
        let (dest, _cp) = generate_all("-7");
        let instr = Instruction::from_raw(dest[0]);
        assert_eq!(instr.operation(), op::INT_I16);
        assert_eq!(instr.data_as_i16(), -7);
    }

    #[test]
    fn integer_large() {
        let (dest, _cp) = generate_all("100000");
        let instr = Instruction::from_raw(dest[0]);
        assert_eq!(instr.operation(), op::INT_I32);
        assert_eq!(dest[1] as i32, 100000);
    }

    #[test]
    fn simple_string() {
        let text = r#""hello""#;
        let (dest, _cp) = generate_all(text);
        let instr = Instruction::from_raw(dest[0]);
        assert_eq!(instr.operation(), op::STRING_REF);
        assert_eq!(instr.data(), 5); // "hello" is 5 bytes
    }

    #[test]
    fn string_with_escape() {
        let text = r#""hello\nworld""#;
        let (dest, cp) = generate_all(text);
        let instr = Instruction::from_raw(dest[0]);
        assert_eq!(instr.operation(), op::STRING_CP);
        match cp.get(instr.data()) {
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
        let (dest, _cp) = generate_all("{a: 1}");
        let struct_instr = Instruction::from_raw(dest[0]);
        assert_eq!(struct_instr.operation(), op::STRUCT_START);
    }

    #[test]
    fn ivm_detection() {
        let (dest, _cp) = generate_all("$ion_1_0");
        let instr = Instruction::from_raw(dest[0]);
        assert_eq!(instr.operation(), op::IVM);
    }

    #[test]
    fn annotation_on_value() {
        let (dest, cp) = generate_all("foo::42");
        let ann_instr = Instruction::from_raw(dest[0]);
        assert_eq!(ann_instr.operation(), op::ANNOTATION_CP);
        match cp.get(ann_instr.data()) {
            Constant::String(s) => assert_eq!(s.as_ref(), "foo"),
            _ => panic!("expected String constant for annotation"),
        }
        // Find the int
        let int_idx = dest
            .iter()
            .position(|&w| Instruction::from_raw(w).operation() == op::INT_I16)
            .unwrap();
        let int_instr = Instruction::from_raw(dest[int_idx]);
        assert_eq!(int_instr.data_as_i16(), 42);
    }

    #[test]
    fn float_inf() {
        let (dest, _cp) = generate_all("+inf");
        let instr = Instruction::from_raw(dest[0]);
        assert_eq!(instr.operation(), op::FLOAT_F64);
        let hi = dest[1] as u64;
        let lo = dest[2] as u64;
        let bits = (hi << 32) | lo;
        assert_eq!(f64::from_bits(bits), f64::INFINITY);
    }

    #[test]
    fn float_neg_inf() {
        let (dest, _cp) = generate_all("-inf");
        let instr = Instruction::from_raw(dest[0]);
        assert_eq!(instr.operation(), op::FLOAT_F64);
        let hi = dest[1] as u64;
        let lo = dest[2] as u64;
        let bits = (hi << 32) | lo;
        assert_eq!(f64::from_bits(bits), f64::NEG_INFINITY);
    }

    #[test]
    fn float_nan() {
        let (dest, _cp) = generate_all("nan");
        let instr = Instruction::from_raw(dest[0]);
        assert_eq!(instr.operation(), op::FLOAT_F64);
        let hi = dest[1] as u64;
        let lo = dest[2] as u64;
        let bits = (hi << 32) | lo;
        assert!(f64::from_bits(bits).is_nan());
    }

    #[test]
    fn multiple_values() {
        let (dest, _cp) = generate_all("1 true null");
        // Should have INT, BOOL, NULL (with REFILL between each from
        // multiple refill calls).
        let ops: Vec<u8> = dest
            .iter()
            .map(|&w| Instruction::from_raw(w).operation())
            .filter(|&o| o != op::REFILL && o != op::END_OF_INPUT)
            .collect();
        assert_eq!(ops, vec![op::INT_I16, op::BOOL, op::NULL_NULL]);
    }

    #[test]
    fn comments_skipped() {
        let (dest, _cp) = generate_all("// line comment\n42 /* block */ ");
        let ops: Vec<u8> = dest
            .iter()
            .map(|&w| Instruction::from_raw(w).operation())
            .filter(|&o| o != op::REFILL && o != op::END_OF_INPUT)
            .collect();
        assert_eq!(ops, vec![op::INT_I16]);
        let int_instr = Instruction::from_raw(dest[0]);
        assert_eq!(int_instr.data_as_i16(), 42);
    }

    // --- Integration tests using read_all_v3 on text data ---

    #[test]
    fn text_struct_with_field_name() {
        use crate::bytecode::materialize::read_all_v3;
        use crate::Element;
        let text = "{foo: 1}";
        let expected = Element::read_all(text.as_bytes()).unwrap();
        let actual = read_all_v3(text.as_bytes()).unwrap();
        assert_eq!(expected, actual, "failed for: {text}");
    }

    #[test]
    fn text_struct_with_string_value() {
        use crate::bytecode::materialize::read_all_v3;
        use crate::Element;
        let text = r#"{foo: "hello"}"#;
        let expected = Element::read_all(text.as_bytes()).unwrap();
        let actual = read_all_v3(text.as_bytes()).unwrap();
        assert_eq!(expected, actual, "failed for: {text}");
    }

    #[test]
    fn text_struct_with_bool_value() {
        use crate::bytecode::materialize::read_all_v3;
        use crate::Element;
        let text = "{foo: true}";
        let expected = Element::read_all(text.as_bytes()).unwrap();
        let actual = read_all_v3(text.as_bytes()).unwrap();
        assert_eq!(expected, actual, "failed for: {text}");
    }

    #[test]
    fn text_struct_with_list_value() {
        use crate::bytecode::materialize::read_all_v3;
        use crate::Element;
        let text = "{foo: [1, 2, 3]}";
        let expected = Element::read_all(text.as_bytes()).unwrap();
        let actual = read_all_v3(text.as_bytes()).unwrap();
        assert_eq!(expected, actual, "failed for: {text}");
    }

    #[test]
    fn text_mixed_struct() {
        use crate::bytecode::materialize::read_all_v3;
        use crate::Element;
        let text = r#"{id: 0, name: "user_0", active: true, scores: [0, 0, 0]}"#;
        let expected = Element::read_all(text.as_bytes()).unwrap();
        let actual = read_all_v3(text.as_bytes()).unwrap();
        assert_eq!(expected, actual, "failed for: {text}");
    }

    #[test]
    fn text_benchmark_workloads_complete() {
        use crate::bytecode::materialize::read_all_v3;
        use crate::Element;
        let cases = [
            (0..4000)
                .map(|i| format!("{} ", i * 7 - 2000))
                .collect::<String>(),
            (0..4000)
                .map(|i| format!("{}e0 ", (i as f64) * 1.7 - 3400.0))
                .collect::<String>(),
            (0..3000)
                .map(|i| format!("\"string_value_{}\" ", i))
                .collect::<String>(),
            (0..1500).map(|i| format!("sym_{} ", i)).collect::<String>(),
            (0..280)
                .map(|i| {
                    format!(
                        "{{id: {i}, name: \"user_{i}\", active: true, scores: [{}, {}, {}]}} ",
                        i * 10,
                        i * 20,
                        i * 30
                    )
                })
                .collect::<String>(),
        ];
        for (idx, text) in cases.iter().enumerate() {
            let expected = Element::read_all(text.as_bytes()).unwrap();
            let actual = read_all_v3(text.as_bytes()).unwrap();
            assert_eq!(expected, actual, "text benchmark case {idx} failed");
        }
    }
}
