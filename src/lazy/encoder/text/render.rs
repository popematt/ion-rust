use std::fmt;
use std::io;
use std::io::Write;

/// Semantic tokens emitted by the Ion text writer.
///
/// Each variant identifies what kind of Ion syntax a span of bytes represents.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum IonToken {
    Null,
    Bool,
    Int,
    Float,
    Decimal,
    Timestamp,
    String,
    Symbol,
    Clob,
    Blob,
    /// Includes `:`
    FieldName,
    /// Includes `::`
    Annotation,
    /// Opening delimiter of a container: `[`, `{`, `(`
    ContainerStart,
    /// Closing delimiter of a container: `]`, `}`, `)`
    ContainerEnd,
    /// Ion version markers: `$ion_1_0`, `$ion_1_1`
    VersionMarker,
}

/// Receives semantically-tagged byte spans during Ion text writing.
///
/// The blanket implementation for all [`Write`] types discards the markers and writes bytes
/// directly, giving zero-cost passthrough for plain output.
///
/// To create a custom renderer (e.g., ANSI terminal colors, HTML `<span>` tags), define a
/// newtype wrapping a [`Write`] impl and implement [`RenderedWrite`] on it. The newtype must NOT
/// implement [`Write`] itself — the blanket impl covers all `Write` types, so a type that
/// implements both `Write` and `Render` would conflict. The newtype pattern is the intended
/// mechanism for providing custom rendering behavior.
pub trait RenderedWrite<D> {
    /// Write bytes that represent the semantic token indicated by `marker`.
    fn write_marked(&mut self, bytes: &[u8], marker: D) -> io::Result<usize>;

    /// Write bytes with no semantic significance (whitespace, indentation).
    fn write_raw(&mut self, bytes: &[u8]) -> io::Result<usize>;

    /// Write multiple byte chunks as a single marked token. The default implementation
    /// collects all chunks into a `Vec` and forwards to [`write_marked`](Self::write_marked),
    /// allocating on every call. Custom renderers should override this to stream
    /// prefix/chunks/suffix directly to their inner writer without buffering.
    fn write_chunked_marked<'i, I>(&mut self, chunks: I, marker: D) -> io::Result<()>
    where
        I: Iterator<Item = &'i [u8]>,
    {
        let mut buf = Vec::new();
        chunks.for_each(|chunk| buf.extend_from_slice(chunk));
        self.write_marked(&buf, marker)?;
        Ok(())
    }

    fn write_chunked_raw<'i, I>(&mut self, chunks: I) -> io::Result<()>
    where
        I: Iterator<Item = &'i [u8]>,
    {
        for chunk in chunks {
            self.write_raw(chunk)?;
        }
        Ok(())
    }

    /// Format arguments directly as a marked token. For the blanket `Write` impl this
    /// formats directly into the output without intermediate allocation. Custom renderers
    /// get a default that buffers into a `Vec` and forwards to `write_marked`.
    fn write_fmt_marked(&mut self, args: fmt::Arguments<'_>, marker: D) -> io::Result<()>
    where
        D: Copy,
    {
        let mut buf = Vec::new();
        buf.write_fmt(args)?;
        self.write_marked(&buf, marker)?;
        Ok(())
    }

    /// Format arguments directly as raw (untagged) output. For the blanket `Write` impl this
    /// formats directly into the output without intermediate allocation. Custom renderers
    /// get a default that buffers into a `Vec` and forwards to `write_raw`.
    fn write_fmt_raw(&mut self, args: fmt::Arguments<'_>) -> io::Result<()> {
        let mut buf = Vec::new();
        buf.write_fmt(args)?;
        self.write_raw(&buf)?;
        Ok(())
    }

    /// Flush any buffered output.
    fn flush(&mut self) -> io::Result<()>;
}

impl<W: Write, D: Copy> RenderedWrite<D> for W {
    #[inline(always)]
    fn write_marked(&mut self, bytes: &[u8], _marker: D) -> io::Result<usize> {
        self.write(bytes)
    }

    #[inline(always)]
    fn write_raw(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.write(bytes)
    }

    #[inline(always)]
    fn write_chunked_marked<'i, I>(&mut self, chunks: I, _marker: D) -> io::Result<()>
    where
        I: Iterator<Item = &'i [u8]>,
    {
        for chunk in chunks {
            self.write_all(chunk)?;
        }
        Ok(())
    }

    #[inline(always)]
    fn write_fmt_marked(&mut self, args: fmt::Arguments<'_>, _marker: D) -> io::Result<()> {
        Write::write_fmt(self, args)
    }

    #[inline(always)]
    fn write_fmt_raw(&mut self, args: fmt::Arguments<'_>) -> io::Result<()> {
        Write::write_fmt(self, args)
    }

    #[inline(always)]
    fn flush(&mut self) -> io::Result<()> {
        Write::flush(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lazy::encoder::text::v1_0::writer::LazyRawTextWriter_1_0;
    use crate::result::IonFailure;
    use crate::symbol_ref::AsSymbolRef;
    use crate::{ion_list, ion_sexp, ion_struct, IntoAnnotatedElement, IonError, IonResult, IonType, Value};

    /// A test renderer that records what tokens were emitted.
    struct TestRenderer {
        buf: Vec<u8>,
        tokens: Vec<(String, IonToken)>,
    }

    impl TestRenderer {
        fn new() -> Self {
            Self {
                buf: Vec::new(),
                tokens: Vec::new(),
            }
        }
    }

    impl RenderedWrite<IonToken> for TestRenderer {
        fn write_marked(&mut self, bytes: &[u8], marker: IonToken) -> io::Result<usize> {
            self.tokens
                .push((String::from_utf8_lossy(bytes).into_owned(), marker));
            self.buf.extend_from_slice(bytes);
            Ok(bytes.len())
        }

        fn write_raw(&mut self, bytes: &[u8]) -> io::Result<usize> {
            self.buf.extend_from_slice(bytes);
            Ok(bytes.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    /// A test renderer that wraps tokens in HTML span elements.
    struct TestHtmlRenderer<W>(W);

    impl<W> TestHtmlRenderer<W>
    where
        W: Write,
    {
        fn wrap(inner: W) -> Self {
            Self(inner)
        }
    }

    impl<W> RenderedWrite<IonToken> for TestHtmlRenderer<W>
    where
        W: Write,
    {
        fn write_marked(&mut self, bytes: &[u8], marker: IonToken) -> io::Result<usize> {
            let (pre, post) = match marker {
                IonToken::Null => ("<span class='null'>", "</span>"),
                IonToken::Bool => ("<span class='bool'>", "</span>"),
                IonToken::Int => ("<span class='int'>", "</span>"),
                IonToken::Float => ("<span class='float'>", "</span>"),
                IonToken::Decimal => ("<span class='decimal'>", "</span>"),
                IonToken::Timestamp => ("<span class='timestamp'>", "</span>"),
                IonToken::String => ("<span class='string'>", "</span>"),
                IonToken::Symbol => ("<span class='symbol'>", "</span>"),
                IonToken::Clob => ("<span class='clob'>", "</span>"),
                IonToken::Blob => ("<span class='blob'>", "</span>"),
                IonToken::FieldName => ("<span class='field-name'>", "</span>"),
                IonToken::Annotation => ("<span class='annotation'>", "</span>"),
                IonToken::ContainerStart => (
                    "<span class='container-delimiter'>",
                    "</span><span class='container-content'>",
                ),
                IonToken::ContainerEnd => ("</span><span class='container-delimiter'>", "</span>"),
                IonToken::VersionMarker => ("<span class='ivm'>", "</span>"),
            };

            self.0.write_all(pre.as_bytes())?;
            self.0.write_all(bytes)?;
            self.0.write_all(post.as_bytes())?;
            Ok(bytes.len())
        }

        fn write_raw(&mut self, bytes: &[u8]) -> io::Result<usize> {
            self.0.write(bytes)
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn test_renderer() -> IonResult<()> {
        let renderer = TestHtmlRenderer::wrap(Vec::new());
        let mut writer = LazyRawTextWriter_1_0 {
            output: renderer,
            whitespace_config: &crate::text::whitespace_config::COMPACT_WHITESPACE_CONFIG,
        };

        writer.write(42)?;
        writer.write(true)?;
        writer.write("hello")?;
        writer.write(
            ion_struct! {
                "a": Value::Null(IonType::Null),
                "b": true,
                "c": 1,
                "d": 1e0,
                "e": ion_list![1, 2, 3],
                "f": "abcde".as_symbol_ref(),
                "g": "Hello world!",
                "h": ion_sexp!(
                    "a".as_symbol_ref()
                    "+".as_symbol_ref()
                    "b".as_symbol_ref()
                ),
            }
            .with_annotations(["abc"]),
        )?;
        writer.write("foo".as_symbol_ref())?;

        let renderer = writer.output;

        let text =
            String::from_utf8(renderer.0).map_err(|e| IonError::encoding_error(e.to_string()))?;
        assert_eq!(
            text,
            r#"<span class='int'>42</span> <span class='bool'>true</span> <span class='string'>"hello"</span> <span class='annotation'>abc::</span><span class='container-delimiter'>{</span><span class='container-content'><span class='field-name'>a:</span> <span class='null'>null</span>, <span class='field-name'>b:</span> <span class='bool'>true</span>, <span class='field-name'>c:</span> <span class='int'>1</span>, <span class='field-name'>d:</span> <span class='float'>1e0</span>, <span class='field-name'>e:</span> <span class='container-delimiter'>[</span><span class='container-content'><span class='int'>1</span>, <span class='int'>2</span>, <span class='int'>3</span>, </span><span class='container-delimiter'>]</span>, <span class='field-name'>f:</span> <span class='symbol'>abcde</span>, <span class='field-name'>g:</span> <span class='string'>"Hello world!"</span>, <span class='field-name'>h:</span> <span class='container-delimiter'>(</span><span class='container-content'><span class='symbol'>a</span> <span class='symbol'>'+'</span> <span class='symbol'>b</span> </span><span class='container-delimiter'>)</span>, </span><span class='container-delimiter'>}</span> <span class='symbol'>foo</span> "#
        );
        Ok(())
    }

    #[test]
    fn test_renderer_receives_tokens() -> IonResult<()> {
        let renderer = TestRenderer::new();
        let mut writer = LazyRawTextWriter_1_0 {
            output: renderer,
            whitespace_config: &crate::text::whitespace_config::COMPACT_WHITESPACE_CONFIG,
        };

        writer.write(42)?;
        writer.write(true)?;
        writer.write("hello")?;
        writer.write("foo".as_symbol_ref())?;

        let renderer = writer.output;
        // Verify the correct tokens were emitted
        assert_eq!(renderer.tokens[0], ("42".to_string(), IonToken::Int));
        assert_eq!(renderer.tokens[1], ("true".to_string(), IonToken::Bool));
        assert_eq!(
            renderer.tokens[2],
            ("\"hello\"".to_string(), IonToken::String)
        );
        assert_eq!(renderer.tokens[3], ("foo".to_string(), IonToken::Symbol));

        // Verify the bytes are correct Ion text
        let text =
            String::from_utf8(renderer.buf).map_err(|e| IonError::encoding_error(e.to_string()))?;
        assert_eq!(text, "42 true \"hello\" foo ");
        Ok(())
    }

    #[test]
    fn test_renderer_struct_tokens() -> IonResult<()> {
        use crate::lazy::encoder::value_writer::{StructWriter, ValueWriter};

        let renderer = TestRenderer::new();
        let mut writer = LazyRawTextWriter_1_0 {
            output: renderer,
            whitespace_config: &crate::text::whitespace_config::COMPACT_WHITESPACE_CONFIG,
        };

        // Use the ValueWriter API directly to write a struct
        let value_writer = crate::lazy::encoder::text::v1_0::value_writer::TextValueWriter_1_0::new(
            &mut writer,
            0,
            "",
            crate::types::ParentType::TopLevel,
        );
        let mut struct_writer = value_writer.struct_writer()?;
        struct_writer.write("name", "Alice")?;
        struct_writer.write("age", 30)?;
        struct_writer.close()?;

        let renderer = writer.output;
        // Find field name tokens
        let field_names: Vec<_> = renderer
            .tokens
            .iter()
            .filter(|(_, t)| *t == IonToken::FieldName)
            .map(|(s, _)| s.as_str())
            .collect();
        assert_eq!(field_names, vec!["name:", "age:"]);

        let starts: Vec<_> = renderer
            .tokens
            .iter()
            .filter(|(_, t)| *t == IonToken::ContainerStart)
            .map(|(s, _)| s.as_str())
            .collect();
        assert_eq!(starts, vec!["{"]);

        let ends: Vec<_> = renderer
            .tokens
            .iter()
            .filter(|(_, t)| *t == IonToken::ContainerEnd)
            .map(|(s, _)| s.as_str())
            .collect();
        assert_eq!(ends, vec!["}"]);

        Ok(())
    }

    #[test]
    fn test_renderer_escaped_and_quoted_tokens() -> IonResult<()> {
        use crate::lazy::encoder::annotate::Annotatable;
        use crate::lazy::encoder::value_writer::{StructWriter, ValueWriter};

        let renderer = TestRenderer::new();
        let mut writer = LazyRawTextWriter_1_0 {
            output: renderer,
            whitespace_config: &crate::text::whitespace_config::COMPACT_WHITESPACE_CONFIG,
        };

        // String with escape characters
        writer.write("line\nbreak")?;
        // Symbol that requires quoting (keyword)
        writer.write("true".as_symbol_ref())?;
        // Symbol that requires quoting (resembles symbol ID)
        writer.write("$99".as_symbol_ref())?;
        // Symbol that requires quoting (contains space)
        writer.write("hello world".as_symbol_ref())?;
        // Annotated value with a keyword annotation
        writer.write(42.annotated_with(["null"]))?;

        let renderer = &writer.output;

        // String should include escape sequence
        assert_eq!(
            renderer.tokens[0],
            ("\"line\\nbreak\"".to_string(), IonToken::String)
        );
        // Keywords are quoted
        assert_eq!(renderer.tokens[1], ("'true'".to_string(), IonToken::Symbol));
        // Symbol-ID-lookalikes are quoted
        assert_eq!(renderer.tokens[2], ("'$99'".to_string(), IonToken::Symbol));
        // Non-identifiers are quoted with escaping
        assert_eq!(
            renderer.tokens[3],
            ("'hello world'".to_string(), IonToken::Symbol)
        );
        // Keyword annotation is quoted and includes ::
        assert_eq!(
            renderer.tokens[4],
            ("'null'::".to_string(), IonToken::Annotation)
        );

        Ok(())
    }

    #[test]
    fn test_renderer_quoted_field_names() -> IonResult<()> {
        use crate::lazy::encoder::value_writer::{StructWriter, ValueWriter};

        let renderer = TestRenderer::new();
        let mut writer = LazyRawTextWriter_1_0 {
            output: renderer,
            whitespace_config: &crate::text::whitespace_config::COMPACT_WHITESPACE_CONFIG,
        };

        let value_writer = crate::lazy::encoder::text::v1_0::value_writer::TextValueWriter_1_0::new(
            &mut writer,
            0,
            "",
            crate::types::ParentType::TopLevel,
        );
        let mut struct_writer = value_writer.struct_writer()?;
        // Field name that is a keyword (needs quoting)
        struct_writer.write("null", 1)?;
        // Field name with special characters (needs quoting + escaping)
        struct_writer.write("line\nbreak", 2)?;
        struct_writer.close()?;

        let renderer = writer.output;
        let field_names: Vec<_> = renderer
            .tokens
            .iter()
            .filter(|(_, t)| *t == IonToken::FieldName)
            .map(|(s, _)| s.as_str())
            .collect();
        assert_eq!(field_names, vec!["'null':", "'line\\nbreak':"]);

        Ok(())
    }
}
