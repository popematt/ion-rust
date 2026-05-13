use std::io;
use std::io::Write;

/// Semantic tokens emitted by the Ion text writer.
///
/// Each variant identifies what kind of Ion syntax a span of bytes represents.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    /// Other structural punctuation: `,`
    Delimiter,
    /// Ion version markers: `$ion_1_0`, `$ion_1_1`
    VersionMarker,
    Comment,
}

/// Receives semantically-tagged byte spans during Ion text writing.
///
/// The blanket implementation for all [`Write`] types discards the markers and writes bytes
/// directly, giving zero-cost passthrough for plain output. Custom renderers (e.g., ANSI
/// terminal colors, HTML `<span>` tags) wrap a [`Write`] impl using the newtype pattern and
/// provide their own [`Render`] implementation.
pub trait Render<D> {
    /// Write bytes that represent the semantic token indicated by `marker`.
    fn write_marked(&mut self, bytes: &[u8], marker: D) -> io::Result<usize>;

    /// Write bytes with no semantic significance (whitespace, indentation).
    fn write_raw(&mut self, bytes: &[u8]) -> io::Result<usize>;

    /// Flush any buffered output. The default implementation is a no-op.
    fn flush(&mut self) -> io::Result<()>;
}

impl<W: Write, D> Render<D> for W {
    #[inline(always)]
    fn write_marked(&mut self, bytes: &[u8], _marker: D) -> io::Result<usize> {
        self.write(bytes)
    }

    #[inline(always)]
    fn write_raw(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.write(bytes)
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
    use crate::symbol_ref::AsSymbolRef;
    use crate::{ion_list, ion_struct, IntoAnnotatedElement, IonResult};

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

    impl Render<IonToken> for TestRenderer {
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


    /// A test renderer that records what tokens were emitted.
    struct TestHtmlRenderer<W>(W);

    impl<W> TestHtmlRenderer<W> where W: Write {
        fn wrap(inner: W) -> Self {
            Self(inner)
        }
    }

    impl<W> Render<IonToken> for TestHtmlRenderer<W> where W: Write {
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
                IonToken::ContainerStart => ("<span class='container-delimiter'>", "</span><span class='container-content'>"),
                IonToken::ContainerEnd => ("</span><span class='container-delimiter'>", "</span>"),
                IonToken::Delimiter => ("<span class='delimiter'>", "</span>"),
                IonToken::VersionMarker => ("<span class='ivm'>", "</span>"),
                IonToken::Comment => ("<span class='comment'>", "</span>"),
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
            whitespace_config:
            &crate::text::whitespace_config::COMPACT_WHITESPACE_CONFIG,
        };

        writer.write(42)?;
        writer.write(true)?;
        writer.write("hello")?;
        writer.write(ion_struct! {
            "foo": 1,
            "bar": ion_list![1, 2, 3],
        }.with_annotations(["abc"]))?;
        writer.write("foo".as_symbol_ref())?;

        let renderer = writer.output;

        let text = String::from_utf8(renderer.0).unwrap();
        assert_eq!(text, r#"<span class='int'>42</span> <span class='bool'>true</span> <span class='string'>"hello"</span> <span class='annotation'>abc::</span><span class='container-delimiter'>{</span><span class='container-content'><span class='field-name'>foo:</span> <span class='int'>1</span>, <span class='field-name'>bar:</span> <span class='container-delimiter'>[</span><span class='container-content'><span class='int'>1</span>, <span class='int'>2</span>, <span class='int'>3</span>, </span><span class='container-delimiter'>]</span>, </span><span class='container-delimiter'>}</span> <span class='symbol'>foo</span> "#);
        Ok(())
    }


    #[test]
    fn test_renderer_receives_tokens() -> IonResult<()> {
        let renderer = TestRenderer::new();
        let mut writer = LazyRawTextWriter_1_0 {
            output: renderer,
            whitespace_config:
                &crate::text::whitespace_config::COMPACT_WHITESPACE_CONFIG,
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
        let text = String::from_utf8(renderer.buf).unwrap();
        assert_eq!(text, "42 true \"hello\" foo ");
        Ok(())
    }

    #[test]
    fn test_renderer_struct_tokens() -> IonResult<()> {
        use crate::lazy::encoder::value_writer::{StructWriter, ValueWriter};

        let renderer = TestRenderer::new();
        let mut writer = LazyRawTextWriter_1_0 {
            output: renderer,
            whitespace_config:
                &crate::text::whitespace_config::COMPACT_WHITESPACE_CONFIG,
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
}

