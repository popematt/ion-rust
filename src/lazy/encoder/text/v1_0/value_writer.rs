use crate::lazy::text::raw::v1_1::reader::MacroIdLike;
use std::fmt::Formatter;
use std::io::Write;

use delegate::delegate;

use crate::lazy::encoder::annotation_seq::{AnnotationSeq, AnnotationsVec};
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoder::text::render::{IonToken, RenderedWrite};
use crate::lazy::encoder::text::v1_0::writer::LazyRawTextWriter_1_0;
use crate::lazy::encoder::value_writer::internal::{FieldEncoder, MakeValueWriter};
use crate::lazy::encoder::value_writer::{
    delegate_value_writer_to, AnnotatableWriter, SequenceWriter, StructWriter, ValueWriter,
};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::never::Never;
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::result::IonFailure;
use crate::text::text_formatter::{token_needs_quoting, EscapedIonText, FmtValueFormatter};
use crate::text::whitespace_config::WhitespaceConfig;
use crate::types::{ContainerType, ParentType};
use crate::{
    v1_0, ContextWriter, Decimal, Encoding, Int, IonResult, IonType, RawSymbolRef, Timestamp,
    ValueWriterConfig,
};

pub struct TextValueWriter_1_0<'value, W: RenderedWrite<IonToken>> {
    pub(crate) writer: &'value mut LazyRawTextWriter_1_0<W>,
    pub(crate) depth: usize,
    value_delimiter: &'static str,
    // This allows us to detect cases where a value writer is being used inside a struct
    // (i.e. following an indented field name) which is the only time we don't write
    // indentation before the value.
    pub(crate) parent_type: ParentType,
    // If `true`, this value had annotations and so should not write its own indentation.
    pub(crate) has_annotations: bool,
}

impl<'value, W: RenderedWrite<IonToken> + 'value> TextValueWriter_1_0<'value, W> {
    pub(crate) fn new(
        writer: &'value mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        delimiter: &'static str,
        parent_type: ParentType,
    ) -> Self {
        Self {
            writer,
            depth,
            value_delimiter: delimiter,
            parent_type,
            has_annotations: false,
        }
    }

    /// Writes the `indentation` string set in the whitespace config to output `depth` times.
    fn write_indentation(&mut self) -> IonResult<()> {
        let indentation = self.whitespace_config().indentation;
        if self.parent_type == ParentType::Struct || self.has_annotations {
            // If this value is part of a struct field, the indentation was written before the
            // field name.
            // If this value has annotations, the indentation was written before the annotations.
            // Either way, there's nothing to do here.
            return Ok(());
        }
        if !indentation.is_empty() {
            for _ in 0..self.depth {
                self.output().write_raw(indentation.as_bytes())?;
            }
        }
        Ok(())
    }
}

impl<W: RenderedWrite<IonToken>> TextValueWriter_1_0<'_, W> {
    fn output(&mut self) -> &mut W {
        &mut self.writer.output
    }

    fn whitespace_config(&self) -> &WhitespaceConfig {
        self.writer.whitespace_config
    }

    pub fn delimiter(&self) -> &'static str {
        self.value_delimiter
    }

    #[inline]
    fn write_delimiter_text(&mut self) -> IonResult<()> {
        let space_between = match self.depth {
            0 => self.whitespace_config().space_between_top_level_values,
            _ => self.whitespace_config().space_between_nested_values,
        };
        let value_delimiter = self.value_delimiter;
        self.output()
            .write_fmt_raw(format_args!("{value_delimiter}{space_between}"))?;
        Ok(())
    }
}

pub struct TextAnnotatedValueWriter_1_0<'value, W: RenderedWrite<IonToken>> {
    pub(crate) annotations: AnnotationsVec<'value>,
    pub(crate) value_writer: TextValueWriter_1_0<'value, W>,
}

impl<'value, W: RenderedWrite<IonToken>> TextAnnotatedValueWriter_1_0<'value, W> {
    fn encode_annotations(mut self) -> IonResult<TextValueWriter_1_0<'value, W>> {
        // The inner ValueWriter knows the indentation depth; we'll have it write the indentation
        // before we write the value.
        self.value_writer.write_indentation()?;
        // After indenting, we set the `has_annotations` flag to `true` so the value won't write
        // indentation a second time.
        self.value_writer.has_annotations = !self.annotations.is_empty();
        let output = &mut self.value_writer.writer.output;
        for annotation in self.annotations {
            match annotation.as_raw_symbol_ref() {
                RawSymbolRef::Text(text) if !token_needs_quoting(text) => {
                    output.write_chunked_marked(
                        [text.as_bytes(), b"::"].into_iter(),
                        IonToken::Annotation,
                    )?;
                }
                RawSymbolRef::Text(text) => {
                    let chunks = std::iter::once(&b"'"[..])
                        .chain(EscapedIonText::wrap(text))
                        .chain(std::iter::once(&b"'::"[..]));
                    output.write_chunked_marked(chunks, IonToken::Annotation)?;
                }
                RawSymbolRef::SymbolId(sid) => {
                    output.write_fmt_marked(format_args!("${sid}::"), IonToken::Annotation)?;
                }
                RawSymbolRef::SystemSymbol_1_1(_symbol) => {
                    return IonResult::encoding_error(
                        "the Ion 1.0 text writer does not support encoding Ion 1.1 system symbols",
                    )
                }
            }
        }

        Ok(self.value_writer)
    }
}

impl<'value, W: RenderedWrite<IonToken> + 'value> Sealed
    for TextAnnotatedValueWriter_1_0<'value, W>
{
}

impl<W: RenderedWrite<IonToken>> Sealed for TextValueWriter_1_0<'_, W> {}

/// Helper type that is home to information and behavior common to the list writer, s-expression writer,
/// and struct writer.
pub(crate) struct TextContainerWriter_1_0<'a, W: RenderedWrite<IonToken>> {
    // Holds a reference to the output stream and a whitespace config
    pub(crate) writer: &'a mut LazyRawTextWriter_1_0<W>,
    // The depth at which this container's child values appear. This value is used for formatting
    // indentation where applicable.
    pub(crate) depth: usize,
    // Tracks whether the `end()` method was called (thereby emitting a closing delimiter) before
    // this value was dropped. This scenario is a contract violation and results in a panic.
    has_been_closed: bool,
    // The Ion type of the container using this TextContainerWriter_1_0. This value is only
    // used for more informative error messages.
    pub(crate) container_type: ContainerType,
    value_delimiter: &'static str,
    trailing_delimiter: &'static str,
}

impl<'a, W: RenderedWrite<IonToken>> TextContainerWriter_1_0<'a, W> {
    pub fn new(
        writer: &'a mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        parent_type: ParentType,
        container_type: ContainerType,
        opening_delimiter: &str,
        value_delimiter: &'static str,
        trailing_delimiter: &'static str,
    ) -> IonResult<Self> {
        let mut container_writer = Self {
            writer,
            depth,
            container_type,
            has_been_closed: false,
            value_delimiter,
            trailing_delimiter,
        };
        if parent_type != ParentType::Struct {
            container_writer.write_indentation(depth)?;
        }
        let space_after_container_start = container_writer
            .writer
            .whitespace_config
            .space_after_container_start;
        container_writer
            .writer
            .output
            .write_marked(opening_delimiter.as_bytes(), IonToken::ContainerStart)?;
        container_writer
            .writer
            .output
            .write_raw(space_after_container_start.as_bytes())?;
        Ok(container_writer)
    }

    /// Writes the `indentation` string set in the whitespace config to output `depth` times.
    fn write_indentation(&mut self, depth: usize) -> IonResult<()> {
        let indentation = self.whitespace_config().indentation;
        if !indentation.is_empty() {
            for _ in 0..depth {
                self.output().write_raw(indentation.as_bytes())?;
            }
        }
        Ok(())
    }

    /// Writes the provided value to output using its implementation of `WriteAsIon`, then writes
    /// the whitespace config's `space_between_nested_values`.
    fn write_value<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.write_indentation(self.depth)?;
        value.write_as_ion(self.value_writer())?;
        Ok(self)
    }

    /// Finalizes the container, preventing further values from being written.
    pub fn close(mut self, closing_delimiter: &str) -> IonResult<()> {
        let space_between = match self.depth {
            0 => self.whitespace_config().space_between_top_level_values,
            _ => self.whitespace_config().space_between_nested_values,
        };
        let trailing_delimiter = self.trailing_delimiter;
        self.write_indentation(self.depth)?;
        self.output()
            .write_marked(closing_delimiter.as_bytes(), IonToken::ContainerEnd)?;
        self.output()
            .write_fmt_raw(format_args!("{trailing_delimiter}{space_between}"))?;
        self.has_been_closed = true;
        Ok(())
    }

    fn output(&mut self) -> &mut W {
        &mut self.writer.output
    }

    fn whitespace_config(&self) -> &WhitespaceConfig {
        self.writer.whitespace_config
    }

    #[inline]
    pub fn value_writer(&mut self) -> TextValueWriter_1_0<'_, W> {
        TextValueWriter_1_0 {
            writer: self.writer,
            depth: self.depth + 1,
            value_delimiter: self.value_delimiter,
            parent_type: self.container_type.into(),
            has_annotations: false,
        }
    }
}

/// Writes Ion 1.0 lists and implements the `SequenceWriter` trait.
pub struct TextListWriter_1_0<'top, W: RenderedWrite<IonToken>> {
    container_writer: TextContainerWriter_1_0<'top, W>,
}

impl<'top, W: RenderedWrite<IonToken>> TextListWriter_1_0<'top, W> {
    pub(crate) fn new(
        writer: &'top mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        parent_type: ParentType,
        trailing_delimiter: &'static str,
    ) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(
            writer,
            depth,
            parent_type,
            ContainerType::List,
            "[",
            ",",
            trailing_delimiter,
        )?;
        Ok(Self { container_writer })
    }

    /// Writes the provided data as a nested value.
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.container_writer.write_value(value)?;
        Ok(self)
    }

    /// Finalizes the list, preventing further values from being written.
    pub fn end(self) -> IonResult<()> {
        self.container_writer.close("]")?;
        Ok(())
    }
}

impl<W: RenderedWrite<IonToken>> ContextWriter for TextListWriter_1_0<'_, W> {
    type NestedValueWriter<'a>
        = TextValueWriter_1_0<'a, W>
    where
        Self: 'a;
}

impl<W: RenderedWrite<IonToken>> MakeValueWriter for TextListWriter_1_0<'_, W> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        self.container_writer.value_writer()
    }
}

impl<W: RenderedWrite<IonToken>> SequenceWriter for TextListWriter_1_0<'_, W> {
    type Resources = ();

    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.write(value)
    }

    fn close(self) -> IonResult<Self::Resources> {
        self.end()
    }
}

/// Incrementally encodes a potentially heterogeneously typed Ion s-expression.
pub struct TextSExpWriter_1_0<'a, W: RenderedWrite<IonToken>> {
    container_writer: TextContainerWriter_1_0<'a, W>,
}

impl<'a, W: RenderedWrite<IonToken>> TextSExpWriter_1_0<'a, W> {
    pub(crate) fn new(
        writer: &'a mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        parent_type: ParentType,
        trailing_delimiter: &'static str,
    ) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(
            writer,
            depth,
            parent_type,
            ContainerType::SExp,
            "(",
            "",
            trailing_delimiter,
        )?;
        Ok(Self { container_writer })
    }

    /// Writes the provided data as a nested value.
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.container_writer.write_value(value)?;
        Ok(self)
    }

    /// Finalizes the sexp, preventing further values from being written.
    pub fn end(self) -> IonResult<()> {
        self.container_writer.close(")")?;
        Ok(())
    }
}

impl<W: RenderedWrite<IonToken>> ContextWriter for TextSExpWriter_1_0<'_, W> {
    type NestedValueWriter<'a>
        = TextValueWriter_1_0<'a, W>
    where
        Self: 'a;
}

impl<W: RenderedWrite<IonToken>> MakeValueWriter for TextSExpWriter_1_0<'_, W> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        self.container_writer.value_writer()
    }
}

impl<W: RenderedWrite<IonToken>> SequenceWriter for TextSExpWriter_1_0<'_, W> {
    type Resources = ();

    delegate! {
        to self {
            fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self>;
        }
    }

    fn close(self) -> IonResult<Self::Resources> {
        self.end()
    }
}

/// Incrementally encodes an Ion struct.
pub struct TextStructWriter_1_0<'a, W: RenderedWrite<IonToken>> {
    container_writer: TextContainerWriter_1_0<'a, W>,
}

impl<'a, W: RenderedWrite<IonToken>> TextStructWriter_1_0<'a, W> {
    pub(crate) fn new(
        writer: &'a mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        parent_type: ParentType,
        trailing_delimiter: &'static str,
    ) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(
            writer,
            depth,
            parent_type,
            ContainerType::Struct,
            "{",
            ",",
            trailing_delimiter,
        )?;
        Ok(Self { container_writer })
    }

    pub fn end(self) -> IonResult<()> {
        self.container_writer.close("}")?;
        Ok(())
    }
}

impl<W: RenderedWrite<IonToken>> FieldEncoder for TextStructWriter_1_0<'_, W> {
    fn encode_field_name(&mut self, name: impl AsRawSymbolRef) -> IonResult<()> {
        // Leading indentation for the current depth
        self.container_writer
            .write_indentation(self.container_writer.depth + 1)?;
        // Write the field name including `:`
        match name.as_raw_symbol_ref() {
            RawSymbolRef::SymbolId(sid) => {
                self.container_writer
                    .output()
                    .write_fmt_marked(format_args!("${sid}:"), IonToken::FieldName)?;
            }
            RawSymbolRef::SystemSymbol_1_1(symbol) => {
                self.container_writer.output().write_chunked_marked(
                    [symbol.text().as_bytes(), b":"].into_iter(),
                    IonToken::FieldName,
                )?;
            }
            RawSymbolRef::Text(text) if !token_needs_quoting(text) => {
                self.container_writer.output().write_chunked_marked(
                    [text.as_bytes(), b":"].into_iter(),
                    IonToken::FieldName,
                )?;
            }
            RawSymbolRef::Text(text) => {
                let chunks = std::iter::once(&b"'"[..])
                    .chain(EscapedIonText::wrap(text))
                    .chain(std::iter::once(&b"':"[..]));
                self.container_writer
                    .output()
                    .write_chunked_marked(chunks, IonToken::FieldName)?;
            }
        }
        let space_after_field_name = self
            .container_writer
            .whitespace_config()
            .space_after_field_name;
        // Write configured trailing whitespace after the field name
        self.container_writer
            .output()
            .write_raw(space_after_field_name.as_bytes())?;
        Ok(())
    }
}

impl<W: RenderedWrite<IonToken>> ContextWriter for TextStructWriter_1_0<'_, W> {
    type NestedValueWriter<'a>
        = TextValueWriter_1_0<'a, W>
    where
        Self: 'a;
}

impl<W: RenderedWrite<IonToken>> MakeValueWriter for TextStructWriter_1_0<'_, W> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        TextValueWriter_1_0 {
            writer: self.container_writer.writer,
            depth: self.container_writer.depth + 1,
            value_delimiter: ",",
            parent_type: ParentType::Struct,
            has_annotations: false,
        }
    }
}

impl<W: RenderedWrite<IonToken>> StructWriter for TextStructWriter_1_0<'_, W> {
    fn close(self) -> IonResult<()> {
        self.end()
    }

    fn config(&self) -> ValueWriterConfig {
        v1_0::Text::default_value_writer_config()
    }
}

impl<'value, W: RenderedWrite<IonToken> + 'value> AnnotatableWriter
    for TextAnnotatedValueWriter_1_0<'value, W>
{
    type AnnotatedValueWriter<'a>
        = TextAnnotatedValueWriter_1_0<'a, W>
    where
        Self: 'a;

    fn with_annotations<'a>(
        self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        Ok(TextAnnotatedValueWriter_1_0 {
            annotations: annotations.into_annotations_vec(),
            value_writer: self.value_writer,
        })
    }
}

impl<'value, W: RenderedWrite<IonToken> + 'value> ValueWriter
    for TextAnnotatedValueWriter_1_0<'value, W>
{
    type ListWriter = TextListWriter_1_0<'value, W>;
    type SExpWriter = TextSExpWriter_1_0<'value, W>;
    type StructWriter = TextStructWriter_1_0<'value, W>;

    // Ion 1.0 does not support macros
    type EExpWriter = Never;

    delegate_value_writer_to!(fallible closure |self_: Self| self_.encode_annotations());
}

impl<W: RenderedWrite<IonToken>> AnnotatableWriter for TextValueWriter_1_0<'_, W> {
    type AnnotatedValueWriter<'a>
        = TextAnnotatedValueWriter_1_0<'a, W>
    where
        Self: 'a;

    fn with_annotations<'a>(
        self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        Ok(TextAnnotatedValueWriter_1_0 {
            annotations: annotations.into_annotations_vec(),
            value_writer: self,
        })
    }
}

impl<'value, W: RenderedWrite<IonToken>> ValueWriter for TextValueWriter_1_0<'value, W> {
    type ListWriter = TextListWriter_1_0<'value, W>;
    type SExpWriter = TextSExpWriter_1_0<'value, W>;
    type StructWriter = TextStructWriter_1_0<'value, W>;

    // Ion 1.0 does not support macros
    type EExpWriter = Never;

    fn write_null(mut self, ion_type: IonType) -> IonResult<()> {
        use crate::IonType::*;
        self.write_indentation()?;

        let null_text = match ion_type {
            Null => "null",
            Bool => "null.bool",
            Int => "null.int",
            Float => "null.float",
            Decimal => "null.decimal",
            Timestamp => "null.timestamp",
            Symbol => "null.symbol",
            String => "null.string",
            Blob => "null.blob",
            Clob => "null.clob",
            List => "null.list",
            SExp => "null.sexp",
            Struct => "null.struct",
        };
        self.output()
            .write_marked(null_text.as_bytes(), IonToken::Null)?;
        self.write_delimiter_text()
    }

    fn write_bool(mut self, value: bool) -> IonResult<()> {
        self.write_indentation()?;
        let bool_text = match value {
            true => "true",
            false => "false",
        };
        self.output()
            .write_marked(bool_text.as_bytes(), IonToken::Bool)?;
        self.write_delimiter_text()
    }

    fn write_i64(mut self, value: i64) -> IonResult<()> {
        self.write_indentation()?;
        self.output()
            .write_fmt_marked(format_args!("{value}"), IonToken::Int)?;
        self.write_delimiter_text()
    }

    fn write_int(mut self, value: &Int) -> IonResult<()> {
        self.write_indentation()?;
        self.output()
            .write_fmt_marked(format_args!("{value}"), IonToken::Int)?;
        self.write_delimiter_text()
    }

    fn write_f32(self, value: f32) -> IonResult<()> {
        self.write_f64(value as f64)
    }

    fn write_f64(mut self, value: f64) -> IonResult<()> {
        self.write_indentation()?;
        if value.is_nan() {
            self.output().write_marked(b"nan", IonToken::Float)?;
        } else if value.is_infinite() {
            if value.is_sign_positive() {
                self.output().write_marked(b"+inf", IonToken::Float)?;
            } else {
                self.output().write_marked(b"-inf", IonToken::Float)?;
            }
        } else if value == 0.0f64 && value.is_sign_negative() {
            // The {:e} formatter drops the sign for -0.0.
            // See: https://github.com/rust-lang/rust/issues/20596
            self.output().write_marked(b"-0e0", IonToken::Float)?;
        } else {
            self.output()
                .write_fmt_marked(format_args!("{value:e}"), IonToken::Float)?;
        }
        self.write_delimiter_text()
    }

    fn write_decimal(mut self, value: &Decimal) -> IonResult<()> {
        self.write_indentation()?;
        self.output()
            .write_fmt_marked(format_args!("{value}"), IonToken::Decimal)?;
        self.write_delimiter_text()
    }

    fn write_timestamp(mut self, value: &Timestamp) -> IonResult<()> {
        self.write_indentation()?;
        self.output()
            .write_fmt_marked(format_args!("{value}"), IonToken::Timestamp)?;
        self.write_delimiter_text()
    }

    fn write_string(mut self, value: impl AsRef<str>) -> IonResult<()> {
        self.write_indentation()?;
        let text = value.as_ref();
        let chunks = std::iter::once(&b"\""[..])
            .chain(EscapedIonText::wrap(text))
            .chain(std::iter::once(&b"\""[..]));
        self.output()
            .write_chunked_marked(chunks, IonToken::String)?;
        self.write_delimiter_text()
    }

    fn write_symbol(mut self, value: impl AsRawSymbolRef) -> IonResult<()> {
        use crate::constants::v1_1;

        self.write_indentation()?;
        match value.as_raw_symbol_ref() {
            RawSymbolRef::SymbolId(sid) => {
                self.output()
                    .write_fmt_marked(format_args!("${sid}"), IonToken::Symbol)?;
            }
            RawSymbolRef::SystemSymbol_1_1(v1_1::system_symbols::EMPTY_TEXT) => {
                self.output().write_marked(b"\'\'", IonToken::Symbol)?;
            }
            RawSymbolRef::SystemSymbol_1_1(symbol) => {
                self.output()
                    .write_marked(symbol.text().as_bytes(), IonToken::Symbol)?;
            }
            RawSymbolRef::Text(text) if !token_needs_quoting(text) => {
                self.output()
                    .write_marked(text.as_bytes(), IonToken::Symbol)?;
            }
            RawSymbolRef::Text(text) => {
                let chunks = std::iter::once(&b"'"[..])
                    .chain(EscapedIonText::wrap(text))
                    .chain(std::iter::once(&b"'"[..]));
                self.output()
                    .write_chunked_marked(chunks, IonToken::Symbol)?;
            }
        }
        self.write_delimiter_text()
    }

    fn write_clob(mut self, value: impl AsRef<[u8]>) -> IonResult<()> {
        // This type exists solely to enable using the IonValueFormatter (which operates on
        // `std::fmt::Write`) to write to a `std::io::Write`.
        struct ClobShim<'a>(&'a [u8]);
        impl std::fmt::Display for ClobShim<'_> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                let mut formatter = FmtValueFormatter { output: f };
                formatter.format_clob(self.0)?;
                Ok(())
            }
        }

        self.write_indentation()?;
        self.output()
            .write_fmt_marked(format_args!("{}", ClobShim(value.as_ref())), IonToken::Clob)?;
        self.write_delimiter_text()
    }

    fn write_blob(mut self, value: impl AsRef<[u8]>) -> IonResult<()> {
        self.write_indentation()?;
        // Rust format strings escape curly braces by doubling them. The following string is:
        // * The opening {{ from a text Ion blob, with each brace doubled to escape it.
        // * A {} pair used by the format string to indicate where the base64-encoded bytes
        //   should be inserted.
        // * The closing }} from a text Ion blob, with each brace doubled to escape it.
        self.output().write_fmt_marked(
            format_args!("{{{{{}}}}}", base64::encode(value)),
            IonToken::Blob,
        )?;
        self.write_delimiter_text()
    }

    fn list_writer(self) -> IonResult<Self::ListWriter> {
        TextListWriter_1_0::new(
            self.writer,
            self.depth,
            self.parent_type,
            self.value_delimiter,
        )
    }
    fn sexp_writer(self) -> IonResult<Self::SExpWriter> {
        TextSExpWriter_1_0::new(
            self.writer,
            self.depth,
            self.parent_type,
            self.value_delimiter,
        )
    }
    fn struct_writer(self) -> IonResult<Self::StructWriter> {
        TextStructWriter_1_0::new(
            self.writer,
            self.depth,
            self.parent_type,
            self.value_delimiter,
        )
    }
    fn eexp_writer<'a>(self, _macro_id: impl MacroIdLike<'a>) -> IonResult<Self::EExpWriter> {
        IonResult::encoding_error("macros are not supported in Ion 1.0")
    }
}
