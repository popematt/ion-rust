#![allow(non_camel_case_types)]

use std::fmt::Debug;
use std::io::Write;

use value_writer::SequenceWriter;

use crate::lazy::encoding::Encoding;
use crate::write_config::WriteConfig;
use crate::IonResult;

pub mod annotate;
pub mod annotation_seq;
pub mod binary;
pub mod text;
pub mod value_writer;
pub mod value_writer_config;
pub mod write_as_ion;
pub mod writer;

/// A family of types that collectively comprise the writer API for an Ion serialization
/// format. These types operate at the 'raw' level; they do not attempt to resolve symbols
/// using the active symbol table.
// Implementations of this trait are typically unit structs that are never instantiated.
// However, many types are generic over some `E: LazyEncoder`, and having this trait
// extend 'static, Sized, Debug, Clone and Copy means that those types can #[derive(...)]
// those traits themselves without boilerplate `where` clauses.
pub trait Encoder: 'static + Sized + Debug + Clone + Copy {
    const SUPPORTS_TEXT_TOKENS: bool;
    const DEFAULT_SYMBOL_CREATION_POLICY: SymbolCreationPolicy;

    /// A writer that serializes Rust values as Ion, emitting the resulting data to an implementation
    /// of [`Write`].
    type Writer<W: Write>: LazyRawWriter<W>;
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum SymbolCreationPolicy {
    // Prefer a compact encoding; create symbol table entries for all field names, annotations,
    // and symbol values. For text Ion, this will result in less human-friendly output.
    RequireSymbolId,
    // When the encoding supports it, write whatever token (symbol ID or text) that the user provided.
    // Do not create new symbol table entries.
    WriteProvidedToken,
    // TODO: Other potential policies, such as:
    //         * Require text (if a SID doesn't map to text, it's an error)
    //         * Wait until the next `flush()` operation to add new symbol definitions in bulk.
    //         * Using a symbol detection mechanism to intern recurring symbols after `N` usages.
}

pub(crate) mod private {
    /// Prevents types outside the crate from implementing traits that extend it.
    // This trait exists only as a visibility constraint, so the compiler considers it dead code.
    #[allow(dead_code)]
    pub trait Sealed {}
}

/// An Ion writer without an encoding context (that is: symbol/macro tables).
pub trait LazyRawWriter<W: Write>: SequenceWriter<Resources = W> {
    fn new(output: W) -> IonResult<Self>
    where
        Self: Sized;

    fn build<E: Encoding>(config: WriteConfig<E>, output: W) -> IonResult<Self>
    where
        Self: Sized;
    fn flush(&mut self) -> IonResult<()>;

    fn output(&self) -> &W;

    fn output_mut(&mut self) -> &mut W;

    fn write_version_marker(&mut self) -> IonResult<()>;
}

#[cfg(test)]
mod tests {
    use crate::lazy::encoder::annotate::Annotatable;
    use crate::lazy::encoder::text::v1_0::writer::LazyRawTextWriter_1_0;
    use crate::lazy::encoder::value_writer::{SequenceWriter, StructWriter};
    use crate::symbol_ref::AsSymbolRef;
    use crate::{Element, IonData, IonResult, Timestamp};

    fn writer_test(
        expected: &str,
        mut test: impl FnMut(&mut LazyRawTextWriter_1_0<&mut Vec<u8>>) -> IonResult<()>,
    ) -> IonResult<()> {
        let expected = Element::read_all(expected)?;
        let mut buffer = Vec::new();
        let mut writer = LazyRawTextWriter_1_0::new(&mut buffer)?;
        test(&mut writer)?;
        writer.flush()?;
        println!("{}", String::from_utf8_lossy(buffer.as_slice()));
        let actual = Element::read_all(buffer)?;
        assert!(
            IonData::eq(&expected, &actual),
            "expected:\n{expected:?}\nwas not Ion equal to actual:\n{actual:?}\n"
        );
        Ok(())
    }

    #[test]
    fn write_scalars() -> IonResult<()> {
        let expected = r#"
            1
            false
            3e0
            "foo"
            bar
            2023-11-09T
            {{4AEA6g==}}
            [1, 2, 3]
        "#;
        let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
            writer
                .write(1)?
                .write(false)?
                .write(3f32)?
                .write("foo")?
                .write("bar".as_symbol_ref())?
                .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
                .write([0xE0u8, 0x01, 0x00, 0xEA])?
                .write([1, 2, 3])?;
            Ok(())
        };
        writer_test(expected, test)
    }

    #[test]
    fn write_annotated_scalars() -> IonResult<()> {
        let expected = r#"
            foo::bar::1
            quux::quuz::gary::false
            Mercury::Venus::3e0
            Earth::"foo"
            Mars::Jupiter::bar
            Saturn::2023-11-09T
            Uranus::{{4AEA6g==}}
        "#;
        let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
            writer
                .write(1.annotated_with(["foo", "bar"]))?
                .write(false.annotated_with(["quux", "quuz", "gary"]))?
                .write(3f32.annotated_with(["Mercury", "Venus"]))?
                .write("foo".annotated_with(["Earth"]))?
                .write("bar".as_symbol_ref().annotated_with(["Mars", "Jupiter"]))?
                .write(
                    Timestamp::with_ymd(2023, 11, 9)
                        .build()?
                        .annotated_with(["Saturn"]),
                )?
                .write([0xE0u8, 0x01, 0x00, 0xEA].annotated_with(["Uranus"]))?;
            Ok(())
        };
        writer_test(expected, test)
    }

    #[test]
    fn write_list() -> IonResult<()> {
        let expected = r#"
            [
              1,
              false,
              3e0,
              "foo",
              bar,
              2023-11-09T,
              {{4AEA6g==}},
            ]
        "#;
        let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
            let mut list = writer.list_writer()?;
            list.write(1)?
                .write(false)?
                .write(3f32)?
                .write("foo")?
                .write("bar".as_symbol_ref())?
                .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
                .write([0xE0u8, 0x01, 0x00, 0xEA])?;
            list.end()
        };
        writer_test(expected, test)
    }

    #[test]
    fn write_sexp() -> IonResult<()> {
        let expected = r#"
            (
              1
              false
              3e0
              "foo"
              bar
              2023-11-09T
              {{4AEA6g==}}
              // Nested list
              [1, 2, 3]
            )
        "#;
        let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
            let mut sexp = writer.sexp_writer()?;
            sexp.write(1)?
                .write(false)?
                .write(3f32)?
                .write("foo")?
                .write("bar".as_symbol_ref())?
                .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
                .write([0xE0u8, 0x01, 0x00, 0xEA])?
                .write([1, 2, 3])?;
            sexp.end()
        };
        writer_test(expected, test)
    }

    #[test]
    fn write_struct() -> IonResult<()> {
        let expected = r#"
            {
              a: 1,
              b: false,
              c: 3e0,
              d: "foo",
              e: bar,
              f: 2023-11-09T,
              g: {{4AEA6g==}},
            }
        "#;
        let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
            let mut struct_ = writer.struct_writer()?;
            struct_
                .write("a", 1)?
                .write("b", false)?
                .write("c", 3f32)?
                .write("d", "foo")?
                .write("e", "bar".as_symbol_ref())?
                .write("f", Timestamp::with_ymd(2023, 11, 9).build()?)?
                .write("g", [0xE0u8, 0x01, 0x00, 0xEA])?;
            struct_.end()
        };
        writer_test(expected, test)
    }
}
