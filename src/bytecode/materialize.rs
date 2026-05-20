//! Element materialization from the bytecode reader.
//!
//! Provides functions to recursively build `Element` values from the
//! bytecode reader's state. The entry points (`read_all_v2` and
//! `read_one_v2`) detect the input format, create the appropriate
//! generator, and wire up the pipeline.

use crate::bytecode::constant_pool::Constant;
use crate::bytecode::instruction::op;
use crate::bytecode::ion10::BinaryIon10Generator;
use crate::bytecode::reader::{BytecodeReader, SymbolToken};
use crate::element::Annotations;
use crate::result::IonFailure;
use crate::{Bytes, Element, IonResult, IonType, Sequence, Str, Struct, Symbol, Value};

/// Reads all top-level values from binary Ion data using the bytecode
/// reader pipeline. Returns a `Sequence` of materialized `Element`s.
pub fn read_all_v2(data: &[u8]) -> IonResult<Sequence> {
    let generator = BinaryIon10Generator::new(data.to_vec());
    let mut reader = BytecodeReader::with_generator(Box::new(generator));
    let mut elements = Vec::new();
    while reader.next()?.is_some() {
        elements.push(materialize_element(&mut reader)?);
    }
    Ok(elements.into())
}

/// Reads a single top-level value from binary Ion data using the
/// bytecode reader pipeline. Returns the first materialized `Element`.
pub(crate) fn read_one_v2(data: &[u8]) -> IonResult<Element> {
    let generator = BinaryIon10Generator::new(data.to_vec());
    let mut reader = BytecodeReader::with_generator(Box::new(generator));
    match reader.next()? {
        Some(_) => materialize_element(&mut reader),
        None => IonResult::decoding_error("empty input"),
    }
}

/// Materializes the current value from the reader into an `Element`.
///
/// The reader must be positioned on a value (i.e., `next()` returned
/// `Some`). This function reads annotations, resolves the value based
/// on its Ion type, and recursively processes containers.
fn materialize_element(reader: &mut BytecodeReader) -> IonResult<Element> {
    // Read annotations
    let annotations = materialize_annotations(reader)?;

    // Read the value
    let value = materialize_value(reader)?;

    Ok(Element::new(annotations, value))
}

/// Resolves annotations from the reader into an `Annotations` value.
fn materialize_annotations(reader: &BytecodeReader) -> IonResult<Annotations> {
    if !reader.has_annotations() {
        return Ok(Annotations::empty());
    }

    let mut symbols = Vec::with_capacity(reader.annotation_count() as usize);
    for token_result in reader.annotations() {
        let token = token_result?;
        symbols.push(resolve_symbol_token(&token, reader.symbol_table()));
    }
    Ok(Annotations::from(symbols))
}

/// Converts a `SymbolToken` to a `Symbol` using the symbol table.
fn resolve_symbol_token(token: &SymbolToken, symbol_table: &[Option<String>]) -> Symbol {
    match token {
        SymbolToken::Sid(sid) => {
            // SID 0 is always unknown text
            if *sid == 0 {
                return Symbol::unknown_text();
            }
            // Look up in symbol table (1-indexed: SID 1 = index 0)
            let index = *sid - 1;
            match symbol_table.get(index) {
                Some(Some(text)) => Symbol::from(text.as_str()),
                Some(None) | None => Symbol::unknown_text(),
            }
        }
        SymbolToken::Text(rc) => Symbol::from(rc.as_ref()),
    }
}

/// Reads the current value from the reader based on its Ion type.
fn materialize_value(reader: &mut BytecodeReader) -> IonResult<Value> {
    let ion_type = reader
        .ion_type()
        .ok_or_else(|| IonResult::<()>::decoding_error("no current value").unwrap_err())?;

    // Handle nulls
    if reader.is_null() {
        return Ok(Value::Null(ion_type));
    }

    match ion_type {
        IonType::Null => Ok(Value::Null(IonType::Null)),
        IonType::Bool => Ok(Value::Bool(reader.bool_value()?)),
        IonType::Int => Ok(Value::Int(reader.int_value()?)),
        IonType::Float => Ok(Value::Float(reader.f64_value()?)),
        IonType::Decimal => Ok(Value::Decimal(reader.decimal_value()?)),
        IonType::Timestamp => Ok(Value::Timestamp(reader.timestamp_value()?)),
        IonType::Symbol => {
            let symbol = materialize_symbol_value(reader)?;
            Ok(Value::Symbol(symbol))
        }
        IonType::String => {
            let text = reader.string_value()?;
            Ok(Value::String(Str::from(text.as_ref())))
        }
        IonType::Clob => {
            let bytes = reader.lob_value()?;
            Ok(Value::Clob(Bytes::from(bytes.as_ref())))
        }
        IonType::Blob => {
            let bytes = reader.lob_value()?;
            Ok(Value::Blob(Bytes::from(bytes.as_ref())))
        }
        IonType::List => {
            let children = materialize_sequence(reader)?;
            Ok(Value::List(children))
        }
        IonType::SExp => {
            let children = materialize_sequence(reader)?;
            Ok(Value::SExp(children))
        }
        IonType::Struct => {
            let s = materialize_struct(reader)?;
            Ok(Value::Struct(s))
        }
    }
}

/// Reads the current symbol value from the reader and resolves it.
fn materialize_symbol_value(reader: &BytecodeReader) -> IonResult<Symbol> {
    let instruction = reader.instruction();
    let data = instruction.data();

    match instruction.operation() {
        op::SYMBOL_SID => {
            let sid = data as usize;
            if sid == 0 {
                Ok(Symbol::unknown_text())
            } else {
                let index = sid - 1;
                match reader.symbol_table().get(index) {
                    Some(Some(text)) => Ok(Symbol::from(text.as_str())),
                    Some(None) | None => Ok(Symbol::unknown_text()),
                }
            }
        }
        op::SYMBOL_CP => match reader.constant_pool().get(data) {
            Constant::String(rc) => Ok(Symbol::from(rc.as_ref())),
            _ => IonResult::decoding_error("symbol CP entry is not a string"),
        },
        op::SYMBOL_CHAR => {
            let ch = char::from_u32(data)
                .ok_or_else(|| IonResult::<()>::decoding_error("invalid char code").unwrap_err())?;
            let mut buf = [0u8; 4];
            let s = ch.encode_utf8(&mut buf);
            Ok(Symbol::from(&*s))
        }
        op::SYMBOL_REF => {
            // STRING_REF-style: data is length, operand at reader.i is offset.
            // We need to use the string_value pattern but for symbols. Since
            // the reader's string_value() requires STRING_REF operation, we use
            // the generator's read_text_ref directly is not available via public
            // API. Instead, we'll adapt: the symbol reader is positioned on
            // SYMBOL_REF which shares the same layout as STRING_REF.
            // We can't call string_value() because it checks op::STRING_REF.
            // For now, treat this as unresolved.
            IonResult::decoding_error("SYMBOL_REF resolution not yet implemented")
        }
        _ => IonResult::decoding_error("not positioned on a symbol value"),
    }
}

/// Steps into a container and materializes all children as a `Sequence`.
fn materialize_sequence(reader: &mut BytecodeReader) -> IonResult<Sequence> {
    reader.step_in()?;
    let mut elements = Vec::new();
    while reader.next()?.is_some() {
        elements.push(materialize_element(reader)?);
    }
    reader.step_out()?;
    Ok(Sequence::from(elements))
}

/// Steps into a struct and materializes all field name/value pairs.
fn materialize_struct(reader: &mut BytecodeReader) -> IonResult<Struct> {
    reader.step_in()?;
    let mut fields: Vec<(Symbol, Element)> = Vec::new();
    while reader.next()?.is_some() {
        let field_name = match reader.field_name()? {
            Some(token) => resolve_symbol_token(&token, reader.symbol_table()),
            None => Symbol::unknown_text(),
        };
        let element = materialize_element(reader)?;
        fields.push((field_name, element));
    }
    reader.step_out()?;
    Ok(Struct::from_iter(fields))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lazy::encoding::Encoding;
    use crate::v1_0;

    /// Helper: encodes Ion text as binary Ion 1.0.
    fn encode_as_binary(text: &str) -> Vec<u8> {
        let elements = Element::read_all(text).unwrap();
        v1_0::Binary::encode_all(elements.iter()).unwrap()
    }

    #[test]
    fn read_one_v2_integer() -> IonResult<()> {
        let binary = encode_as_binary("5");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Int(5.into()));
        Ok(())
    }

    #[test]
    fn read_one_v2_negative_integer() -> IonResult<()> {
        let binary = encode_as_binary("-42");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Int((-42).into()));
        Ok(())
    }

    #[test]
    fn read_one_v2_bool() -> IonResult<()> {
        let binary = encode_as_binary("true");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Bool(true));
        Ok(())
    }

    #[test]
    fn read_one_v2_float() -> IonResult<()> {
        let binary = encode_as_binary("3.14e0");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Float(3.14));
        Ok(())
    }

    #[test]
    fn read_one_v2_string() -> IonResult<()> {
        let binary = encode_as_binary("\"hello\"");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::String(Str::from("hello")));
        Ok(())
    }

    #[test]
    fn read_one_v2_null() -> IonResult<()> {
        let binary = encode_as_binary("null");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Null(IonType::Null));
        Ok(())
    }

    #[test]
    fn read_one_v2_null_int() -> IonResult<()> {
        let binary = encode_as_binary("null.int");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Null(IonType::Int));
        Ok(())
    }

    #[test]
    fn read_one_v2_symbol() -> IonResult<()> {
        let binary = encode_as_binary("name");
        let element = read_one_v2(&binary)?;
        // "name" is system symbol SID 4
        assert_eq!(element.value(), &Value::Symbol(Symbol::from("name")));
        Ok(())
    }

    #[test]
    fn read_all_v2_multiple_values() -> IonResult<()> {
        let binary = encode_as_binary("1 2 3");
        let seq = read_all_v2(&binary)?;
        assert_eq!(seq.len(), 3);
        assert_eq!(seq.get(0).unwrap().value(), &Value::Int(1.into()));
        assert_eq!(seq.get(1).unwrap().value(), &Value::Int(2.into()));
        assert_eq!(seq.get(2).unwrap().value(), &Value::Int(3.into()));
        Ok(())
    }

    #[test]
    fn read_one_v2_list() -> IonResult<()> {
        let binary = encode_as_binary("[1, 2, 3]");
        let element = read_one_v2(&binary)?;
        if let Value::List(seq) = element.value() {
            assert_eq!(seq.len(), 3);
            assert_eq!(seq.get(0).unwrap().value(), &Value::Int(1.into()));
            assert_eq!(seq.get(1).unwrap().value(), &Value::Int(2.into()));
            assert_eq!(seq.get(2).unwrap().value(), &Value::Int(3.into()));
        } else {
            panic!("expected a list, got {:?}", element.value());
        }
        Ok(())
    }

    #[test]
    fn read_one_v2_sexp() -> IonResult<()> {
        let binary = encode_as_binary("(1 2 3)");
        let element = read_one_v2(&binary)?;
        if let Value::SExp(seq) = element.value() {
            assert_eq!(seq.len(), 3);
        } else {
            panic!("expected an sexp, got {:?}", element.value());
        }
        Ok(())
    }

    #[test]
    fn read_one_v2_struct_with_lst() -> IonResult<()> {
        let binary = encode_as_binary("{foo: 1}");
        let element = read_one_v2(&binary)?;
        if let Value::Struct(s) = element.value() {
            let field = s.get("foo");
            assert!(field.is_some(), "struct should have field 'foo'");
            assert_eq!(field.unwrap().value(), &Value::Int(1.into()));
        } else {
            panic!("expected a struct, got {:?}", element.value());
        }
        Ok(())
    }

    #[test]
    fn read_one_v2_annotations() -> IonResult<()> {
        let binary = encode_as_binary("foo::5");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Int(5.into()));
        let annotations: Vec<&Symbol> = element.annotations().iter().collect();
        assert_eq!(annotations.len(), 1);
        assert_eq!(annotations[0].text(), Some("foo"));
        Ok(())
    }

    #[test]
    fn read_one_v2_multiple_annotations() -> IonResult<()> {
        let binary = encode_as_binary("foo::bar::5");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Int(5.into()));
        let annotations: Vec<&Symbol> = element.annotations().iter().collect();
        assert_eq!(annotations.len(), 2);
        assert_eq!(annotations[0].text(), Some("foo"));
        assert_eq!(annotations[1].text(), Some("bar"));
        Ok(())
    }

    #[test]
    fn read_one_v2_nested_list() -> IonResult<()> {
        let binary = encode_as_binary("[[1, 2], [3]]");
        let element = read_one_v2(&binary)?;
        if let Value::List(outer) = element.value() {
            assert_eq!(outer.len(), 2);
            if let Value::List(inner1) = outer.get(0).unwrap().value() {
                assert_eq!(inner1.len(), 2);
            } else {
                panic!("expected inner list");
            }
            if let Value::List(inner2) = outer.get(1).unwrap().value() {
                assert_eq!(inner2.len(), 1);
            } else {
                panic!("expected inner list");
            }
        } else {
            panic!("expected a list");
        }
        Ok(())
    }

    #[test]
    fn read_one_v2_empty_input() {
        // Binary Ion with just the IVM and nothing else
        let binary: Vec<u8> = vec![0xE0, 0x01, 0x00, 0xEA];
        let result = read_one_v2(&binary);
        assert!(result.is_err());
    }

    #[test]
    fn read_one_v2_matches_existing_reader() -> IonResult<()> {
        let test_cases = &[
            "5",
            "-100",
            "true",
            "false",
            "null",
            "null.bool",
            "null.int",
            "null.string",
            "\"hello world\"",
            "[1, 2, 3]",
            "{foo: 1, bar: 2}",
            "foo::bar::5",
            "[[[]]]",
            "(1 2 (3 4))",
        ];

        for text in test_cases {
            let binary = encode_as_binary(text);
            let expected = Element::read_one(&binary)?;
            let actual = read_one_v2(&binary)?;
            assert_eq!(
                expected, actual,
                "mismatch for input: {text}\nexpected: {expected:?}\nactual: {actual:?}"
            );
        }
        Ok(())
    }

    #[test]
    fn read_all_v2_matches_existing_reader() -> IonResult<()> {
        let text = "1 true \"hello\" [1, 2] {a: 1}";
        let binary = encode_as_binary(text);
        let expected = Element::read_all(&binary)?;
        let actual = read_all_v2(&binary)?;
        assert_eq!(expected, actual);
        Ok(())
    }

    #[test]
    fn read_one_v2_user_symbol() -> IonResult<()> {
        // "hello" is not a system symbol, so it must go through an LST
        let binary = encode_as_binary("hello");
        let element = read_one_v2(&binary)?;
        assert_eq!(element.value(), &Value::Symbol(Symbol::from("hello")));
        Ok(())
    }

    #[test]
    fn read_one_v2_struct_multiple_fields() -> IonResult<()> {
        let binary = encode_as_binary("{a: 1, b: 2, c: 3}");
        let element = read_one_v2(&binary)?;
        if let Value::Struct(s) = element.value() {
            assert_eq!(s.get("a").unwrap().value(), &Value::Int(1.into()));
            assert_eq!(s.get("b").unwrap().value(), &Value::Int(2.into()));
            assert_eq!(s.get("c").unwrap().value(), &Value::Int(3.into()));
        } else {
            panic!("expected a struct");
        }
        Ok(())
    }

    #[test]
    fn read_all_v2_many_short_strings() -> IonResult<()> {
        // Generate a stream of 20 short strings
        let mut text_values = Vec::new();
        for i in 0..20 {
            text_values.push(format!("\"str{i}\""));
        }
        let text = text_values.join(" ");
        let binary = encode_as_binary(&text);
        let expected = Element::read_all(&binary)?;
        let actual = read_all_v2(&binary)?;
        assert_eq!(expected.len(), actual.len());
        for (i, (e, a)) in expected.iter().zip(actual.iter()).enumerate() {
            assert_eq!(e, a, "mismatch at index {i}");
        }
        Ok(())
    }

    #[test]
    fn read_all_v2_long_strings() -> IonResult<()> {
        // Generate strings that exceed 13 bytes (VarUInt length in Ion 1.0)
        let mut text_values = Vec::new();
        for i in 0..20 {
            let long_str = format!("\"this_is_a_longer_string_value_number_{i}\"");
            text_values.push(long_str);
        }
        let text = text_values.join(" ");
        let binary = encode_as_binary(&text);
        let expected = Element::read_all(&binary)?;
        let actual = read_all_v2(&binary)?;
        assert_eq!(expected.len(), actual.len());
        for (i, (e, a)) in expected.iter().zip(actual.iter()).enumerate() {
            assert_eq!(e, a, "mismatch at index {i}");
        }
        Ok(())
    }

    #[test]
    fn read_all_v2_100_strings() -> IonResult<()> {
        // Generate 100 strings - this tests that the generator correctly
        // handles VarUInt-encoded lengths >= 15 (the old null sentinel).
        let mut text_values = Vec::new();
        for i in 0..100 {
            text_values.push(format!("\"string_value_{i}\""));
        }
        let text = text_values.join(" ");
        let binary = encode_as_binary(&text);
        let expected = Element::read_all(&binary)?;
        let actual = read_all_v2(&binary)?;
        assert_eq!(expected.len(), actual.len());
        for (i, (e, a)) in expected.iter().zip(actual.iter()).enumerate() {
            assert_eq!(e, a, "mismatch at index {i}");
        }
        Ok(())
    }

    #[test]
    fn read_all_v2_200_strings() -> IonResult<()> {
        // Stress test with 200 strings to ensure no hang or panic
        let mut text_values = Vec::new();
        for i in 0..200 {
            text_values.push(format!("\"string_value_{i}\""));
        }
        let text = text_values.join(" ");
        let binary = encode_as_binary(&text);
        let expected = Element::read_all(&binary)?;
        let actual = read_all_v2(&binary)?;
        assert_eq!(expected.len(), actual.len());
        for (i, (e, a)) in expected.iter().zip(actual.iter()).enumerate() {
            assert_eq!(e, a, "mismatch at index {i}");
        }
        Ok(())
    }
}
