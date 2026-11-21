//! # Serialization and deserialization of Ion data
//!
//! This module offers APIs for serialization of Rust data structures into Ion data and deserialization
//! of Ion data into Rust data structures. The APIs use the `serde` framework for serialization and
//! deserialization. See [the Serde website](https://serde.rs/) for additional documentation and
//! usage examples. This feature doesn't yet support [Ion annotations] and [Ion SExpressions] for
//! serialization and deserialization.
//!
//! There are three different APIs for serializing Ion data:
//!
//! * `to_string`: Serialize an object into compact Ion text format.
//! * `to_pretty`: Serialize an object into pretty formatted Ion text.
//! * `to_binary`:  Serialize an object into Ion binary format.
//!
//! For deserialization `from_ion` API is provided through this module.
//!
//! ## Mapping of Ion data types to Rust and serde data types
//!
//!| Ion data type | Rust data structure                  | Serde data type                                       |
//!|---------------|--------------------------------------|-------------------------------------------------------|
//!| int           | u64, i64, u32, i32, u16, i16, u8, i8 | u64, i64, u32, i32, u16, i16, u8, i8                  |
//!| float         | f32, f64                             | f32, f64                                              |
//!| decimal       | Decimal(Ion Element API)             | newtype_struct (with name as `$__ion_rs_decimal__`)   |
//!| timestamp     | Timestamp(Ion Element API)           | newtype_struct (with name as `$__ion_rs_timestamp__`) |
//!| blob          | byte array                           | byte array                                            |
//!| clob          | byte array                           | byte array                                            |
//!| bool          | bool                                 | bool                                                  |
//!| symbol        | string                               | string                                                |
//!| string        | string                               | string                                                |
//!| struct        | struct                               | struct                                                |
//!| list          | vector                               | seq                                                   |
//!| null          | None                                 | unit                                                  |
//!
//! ## Mapping of serde data types to Ion representation
//!
//!| Serde data type                                              | Ion representation                          |
//!|--------------------------------------------------------------|---------------------------------------------|
//!| u64, i64, u32, i32, u16, i16, u8, i8                         | int                                         |
//!| char, string, unit_variant                                   | string                                      |
//!| byte-array                                                   | blob                                        |
//!| option                                                       | None - null, Some - based on other mappings |
//!| unit                                                         | null                                        |
//!| unit_struct                                                  | symbol                                      |
//!| seq, tuple, tuple_struct                                     | list                                        |
//!| newtype_struct, map, struct                                  | struct                                      |
//!| newtype_variant                                              | variant value with annotation               |
//!| struct_variant                                               | struct with annotation                      |
//!| tuple_variant                                                | list with annotation                        |
//!
//! _Note: Since the serde framework doesn't support [Ion decimal] and [Ion timestamp] types, distinct serialization
//! and deserialization of these types are defined in this module. It uses `newtype_struct` with `$__ion_rs_decimal__`
//! and `$__ion_rs_timestamp__` as struct names from [serde data model], to indicate serde framework to use Ion's
//! implementation of decimal and timestamp serialization and deserialization. If one wants to use [chrono::DateTime],
//! it needs to be tagged with `#[serde_as(as = crate::Timestamp)]`._
//!
//! _Serializers other than Ion's receive `Decimal` and `Timestamp` as these `newtype_struct`s wrapping
//! opaque bytes, and deserializing an Ion decimal or timestamp through `deserialize_any` produces
//! the same `newtype_struct`s. The byte layout is unspecified and may change between versions.
//! Formats that cannot deserialize bytes natively, such as JSON, cannot read them back._
//!
//! ## Example of serialization of Rust struct into Ion data
//! ```
//! use ion_rs::IonResult;
//! use crate::ion_rs::serde::to_string;
//! use serde::{Deserialize, Serialize};
//!
//!#[derive(Serialize, Deserialize)]
//! struct Address {
//!     street: String,
//!     city: String,
//! }
//!
//! fn main() -> IonResult<()> {
//!     // data structure for representing address
//!     let address = Address {
//!         street: "10 Downing Street".to_owned(),
//!         city: "London".to_owned(),
//!     };
//!
//!     // serialize it to Ion text
//!     let ion = to_string(&address)?;
//!
//!     // assert that the serialized Ion data is as expected
//!     assert_eq!(r#"{street: "10 Downing Street", city: "London", } "#, ion);
//!
//!     Ok(())
//! }
//! ```
//!
//! ## Example of deserialization of Ion data into Rust struct
//! ```
//! use ion_rs::IonResult;
//! use crate::ion_rs::serde::from_ion;
//! use serde::{Deserialize, Serialize};
//!
//!#[derive(Serialize, Deserialize)]
//! struct Address {
//!     street: String,
//!     city: String,
//! }
//!
//! fn main() -> IonResult<()> {
//!     // represents Ion data with address information
//!     let data = r#"
//!         {
//!             street: "10 Downing Street",
//!             city: "London"    
//!         }
//!     "#;
//!
//!     // deserialize Ion data into Rust struct for address
//!     let address: Address = from_ion(data)?;
//!
//!     // assert that the deserialized Rust struct has street and city field set correctly
//!     assert_eq!(address.street, "10 Downing Street");
//!     assert_eq!(address.city, "London");
//!
//!     Ok(())
//! }
//! ```
//!
//! ## Example of serialization and deserialization for Timestamp
//!```
//! use serde::{Deserialize, Serialize};
//! use ion_rs::Timestamp;
//! use ion_rs::IonResult;
//! use ion_rs::serde::from_ion;
//! use serde_with::serde_as;
//! use chrono::{Utc, TimeZone, FixedOffset, DateTime};
//!
//! #[serde_as]
//! #[derive(Serialize, Deserialize)]
//! struct Event {
//!     name: String,
//!     start_time: Timestamp,
//!     #[serde_as(as = "crate::Timestamp")]
//!     end_time: DateTime<FixedOffset>
//! }
//!
//! fn main() -> IonResult<()> {
//! // represents Ion data with event information
//! let data = r#"
//!         {
//!             name: "Annual Conference",
//!             start_time: 2023-01-01T16:30:00Z,
//!             end_time: 2023-01-01T18:00:00Z
//!         }
//!     "#;
//!
//!     // deserialize Ion data into Rust struct for event
//!     let event: Event = from_ion(data)?;
//!
//!     // assert that the deserialized Rust struct has name, start_time and end_time set correctly
//!     assert_eq!(event.name, "Annual Conference");
//!     assert_eq!(event.start_time, Timestamp::with_ymd(2023, 1, 1).with_hms(16, 30, 0).build()?);
//!     assert_eq!(event.end_time, Utc.with_ymd_and_hms(2023, 1, 1, 18, 0, 0).unwrap());
//!
//!    Ok(())
//! }
//! ```
//!
//! ## Example of serialization and deserialization for Decimal
//!```
//! use serde::{Deserialize, Serialize};
//! use ion_rs::Decimal;
//! use ion_rs::IonResult;
//! use ion_rs::serde::from_ion;
//!
//! #[derive(Serialize, Deserialize)]
//! struct Product {
//!     name: String,
//!     price: Decimal
//! }
//!
//! fn main() -> IonResult<()> {
//! // represents Ion data with product information
//! let data = r#"
//!         {
//!             name: "Chair",
//!             price: 35.5
//!         }
//!     "#;
//!
//!     // deserialize Ion data into Rust struct for product
//!     let product: Product = from_ion(data)?;
//!
//!     // assert that the deserialized Rust struct has name and price field set correctly
//!     assert_eq!(product.name, "Chair");
//!     assert_eq!(product.price, Decimal::new(355, -1));
//!
//!    Ok(())
//! }
//! ```
//!
//! [Ion annotations]: https://amazon-ion.github.io/ion-docs/docs/spec.html#annot
//! [Ion SExpressions]: https://amazon-ion.github.io/ion-docs/docs/spec.html#sexp
//! [Ion decimal]: https://amazon-ion.github.io/ion-docs/docs/spec.html#decimal
//! [Ion timestamp]: https://amazon-ion.github.io/ion-docs/docs/spec.html#timestamp
//! [serde data model]: https://serde.rs/data-model.html#types

pub mod de;
mod decimal;
pub mod ser;
mod timestamp;

pub use de::from_ion;
pub use ser::{to_binary, to_pretty, to_string};
use serde::de::Visitor;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;

/// Kind tag in byte 0 of a [`Decimal`](crate::Decimal) tunnel payload.
const DECIMAL_KIND: u8 = 1;
/// Kind tag in byte 0 of a [`Timestamp`](crate::Timestamp) tunnel payload.
const TIMESTAMP_KIND: u8 = 2;

/// Bytes that carry a [`Decimal`](crate::Decimal) or [`Timestamp`](crate::Timestamp) through
/// serde as the payload of its tunnel `newtype_struct`. Private to that tunnel; each type's
/// `From<&T> for TunnelBytes` documents its layout. Its visitor accepts only bytes so that
/// serde's buffered `flatten` and `untagged` paths do not decode Ion lists or strings as payloads.
struct TunnelBytes(Vec<u8>);

impl Serialize for TunnelBytes {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&self.0)
    }
}

impl<'de> Deserialize<'de> for TunnelBytes {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct TunnelBytesVisitor;

        impl Visitor<'_> for TunnelBytesVisitor {
            type Value = TunnelBytes;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("an Ion serde tunnel payload")
            }

            fn visit_bytes<E>(self, bytes: &[u8]) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(TunnelBytes(bytes.to_vec()))
            }

            fn visit_byte_buf<E>(self, bytes: Vec<u8>) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(TunnelBytes(bytes))
            }
        }

        deserializer.deserialize_bytes(TunnelBytesVisitor)
    }
}

#[cfg(test)]
#[cfg(feature = "experimental-serde")]
mod tests {
    use crate::serde::{
        decimal, from_ion, timestamp, to_binary, to_pretty, to_string, TunnelBytes, DECIMAL_KIND,
        TIMESTAMP_KIND,
    };
    use std::fmt;
    use std::net::IpAddr;

    use crate::{Decimal, Element, Int, IonData, IonResult, Timestamp};
    use chrono::{DateTime, FixedOffset, TimeZone, Utc};
    use rstest::*;
    use serde::de::{DeserializeOwned, Visitor};
    use serde::{Deserialize, Deserializer, Serialize};
    use serde_with::serde_as;

    #[rstest]
    #[case::i8(to_binary(&-1_i8).unwrap(),     &[0xE0, 0x01, 0x00, 0xEA, 0x31, 0x01])]
    #[case::i16(to_binary(&-1_i16).unwrap(),   &[0xE0, 0x01, 0x00, 0xEA, 0x31, 0x01])]
    #[case::i32(to_binary(&-1_i32).unwrap(),   &[0xE0, 0x01, 0x00, 0xEA, 0x31, 0x01])]
    #[case::i64(to_binary(&-1_i64).unwrap(),   &[0xE0, 0x01, 0x00, 0xEA, 0x31, 0x01])]
    #[case::u8(to_binary(&1_u8).unwrap(),      &[0xE0, 0x01, 0x00, 0xEA, 0x21, 0x01])]
    #[case::u16(to_binary(&1_u16).unwrap(),    &[0xE0, 0x01, 0x00, 0xEA, 0x21, 0x01])]
    #[case::u32(to_binary(&1_u32).unwrap(),    &[0xE0, 0x01, 0x00, 0xEA, 0x21, 0x01])]
    #[case::u64(to_binary(&1_u64).unwrap(),    &[0xE0, 0x01, 0x00, 0xEA, 0x21, 0x01])]
    #[case::f32(to_binary(&1_f32).unwrap(),    &[0xE0, 0x01, 0x00, 0xEA, 0x44, 0x3f, 0x80, 0x00, 0x00])]
    #[case::f64(to_binary(&1_f64).unwrap(),    &[0xE0, 0x01, 0x00, 0xEA, 0x44, 0x3f, 0x80, 0x00, 0x00])]
    #[case::char(to_binary(&'a').unwrap(),     &[0xE0, 0x01, 0x00, 0xEA, 0x81, 0x61])]
    #[case::str(to_binary(&"a").unwrap(),      &[0xE0, 0x01, 0x00, 0xEA, 0x81, 0x61])]
    #[case::some(to_binary(&Some(1)).unwrap(), &[0xE0, 0x01, 0x00, 0xEA, 0x21, 0x01])]
    #[case::unit(to_binary(&()).unwrap(),      &[0xE0, 0x01, 0x00, 0xEA, 0x0F])]
    fn test_primitives_binary(#[case] ion_data: Vec<u8>, #[case] expected: &[u8]) {
        assert_eq!(&ion_data[..], expected);
    }

    #[rstest]
    #[case::text(b"'$ion_1_0' 5")]
    #[case::binary(&[0xE0, 0x01, 0x00, 0xEA, 0x71, 0x02, 0x21, 0x05])]
    fn from_ion_skips_top_level_ion_1_0_symbol(#[case] ion_data: &[u8]) -> IonResult<()> {
        assert_eq!(from_ion::<i32, _>(ion_data)?, 5);
        Ok(())
    }

    #[rstest]
    #[case::i8(to_string(&-1_i8).unwrap(),     "-1")]
    #[case::i16(to_string(&-1_i16).unwrap(),   "-1")]
    #[case::i32(to_string(&-1_i32).unwrap(),   "-1")]
    #[case::i64(to_string(&-1_i64).unwrap(),   "-1")]
    #[case::u8(to_string(&1_u8).unwrap(),      "1")]
    #[case::u16(to_string(&1_u16).unwrap(),    "1")]
    #[case::u32(to_string(&1_u32).unwrap(),    "1")]
    #[case::u64(to_string(&1_u64).unwrap(),    "1")]
    #[case::char(to_string(&'a').unwrap(),     "\"a\"")]
    #[case::str(to_string(&"a").unwrap(),      "\"a\"")]
    #[case::some(to_string(&Some(1)).unwrap(), "1" )]
    #[case::unit(to_string(&()).unwrap(),      "null")]
    fn test_primitives_text(#[case] ion_data: String, #[case] expected: &str) {
        assert_eq!(ion_data.trim(), expected);
    }

    #[test]
    fn test_blob() {
        #[derive(Serialize, Deserialize)]
        struct Test {
            #[serde(with = "serde_bytes")]
            binary: Vec<u8>,
        }
        #[rustfmt::skip]
        let expected = &[
            0xE0, 0x01, 0x00, 0xEA,                               // IVM
            0xEE, 0x8F, 0x81, 0x83, 0xDC,                         // $ion_symbol_table:: {
            0x86, 0x71, 0x03,                                     //   imports: $ion_symbol_table,
            0x87, 0xB7, 0x86, 0x62, 0x69, 0x6E, 0x61, 0x72, 0x79, // symbols: ["binary"] ]}
            0xD7, 0x8A, 0xA5, 0x68, 0x65, 0x6C, 0x6C, 0x6F,       // {binary: {{ aGVsbG8= }}
        ];

        let test = Test {
            binary: b"hello".to_vec(),
        }; // aGVsbG8=
        let ion_data = to_binary(&test).unwrap();
        assert_eq!(&ion_data[..], expected);
        let de: Test = from_ion(ion_data).expect("unable to parse test");
        assert_eq!(de.binary, test.binary);

        let ion_data_str = to_string(&test).unwrap();
        assert_eq!(ion_data_str.trim(), "{binary: {{aGVsbG8=}}, }");
        let de: Test = from_ion(ion_data_str).expect("unable to parse test");
        assert_eq!(de.binary, test.binary);
    }

    #[test]
    fn test_struct() {
        #[serde_as]
        #[derive(Serialize, Deserialize)]
        struct Test {
            int: u32,
            float: f64,
            #[serde(with = "serde_bytes")]
            binary: Vec<u8>,
            seq: Vec<String>,
            decimal: Decimal,
            date: Timestamp,
            #[serde_as(as = "crate::Timestamp")]
            date0: DateTime<Utc>,
            #[serde_as(as = "crate::Timestamp")]
            date1: DateTime<FixedOffset>,
            nested_struct: NestedTest,
            unit_struct: UnitStruct,
            newtype_struct: NewTypeStruct,
            tuple_struct: TupleStruct,
            optional: Option<i64>,
        }

        #[serde_as]
        #[derive(Serialize, Deserialize)]
        struct NestedTest {
            boolean: bool,
            str: String,
        }

        #[serde_as]
        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct UnitStruct;

        #[serde_as]
        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct NewTypeStruct(i64);

        #[serde_as]
        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct TupleStruct(i64, i64);

        let datetime: DateTime<FixedOffset> = Utc::now().into();
        let my_date0 = Utc::now();
        let my_date = Timestamp::from(datetime);
        let my_decimal = Decimal::new(1225, -2);
        let test = Test {
            int: 1,
            float: 3.46,
            binary: b"EDO".to_vec(),
            seq: vec!["a".to_string(), "b".to_string()],
            decimal: my_decimal.clone(),
            date: my_date.clone(),
            date0: my_date0,
            date1: datetime,
            nested_struct: NestedTest {
                boolean: true,
                str: "hello".to_string(),
            },

            unit_struct: UnitStruct,
            newtype_struct: NewTypeStruct(5),
            tuple_struct: TupleStruct(5, 10),
            optional: None,
        };

        let result = to_pretty(&test).expect("failed to serialize");
        println!("result: {result}");
        let back_result: Test = from_ion(result.as_str()).expect("failed to deserialize");

        assert_eq!(back_result.int, 1);
        assert_eq!(back_result.float, 3.46);
        assert_eq!(back_result.binary, b"EDO");
        assert_eq!(back_result.seq.len(), 2);
        assert_eq!(back_result.seq[0], "a");
        assert_eq!(back_result.seq[1], "b");
        assert_eq!(back_result.decimal, my_decimal.clone());
        assert_eq!(back_result.date, my_date.clone());
        assert_eq!(back_result.date0, my_date0.clone());
        assert_eq!(back_result.date1, datetime.clone());
        assert!(back_result.nested_struct.boolean);
        assert_eq!(&back_result.nested_struct.str, "hello");
        assert_eq!(back_result.unit_struct, UnitStruct);
        assert_eq!(back_result.newtype_struct, NewTypeStruct(5));
        assert_eq!(back_result.tuple_struct, TupleStruct(5, 10));
        assert_eq!(back_result.optional, None);
    }

    #[test]
    fn test_enum() {
        #[serde_as]
        #[derive(Serialize, Deserialize, PartialEq, Debug)]
        enum E {
            Unit,
            Newtype(u32),
            Tuple(u32, u32),
            Struct { a: u32 },
        }

        let i = r#"Unit"#;
        let expected = E::Unit;
        assert_eq!(expected, from_ion(i).unwrap());
        assert_eq!(
            Element::read_first(i),
            Element::read_first(to_string(&expected).unwrap())
        );

        let i = r#"Newtype::1"#;
        let expected = E::Newtype(1);
        assert_eq!(expected, from_ion(i).unwrap());
        assert_eq!(
            Element::read_first(i),
            Element::read_first(to_string(&expected).unwrap())
        );

        let i = r#"Tuple::[1, 2]"#;
        let expected = E::Tuple(1, 2);
        assert_eq!(expected, from_ion(i).unwrap());
        assert_eq!(
            Element::read_first(i),
            Element::read_first(to_string(&expected).unwrap())
        );

        let i = r#"Struct::{a: 1}"#;
        let expected = E::Struct { a: 1 };
        assert_eq!(expected, from_ion(i).unwrap());
        assert_eq!(
            Element::read_first(i),
            Element::read_first(to_string(&expected).unwrap())
        );
    }

    #[test]
    fn test_nested_newtype_variant() {
        #[derive(Serialize, Deserialize, PartialEq, Debug)]
        enum Outter {
            First(Inner),
        }

        #[derive(Serialize, Deserialize, PartialEq, Debug)]
        enum Inner {
            Second(u32),
        }

        #[rustfmt::skip]
        let expected_binary = [
            0xE0, 0x01, 0x00, 0xEA,                          // IVM
            0xEE, 0x96, 0x81, 0x83,                          // $ion_symbol_table::
            0xDE, 0x92, 0x86, 0x71, 0x03,                    // { imports: $ion_symbol_table,
            0x87, 0xBD, 0x85, 0x46, 0x69, 0x72, 0x73, 0x74,  //   symbols: ["First",
            0x86, 0x53, 0x65, 0x63, 0x6F, 0x6E, 0x64,        //             "Second"]}
            0xE5, 0x82, 0x8A, 0x8B, 0x21, 0x03,              // First::Second::3

        ];

        let i = r#"First::Second::3"#;
        let expected = Outter::First(Inner::Second(3));
        assert_eq!(expected, from_ion(i).unwrap());

        let b = to_binary(&expected).unwrap();
        assert_eq!(expected_binary, &b[..]);
    }

    #[test]
    fn test_symbol() {
        let i = r#"inches"#;
        let expected = String::from("inches");
        assert_eq!(expected, from_ion::<String, _>(i).unwrap());

        let i = r#"'with space'"#;
        let expected = String::from("with space");
        assert_eq!(expected, from_ion::<String, _>(i).unwrap());

        let i = r#"'\'embedded quotes\''"#;
        let expected = String::from("'embedded quotes'");
        assert_eq!(expected, from_ion::<String, _>(i).unwrap());
    }

    #[test]
    fn human_readable() {
        // IpAddr has different repr based on if codec is considered
        // human readable or not {true: string, false: byte array}
        let ip: IpAddr = "127.0.0.1".parse().unwrap();
        let expected_binary = [
            224, 1, 0, 234, 235, 129, 131, 216, 134, 113, 3, 135, 179, 130, 86, 52, 233, 129, 138,
            182, 33, 127, 32, 32, 33, 1,
        ];
        let expected_s = "\"127.0.0.1\" ";
        let binary = to_binary(&ip).unwrap();
        let s = to_string(&ip).unwrap();
        assert_eq!(&binary[..], &expected_binary[..]);
        assert_eq!(s, expected_s);
        assert_eq!(&from_ion::<IpAddr, _>(s).unwrap(), &ip);
        assert_eq!(&from_ion::<IpAddr, _>(binary).unwrap(), &ip);
    }

    #[derive(Serialize, Deserialize, PartialEq, Debug)]
    #[serde(tag = "kind")]
    enum Shape {
        Circle { radius: u32 },
        Square { side: u32 },
    }

    #[rstest]
    #[case::text("{kind: \"Circle\", radius: 2}", Shape::Circle { radius: 2 })]
    #[case::text_symbol_tag("{kind: Square, side: 3}", Shape::Square { side: 3 })]
    #[case::binary(to_binary(&Shape::Circle { radius: 2 }).unwrap(), Shape::Circle { radius: 2 })]
    fn internally_tagged_enum<I: crate::IonInput>(#[case] ion: I, #[case] expected: Shape) {
        assert_eq!(from_ion::<Shape, _>(ion).unwrap(), expected);
    }

    /// Regression tests for annotations being correctly written for all value types
    /// when serialized through newtype variants (which produce annotations in Ion).
    mod newtype_variant_annotations {
        use super::*;
        use std::collections::BTreeMap;

        #[derive(Serialize, Deserialize, PartialEq, Debug)]
        enum Wrapper {
            Tag(bool),
            Num(f32),
            Big(f64),
            Items(Vec<u32>),
            Dict(BTreeMap<String, u32>),
            Record { x: i32, y: i32 },
            Price(Decimal),
            When(Timestamp),
        }

        #[test]
        fn newtype_variant_bool() {
            let val = Wrapper::Tag(true);
            let ion = to_string(&val).unwrap();
            assert_eq!(Element::read_first("Tag::true"), Element::read_first(&ion));
            let roundtrip: Wrapper = from_ion(&ion).unwrap();
            assert_eq!(val, roundtrip);
        }

        #[test]
        fn newtype_variant_f32() {
            let val = Wrapper::Num(2.5f32);
            let ion = to_string(&val).unwrap();
            assert_eq!(Element::read_first("Num::2.5e0"), Element::read_first(&ion));
            let roundtrip: Wrapper = from_ion(&ion).unwrap();
            assert_eq!(val, roundtrip);
        }

        #[test]
        fn newtype_variant_f64() {
            let val = Wrapper::Big(1.234f64);
            let ion = to_string(&val).unwrap();
            assert_eq!(
                Element::read_first("Big::1.234e0"),
                Element::read_first(&ion)
            );
            let roundtrip: Wrapper = from_ion(&ion).unwrap();
            assert_eq!(val, roundtrip);
        }

        #[test]
        fn newtype_variant_seq() {
            let val = Wrapper::Items(vec![1, 2, 3]);
            let ion = to_string(&val).unwrap();
            assert_eq!(
                Element::read_first("Items::[1, 2, 3]"),
                Element::read_first(&ion)
            );
            let roundtrip: Wrapper = from_ion(&ion).unwrap();
            assert_eq!(val, roundtrip);
        }

        #[test]
        fn newtype_variant_map() {
            let mut map = BTreeMap::new();
            map.insert("a".to_string(), 1u32);
            let val = Wrapper::Dict(map);
            let ion = to_string(&val).unwrap();
            assert_eq!(
                Element::read_first("Dict::{a: 1}"),
                Element::read_first(&ion)
            );
            let roundtrip: Wrapper = from_ion(&ion).unwrap();
            assert_eq!(val, roundtrip);
        }

        #[test]
        fn newtype_variant_struct() {
            let val = Wrapper::Record { x: 10, y: 20 };
            let ion = to_string(&val).unwrap();
            assert_eq!(
                Element::read_first("Record::{x: 10, y: 20}"),
                Element::read_first(&ion)
            );
            let roundtrip: Wrapper = from_ion(&ion).unwrap();
            assert_eq!(val, roundtrip);
        }

        #[test]
        fn newtype_variant_decimal() {
            let val = Wrapper::Price(Decimal::new(199, -2));
            let ion = to_string(&val).unwrap();
            assert_eq!(
                Element::read_first("Price::1.99"),
                Element::read_first(&ion)
            );
            let roundtrip: Wrapper = from_ion(&ion).unwrap();
            assert_eq!(val, roundtrip);
        }

        #[test]
        fn newtype_variant_timestamp() {
            let ts = Timestamp::with_ymd(2024, 6, 15)
                .with_hms(12, 0, 0)
                .build()
                .unwrap();
            let val = Wrapper::When(ts.clone());
            let ion = to_string(&val).unwrap();
            assert_eq!(
                Element::read_first("When::2024-06-15T12:00:00-00:00"),
                Element::read_first(&ion)
            );
            let roundtrip: Wrapper = from_ion(&ion).unwrap();
            assert_eq!(val, roundtrip);
        }
    }

    /// 2^128, too wide for an inline coefficient.
    fn heap_backed_coefficient() -> Int {
        let mut bytes = [0u8; 17];
        bytes[16] = 1;
        let coefficient = Int::from_le_signed_bytes(&bytes);
        #[cfg(feature = "experimental")]
        assert!(!coefficient.is_inline());
        coefficient
    }

    #[rstest]
    #[case::positive(Decimal::new(355, -1))]
    #[case::negative(Decimal::new(-355, -1))]
    #[case::zero(Decimal::new(0, 3))]
    #[case::negative_zero(Decimal::negative_zero_with_exponent(-3))]
    #[case::heap_backed(Decimal::new(heap_backed_coefficient(), -4))]
    #[case::negative_heap_backed(Decimal::new(heap_backed_coefficient().neg(), -4))]
    fn decimal_roundtrip(#[case] decimal: Decimal) {
        let from_text: Decimal = from_ion(to_string(&decimal).unwrap().as_str()).unwrap();
        assert_eq!(IonData::from(&from_text), IonData::from(&decimal));

        let from_binary: Decimal = from_ion(to_binary(&decimal).unwrap().as_slice()).unwrap();
        assert_eq!(IonData::from(&from_binary), IonData::from(&decimal));
    }

    #[rstest]
    #[case::year(Timestamp::with_year(2024).build())]
    #[case::month(Timestamp::with_year(2024).with_month(6).build())]
    #[case::day(Timestamp::with_ymd(2024, 6, 15).build())]
    #[case::minute_unknown_offset(Timestamp::with_ymd(2024, 6, 15).with_hour_and_minute(12, 30).build())]
    #[case::minute_negative_offset(Timestamp::with_ymd(2024, 6, 15).with_hour_and_minute(12, 30).with_offset(-1439).build())]
    #[case::second(Timestamp::with_ymd(2024, 6, 15).with_hms(12, 30, 45).with_offset(1439).build())]
    #[case::fractional_zero(Timestamp::with_ymd(2024, 6, 15).with_hms(12, 30, 45).with_milliseconds(0).with_offset(0).build())]
    #[case::fractional_arbitrary(Timestamp::with_ymd(3030, 3, 31).with_hms(17, 31, 57).with_fractional_seconds(Decimal::new(27, -12)).with_offset(0).build())]
    #[case::second_unknown_offset(Timestamp::with_ymd(2024, 6, 15).with_hms(12, 30, 45).build())]
    #[case::fractional_unknown_offset(Timestamp::with_ymd(2024, 6, 15).with_hms(12, 30, 45).with_milliseconds(123).build())]
    #[case::minute_positive_offset(Timestamp::with_ymd(2024, 6, 15).with_hour_and_minute(12, 30).with_offset(330).build())]
    #[case::fractional_18_digits(Timestamp::with_ymd(2024, 6, 15).with_hms(12, 30, 45).with_fractional_seconds(Decimal::new(123_456_789_012_345_678_i64, -18)).with_offset(-480).build())]
    #[case::year_1(Timestamp::with_year(1).build())]
    #[case::year_9999(Timestamp::with_year(9999).build())]
    fn timestamp_roundtrip(#[case] timestamp: IonResult<Timestamp>) {
        let timestamp = timestamp.unwrap();
        let from_text: Timestamp = from_ion(to_string(&timestamp).unwrap().as_str()).unwrap();
        assert_eq!(IonData::from(&from_text), IonData::from(&timestamp));

        let from_binary: Timestamp = from_ion(to_binary(&timestamp).unwrap().as_slice()).unwrap();
        assert_eq!(IonData::from(&from_binary), IonData::from(&timestamp));
    }

    /// Serializes a non-payload value under a tunnel type name.
    struct SpoofedTunnel(&'static str);

    impl Serialize for SpoofedTunnel {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            serializer.serialize_newtype_struct(self.0, "not a tunnel payload")
        }
    }

    #[rstest]
    #[case::decimal(decimal::TUNNELED_DECIMAL_TYPE_NAME)]
    #[case::timestamp(timestamp::TUNNELED_TIMESTAMP_TYPE_NAME)]
    fn spoofed_tunnel_name_errors(#[case] name: &'static str) {
        assert!(to_string(&SpoofedTunnel(name)).is_err());
        assert!(to_binary(&SpoofedTunnel(name)).is_err());
    }

    #[derive(Debug, Deserialize)]
    #[serde(untagged)]
    enum DecimalOrTimestamp {
        Decimal(Decimal),
        Timestamp(Timestamp),
    }

    /// Reaches `value` through serde's buffered `flatten` path.
    #[derive(Deserialize)]
    struct Flattened<T> {
        #[serde(flatten)]
        inner: Field<T>,
    }

    #[derive(Deserialize)]
    struct Field<T> {
        value: T,
    }

    fn from_flattened<T: DeserializeOwned>(value: &str) -> IonResult<T> {
        from_ion::<Flattened<T>, _>(format!("{{value: {value}}}").as_str()).map(|f| f.inner.value)
    }

    #[rstest]
    #[case::inline(Decimal::new(35, -1))]
    #[case::heap_backed(Decimal::new(heap_backed_coefficient(), -4))]
    fn decimal_deserializes_through_buffered_paths(#[case] decimal: Decimal) {
        let ion = decimal.to_string();

        let flattened: Decimal = from_flattened(&ion).unwrap();
        assert_eq!(IonData::from(&flattened), IonData::from(&decimal));

        match from_ion(ion.as_str()).unwrap() {
            DecimalOrTimestamp::Decimal(untagged) => {
                assert_eq!(IonData::from(&untagged), IonData::from(&decimal))
            }
            other => panic!("expected a Decimal, got {other:?}"),
        }
    }

    /// The untagged cases also check that a timestamp is not taken for the `Decimal` variant,
    /// which is tried first.
    #[rstest]
    #[case::whole_seconds(Timestamp::with_ymd(2024, 6, 15).with_hms(12, 30, 0).with_offset(0).build())]
    #[case::fractional(Timestamp::with_ymd(2024, 6, 15).with_hms(12, 30, 45).with_milliseconds(123).with_offset(-480).build())]
    fn timestamp_deserializes_through_buffered_paths(#[case] timestamp: IonResult<Timestamp>) {
        let timestamp = timestamp.unwrap();
        let ion = timestamp.to_string();

        let flattened: Timestamp = from_flattened(&ion).unwrap();
        assert_eq!(IonData::from(&flattened), IonData::from(&timestamp));

        match from_ion(ion.as_str()).unwrap() {
            DecimalOrTimestamp::Timestamp(untagged) => {
                assert_eq!(IonData::from(&untagged), IonData::from(&timestamp))
            }
            other => panic!("expected a Timestamp, got {other:?}"),
        }
    }

    /// The list and string cases hold a well-formed `Decimal` payload for `5`.
    #[rstest]
    #[case::list(
        "[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5]",
        "expected an Ion serde tunnel payload"
    )]
    #[case::string(
        r#""\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x05""#,
        "expected an Ion serde tunnel payload"
    )]
    #[case::timestamp("2024-06-15T12:30:00Z", "missing or wrong kind")]
    fn flattened_decimal_rejects_other_types(#[case] value: &str, #[case] expected: &str) {
        let result = from_flattened::<Decimal>(value);
        assert!(result.is_err_and(|e| e.to_string().contains(expected)));
    }

    #[test]
    fn flattened_timestamp_rejects_decimal() {
        assert!(from_flattened::<Timestamp>("3.5").is_err());
    }

    /// Requests a tunnel `newtype_struct` with a visitor that only accepts a `u64`.
    struct SpoofedTunnelRequest<const TIMESTAMP: bool>;

    impl<'de, const TIMESTAMP: bool> Deserialize<'de> for SpoofedTunnelRequest<TIMESTAMP> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            struct U64Visitor;

            impl Visitor<'_> for U64Visitor {
                type Value = u64;

                fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                    formatter.write_str("a u64")
                }

                fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E> {
                    Ok(value)
                }
            }

            let name = if TIMESTAMP {
                timestamp::TUNNELED_TIMESTAMP_TYPE_NAME
            } else {
                decimal::TUNNELED_DECIMAL_TYPE_NAME
            };
            deserializer.deserialize_newtype_struct(name, U64Visitor)?;
            Ok(SpoofedTunnelRequest)
        }
    }

    #[test]
    fn spoofed_tunnel_name_deserialize_errors() {
        let decimal = from_ion::<SpoofedTunnelRequest<false>, _>("3.5");
        assert!(decimal.is_err_and(|e| e.to_string().contains("expected a u64")));

        let timestamp = from_ion::<SpoofedTunnelRequest<true>, _>("2024-06-15T12:30:00Z");
        assert!(timestamp.is_err_and(|e| e.to_string().contains("expected a u64")));
    }

    #[rstest]
    #[case::empty(vec![])]
    #[case::wrong_kind(vec![TIMESTAMP_KIND, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5])]
    #[case::truncated_exponent(vec![DECIMAL_KIND, 0, 0, 0])]
    #[case::missing_sign(vec![DECIMAL_KIND, 0, 0, 0, 0, 0, 0, 0, 0])]
    #[case::bad_sign(vec![DECIMAL_KIND, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5])]
    fn malformed_decimal_payload_errors(#[case] bytes: Vec<u8>) {
        assert!(Decimal::try_from(TunnelBytes(bytes)).is_err());
    }

    /// A valid timestamp payload with its kind byte replaced and its length changed to `len`.
    fn timestamp_payload(kind: u8, len: usize) -> Vec<u8> {
        let TunnelBytes(mut bytes) =
            TunnelBytes::from(&Timestamp::with_year(2024).build().unwrap());
        bytes[0] = kind;
        bytes.resize(len, 0);
        bytes
    }

    #[rstest]
    #[case::empty(vec![])]
    #[case::wrong_kind(timestamp_payload(DECIMAL_KIND, 17))]
    #[case::truncated(timestamp_payload(TIMESTAMP_KIND, 16))]
    #[case::too_long(timestamp_payload(TIMESTAMP_KIND, 18))]
    fn malformed_timestamp_payload_errors(#[case] bytes: Vec<u8>) {
        assert!(Timestamp::try_from(TunnelBytes(bytes)).is_err());
    }

    /// Exact text of `to_string` and `to_pretty`. In a module of its own so that its types keep
    /// the names their serialized annotations are expected to have.
    mod exact_text {
        use super::*;
        use indoc::indoc;

        #[derive(Serialize)]
        struct Inner {
            a: i32,
            b: Vec<String>,
        }

        #[derive(Serialize)]
        struct Outer {
            name: String,
            inner: Inner,
            tags: Vec<i32>,
        }

        fn outer() -> Outer {
            Outer {
                name: "n".to_string(),
                inner: Inner {
                    a: 1,
                    b: vec!["x".to_string(), "y".to_string()],
                },
                tags: vec![2, 3],
            }
        }

        #[derive(Serialize)]
        struct Pair(i32, String);

        #[derive(Serialize)]
        enum Shape {
            Circle(f64),
            Rect(i32, i32),
        }

        /// `to_string` and `to_pretty` produce exactly this text, including the whitespace after
        /// the value. The Pretty cases pin the existing indentation of sequence elements, which is
        /// written twice.
        #[rstest]
        #[case::struct_compact(
            to_string(&outer()),
            r#"{name: "n", inner: {a: 1, b: ["x", "y", ], }, tags: [2, 3, ], } "#
        )]
        #[case::struct_pretty(
            to_pretty(&outer()),
            indoc! {r#"
                {
                  name: "n",
                  inner: {
                    a: 1,
                    b: [
                            "x",
                            "y",
                    ],
                  },
                  tags: [
                        2,
                        3,
                  ],
                }
            "#}
        )]
        #[case::vec_compact(to_string(&vec![1, 2, 3]), "[1, 2, 3, ] ")]
        #[case::vec_pretty(
            to_pretty(&vec![1, 2, 3]),
            indoc! {"
                [
                    1,
                    2,
                    3,
                ]
            "}
        )]
        #[case::tuple_struct_compact(to_string(&Pair(1, "x".to_string())), r#"Pair::[1, "x", ] "#)]
        #[case::tuple_struct_pretty(
            to_pretty(&Pair(1, "x".to_string())),
            indoc! {r#"
                Pair::[
                    1,
                    "x",
                ]
            "#}
        )]
        #[case::newtype_variant_compact(to_string(&Shape::Circle(1.5)), "Circle::1.5e0 ")]
        #[case::newtype_variant_pretty(to_pretty(&Shape::Circle(1.5)), "Circle::1.5e0\n")]
        #[case::tuple_variant_compact(to_string(&Shape::Rect(2, 3)), "Rect::[2, 3, ] ")]
        #[case::tuple_variant_pretty(
            to_pretty(&Shape::Rect(2, 3)),
            indoc! {"
                Rect::[
                    2,
                    3,
                ]
            "}
        )]
        fn text_serialization_is_exact(
            #[case] actual: IonResult<String>,
            #[case] expected: &str,
        ) -> IonResult<()> {
            assert_eq!(actual?, expected);
            Ok(())
        }
    }

    /// The local year of this `DateTime` is 10000, which `Timestamp` cannot represent.
    #[test]
    fn chrono_datetime_with_local_year_10000_fails_to_serialize() {
        #[serde_as]
        #[derive(Serialize)]
        struct Test {
            #[serde_as(as = "crate::Timestamp")]
            date: DateTime<FixedOffset>,
        }

        let offset = FixedOffset::east_opt(2 * 60 * 60).unwrap();
        let date = Utc
            .with_ymd_and_hms(9999, 12, 31, 23, 0, 0)
            .unwrap()
            .with_timezone(&offset);
        assert!(to_string(&Test { date }).is_err());
        assert!(to_binary(&Test { date }).is_err());
    }

    /// `to_utc` can produce UTC year 0, which is outside Ion's 1..=9999 range.
    #[test]
    fn to_utc_with_year_0_fails_to_serialize() {
        let timestamp = Timestamp::with_ymd(1, 1, 1)
            .with_hour_and_minute(0, 30)
            .with_offset(60)
            .build()
            .unwrap()
            .to_utc();
        assert_eq!(timestamp.year(), 0);
        assert!(to_string(&timestamp).is_err());
        assert!(to_binary(&timestamp).is_err());
    }

    mod depth_limit {
        use std::fmt::Debug;
        use std::thread;

        use rstest::rstest;
        use serde::{Deserialize, Serialize};

        use crate::constants::MAX_READ_WRITE_DEPTH;
        use crate::lazy::binary::test_utilities::{
            binary_nested, binary_type_descriptor, binary_value, to_binary_ion,
            LAZY_BINARY_DEPTH_IS_CHECKED,
        };
        use crate::read_config::assert_max_read_depth_exceeded;
        use crate::serde::de::{
            max_recursion_depth_exceeded_message, MAX_RECURSION_DEPTH,
            MAX_RECURSION_DEPTH_EXCEEDED_PREFIX,
        };
        use crate::serde::{from_ion, to_binary, to_string};
        use crate::{IonError, IonResult, IonType};

        const MAX: usize = MAX_READ_WRITE_DEPTH as usize;
        const MAX_RECURSION: usize = MAX_RECURSION_DEPTH as usize;

        #[derive(Deserialize, Debug)]
        struct ListTree(#[allow(dead_code)] Vec<ListTree>);

        /// Binary structs built by `binary_nested` have one field, named `name`.
        #[derive(Serialize, Deserialize, Debug, PartialEq)]
        struct StructTree {
            name: Option<Box<StructTree>>,
        }

        /// `levels` nested `StructTree`s.
        fn struct_tree(levels: usize) -> StructTree {
            (1..levels).fold(StructTree { name: None }, |inner, _| StructTree {
                name: Some(Box::new(inner)),
            })
        }

        /// Refers to itself through `Option` alone, so deserialization reads any non-null value as
        /// nested `Some`s. Every `SelfOpt` serializes as `null`.
        #[derive(Serialize, Deserialize, Debug)]
        struct SelfOpt(Option<Box<SelfOpt>>);

        /// A `SelfOpt` with `somes` nested `Some`s.
        fn self_opt(somes: usize) -> SelfOpt {
            (0..somes).fold(SelfOpt(None), |inner, _| SelfOpt(Some(Box::new(inner))))
        }

        #[derive(Serialize, Deserialize, Debug, PartialEq)]
        enum Chain {
            Leaf,
            Wrap(Box<Chain>),
            List(Vec<Chain>),
            Struct(Child),
        }

        /// The payload of `Chain::Struct`.
        #[derive(Serialize, Deserialize, Debug, PartialEq)]
        struct Child {
            child: Box<Chain>,
        }

        /// A `Chain` with `wraps` newtype variants around `Leaf`.
        fn chain(wraps: usize) -> Chain {
            (0..wraps).fold(Chain::Leaf, |inner, _| Chain::Wrap(Box::new(inner)))
        }

        /// The number of `Wrap`s around each container in `wrapped_containers`.
        const WRAPS_PER_LEVEL: usize = MAX_RECURSION / MAX - 2;

        /// The part of the recursion limit that `wrapped_containers` leaves for its innermost
        /// `Wrap`s.
        const REMAINDER: usize = MAX_RECURSION % MAX;

        /// `chain(innermost_wraps)` in `MAX` nested `container` variants (`List` or `Struct`), each
        /// in `WRAPS_PER_LEVEL` `Wrap`s. Each level uses the `List` or `Struct` variant, its
        /// container, and the `Wrap`s. With `innermost_wraps` of 0, the result uses all of the
        /// recursion limit except `REMAINDER`.
        fn wrapped_containers(container: &str, innermost_wraps: usize) -> Chain {
            (0..MAX).fold(chain(innermost_wraps), |inner, _| {
                let level = match container {
                    "List" => Chain::List(vec![inner]),
                    "Struct" => Chain::Struct(Child {
                        child: Box::new(inner),
                    }),
                    _ => {
                        unreachable!("not a `Chain` variant with a container payload: {container}")
                    }
                };
                (0..WRAPS_PER_LEVEL).fold(level, |inner, _| Chain::Wrap(Box::new(inner)))
            })
        }

        /// Encodes `wrapped_containers(container, innermost_wraps)` in `outer_wraps` more `Wrap`s
        /// as binary Ion if `binary` is true, and as text Ion otherwise. The serializer rejects
        /// values beyond the recursion limit, so the text is written by hand.
        fn wrapped_containers_data(
            container: &str,
            outer_wraps: usize,
            innermost_wraps: usize,
            binary: bool,
        ) -> IonResult<Vec<u8>> {
            let wraps = "Wrap::".repeat(WRAPS_PER_LEVEL);
            let innermost = format!("{}Leaf", "Wrap::".repeat(innermost_wraps));
            let text = (0..MAX).fold(innermost, |inner, _| match container {
                "List" => format!("{wraps}List::[{inner}]"),
                "Struct" => format!("{wraps}Struct::{{child: {inner}}}"),
                _ => unreachable!("not a `Chain` variant with a container payload: {container}"),
            });
            let text = format!("{}{text}", "Wrap::".repeat(outer_wraps));
            if binary {
                to_binary_ion(&text)
            } else {
                Ok(text.into_bytes())
            }
        }

        /// With `Body`, a recursive type with two newtype variants and one list per level.
        #[derive(Serialize, Deserialize, Debug, PartialEq)]
        enum Message {
            Payload(Body),
        }

        #[derive(Serialize, Deserialize, Debug, PartialEq)]
        enum Body {
            Items(Vec<Message>),
        }

        /// A `Message` with `levels` nested lists, the innermost of which is empty.
        fn message(levels: usize) -> Message {
            let items = (1..levels).fold(vec![], |items, _| {
                vec![Message::Payload(Body::Items(items))]
            });
            Message::Payload(Body::Items(items))
        }

        /// Encodes `message(levels)` as an Ion 1.0 binary stream. The managed writer rejects values
        /// deeper than the limit, so the encoding is written by hand.
        fn binary_message(levels: usize) -> Vec<u8> {
            let body = (0..levels).fold(vec![], |items, _| {
                // Annotated with `Payload` (`$10`) and `Items` (`$11`).
                binary_value(
                    0xE0,
                    [vec![0x82, 0x8A, 0x8B], binary_value(0xB0, items)].concat(),
                )
            });
            binary_stream(&["Payload", "Items"], body)
        }

        /// A recursive enum with one variant of each kind whose payload is a container.
        #[derive(Serialize, Deserialize, Debug, PartialEq)]
        enum Node {
            Leaf,
            List(Vec<Node>),
            Tuple(Box<Node>, u8),
            Struct { child: Box<Node> },
        }

        /// `Leaf` in `levels` nested `variant` variants.
        fn node(variant: &str, levels: usize) -> Node {
            (0..levels).fold(Node::Leaf, |child, _| match variant {
                "List" => Node::List(vec![child]),
                "Tuple" => Node::Tuple(Box::new(child), 0),
                "Struct" => Node::Struct {
                    child: Box::new(child),
                },
                _ => unreachable!("not a `Node` variant with a container payload: {variant}"),
            })
        }

        /// Encodes `node(variant, levels)` as an Ion 1.0 binary stream. The managed writer rejects
        /// values deeper than the limit, so the encoding is written by hand.
        fn binary_node(variant: &str, levels: usize) -> Vec<u8> {
            let leaf = binary_value(0x70, vec![10]);
            let body = (0..levels).fold(leaf, |child, _| {
                let (annotation, container) = match variant {
                    "List" => (11, binary_value(0xB0, child)),
                    // The second element is the integer 0.
                    "Tuple" => (12, binary_value(0xB0, [child, vec![0x20]].concat())),
                    // The field is named `child` (`$14`).
                    "Struct" => (13, binary_value(0xD0, [vec![0x80 | 14], child].concat())),
                    _ => unreachable!("not a `Node` variant with a container payload: {variant}"),
                };
                binary_value(0xE0, [vec![0x81, 0x80 | annotation], container].concat())
            });
            binary_stream(&["Leaf", "List", "Tuple", "Struct", "child"], body)
        }

        /// Encodes `body` as an Ion 1.0 binary stream whose local symbol table defines `symbols`
        /// as `$10` onward.
        fn binary_stream(symbols: &[&str], body: Vec<u8>) -> Vec<u8> {
            let symbols = symbols
                .iter()
                .flat_map(|text| binary_value(0x80, text.as_bytes().to_vec()))
                .collect();
            // `{symbols: [...]}` annotated with `$ion_symbol_table` (`$3`).
            let symbol_table = binary_value(
                0xE0,
                [
                    vec![0x81, 0x83],
                    binary_value(0xD0, [vec![0x87], binary_value(0xB0, symbols)].concat()),
                ]
                .concat(),
            );
            [vec![0xE0, 0x01, 0x00, 0xEA], symbol_table, body].concat()
        }

        /// Encodes `value` as binary Ion if `binary` is true, and as text Ion otherwise.
        fn encode(value: &impl Serialize, binary: bool) -> IonResult<Vec<u8>> {
            if binary {
                to_binary(value)
            } else {
                to_string(value).map(String::into_bytes)
            }
        }

        /// Deserializes binary input made of `containers` nested containers of type `kind`, the
        /// innermost of which is empty.
        fn from_binary_nested(kind: IonType, containers: usize) -> IonResult<()> {
            let data = binary_nested(kind, containers - 1, vec![binary_type_descriptor(kind)]);
            match kind {
                IonType::List | IonType::SExp => from_ion::<ListTree, _>(data).map(drop),
                IonType::Struct => from_ion::<StructTree, _>(data).map(drop),
                _ => unreachable!("not a tested container type: {kind}"),
            }
        }

        /// Runs `test` on a thread with a 2 MiB stack, the default for threads spawned by `std`.
        fn on_2_mib_stack(test: impl FnOnce() -> IonResult<()> + Send + 'static) -> IonResult<()> {
            thread::Builder::new()
                .stack_size(2 * 1024 * 1024)
                .spawn(test)?
                .join()
                .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
        }

        /// Asserts that `result` is a decoding error whose description starts with `prefix`.
        #[track_caller]
        fn assert_decoding_error(result: IonResult<impl Debug>, prefix: &str) {
            match result {
                Err(IonError::Decoding(e)) if e.description().starts_with(prefix) => {}
                other => {
                    panic!("expected a decoding error starting with {prefix:?}, found {other:?}")
                }
            }
        }

        #[rstest]
        fn reads_binary_containers_at_the_maximum_depth(
            #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
        ) -> IonResult<()> {
            from_binary_nested(kind, MAX)
        }

        #[rstest]
        fn rejects_binary_containers_beyond_the_maximum_depth(
            #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
        ) {
            assert_max_read_depth_exceeded(from_binary_nested(kind, MAX + 1));
        }

        #[rstest]
        #[cfg_attr(miri, ignore = "too slow under Miri")]
        fn rejects_binary_containers_far_beyond_the_maximum_depth(
            #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
        ) {
            assert_max_read_depth_exceeded(from_binary_nested(kind, 10_000));
        }

        /// Deserializing an `i64` from a list fails with an error that describes the list.
        #[test]
        fn rejects_lists_nested_beyond_the_maximum_depth_as_an_i64() {
            let data = binary_nested(IonType::List, MAX + 1, vec![0x21, 0x01]);
            assert_decoding_error(from_ion::<i64, _>(data), "expected an int");
        }

        #[test]
        #[cfg_attr(miri, ignore = "too slow under Miri")]
        fn rejects_lists_nested_far_beyond_the_maximum_depth_as_an_i64() {
            // Formatting the list recurses once per level until a list cannot be read, so without
            // the depth check it would recurse 100,000 times.
            if !LAZY_BINARY_DEPTH_IS_CHECKED {
                return;
            }
            let data = binary_nested(IonType::List, 100_000, vec![0x21, 0x01]);
            assert_decoding_error(from_ion::<i64, _>(data), "expected an int");
        }

        /// Newtype variants do not use container levels, so two of them per list do not lower the
        /// number of lists that can be nested.
        #[rstest]
        fn round_trips_newtype_variants_in_containers_at_the_maximum_depth(
            #[values(false, true)] binary: bool,
        ) -> IonResult<()> {
            on_2_mib_stack(move || {
                let expected = message(MAX);
                assert_eq!(
                    from_ion::<Message, _>(encode(&expected, binary)?)?,
                    expected
                );
                Ok(())
            })
        }

        #[test]
        fn reads_hand_encoded_newtype_variants_in_containers_at_the_maximum_depth() -> IonResult<()>
        {
            assert_eq!(from_ion::<Message, _>(binary_message(MAX))?, message(MAX));
            Ok(())
        }

        #[test]
        fn rejects_newtype_variants_in_containers_beyond_the_maximum_depth() {
            assert_max_read_depth_exceeded(from_ion::<Message, _>(binary_message(MAX + 1)));
        }

        /// A variant whose payload is a container uses one level, like the container alone.
        #[rstest]
        fn round_trips_container_variants_at_the_maximum_depth(
            #[values("List", "Tuple", "Struct")] variant: &str,
            #[values(false, true)] binary: bool,
        ) -> IonResult<()> {
            let expected = node(variant, MAX);
            assert_eq!(from_ion::<Node, _>(encode(&expected, binary)?)?, expected);
            Ok(())
        }

        #[rstest]
        fn reads_hand_encoded_container_variants_at_the_maximum_depth(
            #[values("List", "Tuple", "Struct")] variant: &str,
        ) -> IonResult<()> {
            let actual: Node = from_ion(binary_node(variant, MAX))?;
            assert_eq!(actual, node(variant, MAX));
            Ok(())
        }

        #[rstest]
        fn rejects_container_variants_beyond_the_maximum_depth(
            #[values("List", "Tuple", "Struct")] variant: &str,
        ) {
            assert_max_read_depth_exceeded(from_ion::<Node, _>(binary_node(variant, MAX + 1)));
        }

        /// The binary reader rejects annotation sequences longer than 255 bytes, which is fewer
        /// than `MAX_RECURSION` one-byte symbol IDs by default, so this chain is read from text.
        #[test]
        #[cfg_attr(miri, ignore = "too slow under Miri")]
        fn round_trips_newtype_variants_at_the_maximum_recursion_depth() -> IonResult<()> {
            on_2_mib_stack(|| {
                let expected = chain(MAX_RECURSION);
                assert_eq!(from_ion::<Chain, _>(to_string(&expected)?)?, expected);
                Ok(())
            })
        }

        /// Newtype variants are annotations on one value, so a chain of them recurses without
        /// entering any container.
        #[rstest]
        #[cfg_attr(miri, ignore = "too slow under Miri")]
        fn rejects_newtype_variants_beyond_the_maximum_recursion_depth(
            #[values(MAX_RECURSION + 1, 10_000)] wraps: usize,
        ) {
            let text = format!("{}Leaf", "Wrap::".repeat(wraps));
            assert_decoding_error(
                from_ion::<Chain, _>(text),
                MAX_RECURSION_DEPTH_EXCEEDED_PREFIX,
            );
        }

        /// `Some` is the value itself, so a type that refers to itself through `Option` recurses on
        /// any non-null value until the recursion limit.
        #[test]
        fn rejects_a_type_that_recurses_through_option() -> IonResult<()> {
            on_2_mib_stack(|| {
                assert_decoding_error(
                    from_ion::<SelfOpt, _>("1"),
                    MAX_RECURSION_DEPTH_EXCEEDED_PREFIX,
                );
                Ok(())
            })
        }

        /// Each level uses one struct and one `Some`, so `MAX` levels are within the recursion
        /// limit.
        #[rstest]
        fn round_trips_optional_struct_fields_at_the_maximum_depth(
            #[values(false, true)] binary: bool,
        ) -> IonResult<()> {
            let expected = struct_tree(MAX);
            assert_eq!(
                from_ion::<StructTree, _>(encode(&expected, binary)?)?,
                expected
            );
            Ok(())
        }

        #[rstest]
        fn round_trips_containers_and_newtype_variants_at_the_maximum_recursion_depth(
            #[values("List", "Struct")] container: &str,
            #[values(false, true)] binary: bool,
        ) -> IonResult<()> {
            let container = container.to_owned();
            on_2_mib_stack(move || {
                let expected = wrapped_containers(&container, REMAINDER);
                assert_eq!(from_ion::<Chain, _>(encode(&expected, binary)?)?, expected);
                Ok(())
            })
        }

        /// One more `Wrap` innermost exceeds the recursion limit at a newtype variant. One more
        /// outermost, with none innermost, exceeds it on entering the innermost container.
        #[rstest]
        #[case::at_a_newtype_variant(0, REMAINDER + 1)]
        #[case::entering_a_container(REMAINDER + 1, 0)]
        fn rejects_containers_and_newtype_variants_beyond_the_maximum_recursion_depth(
            #[case] outer_wraps: usize,
            #[case] innermost_wraps: usize,
            #[values("List", "Struct")] container: &str,
            #[values(false, true)] binary: bool,
        ) -> IonResult<()> {
            let data = wrapped_containers_data(container, outer_wraps, innermost_wraps, binary)?;
            assert_decoding_error(
                from_ion::<Chain, _>(data),
                MAX_RECURSION_DEPTH_EXCEEDED_PREFIX,
            );
            Ok(())
        }

        /// The binary reader cannot read `chain(MAX_RECURSION)` back (see
        /// `round_trips_newtype_variants_at_the_maximum_recursion_depth`), and every `SelfOpt` is
        /// written as `null`, so these values are only written.
        #[rstest]
        #[case::newtype_variants(|binary| encode(&chain(MAX_RECURSION), binary))]
        #[case::somes(|binary| encode(&self_opt(MAX_RECURSION), binary))]
        fn writes_values_at_the_maximum_recursion_depth(
            #[case] write: fn(bool) -> IonResult<Vec<u8>>,
            #[values(false, true)] binary: bool,
        ) -> IonResult<()> {
            write(binary).map(drop)
        }

        /// Serialization applies the recursion limit that deserialization checks.
        #[rstest]
        #[case::newtype_variants(|binary| encode(&chain(MAX_RECURSION + 1), binary))]
        #[case::somes(|binary| encode(&self_opt(MAX_RECURSION + 1), binary))]
        #[case::lists(|binary| encode(&wrapped_containers("List", REMAINDER + 1), binary))]
        #[case::structs(|binary| encode(&wrapped_containers("Struct", REMAINDER + 1), binary))]
        fn rejects_writing_values_beyond_the_maximum_recursion_depth(
            #[case] write: fn(bool) -> IonResult<Vec<u8>>,
            #[values(false, true)] binary: bool,
        ) {
            match write(binary) {
                Err(IonError::Encoding(e))
                    if e.to_string() == max_recursion_depth_exceeded_message() => {}
                other => panic!("expected a maximum recursion depth error, found {other:?}"),
            }
        }

        /// The value's own symbol names the variant of the enum after the one named by its last
        /// annotation, and no enum after that.
        #[rstest]
        fn reads_variant_names_from_annotations_and_the_symbol(
            #[values(("Leaf", 0), ("Wrap::Leaf", 1), ("Wrap::Wrap::Leaf", 2))] case: (&str, usize),
            #[values(false, true)] binary: bool,
        ) -> IonResult<()> {
            let (text, wraps) = case;
            let data = if binary {
                to_binary_ion(text)?
            } else {
                text.as_bytes().to_vec()
            };
            assert_eq!(from_ion::<Chain, _>(data)?, chain(wraps));
            Ok(())
        }

        /// The symbol `Wrap` names the variant of the enum after the one named by the value's last
        /// annotation. The newtype variant's payload is another enum on the same value, which has
        /// neither an annotation nor the symbol to name its variant.
        #[rstest]
        fn rejects_a_newtype_variant_payload_without_a_variant_annotation(
            #[values("Wrap", "Wrap::Wrap")] text: &str,
            #[values(false, true)] binary: bool,
        ) -> IonResult<()> {
            let data = if binary {
                to_binary_ion(text)?
            } else {
                text.as_bytes().to_vec()
            };
            assert_decoding_error(
                from_ion::<Chain, _>(data),
                "expected an enum variant annotation",
            );
            Ok(())
        }
    }
}
