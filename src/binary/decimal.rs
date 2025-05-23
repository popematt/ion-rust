// Copyright Amazon.com, Inc. or its affiliates.

use std::io::Write;

use arrayvec::ArrayVec;

use crate::binary::int::DecodedInt;
use crate::binary::var_int::VarInt;
use crate::binary::var_uint::VarUInt;
use crate::decimal::coefficient::Sign;
use crate::ion_data::IonEq;
use crate::result::{IonFailure, IonResult};
use crate::{Decimal, Int, IonError};

const MAX_INLINE_LENGTH: usize = 13;

const DECIMAL_BUFFER_SIZE: usize = 32;
const DECIMAL_POSITIVE_ZERO: Decimal = Decimal {
    coefficient_value: Int::ZERO,
    coefficient_sign: Sign::Positive,
    exponent: 0,
};

/// Provides support to write [`Decimal`] into [Ion binary].
///
/// [Ion binary]: https://amazon-ion.github.io/ion-docs/docs/binary.html#5-decimal
pub trait DecimalBinaryEncoder {
    /// Encodes the content of a [`Decimal`] as per the Ion binary encoding.
    /// Returns the length of the encoded bytes.
    ///
    /// This does not encode the type descriptor nor the associated length.
    /// Prefer [`DecimalBinaryEncoder::encode_decimal_value`] for that.
    fn encode_decimal(&mut self, decimal: &Decimal) -> IonResult<usize>;

    /// Encodes a [`Decimal`] as an Ion value with the type descriptor and
    /// length. Returns the length of the encoded bytes.
    fn encode_decimal_value(&mut self, decimal: &Decimal) -> IonResult<usize>;
}

impl<W> DecimalBinaryEncoder for W
where
    W: Write,
{
    fn encode_decimal(&mut self, decimal: &Decimal) -> IonResult<usize> {
        // 0d0 has no representation, as per the spec.
        if decimal.ion_eq(&DECIMAL_POSITIVE_ZERO) {
            return Ok(0);
        }

        let mut bytes_written: usize = 0;

        bytes_written += VarInt::write_i64(self, decimal.exponent)?;

        match decimal.coefficient().as_int() {
            Some(int) if int == Int::ZERO => {
                // From the spec: "The subfield should not be present (that is, it
                // has zero length) when the coefficient’s value is (positive)
                // zero."
            }
            Some(int) => {
                bytes_written += DecodedInt::write(self, int)?;
            }
            None => {
                bytes_written += DecodedInt::write_negative_zero(self)?;
            }
        }

        Ok(bytes_written)
    }

    fn encode_decimal_value(&mut self, decimal: &Decimal) -> IonResult<usize> {
        let mut bytes_written: usize = 0;
        // First encode the decimal value to a stack-allocated buffer.
        // We need to know its encoded length before we can write out
        // the preceding type descriptor.
        let mut encoded: ArrayVec<u8, DECIMAL_BUFFER_SIZE> = ArrayVec::new();
        encoded.encode_decimal(decimal).map_err(|_e| {
            IonError::encoding_error("found a decimal that was too large for the configured buffer")
        })?;

        // Now that we have the value's encoded bytes, we can encode its header
        // and write it to the output stream.
        let type_descriptor: u8;
        if encoded.len() <= MAX_INLINE_LENGTH {
            // The value is small enough to encode its length in the type
            // descriptor byte.
            type_descriptor = 0x50 | encoded.len() as u8;
            self.write_all(&[type_descriptor])?;
            bytes_written += 1;
        } else {
            // The value is too large to encode its length in the type descriptor
            // byte; we'll encode it as a VarUInt that follows the type descriptor
            // byte instead.
            type_descriptor = 0x5E;
            self.write_all(&[type_descriptor])?;
            bytes_written += 1;
            bytes_written += VarUInt::write_u64(self, encoded.len() as u64)?;
        }

        // Now that we've written the header to the output stream, we can write
        // the value's encoded bytes.
        self.write_all(&encoded[..])?;
        bytes_written += encoded.len();

        Ok(bytes_written)
    }
}

#[cfg(test)]
mod binary_decimal_tests {
    use crate::lazy::any_encoding::AnyEncoding;
    use crate::lazy::encoder::writer::Writer;
    use crate::lazy::encoding::{BinaryEncoding_1_0, Encoding};
    use crate::lazy::reader::Reader;
    use rstest::*;

    use super::*;

    /// This test ensures that we implement [PartialEq] and [IonEq] correctly for the special
    /// decimal value 0d0.
    #[test]
    fn decimal_0d0_is_a_special_zero_value() {
        assert_eq!(DECIMAL_POSITIVE_ZERO, Decimal::new(0, 0));
        assert!(DECIMAL_POSITIVE_ZERO.ion_eq(&Decimal::new(0, 0)));

        assert_eq!(DECIMAL_POSITIVE_ZERO, Decimal::new(0, 10));
        assert!(!DECIMAL_POSITIVE_ZERO.ion_eq(&Decimal::new(0, 10)));

        assert_eq!(DECIMAL_POSITIVE_ZERO, Decimal::new(0, 100));
        assert!(!DECIMAL_POSITIVE_ZERO.ion_eq(&Decimal::new(0, 100)));
    }

    #[rstest]
    #[case::exactly_zero(Decimal::new(0, 0), 1)]
    #[case::zero_with_nonzero_exp(Decimal::new(0, 10), 2)]
    #[case::meaning_of_life(Decimal::new(42, 0), 3)]
    fn bytes_written(#[case] input: Decimal, #[case] expected: usize) -> IonResult<()> {
        let mut buf = vec![];
        let written = buf.encode_decimal_value(&input)?;
        assert_eq!(buf.len(), expected);
        assert_eq!(written, expected);
        Ok(())
    }

    #[rstest]
    #[case::foo(Decimal::new(i128::MAX, 0))]
    #[case::foo(Decimal::new(i128::MAX - 1, 0))]
    #[case::foo(Decimal::new(i128::MIN, 0))]
    #[case::foo(Decimal::new(i128::MIN + 1, 0))]
    #[case::foo(Decimal::new(i128::MAX, i32::MAX))]
    #[case::foo(Decimal::new(i128::MAX - 1, i32::MAX))]
    #[case::foo(Decimal::new(i128::MIN, i32::MIN))]
    #[case::foo(Decimal::new(i128::MIN, i32::MIN))]
    #[case::foo(Decimal::new(i128::MIN + 1, i32::MIN))]
    fn roundtrip_decimals_with_extreme_values(#[case] value: Decimal) -> IonResult<()> {
        let mut writer = Writer::new(BinaryEncoding_1_0::default_write_config(), Vec::new())?;
        writer.write(value)?;
        let output = writer.close()?;
        let mut reader = Reader::new(AnyEncoding, output)?;
        let after_round_trip = reader.expect_next()?.read()?.expect_decimal()?;
        assert_eq!(value, after_round_trip);
        Ok(())
    }
}
