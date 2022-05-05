use num_bigint::BigUint;
use std::io::Write;
use std::mem;

use crate::data_source::IonDataSource;
use crate::result::{decoding_error, IonResult};
use crate::types::integer::{Integer, UInteger};

// This limit is used for stack-allocating buffer space to encode/decode UInts.
const UINT_STACK_BUFFER_SIZE: usize = 16;
// This number was chosen somewhat arbitrarily and could be lifted if a use case demands it.
const MAX_UINT_SIZE_IN_BYTES: usize = 2048;

/// Represents a fixed-length unsigned integer. See the
/// [UInt and Int Fields](http://amzn.github.io/ion-docs/docs/binary.html#uint-and-int-fields)
/// section of the binary Ion spec for more details.
#[derive(Debug)]
pub struct DecodedUInt {
    size_in_bytes: usize,
    value: UInteger,
}

impl DecodedUInt {
    /// Reads a UInt with `length` bytes from the provided data source.
    pub fn read<R: IonDataSource>(data_source: &mut R, length: usize) -> IonResult<DecodedUInt> {
        if length > MAX_UINT_SIZE_IN_BYTES {
            return decoding_error(format!(
                "Found a {}-byte UInt. Max supported size is {} bytes.",
                length, MAX_UINT_SIZE_IN_BYTES
            ));
        }

        if length <= UINT_STACK_BUFFER_SIZE {
            let buffer = &mut [0u8; UINT_STACK_BUFFER_SIZE];
            DecodedUInt::read_using_buffer(data_source, length, buffer)
        } else {
            // We're reading an enormous int. Heap-allocate a Vec to use as storage.
            let mut buffer = vec![0u8; length];
            DecodedUInt::read_using_buffer(data_source, length, buffer.as_mut_slice())
        }
    }

    fn read_using_buffer<R: IonDataSource>(
        data_source: &mut R,
        length: usize,
        buffer: &mut [u8],
    ) -> IonResult<DecodedUInt> {
        // Get a mutable reference to a portion of the buffer just big enough to fit
        // the requested number of bytes.
        let buffer = &mut buffer[0..length];

        data_source.read_exact(buffer)?;

        let value = if length <= mem::size_of::<u64>() {
            // The UInt is small enough to fit in a u64.
            let mut magnitude: u64 = 0;
            for &byte in buffer.iter() {
                let byte = u64::from(byte);
                magnitude <<= 8;
                magnitude |= byte;
            }
            UInteger::U64(magnitude)
        } else {
            // The UInt is too large to fit in a u64; read it as a BigUInt instead
            let magnitude = BigUint::from_bytes_be(buffer);
            UInteger::BigUInt(magnitude)
        };

        Ok(DecodedUInt {
            size_in_bytes: length,
            value,
        })
    }

    /// Encodes the provided `magnitude` as a UInt and writes it to the provided `sink`.
    pub fn write_u64<W: Write>(sink: &mut W, magnitude: u64) -> IonResult<usize> {
        let encoded = encode_uint(magnitude);
        let bytes_to_write = encoded.as_ref();

        sink.write_all(bytes_to_write)?;
        Ok(bytes_to_write.len())
    }

    /// Returns the magnitude of the unsigned integer.
    #[inline(always)]
    pub fn value(&self) -> &UInteger {
        &self.value
    }

    /// Returns the number of bytes that were read from the data source to construct this
    /// unsigned integer.
    #[inline(always)]
    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }
}

impl From<DecodedUInt> for Integer {
    fn from(uint: DecodedUInt) -> Self {
        let DecodedUInt {
            value,
            .. // Ignore 'size_in_bytes'
        } = uint;
        Integer::from(value)
    }
}

/// The big-endian, compact slice of bytes for a UInt (`u64`). Leading zero
/// octets are not part of the representation. See the [spec] for more
/// information.
///
/// [spec]: https://amzn.github.io/ion-docs/docs/binary.html#uint-and-int-fields
#[derive(Copy, Clone, Debug)]
pub struct EncodedUInt {
    be_bytes: [u8; mem::size_of::<u64>()],
    first_occupied_byte: usize,
}

impl EncodedUInt {
    /// Returns the slice view of the encoded UInt.
    pub fn as_bytes(&self) -> &[u8] {
        &self.be_bytes[self.first_occupied_byte..]
    }
}

impl AsRef<[u8]> for EncodedUInt {
    /// The same as [`as_bytes`].
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

/// Returns the magnitude as big-endian bytes.
///
/// ```
/// use ion_rs::binary::uint;
///
/// let repr = uint::encode_uint(5u64);
/// assert_eq!(&[0x05], repr.as_bytes());
///
/// let two_bytes = uint::encode_uint(256u64);
/// assert_eq!(&[0x01, 0x00], two_bytes.as_bytes());
/// ```
pub fn encode_uint(magnitude: u64) -> EncodedUInt {
    // We can divide the number of leading zero bits by 8
    // to to get the number of leading zero bytes.
    let empty_leading_bytes: u32 = magnitude.leading_zeros() / 8;
    let first_occupied_byte = empty_leading_bytes as usize;

    let magnitude_bytes: [u8; mem::size_of::<u64>()] = magnitude.to_be_bytes();

    EncodedUInt {
        be_bytes: magnitude_bytes,
        first_occupied_byte,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    const READ_ERROR_MESSAGE: &str = "Failed to read a UInt from the provided cursor.";
    const WRITE_ERROR_MESSAGE: &str = "Writing a UInt to the provided sink failed.";

    #[test]
    fn test_read_one_byte_uint() {
        let data = &[0b1000_0000];
        let uint = DecodedUInt::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(uint.size_in_bytes(), 1);
        assert_eq!(uint.value(), &UInteger::U64(128));
    }

    #[test]
    fn test_read_two_byte_uint() {
        let data = &[0b0111_1111, 0b1111_1111];
        let uint = DecodedUInt::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(uint.size_in_bytes(), 2);
        assert_eq!(uint.value(), &UInteger::U64(32_767));
    }

    #[test]
    fn test_read_three_byte_uint() {
        let data = &[0b0011_1100, 0b1000_0111, 0b1000_0001];
        let uint = DecodedUInt::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(uint.size_in_bytes(), 3);
        assert_eq!(uint.value(), &UInteger::U64(3_966_849));
    }

    #[test]
    fn test_read_uint_too_large() {
        let mut buffer = Vec::with_capacity(MAX_UINT_SIZE_IN_BYTES + 1);
        for _ in 0..(MAX_UINT_SIZE_IN_BYTES + 1) {
            buffer.push(1);
        }
        let data = buffer.as_slice();
        let _uint = DecodedUInt::read(&mut Cursor::new(data), data.len())
            .expect_err("This exceeded the configured max UInt size.");
    }

    #[test]
    fn test_write_eight_byte_uint() {
        let value = 0x01_23_45_67_89_AB_CD_EF;
        let mut buffer: Vec<u8> = vec![];
        DecodedUInt::write_u64(&mut buffer, value).expect(WRITE_ERROR_MESSAGE);
        let expected_bytes = &[0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF];
        assert_eq!(expected_bytes, buffer.as_slice());
    }

    #[test]
    fn test_write_five_byte_uint() {
        let value = 0x01_23_45_67_89;
        let mut buffer: Vec<u8> = vec![];
        DecodedUInt::write_u64(&mut buffer, value).expect(WRITE_ERROR_MESSAGE);
        let expected_bytes = &[0x01, 0x23, 0x45, 0x67, 0x89];
        assert_eq!(expected_bytes, buffer.as_slice());
    }

    #[test]
    fn test_write_three_byte_uint() {
        let value = 0x01_23_45;
        let mut buffer: Vec<u8> = vec![];
        DecodedUInt::write_u64(&mut buffer, value).expect(WRITE_ERROR_MESSAGE);
        let expected_bytes: &[u8] = &[0x01, 0x23, 0x45];
        assert_eq!(expected_bytes, buffer.as_slice());
    }

    #[test]
    fn test_write_uint_zero() {
        let value = 0x00;
        let mut buffer: Vec<u8> = vec![];
        DecodedUInt::write_u64(&mut buffer, value).expect(WRITE_ERROR_MESSAGE);
        let expected_bytes: &[u8] = &[];
        assert_eq!(expected_bytes, buffer.as_slice());
    }
}
