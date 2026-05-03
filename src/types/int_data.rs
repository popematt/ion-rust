use crate::result::IonFailure;
use crate::types::CountDecimalDigits;
use crate::{IonError, IonResult};
use ice_code::ice as cold_path;
use std::mem::ManuallyDrop;
use std::ops::Neg;

/// A 16-byte tagged union: either an inline `u128` (LSB=1, value shifted left by 1)
/// or an `Box<[u8]>` of unsigned little-endian bytes (LSB=0).
///
/// 127 usable bits for inline values.
pub(crate) union UIntData {
    inline: u128,
    heap: ManuallyDrop<Box<[u8]>>,
}

/// A 16-byte tagged union: either an inline `i128` (LSB=1, value shifted left by 1)
/// or an `Box<[u8]>` of two's complement little-endian bytes (LSB=0).
///
/// 127 usable bits for inline signed values.
pub(crate) union IntData {
    inline: i128,
    heap: ManuallyDrop<Box<[u8]>>,
}

// The maximum value that fits inline (unsigned): 2^127 - 1
const UINT_INLINE_MAX: u128 = (1u128 << 127) - 1;
// Signed inline range: -(2^126) to 2^126 - 1
// After shifting left by 1 and setting LSB=1, the i128 must be valid.
// Positive max: value << 1 | 1 must fit in i128, so value <= (i128::MAX - 1) / 2 = 2^126 - 1
const INT_INLINE_MAX: i128 = (1i128 << 126) - 1;
const INT_INLINE_MIN: i128 = -(1i128 << 126);

impl UIntData {
    pub(crate) const ZERO: UIntData = UIntData { inline: 1 };

    #[inline]
    pub(crate) const fn is_inline(&self) -> bool {
        // SAFETY: reading the low byte is valid for both variants
        unsafe { (self.inline & 1) == 1 }
    }

    #[inline]
    pub(crate) fn from_u128(value: u128) -> Self {
        if value <= UINT_INLINE_MAX {
            UIntData {
                inline: (value << 1) | 1,
            }
        } else {
            // Value doesn't fit inline; store as LE bytes on heap
            let bytes: Box<[u8]> = Box::from(value.to_le_bytes().as_slice());
            UIntData {
                heap: ManuallyDrop::new(bytes),
            }
        }
    }

    pub(crate) fn expect_u128(&self) -> IonResult<u128> {
        self.as_u128()
            .ok_or_else(|| IonError::decoding_error("value was outside the range of a(n) u128"))
    }

    #[inline]
    pub(crate) fn as_u128(&self) -> Option<u128> {
        if self.is_inline() {
            Some(unsafe { self.inline >> 1 })
        } else {
            cold_path! {{
                let bytes = unsafe { &*self.heap };
                // Try to convert heap bytes back to u128
                if bytes.len() <= 16 {
                    let mut buf = [0u8; 16];
                    buf[..bytes.len()].copy_from_slice(bytes);
                    Some(u128::from_le_bytes(buf))
                } else {
                    // Check if the value fits in u128 (all bytes beyond 16 must be zero)
                    if bytes[16..].iter().all(|&b| b == 0) {
                        let mut buf = [0u8; 16];
                        buf.copy_from_slice(&bytes[..16]);
                        Some(u128::from_le_bytes(buf))
                    } else {
                        None
                    }
                }
            }}
        }
    }

    pub(crate) fn from_bytes_le(bytes: &[u8]) -> Self {
        // Strip trailing zeros to normalize
        let len = bytes.iter().rposition(|&b| b != 0).map_or(0, |p| p + 1);
        let bytes = if len == 0 {
            &[0u8] as &[u8]
        } else {
            &bytes[..len]
        };

        if bytes.len() <= 16 {
            let mut buf = [0u8; 16];
            buf[..bytes.len()].copy_from_slice(bytes);
            let value = u128::from_le_bytes(buf);
            if value <= UINT_INLINE_MAX {
                return UIntData {
                    inline: (value << 1) | 1,
                };
            }
        }
        // Heap path
        let boxed: Box<[u8]> = Box::from(bytes);
        UIntData {
            heap: ManuallyDrop::new(boxed),
        }
    }

    /// Returns the value as LE bytes, allocating if necessary for inline values.
    pub(crate) fn to_le_bytes(&self) -> Vec<u8> {
        if self.is_inline() {
            let value = unsafe { self.inline >> 1 };
            let bytes = value.to_le_bytes();
            // Trim trailing zeros
            let len = 16 - (value.leading_zeros() / 8) as usize;
            bytes[..len.max(1)].to_vec()
        } else {
            let slice = unsafe { &*self.heap };
            slice.to_vec()
        }
    }

    /// Returns the value as unsigned big-endian bytes with leading zeros stripped.
    /// Always returns at least one byte.
    pub(crate) fn to_be_bytes(&self) -> Vec<u8> {
        if self.is_inline() {
            let value = unsafe { self.inline >> 1 };
            let bytes = value.to_be_bytes();
            let start = bytes
                .iter()
                .position(|&b| b != 0)
                .unwrap_or(bytes.len() - 1);
            bytes[start..].to_vec()
        } else {
            let slice = unsafe { &*self.heap };
            let mut be = slice.to_vec();
            be.reverse();
            let start = be.iter().position(|&b| b != 0).unwrap_or(be.len() - 1);
            be[start..].to_vec()
        }
    }

    pub(crate) fn is_zero(&self) -> bool {
        if self.is_inline() {
            unsafe { self.inline == 1 } // value 0 is stored as (0 << 1) | 1 = 1
        } else {
            let bytes = unsafe { &*self.heap };
            bytes.iter().all(|&b| b == 0)
        }
    }

    /// Returns the number of leading zero bits in the value.
    pub(crate) fn leading_zeros(&self) -> u32 {
        if self.is_inline() {
            let value = unsafe { self.inline >> 1 };
            value.leading_zeros()
        } else {
            let bytes = unsafe { &*self.heap };
            let mut zeros = 0u32;
            for &b in bytes.iter().rev() {
                if b == 0 {
                    zeros += 8;
                } else {
                    zeros += b.leading_zeros();
                    break;
                }
            }
            zeros
        }
    }
}

impl IntData {
    pub(crate) const ZERO: IntData = IntData { inline: 1 };

    #[inline]
    pub(crate) const fn is_inline(&self) -> bool {
        unsafe { (self.inline & 1) == 1 }
    }

    #[inline]
    pub(crate) fn from_i128(value: i128) -> Self {
        if value >= INT_INLINE_MIN && value <= INT_INLINE_MAX {
            IntData {
                inline: (value << 1) | 1,
            }
        } else {
            // Store as two's complement LE bytes
            let bytes: Box<[u8]> = Box::from(value.to_le_bytes().as_slice());
            IntData {
                heap: ManuallyDrop::new(bytes),
            }
        }
    }

    pub(crate) fn expect_i128(&self) -> IonResult<i128> {
        self.as_i128()
            .ok_or_else(|| IonError::decoding_error("value was outside the range of a(n) i128"))
    }

    #[inline]
    pub(crate) fn as_i128(&self) -> Option<i128> {
        if self.is_inline() {
            Some(unsafe { self.inline >> 1 }) // arithmetic shift preserves sign
        } else {
            cold_path! {{
                let bytes = unsafe { &*self.heap };
                if bytes.len() <= 16 {
                    let is_neg = bytes.last().map_or(false, |&b| b & 0x80 != 0);
                    let pad = if is_neg { 0xFF } else { 0x00 };
                    let mut buf = [pad; 16];
                    buf[..bytes.len()].copy_from_slice(bytes);
                    Some(i128::from_le_bytes(buf))
                } else {
                    // Check if value fits in i128: bytes beyond 16 must all be sign extension
                    let is_neg = bytes.last().map_or(false, |&b| b & 0x80 != 0);
                    let pad = if is_neg { 0xFF } else { 0x00 };
                    let sign_ok = bytes[16..].iter().all(|&b| b == pad);
                    if sign_ok {
                        // Also check that byte 15 has the right sign bit
                        let byte15_neg = bytes[15] & 0x80 != 0;
                        if byte15_neg == is_neg {
                            let mut buf = [0u8; 16];
                            buf.copy_from_slice(&bytes[..16]);
                            return Some(i128::from_le_bytes(buf));
                        }
                    }
                    None
                }
            }}
        }
    }

    pub(crate) fn from_signed_bytes_le(bytes: &[u8]) -> Self {
        if bytes.is_empty() {
            return IntData::from_i128(0);
        }
        // Normalize: strip redundant sign-extension bytes
        let is_neg = bytes.last().unwrap() & 0x80 != 0;
        let pad = if is_neg { 0xFF } else { 0x00 };
        let mut len = bytes.len();
        while len > 1 && bytes[len - 1] == pad {
            // Don't strip if it would change the sign
            if (bytes[len - 2] & 0x80 != 0) != is_neg {
                break;
            }
            len -= 1;
        }
        let bytes = &bytes[..len];

        if bytes.len() <= 16 {
            let mut buf = [pad; 16];
            buf[..bytes.len()].copy_from_slice(bytes);
            let value = i128::from_le_bytes(buf);
            if value >= INT_INLINE_MIN && value <= INT_INLINE_MAX {
                return IntData {
                    inline: (value << 1) | 1,
                };
            }
        }
        let boxed: Box<[u8]> = Box::from(bytes);
        IntData {
            heap: ManuallyDrop::new(boxed),
        }
    }

    pub(crate) fn to_le_bytes(&self) -> Vec<u8> {
        if self.is_inline() {
            let value = unsafe { self.inline >> 1 };
            let bytes = value.to_le_bytes();
            let is_neg = value < 0;
            let pad = if is_neg { 0xFF } else { 0x00 };
            let mut len = 16;
            while len > 1 && bytes[len - 1] == pad {
                if (bytes[len - 2] & 0x80 != 0) != is_neg {
                    break;
                }
                len -= 1;
            }
            bytes[..len].to_vec()
        } else {
            let slice = unsafe { &*self.heap };
            slice.to_vec()
        }
    }

    /// Returns the number of bytes in the normalized LE representation.
    pub(crate) fn byte_len(&self) -> usize {
        if self.is_inline() {
            self.to_le_bytes().len()
        } else {
            unsafe { (*self.heap).len() }
        }
    }

    pub(crate) fn is_zero(&self) -> bool {
        if self.is_inline() {
            unsafe { self.inline == 1 }
        } else {
            let bytes = unsafe { &*self.heap };
            bytes.iter().all(|&b| b == 0)
        }
    }

    pub(crate) fn is_negative(&self) -> bool {
        if self.is_inline() {
            unsafe { self.inline < 0 } // sign bit of the tagged value == sign of original
        } else {
            let bytes = unsafe { &*self.heap };
            bytes.last().map_or(false, |&b| b & 0x80 != 0)
        }
    }

    /// Returns the number of leading sign bits (leading zeros for non-negative,
    /// leading ones for negative).
    pub(crate) fn leading_sign_bits(&self) -> u32 {
        if self.is_inline() {
            let value = unsafe { self.inline >> 1 };
            if value < 0 {
                value.leading_ones()
            } else {
                value.leading_zeros()
            }
        } else {
            let bytes = unsafe { &*self.heap };
            let is_neg = bytes.last().map_or(false, |&b| b & 0x80 != 0);
            let target = if is_neg { 0xFF } else { 0x00 };
            let mut bits = 0u32;
            for &b in bytes.iter().rev() {
                if b == target {
                    bits += 8;
                } else {
                    bits += if is_neg {
                        b.leading_ones()
                    } else {
                        b.leading_zeros()
                    };
                    break;
                }
            }
            bits
        }
    }

    /// Returns the unsigned absolute value.
    pub(crate) fn unsigned_abs(&self) -> UIntData {
        if self.is_inline() {
            let value = unsafe { self.inline >> 1 };
            UIntData::from_u128(value.unsigned_abs())
        } else {
            if !self.is_negative() {
                // Positive: bytes are already the magnitude
                let bytes = unsafe { &*self.heap };
                UIntData::from_bytes_le(bytes)
            } else {
                // Negative: neg to get magnitude
                let negd = self.neg();
                if negd.is_inline() {
                    let value = unsafe { negd.inline >> 1 };
                    UIntData::from_u128(value as u128)
                } else {
                    let bytes = unsafe { &*negd.heap };
                    let result = UIntData::from_bytes_le(bytes);
                    // Drop the negd IntData
                    std::mem::drop(negd);
                    result
                }
            }
        }
    }
}

// ===== Clone =====

impl Clone for UIntData {
    fn clone(&self) -> Self {
        if self.is_inline() {
            UIntData {
                inline: unsafe { self.inline },
            }
        } else {
            let boxed = unsafe { &*self.heap };
            UIntData {
                heap: ManuallyDrop::new(boxed.clone()),
            }
        }
    }
}

impl Clone for IntData {
    fn clone(&self) -> Self {
        if self.is_inline() {
            IntData {
                inline: unsafe { self.inline },
            }
        } else {
            let boxed = unsafe { &*self.heap };
            IntData {
                heap: ManuallyDrop::new(boxed.clone()),
            }
        }
    }
}

// ===== Drop =====

impl Drop for UIntData {
    fn drop(&mut self) {
        if !self.is_inline() {
            unsafe { ManuallyDrop::drop(&mut self.heap) };
        }
    }
}

impl Drop for IntData {
    fn drop(&mut self) {
        if !self.is_inline() {
            unsafe { ManuallyDrop::drop(&mut self.heap) };
        }
    }
}

// Arithmetic

impl CountDecimalDigits for &UIntData {
    fn count_decimal_digits(self) -> u32 {
        if self.is_inline() {
            let value = unsafe { self.inline >> 1 };
            if value == 0 {
                1
            } else {
                value.ilog10() + 1
            }
        } else {
            // For really large values, just format and count
            let s = format!("{self}");
            s.len() as u32
        }
    }
}

impl CountDecimalDigits for &IntData {
    fn count_decimal_digits(self) -> u32 {
        if self.is_inline() {
            let value = unsafe { self.inline >> 1 };
            let abs = value.unsigned_abs();
            if abs == 0 {
                1
            } else {
                abs.ilog10() + 1
            }
        } else {
            // For really large values, just format and count
            let s = format!("{self}");
            let s = s.strip_prefix('-').unwrap_or(&s);
            s.len() as u32
        }
    }
}

impl Neg for &IntData {
    type Output = IntData;

    fn neg(self) -> Self::Output {
        if self.is_inline() {
            // Safe to unwrap because we checked that it's inline.
            let value = self.as_i128().unwrap();
            // If it fits inline, it can't be more than 127 bits, so it's safe to neg the i128.
            IntData::from_i128(-value)
        } else {
            let bytes = unsafe { &*self.heap };
            let negd = neg_twos_complement(bytes);
            IntData::from_signed_bytes_le(&negd)
        }
    }
}

// ===== PartialEq / Eq =====

impl PartialEq for UIntData {
    fn eq(&self, other: &Self) -> bool {
        // With normalization, equal values always have the same representation
        if self.is_inline() && other.is_inline() {
            unsafe { self.inline == other.inline }
        } else if !self.is_inline() && !other.is_inline() {
            let a = unsafe { &*self.heap };
            let b = unsafe { &*other.heap };
            a == b
        } else {
            // One inline, one heap — can't be equal if normalization is correct
            false
        }
    }
}

impl Eq for UIntData {}

impl PartialEq for IntData {
    fn eq(&self, other: &Self) -> bool {
        if self.is_inline() && other.is_inline() {
            unsafe { self.inline == other.inline }
        } else if !self.is_inline() && !other.is_inline() {
            let a = unsafe { &*self.heap };
            let b = unsafe { &*other.heap };
            a == b
        } else {
            false
        }
    }
}

impl Eq for IntData {}

// ===== Ord =====

impl PartialOrd for UIntData {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for UIntData {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        match (self.as_u128(), other.as_u128()) {
            (Some(a), Some(b)) => a.cmp(&b),
            (Some(_), None) => Ordering::Less, // fits in u128 < doesn't fit
            (None, Some(_)) => Ordering::Greater,
            (None, None) => {
                cold_path!({
                    // Both heap, compare LE byte slices by length then content (MSB first)
                    let a = unsafe { &*self.heap };
                    let b = unsafe { &*other.heap };
                    a.len()
                        .cmp(&b.len())
                        .then_with(|| a.iter().rev().cmp(b.iter().rev()))
                })
            }
        }
    }
}

impl PartialOrd for IntData {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for IntData {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        match (self.as_i128(), other.as_i128()) {
            (Some(a), Some(b)) => a.cmp(&b),
            _ => {
                cold_path!({
                    let a_neg = self.is_negative();
                    let b_neg = other.is_negative();
                    if a_neg != b_neg {
                        if a_neg {
                            Ordering::Less
                        } else {
                            Ordering::Greater
                        }
                    } else {
                        let a_bytes = self.to_le_bytes();
                        let b_bytes = other.to_le_bytes();
                        let mag_cmp = a_bytes
                            .len()
                            .cmp(&b_bytes.len())
                            .then_with(|| a_bytes.iter().rev().cmp(b_bytes.iter().rev()));
                        if a_neg {
                            mag_cmp.reverse()
                        } else {
                            mag_cmp
                        }
                    }
                })
            }
        }
    }
}

// ===== Hash =====

impl std::hash::Hash for UIntData {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        if self.is_inline() {
            // Hash the unshifted value directly
            let value = unsafe { self.inline >> 1 };
            value.hash(state);
        } else {
            let bytes = unsafe { &*self.heap };
            bytes.hash(state);
        }
    }
}

impl std::hash::Hash for IntData {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        if self.is_inline() {
            let value = unsafe { self.inline >> 1 };
            value.hash(state);
        } else {
            let bytes = unsafe { &*self.heap };
            bytes.hash(state);
        }
    }
}

// ===== Debug =====

impl std::fmt::Debug for UIntData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(v) = self.as_u128() {
            write!(f, "UIntData({v})")
        } else {
            let bytes = unsafe { &*self.heap };
            write!(f, "UIntData({bytes:02x?})")
        }
    }
}

impl std::fmt::Debug for IntData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(v) = self.as_i128() {
            write!(f, "IntData({v})")
        } else {
            let bytes = unsafe { &*self.heap };
            write!(f, "IntData({bytes:02x?})")
        }
    }
}

// ===== Display =====

impl std::fmt::Display for UIntData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(v) = self.as_u128() {
            return write!(f, "{v}");
        }
        display_big_uint(unsafe { &*self.heap }, f)
    }
}

#[cold]
#[inline(never)]
fn display_big_uint(bytes: &[u8], f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut digits = Vec::new();
    let mut remainder = bytes.to_vec();
    loop {
        let (quotient, rem) = div_bytes_by_u32(&remainder, 10);
        digits.push(b'0' + rem as u8);
        if quotient.iter().all(|&b| b == 0) {
            break;
        }
        remainder = quotient;
    }
    digits.reverse();
    // SAFETY: digits is only ascii
    let s = unsafe { std::str::from_utf8_unchecked(&digits) };
    write!(f, "{s}")
}

impl std::fmt::Display for IntData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(v) = self.as_i128() {
            return write!(f, "{v}");
        }
        display_big_int(self, f)
    }
}

#[cold]
#[inline(never)]
fn display_big_int(data: &IntData, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if data.is_negative() {
        write!(f, "-")?;
        let abs = data.unsigned_abs();
        write!(f, "{abs}")
    } else {
        let bytes = unsafe { &*data.heap };
        let uint = UIntData::from_bytes_le(bytes);
        write!(f, "{uint}")
    }
}

/// Two's complement neg: invert all bytes, add 1.
/// Adds a sign extension byte if needed to preserve the correct sign.
fn neg_twos_complement(bytes: &[u8]) -> Vec<u8> {
    let mut result = vec![0u8; bytes.len()];
    let mut carry = 1u16;
    for (i, &b) in bytes.iter().enumerate() {
        let sum = (!b) as u16 + carry;
        result[i] = sum as u8;
        carry = sum >> 8;
    }
    if carry > 0 {
        result.push(carry as u8);
    }
    // If the input was negative and the result looks negative, add a 0x00 byte
    // If the input was positive and the result looks positive, add a 0xFF byte
    let input_neg = bytes.last().map_or(false, |&b| b & 0x80 != 0);
    let result_neg = result.last().map_or(false, |&b| b & 0x80 != 0);
    if input_neg && result_neg {
        // Negating a negative should give positive; need sign extension
        result.push(0x00);
    } else if !input_neg && !result_neg && !bytes.iter().all(|&b| b == 0) {
        // Negating a positive should give negative; need sign extension
        result.push(0xFF);
    }
    result
}

/// Divides unsigned LE bytes by a small u32 divisor. Returns (quotient_bytes, remainder).
fn div_bytes_by_u32(bytes: &[u8], divisor: u32) -> (Vec<u8>, u32) {
    let mut quotient = vec![0u8; bytes.len()];
    let mut remainder: u64 = 0;
    // Process from most significant byte to least
    for i in (0..bytes.len()).rev() {
        remainder = (remainder << 8) | bytes[i] as u64;
        quotient[i] = (remainder / divisor as u64) as u8;
        remainder %= divisor as u64;
    }
    (quotient, remainder as u32)
}

// Static size assertions
#[cfg(target_pointer_width = "64")]
const _: () = assert!(std::mem::size_of::<UIntData>() == 16);
#[cfg(target_pointer_width = "64")]
const _: () = assert!(std::mem::size_of::<IntData>() == 16);

// Conversions
macro_rules! out_of_range_err {
    ($t:ty) => {
        IonError::Decoding(crate::result::DecodingError::new(concat!(
            "value was outside the range of a(n) ",
            stringify!($t)
        )))
    };
}

impl TryFrom<IntData> for UIntData {
    type Error = IonError;

    fn try_from(value: IntData) -> Result<Self, Self::Error> {
        if let Some(i) = value.as_i128() {
            Ok(UIntData::from_u128(
                i.try_into().map_err(|_| out_of_range_err!(u128))?,
            ))
        } else {
            cold_path! {
                if value.is_negative() {
                    Err(IonError::decoding_error("negative integer cannot be converted to unsigned integer"))
                } else {
                    // If it's positive, then we know the bytes are also valid for an unsigned integer without any special treatment.
                    Ok(UIntData::from_bytes_le(&value.to_le_bytes()))
                }
            }
        }
    }
}

impl From<UIntData> for IntData {
    fn from(value: UIntData) -> Self {
        if value.is_inline() {
            // If it's inline, then it must be small enough not only to fit into u128, but also
            // to fit in i128.
            IntData::from_i128(i128::try_from(value.as_u128().unwrap()).unwrap())
        } else {
            cold_path! {{
                let mut bytes = value.to_le_bytes();
                bytes.push(0);
                IntData::from_signed_bytes_le(&bytes)
            }}
        }
    }
}

macro_rules! impl_small_int_try_from_int {
    ($($t:ty),*) => {
        $(
        impl TryFrom<IntData> for $t {
            type Error = IonError;

            fn try_from(value: IntData) -> Result<Self, Self::Error> {
                <$t>::try_from(value.expect_i128()?).map_err(|_| out_of_range_err!($t))
            }
        }

        impl TryFrom<UIntData> for $t {
            type Error = IonError;

            fn try_from(value: UIntData) -> Result<Self, Self::Error> {
                <$t>::try_from(value.expect_u128()?).map_err(|_| out_of_range_err!($t))
            }
        }

        impl TryFrom<&IntData> for $t {
            type Error = IonError;

            fn try_from(value: &IntData) -> Result<Self, Self::Error> {
                <$t>::try_from(value.expect_i128()?).map_err(|_| out_of_range_err!($t))
            }
        }

        impl TryFrom<&UIntData> for $t {
            type Error = IonError;

            fn try_from(value: &UIntData) -> Result<Self, Self::Error> {
                <$t>::try_from(value.expect_u128()?).map_err(|_| out_of_range_err!($t))
            }
        }
        )*
    }
}

impl_small_int_try_from_int!(i8, i16, i32, i64, i128, isize);
impl_small_int_try_from_int!(u8, u16, u32, u64, u128, usize);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uint_inline_roundtrip() {
        for v in [0u128, 1, 42, u64::MAX as u128, UINT_INLINE_MAX] {
            let d = UIntData::from_u128(v);
            assert!(d.is_inline());
            assert_eq!(d.as_u128(), Some(v));
        }
    }

    #[test]
    fn uint_heap_roundtrip() {
        let v = UINT_INLINE_MAX + 1; // 2^127
        let d = UIntData::from_u128(v);
        assert!(!d.is_inline());
        assert_eq!(d.as_u128(), Some(v));
    }

    #[test]
    fn uint_u128_max() {
        let d = UIntData::from_u128(u128::MAX);
        assert!(!d.is_inline());
        assert_eq!(d.as_u128(), Some(u128::MAX));
    }

    #[test]
    fn int_inline_roundtrip() {
        for v in [0i128, 1, -1, 42, -42, INT_INLINE_MAX, INT_INLINE_MIN] {
            let d = IntData::from_i128(v);
            assert!(d.is_inline(), "value {v} should be inline");
            assert_eq!(d.as_i128(), Some(v));
        }
    }

    #[test]
    fn int_heap_roundtrip() {
        for v in [i128::MAX, i128::MIN, INT_INLINE_MAX + 1, INT_INLINE_MIN - 1] {
            let d = IntData::from_i128(v);
            assert!(!d.is_inline(), "value {v} should be heap");
            assert_eq!(d.as_i128(), Some(v));
        }
    }

    #[test]
    fn uint_clone_drop() {
        let d = UIntData::from_u128(u128::MAX);
        let d2 = d.clone();
        assert_eq!(d.as_u128(), d2.as_u128());
        drop(d);
        assert_eq!(d2.as_u128(), Some(u128::MAX));
    }

    #[test]
    fn int_neg() {
        assert_eq!(IntData::from_i128(42).neg().as_i128(), Some(-42));
        assert_eq!(IntData::from_i128(-42).neg().as_i128(), Some(42));
        assert_eq!(IntData::from_i128(0).neg().as_i128(), Some(0));
        // i128::MIN negd doesn't fit in i128
        let neg_min = IntData::from_i128(i128::MIN).neg();
        assert!(neg_min.as_i128().is_none());
    }

    #[test]
    fn uint_from_bytes_le_normalizes() {
        // Small value from bytes should be inline
        let d = UIntData::from_bytes_le(&[42, 0, 0, 0]);
        assert!(d.is_inline());
        assert_eq!(d.as_u128(), Some(42));
    }

    #[test]
    fn int_from_signed_bytes_le_normalizes() {
        let d = IntData::from_signed_bytes_le(&[42]);
        assert!(d.is_inline());
        assert_eq!(d.as_i128(), Some(42));

        let d = IntData::from_signed_bytes_le(&[0xFE]); // -2
        assert!(d.is_inline());
        assert_eq!(d.as_i128(), Some(-2));
    }

    #[test]
    fn uint_ordering() {
        let a = UIntData::from_u128(1);
        let b = UIntData::from_u128(2);
        assert!(a < b);

        // Inline vs heap
        let small = UIntData::from_u128(42);
        let big = UIntData::from_u128(u128::MAX);
        assert!(small < big);
    }

    #[test]
    fn int_ordering() {
        assert!(IntData::from_i128(-1) < IntData::from_i128(0));
        assert!(IntData::from_i128(0) < IntData::from_i128(1));
        // Inline vs heap
        assert!(IntData::from_i128(42) < IntData::from_i128(i128::MAX));
    }

    #[test]
    fn uint_display() {
        assert_eq!(format!("{}", UIntData::from_u128(0)), "0");
        assert_eq!(format!("{}", UIntData::from_u128(42)), "42");
        assert_eq!(
            format!("{}", UIntData::from_u128(u128::MAX)),
            format!("{}", u128::MAX)
        );
    }

    #[test]
    fn int_display() {
        assert_eq!(format!("{}", IntData::from_i128(0)), "0");
        assert_eq!(format!("{}", IntData::from_i128(-42)), "-42");
        assert_eq!(
            format!("{}", IntData::from_i128(i128::MAX)),
            format!("{}", i128::MAX)
        );
        assert_eq!(
            format!("{}", IntData::from_i128(i128::MIN)),
            format!("{}", i128::MIN)
        );
    }

    #[test]
    fn uint_big_from_bytes_display() {
        // 2^128 as LE bytes: 17 bytes, byte[16] = 1
        let mut bytes = vec![0u8; 17];
        bytes[16] = 1;
        let d = UIntData::from_bytes_le(&bytes);
        assert!(!d.is_inline());
        assert_eq!(d.as_u128(), None);
        assert_eq!(format!("{d}"), "340282366920938463463374607431768211456");
    }

    #[test]
    fn int_big_from_bytes_display() {
        // 2^128 as signed LE: 17 bytes with byte[16]=1, plus a zero byte for sign
        let mut bytes = vec![0u8; 18];
        bytes[16] = 1;
        let d = IntData::from_signed_bytes_le(&bytes);
        assert!(!d.is_inline());
        assert_eq!(format!("{d}"), "340282366920938463463374607431768211456");

        // Negative: -(2^128)
        let neg = d.neg();
        assert_eq!(format!("{neg}"), "-340282366920938463463374607431768211456");
    }

    #[test]
    fn hash_consistency() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let hash = |d: &UIntData| {
            let mut h = DefaultHasher::new();
            d.hash(&mut h);
            h.finish()
        };

        let a = UIntData::from_u128(42);
        let b = UIntData::from_u128(42);
        assert_eq!(hash(&a), hash(&b));
    }

    #[test]
    fn hash_inline_vs_inline_same_value() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let hash_uint = |d: &UIntData| {
            let mut h = DefaultHasher::new();
            d.hash(&mut h);
            h.finish()
        };
        let hash_int = |d: &IntData| {
            let mut h = DefaultHasher::new();
            d.hash(&mut h);
            h.finish()
        };

        // Same inline values must hash equally
        assert_eq!(
            hash_uint(&UIntData::from_u128(0)),
            hash_uint(&UIntData::from_u128(0))
        );
        assert_eq!(
            hash_uint(&UIntData::from_u128(42)),
            hash_uint(&UIntData::from_u128(42))
        );
        assert_eq!(
            hash_int(&IntData::from_i128(0)),
            hash_int(&IntData::from_i128(0))
        );
        assert_eq!(
            hash_int(&IntData::from_i128(-42)),
            hash_int(&IntData::from_i128(-42))
        );

        // Same heap values must hash equally
        let big1 =
            UIntData::from_bytes_le(&[0; 17].iter().chain(&[1]).copied().collect::<Vec<_>>());
        let big2 =
            UIntData::from_bytes_le(&[0; 17].iter().chain(&[1]).copied().collect::<Vec<_>>());
        assert_eq!(hash_uint(&big1), hash_uint(&big2));
    }

    #[test]
    fn send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<UIntData>();
        assert_send_sync::<IntData>();
    }

    #[test]
    fn to_bytes_le_roundtrip() {
        // Inline values
        for v in [0u128, 1, 42, u64::MAX as u128, UINT_INLINE_MAX] {
            let d = UIntData::from_u128(v);
            let bytes = d.to_le_bytes();
            let d2 = UIntData::from_bytes_le(&bytes);
            assert_eq!(d, d2, "UInt roundtrip failed for {v}");
        }
        // Heap values
        for v in [UINT_INLINE_MAX + 1, u128::MAX] {
            let d = UIntData::from_u128(v);
            let bytes = d.to_le_bytes();
            let d2 = UIntData::from_bytes_le(&bytes);
            assert_eq!(d, d2, "UInt heap roundtrip failed for {v}");
        }
        // Signed inline
        for v in [0i128, 1, -1, 42, -42, INT_INLINE_MAX, INT_INLINE_MIN] {
            let d = IntData::from_i128(v);
            let bytes = d.to_le_bytes();
            let d2 = IntData::from_signed_bytes_le(&bytes);
            assert_eq!(d, d2, "Int roundtrip failed for {v}");
        }
        // Signed heap
        for v in [i128::MAX, i128::MIN, INT_INLINE_MAX + 1, INT_INLINE_MIN - 1] {
            let d = IntData::from_i128(v);
            let bytes = d.to_le_bytes();
            let d2 = IntData::from_signed_bytes_le(&bytes);
            assert_eq!(d, d2, "Int heap roundtrip failed for {v}");
        }
    }

    #[test]
    fn uint_to_be_bytes() {
        // Zero
        assert_eq!(UIntData::from_u128(0).to_be_bytes(), vec![0]);
        // Single byte
        assert_eq!(UIntData::from_u128(0xFF).to_be_bytes(), vec![0xFF]);
        // Multi-byte
        assert_eq!(UIntData::from_u128(0x0102).to_be_bytes(), vec![0x01, 0x02]);
        // u128::MAX (heap)
        let max = UIntData::from_u128(u128::MAX);
        assert_eq!(max.to_be_bytes(), u128::MAX.to_be_bytes().to_vec());
        // Big value beyond u128
        let mut le = vec![0u8; 17];
        le[16] = 1; // 2^128
        let big = UIntData::from_bytes_le(&le);
        let be = big.to_be_bytes();
        assert_eq!(be[0], 1);
        assert!(be[1..].iter().all(|&b| b == 0));
        assert_eq!(be.len(), 17);
    }
}
