use crate::ion_data::{IonDataHash, IonDataOrd, IonEq};
use crate::result::{IonError, IonFailure, IonResult};
use crate::types::{CountDecimalDigits, Decimal};
#[cfg(feature = "experimental-chrono")]
use chrono::{DateTime, Datelike, FixedOffset, NaiveDate, NaiveDateTime, TimeZone, Timelike};
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

/// Indicates the most precise time unit that has been specified in the accompanying [Timestamp].
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Default, Hash)]
pub enum TimestampPrecision {
    /// Year-level precision (e.g. `2020T`)
    #[default]
    Year,
    /// Month-level precision (e.g. `2020-08T`)
    Month,
    /// Day-level precision (e.g. `2020-08-01T`)
    Day,
    /// Minute-level precision (e.g. `2020-08-01T12:34Z`)
    HourAndMinute,
    /// Second-level precision or greater. (e.g. `2020-08-01T12:34:56Z` or `2020-08-01T12:34:56.123456789Z`)
    Second,
}

/// Represents the fractional seconds component of a Timestamp during construction.
/// Used internally by [`TimestampBuilder`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Mantissa {
    /// The number of digits of precision in the Timestamp's fractional seconds. For example, a
    /// value of `3` would indicate millisecond precision. A value of `6` would indicate
    /// microsecond precision. All precisions less than or equal to nanoseconds should use
    /// this representation when possible.
    Digits(u32),
    /// Specifies the fractional seconds precisely as a `Decimal` in the range `>= 0` and `< 1`.
    /// The Decimal will have the correct precision; the complete value can and should be used.
    /// This representation should only be used for precisions greater than nanoseconds as it can
    /// require allocations.
    Arbitrary(Decimal),
}

/// Constructs a [`FixedOffset`] at the specified offset seconds from UTC. If the specified offset
/// is out of bounds, this method will panic.
#[cfg(feature = "experimental-chrono")]
fn offset_east(seconds_east: i32) -> FixedOffset {
    FixedOffset::east_opt(seconds_east).expect("seconds_east was outside the supported range")
}

// ─── Packed bit layout ────────────────────────────────────────────────
//
// All date-time fields are stored as LOCAL time in a single u64.
// A second u64 holds the fractional seconds payload.
//
// Bit layout of `packed` (LSB = bit 0):
//
//   [13:0]  year      (14 bits, 0-9999)
//   [17:14] month     (4 bits, 1-12)
//   [22:18] day       (5 bits, 1-31)
//   [27:23] hour      (5 bits, 0-23)
//   [33:28] minute    (6 bits, 0-59)
//   [45:34] offset    (12 bits, two's complement minutes; 0x800 = unknown)
//   [51:46] second    (6 bits, 0-59)
//   [54:52] precision (3 bits, 0-4 maps to TimestampPrecision)
//   [60:56] frac_kind (5 bits, 0 = none, 1-19 = digit count)
//   [55]    spare
//   [63:61] spare
//
// `frac_payload`: when frac_kind is 1-19, this is the coefficient
// at that scale (e.g. kind=3, payload=123 means 0.123 seconds).

const YEAR_BITS: u64 = 14;
const MONTH_BITS: u64 = 4;
const DAY_BITS: u64 = 5;
const HOUR_BITS: u64 = 5;
const MINUTE_BITS: u64 = 6;
const OFFSET_BITS: u64 = 12;
const SECOND_BITS: u64 = 6;
const PRECISION_BITS: u64 = 3;
const FRAC_KIND_BITS: u64 = 5;

const YEAR_SHIFT: u64 = 0;
const MONTH_SHIFT: u64 = YEAR_SHIFT + YEAR_BITS; // 14
const DAY_SHIFT: u64 = MONTH_SHIFT + MONTH_BITS; // 18
const HOUR_SHIFT: u64 = DAY_SHIFT + DAY_BITS; // 23
const MINUTE_SHIFT: u64 = HOUR_SHIFT + HOUR_BITS; // 28
const OFFSET_SHIFT: u64 = MINUTE_SHIFT + MINUTE_BITS; // 34
const SECOND_SHIFT: u64 = OFFSET_SHIFT + OFFSET_BITS; // 46
const PRECISION_SHIFT: u64 = SECOND_SHIFT + SECOND_BITS; // 52
                                                         // bit 55 is spare
const FRAC_KIND_SHIFT: u64 = 56;

const YEAR_MASK: u64 = (1 << YEAR_BITS) - 1; // 0x3FFF
const MONTH_MASK: u64 = (1 << MONTH_BITS) - 1; // 0xF
const DAY_MASK: u64 = (1 << DAY_BITS) - 1; // 0x1F
const HOUR_MASK: u64 = (1 << HOUR_BITS) - 1; // 0x1F
const MINUTE_MASK: u64 = (1 << MINUTE_BITS) - 1; // 0x3F
const OFFSET_MASK: u64 = (1 << OFFSET_BITS) - 1; // 0xFFF
const SECOND_MASK: u64 = (1 << SECOND_BITS) - 1; // 0x3F
const PRECISION_MASK: u64 = (1 << PRECISION_BITS) - 1; // 0x7
const FRAC_KIND_MASK: u64 = (1 << FRAC_KIND_BITS) - 1; // 0x1F

const OFFSET_UNKNOWN_SENTINEL: u16 = 0x800;
const MAX_FRAC_DIGITS: u32 = 19;

const DAYS_IN_MONTH: [u8; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];

fn is_leap_year(year: u16) -> bool {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
}

fn days_in_month(year: u16, month: u8) -> u8 {
    if month == 2 && is_leap_year(year) {
        29
    } else {
        DAYS_IN_MONTH[(month - 1) as usize]
    }
}

fn validate_fields(y: u16, m: u8, d: u8, h: u8, min: u8, s: u8) -> bool {
    if y > 9999 {
        return false;
    }
    if m < 1 || m > 12 {
        return false;
    }
    let max_day = days_in_month(y, m);
    d >= 1 && d <= max_day && h <= 23 && min <= 59 && s <= 59
}

/// Adds `offset_minutes` to a local time represented by the given fields,
/// returning the adjusted (year, month, day, hour, minute).
fn add_offset_to_utc(
    year: u16,
    month: u8,
    day: u8,
    hour: u8,
    minute: u8,
    offset_minutes: i16,
) -> (u16, u8, u8, u8, u8) {
    let total_minutes = hour as i32 * 60 + minute as i32 + offset_minutes as i32;
    let (mut d, h, m) = if total_minutes >= 0 && total_minutes < 24 * 60 {
        // Common fast path: no day rollover
        (
            day as i32,
            (total_minutes / 60) as u8,
            (total_minutes % 60) as u8,
        )
    } else {
        let day_offset = total_minutes.div_euclid(24 * 60);
        let time_of_day = total_minutes.rem_euclid(24 * 60);
        (
            day as i32 + day_offset,
            (time_of_day / 60) as u8,
            (time_of_day % 60) as u8,
        )
    };

    let mut mo = month as i32;
    let mut y = year as i32;

    // Handle day overflow
    loop {
        let max = days_in_month(y as u16, mo as u8) as i32;
        if d <= max {
            break;
        }
        d -= max;
        mo += 1;
        if mo > 12 {
            mo = 1;
            y += 1;
        }
    }
    // Handle day underflow
    while d < 1 {
        mo -= 1;
        if mo < 1 {
            mo = 12;
            y -= 1;
        }
        d += days_in_month(y as u16, mo as u8) as i32;
    }

    (y as u16, mo as u8, d as u8, h, m)
}

/// Subtracts `offset_minutes` from local time to get UTC fields.
fn subtract_offset_to_utc(
    year: u16,
    month: u8,
    day: u8,
    hour: u8,
    minute: u8,
    offset_minutes: i16,
) -> (u16, u8, u8, u8, u8) {
    add_offset_to_utc(year, month, day, hour, minute, -offset_minutes)
}

/// Represents a point in time to a specified degree of precision. Unlike chrono's
/// `NaiveDateTime` and `DateTime`, a `Timestamp` has variable precision ranging from a year
/// to fractional seconds of an arbitrary unit.
///
/// Internally stored as two `u64`s: a packed bit-field of local-time date-time fields,
/// and a fractional-seconds coefficient. Total size: 16 bytes.
#[derive(Clone, Copy)]
pub struct Timestamp {
    packed: u64,
    frac_payload: u64,
}

impl Debug for Timestamp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Timestamp({})", self)
    }
}

impl Timestamp {
    /// Pack fields into the u64 bit-field. All fields must already be validated.
    fn pack(
        precision: TimestampPrecision,
        year: u16,
        month: u8,
        day: u8,
        hour: u8,
        minute: u8,
        second: u8,
        offset_raw: u16,
        frac_kind: u8,
    ) -> u64 {
        let prec_bits = match precision {
            TimestampPrecision::Year => 0u64,
            TimestampPrecision::Month => 1,
            TimestampPrecision::Day => 2,
            TimestampPrecision::HourAndMinute => 3,
            TimestampPrecision::Second => 4,
        };
        (year as u64) << YEAR_SHIFT
            | (month as u64) << MONTH_SHIFT
            | (day as u64) << DAY_SHIFT
            | (hour as u64) << HOUR_SHIFT
            | (minute as u64) << MINUTE_SHIFT
            | (offset_raw as u64 & OFFSET_MASK) << OFFSET_SHIFT
            | (second as u64) << SECOND_SHIFT
            | prec_bits << PRECISION_SHIFT
            | (frac_kind as u64) << FRAC_KIND_SHIFT
    }

    /// Direct construction from LOCAL time fields.
    pub(crate) fn from_fields(
        precision: TimestampPrecision,
        offset: Option<i16>,
        year: u16,
        month: u8,
        day: u8,
        hour: u8,
        minute: u8,
        second: u8,
        frac_digits: u32,
        frac_coefficient: u64,
    ) -> IonResult<Self> {
        if year == 0 || year > 9999 {
            return IonResult::illegal_operation(format!(
                "Timestamp year '{}' out of range (1-9999)",
                year
            ));
        }
        if precision >= TimestampPrecision::Month
            && !validate_fields(year, month, day, hour, minute, second)
        {
            return IonResult::illegal_operation("one or more timestamp fields are out of range");
        }
        if frac_digits > MAX_FRAC_DIGITS {
            return IonResult::illegal_operation(format!(
                "fractional seconds precision ({} digits) exceeds maximum ({})",
                frac_digits, MAX_FRAC_DIGITS
            ));
        }

        let offset_raw = match offset {
            None => OFFSET_UNKNOWN_SENTINEL,
            Some(m) => {
                if m < -1439 || m > 1439 {
                    return IonResult::illegal_operation(format!(
                        "offset ({} minutes) exceeds valid range (-1439..=1439)",
                        m
                    ));
                }
                m as u16
            }
        };

        let frac_kind = frac_digits as u8;
        let packed = Self::pack(
            precision, year, month, day, hour, minute, second, offset_raw, frac_kind,
        );

        Ok(Timestamp {
            packed,
            frac_payload: frac_coefficient,
        })
    }

    /// Construction from UTC fields + offset. Adds offset to convert to local time.
    pub(crate) fn from_utc_fields(
        precision: TimestampPrecision,
        offset_minutes: i16,
        year: u16,
        month: u8,
        day: u8,
        hour: u8,
        minute: u8,
        second: u8,
        frac_digits: u32,
        frac_coefficient: u64,
    ) -> IonResult<Self> {
        // Validate the raw UTC fields before offset conversion
        if precision >= TimestampPrecision::Month
            && !validate_fields(year, month, day, hour, minute, second)
        {
            return IonResult::illegal_operation(
                "one or more timestamp UTC fields are out of range",
            );
        }
        let (ly, lmo, ld, lh, lmi) =
            add_offset_to_utc(year, month, day, hour, minute, offset_minutes);
        Self::from_fields(
            precision,
            Some(offset_minutes),
            ly,
            lmo,
            ld,
            lh,
            lmi,
            second,
            frac_digits,
            frac_coefficient,
        )
    }

    /// Converts a [`NaiveDateTime`] or [`DateTime<FixedOffset>`] to a Timestamp with the specified
    /// precision. If the precision is [`TimestampPrecision::Second`], nanosecond precision (the
    /// maximum supported by a `Timelike`) is assumed.
    #[cfg(feature = "experimental-chrono")]
    pub fn from_datetime<D>(datetime: D, precision: TimestampPrecision) -> Timestamp
    where
        D: Datelike + Timelike + Into<Timestamp>,
    {
        let mut timestamp: Timestamp = datetime.into();
        if precision < TimestampPrecision::Second {
            timestamp.set_frac_kind(0);
            timestamp.frac_payload = 0;
        }
        timestamp.set_precision(precision);
        timestamp
    }

    #[cfg(feature = "experimental-chrono")]
    pub(crate) fn from_naive_datetime(date_time: NaiveDateTime) -> Self {
        Self::from_fields(
            TimestampPrecision::Second,
            None,
            date_time.year() as u16,
            date_time.month() as u8,
            date_time.day() as u8,
            date_time.hour() as u8,
            date_time.minute() as u8,
            date_time.second() as u8,
            9,
            date_time.nanosecond() as u64,
        )
        .expect("chrono NaiveDateTime fields are always valid")
    }

    #[cfg(feature = "experimental-chrono")]
    pub(crate) fn from_fixed_offset_datetime(
        fixed_offset_date_time: DateTime<FixedOffset>,
    ) -> Self {
        let offset_seconds = fixed_offset_date_time.offset().local_minus_utc();
        let offset_minutes = (offset_seconds / 60) as i16;
        let local = fixed_offset_date_time.naive_local();
        // Pack directly from local fields — chrono guarantees validity of the
        // DateTime, and local year may exceed 9999 (e.g., UTC year 9999 Dec 31
        // with negative offset). We bypass from_fields validation to avoid panic.
        let packed = Self::pack(
            TimestampPrecision::Second,
            local.year() as u16,
            local.month() as u8,
            local.day() as u8,
            local.hour() as u8,
            local.minute() as u8,
            local.second() as u8,
            offset_minutes as u16,
            9,
        );
        Timestamp {
            packed,
            frac_payload: local.nanosecond() as u64,
        }
    }

    fn frac_kind(&self) -> u8 {
        ((self.packed >> FRAC_KIND_SHIFT) & FRAC_KIND_MASK) as u8
    }

    fn set_frac_kind(&mut self, kind: u8) {
        self.packed &= !(FRAC_KIND_MASK << FRAC_KIND_SHIFT);
        self.packed |= (kind as u64) << FRAC_KIND_SHIFT;
    }

    fn set_precision(&mut self, precision: TimestampPrecision) {
        let prec_bits: u64 = match precision {
            TimestampPrecision::Year => 0,
            TimestampPrecision::Month => 1,
            TimestampPrecision::Day => 2,
            TimestampPrecision::HourAndMinute => 3,
            TimestampPrecision::Second => 4,
        };
        self.packed &= !(PRECISION_MASK << PRECISION_SHIFT);
        self.packed |= prec_bits << PRECISION_SHIFT;
    }

    #[cfg(feature = "experimental-chrono")]
    pub(crate) fn try_to_naive_datetime(&self) -> IonResult<NaiveDateTime> {
        if self.offset().is_some() {
            return IonResult::illegal_operation(
                "cannot convert a Timestamp with a known offset into a NaiveDateTime",
            );
        }
        let nanos = self.fractional_seconds_as_nanoseconds().unwrap_or(0);
        let dt = NaiveDate::from_ymd_opt(self.year() as i32, self.month(), self.day())
            .and_then(|d| d.and_hms_nano_opt(self.hour(), self.minute(), self.second(), nanos))
            .ok_or_else(|| {
                IonError::illegal_operation("timestamp fields produce invalid NaiveDateTime")
            })?;
        Ok(dt)
    }

    #[cfg(feature = "experimental-chrono")]
    pub(crate) fn try_to_datetime_fixed_offset(&self) -> IonResult<DateTime<FixedOffset>> {
        let offset_minutes = self.offset().ok_or_else(|| {
            IonError::illegal_operation(
                "cannot convert a Timestamp with an unknown offset into a DateTime<FixedOffset>",
            )
        })?;
        // Convert to UTC fields, then construct DateTime at the offset
        let (uy, umo, ud, uh, umi) = subtract_offset_to_utc(
            self.year() as u16,
            self.month() as u8,
            self.day() as u8,
            self.hour() as u8,
            self.minute() as u8,
            offset_minutes as i16,
        );
        let nanos = self.fractional_seconds_as_nanoseconds().unwrap_or(0);
        let utc_naive = NaiveDate::from_ymd_opt(uy as i32, umo as u32, ud as u32)
            .and_then(|d| d.and_hms_nano_opt(uh as u32, umi as u32, self.second(), nanos))
            .ok_or_else(|| {
                IonError::illegal_operation("timestamp UTC conversion produces invalid DateTime")
            })?;
        let offset = FixedOffset::east_opt(offset_minutes * 60).ok_or_else(|| {
            IonError::illegal_operation("timestamp offset out of range for chrono")
        })?;
        Ok(offset.from_utc_datetime(&utc_naive))
    }

    /// If the precision is [TimestampPrecision::Second], returns the Decimal scale of this
    /// Timestamp's fractional seconds; otherwise, returns None.
    pub fn fractional_seconds_scale(&self) -> Option<i64> {
        let kind = self.frac_kind();
        if kind == 0 {
            None
        } else {
            Some(kind as i64)
        }
    }

    /// Returns a Decimal representation of the fractional seconds, or None if precision
    /// is below Second or there are no fractional seconds.
    pub(crate) fn fractional_seconds_as_decimal(&self) -> Option<Decimal> {
        let kind = self.frac_kind();
        if kind == 0 {
            return None;
        }
        let coefficient = self.frac_payload;
        let exponent = -(kind as i64);
        Some(Decimal::new(coefficient, exponent))
    }

    /// Returns fractional seconds as nanoseconds (potentially lossy).
    fn fractional_seconds_as_nanoseconds(&self) -> Option<u32> {
        let kind = self.frac_kind() as u32;
        if kind == 0 {
            return None;
        }
        let coefficient = self.frac_payload;
        // Convert coefficient at `kind` digits of precision to nanoseconds (9 digits).
        let nanos = if kind <= 9 {
            // Scale up: multiply by 10^(9 - kind)
            let factor = 10u64.pow(9 - kind);
            coefficient.saturating_mul(factor)
        } else {
            // Scale down: divide by 10^(kind - 9)
            let divisor = 10u64.pow(kind - 9);
            coefficient / divisor
        };
        Some(nanos as u32)
    }

    fn fractional_seconds_compare(&self, other: &Timestamp) -> Ordering {
        let sk = self.frac_kind();
        let ok = other.frac_kind();
        if sk == 0 && ok == 0 {
            return Ordering::Equal;
        }
        // Same precision: direct coefficient comparison
        if sk == ok {
            return self.frac_payload.cmp(&other.frac_payload);
        }
        // Different precisions: normalize via decimal comparison
        let sd = self
            .fractional_seconds_as_decimal()
            .unwrap_or(Decimal::new(0u64, 0));
        let od = other
            .fractional_seconds_as_decimal()
            .unwrap_or(Decimal::new(0u64, 0));
        sd.cmp(&od)
    }

    fn fractional_seconds_equal(&self, other: &Timestamp) -> bool {
        let sk = self.frac_kind();
        let ok = other.frac_kind();
        if sk != ok {
            return false;
        }
        self.frac_payload == other.frac_payload
    }

    /// Writes the fractional seconds portion of a text timestamp, including a leading `.`.
    fn format_fractional_seconds<W: std::fmt::Write>(&self, output: &mut W) -> IonResult<()> {
        let kind = self.frac_kind() as u32;
        if kind == 0 {
            return Ok(());
        }
        let coefficient = self.frac_payload;
        if coefficient == 0 {
            // Write `.` followed by `kind` zeros (e.g., `.000` for millis precision)
            write!(output, ".")?;
            for _ in 0..kind {
                write!(output, "0")?;
            }
        } else {
            let actual_digits = coefficient.count_decimal_digits();
            let leading_zeros = kind.saturating_sub(actual_digits);
            write!(output, ".")?;
            for _ in 0..leading_zeros {
                write!(output, "0")?;
            }
            write!(output, "{coefficient}")?;
        }
        Ok(())
    }

    pub(crate) fn format<W: std::fmt::Write>(&self, output: &mut W) -> IonResult<()> {
        write!(output, "{:0>4}", self.year())?;
        if self.precision() == TimestampPrecision::Year {
            write!(output, "T")?;
            return Ok(());
        }

        write!(output, "-{:0>2}", self.month())?;
        if self.precision() == TimestampPrecision::Month {
            write!(output, "T")?;
            return Ok(());
        }

        write!(output, "-{:0>2}", self.day())?;
        if self.precision() == TimestampPrecision::Day {
            write!(output, "T")?;
            return Ok(());
        }

        write!(output, "T{:0>2}:{:0>2}", self.hour(), self.minute())?;
        if self.precision() == TimestampPrecision::HourAndMinute {
            self.format_offset(self.offset(), output)?;
            return Ok(());
        }

        write!(output, ":{:0>2}", self.second())?;
        self.format_fractional_seconds(output)?;
        self.format_offset(self.offset(), output)?;
        Ok(())
    }

    fn format_offset<W: std::fmt::Write>(
        &self,
        offset_minutes: Option<i32>,
        output: &mut W,
    ) -> IonResult<()> {
        let (sign, hours, minutes) = match offset_minutes {
            None => ("-", 0, 0),
            Some(offset_minutes) => {
                const MINUTES_PER_HOUR: i32 = 60;
                let sign = if offset_minutes >= 0 { "+" } else { "-" };
                let offset_minutes = offset_minutes.abs();
                let hours = offset_minutes / MINUTES_PER_HOUR;
                let minutes = offset_minutes % MINUTES_PER_HOUR;
                (sign, hours, minutes)
            }
        };
        write!(output, "{sign}{hours:0>2}:{minutes:0>2}")?;
        Ok(())
    }

    /// Creates a TimestampBuilder with the specified year and [TimestampPrecision::Year].
    pub fn with_year(year: u32) -> TimestampBuilder<HasYear> {
        TimestampBuilder::with_year(year)
    }

    /// Creates a TimestampBuilder with the specified year, month, and day. Its precision is
    /// set to [TimestampPrecision::Day].
    pub fn with_ymd(year: u32, month: u32, day: u32) -> TimestampBuilder<HasDay> {
        TimestampBuilder::with_year(year)
            .with_month(month)
            .with_day(day)
    }

    /// Returns the offset in minutes that has been specified in the [Timestamp].
    /// A positive value indicates Eastern Hemisphere, while a negative value indicates
    /// Western Hemisphere.
    pub fn offset(&self) -> Option<i32> {
        let raw = ((self.packed >> OFFSET_SHIFT) & OFFSET_MASK) as u16;
        if raw == OFFSET_UNKNOWN_SENTINEL {
            return None;
        }
        // Sign-extend from 12 bits
        let val = ((raw as i16) << 4) >> 4;
        Some(val as i32)
    }

    /// Returns the precision that has been specified in the [Timestamp].
    pub fn precision(&self) -> TimestampPrecision {
        match (self.packed >> PRECISION_SHIFT) & PRECISION_MASK {
            0 => TimestampPrecision::Year,
            1 => TimestampPrecision::Month,
            2 => TimestampPrecision::Day,
            3 => TimestampPrecision::HourAndMinute,
            _ => TimestampPrecision::Second,
        }
    }

    /// Returns the year that has been specified in the [Timestamp].
    pub fn year(&self) -> u32 {
        ((self.packed >> YEAR_SHIFT) & YEAR_MASK) as u32
    }

    /// Returns the month that has been specified in the [Timestamp].
    /// Returns the month number starting from 1. The return value ranges from 1 to 12.
    pub fn month(&self) -> u32 {
        ((self.packed >> MONTH_SHIFT) & MONTH_MASK) as u32
    }

    /// Returns the day that has been specified in the [Timestamp].
    /// Returns the day of month starting from 1.
    pub fn day(&self) -> u32 {
        ((self.packed >> DAY_SHIFT) & DAY_MASK) as u32
    }

    /// Returns the hour(s) that has been specified in the [Timestamp].
    /// Returns the hour number from 0 to 23.
    pub fn hour(&self) -> u32 {
        ((self.packed >> HOUR_SHIFT) & HOUR_MASK) as u32
    }

    /// Returns the minute(s) that has been specified in the [Timestamp].
    /// Returns the minute number from 0 to 59.
    pub fn minute(&self) -> u32 {
        ((self.packed >> MINUTE_SHIFT) & MINUTE_MASK) as u32
    }

    /// Returns the second(s) that has been specified in the [Timestamp].
    /// Returns the second number from 0 to 59.
    pub fn second(&self) -> u32 {
        ((self.packed >> SECOND_SHIFT) & SECOND_MASK) as u32
    }

    /// Return a UTC timestamp for this [Timestamp]
    pub fn to_utc(&self) -> Timestamp {
        let offset_minutes = match self.offset() {
            None => return *self,
            Some(m) => m as i16,
        };
        let (uy, umo, ud, uh, umi) = subtract_offset_to_utc(
            self.year() as u16,
            self.month() as u8,
            self.day() as u8,
            self.hour() as u8,
            self.minute() as u8,
            offset_minutes,
        );
        // Pack directly without validation — the source timestamp was already
        // valid, and UTC conversion can produce year 0 (e.g., 0001-01-01T00:30+01:00
        // → 0000-12-31T23:30 UTC). This is fine for comparison purposes.
        let packed = Self::pack(
            self.precision(),
            uy,
            umo,
            ud,
            uh,
            umi,
            self.second() as u8,
            OFFSET_UNKNOWN_SENTINEL,
            self.frac_kind(),
        );
        Timestamp {
            packed,
            frac_payload: self.frac_payload,
        }
    }

    /// Returns this Timestamp's fractional seconds in nanoseconds
    ///
    /// NOTE: This is a potentially lossy operation. A Timestamp with picoseconds would
    /// return a number of nanoseconds, losing precision. If it loses precision then
    /// truncation is performed.
    pub fn nanoseconds(&self) -> u32 {
        self.fractional_seconds_as_nanoseconds().unwrap_or_default()
    }

    /// Returns this Timestamp's fractional seconds in microseconds
    ///
    /// NOTE: This is a potentially lossy operation. A Timestamp with picoseconds would
    /// return a number of microseconds, losing precision. If it loses precision then
    /// truncation is performed.
    pub fn microseconds(&self) -> u32 {
        self.fractional_seconds_as_nanoseconds()
            .map(|s| s / 1_000)
            .unwrap_or_default()
    }

    /// Returns this Timestamp's fractional seconds in milliseconds
    ///
    /// NOTE: This is a potentially lossy operation. A Timestamp with picoseconds would
    /// return a number of milliseconds, losing precision. If it loses precision then
    /// truncation is performed.
    pub fn milliseconds(&self) -> u32 {
        self.fractional_seconds_as_nanoseconds()
            .map(|s| s / 1_000_000)
            .unwrap_or_default()
    }
}

/// Formats an ISO-8601 timestamp of appropriate precision and offset.
impl Display for Timestamp {
    fn fmt(&self, output: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.format(output).map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}

impl PartialOrd for Timestamp {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Timestamp {
    fn cmp(&self, other: &Self) -> Ordering {
        // Convert both to UTC for instant comparison
        let self_utc = self.to_utc();
        let other_utc = other.to_utc();

        let cmp = self_utc.year().cmp(&other_utc.year());
        if cmp != Ordering::Equal {
            return cmp;
        }
        let cmp = self_utc.month().cmp(&other_utc.month());
        if cmp != Ordering::Equal {
            return cmp;
        }
        let cmp = self_utc.day().cmp(&other_utc.day());
        if cmp != Ordering::Equal {
            return cmp;
        }
        let cmp = self_utc.hour().cmp(&other_utc.hour());
        if cmp != Ordering::Equal {
            return cmp;
        }
        let cmp = self_utc.minute().cmp(&other_utc.minute());
        if cmp != Ordering::Equal {
            return cmp;
        }
        let cmp = self_utc.second().cmp(&other_utc.second());
        if cmp != Ordering::Equal {
            return cmp;
        }
        self.fractional_seconds_compare(other)
    }
}

/// Two Timestamps are considered equal (though not necessarily IonEq) if they represent the same
/// instant in time. TimestampPrecision is ignored. Offsets do not have to match as long as the
/// instants being represented match.
impl PartialEq for Timestamp {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Timestamp {}

impl IonEq for Timestamp {
    fn ion_eq(&self, other: &Self) -> bool {
        let prec = self.precision();
        if prec != other.precision() {
            return false;
        }
        if self.offset() != other.offset() {
            return false;
        }
        if self.year() != other.year() {
            return false;
        }
        if prec >= TimestampPrecision::Month && self.month() != other.month() {
            return false;
        }
        if prec >= TimestampPrecision::Day && self.day() != other.day() {
            return false;
        }
        if prec >= TimestampPrecision::HourAndMinute
            && (self.hour() != other.hour() || self.minute() != other.minute())
        {
            return false;
        }
        if prec <= TimestampPrecision::HourAndMinute {
            return true;
        }
        if self.second() != other.second() {
            return false;
        }
        self.fractional_seconds_equal(other)
    }
}

impl IonDataOrd for Timestamp {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        let ord = self.cmp(other);
        if ord != Ordering::Equal {
            return ord;
        };

        let ord = self.precision().cmp(&other.precision());
        if ord != Ordering::Equal {
            return ord;
        };
        match [
            self.fractional_seconds_scale(),
            other.fractional_seconds_scale(),
        ] {
            [None, Some(b)] if b > 0 => return Ordering::Less,
            [Some(a), None] if a > 0 => return Ordering::Greater,
            [Some(a), Some(b)] => {
                let ord = a.cmp(&b);
                if ord != Ordering::Equal {
                    return ord;
                }
            }
            _ => {}
        }

        // By offset (unknown, then least to greatest)
        match [self.offset(), other.offset()] {
            [None, Some(_)] => Ordering::Less,
            [None, None] => Ordering::Equal,
            [Some(_), None] => Ordering::Greater,
            [Some(o1), Some(o2)] => o1.cmp(&o2),
        }
    }
}

impl IonDataHash for Timestamp {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        let prec = self.precision();
        prec.hash(state);
        self.year().hash(state);
        if prec >= TimestampPrecision::Month {
            self.month().hash(state)
        }
        if prec >= TimestampPrecision::Day {
            self.day().hash(state)
        }
        if prec >= TimestampPrecision::HourAndMinute {
            self.hour().hash(state);
            self.minute().hash(state);
        }
        if prec == TimestampPrecision::Second {
            self.second().hash(state);
            let scale = self.fractional_seconds_scale();
            match scale {
                None | Some(0) => {}
                Some(1..=9) => {
                    scale.unwrap().hash(state);
                    self.fractional_seconds_as_nanoseconds()
                        .unwrap()
                        .hash(state);
                }
                Some(_) => {
                    self.fractional_seconds_as_decimal()
                        .unwrap()
                        .ion_data_hash(state);
                }
            }
        }
        self.offset().hash(state);
    }
}

/// A Builder object for incrementally configuring and finally instantiating a [Timestamp].
/// This builder uses the type-state pattern to expose only those methods which can result in a
/// valid Timestamp. For example, it is not possible to set the `day` field without first setting
/// the `year` and `month` fields.
#[derive(Debug, Clone)]
pub struct TimestampBuilder<T> {
    _state: PhantomData<T>,
    fields_are_utc: bool,
    precision: TimestampPrecision,
    offset: Option<i32>,
    year: u32,
    month: u32,
    day: u32,
    hour: u32,
    minute: u32,
    second: u32,
    fractional_seconds: Option<Mantissa>,
    nanoseconds: Option<u32>,
}

impl<T> TimestampBuilder<T> {
    fn change_state<U>(self) -> TimestampBuilder<U> {
        TimestampBuilder {
            _state: PhantomData,
            fields_are_utc: self.fields_are_utc,
            precision: self.precision,
            offset: self.offset,
            year: self.year,
            month: self.month,
            day: self.day,
            hour: self.hour,
            minute: self.minute,
            second: self.second,
            fractional_seconds: self.fractional_seconds,
            nanoseconds: self.nanoseconds,
        }
    }

    /// Attempt to construct a [Timestamp] using the values configured on the [TimestampBuilder].
    pub fn build(self) -> IonResult<Timestamp> {
        // Determine fractional seconds digits and coefficient
        let (frac_digits, frac_coefficient) = if self.precision == TimestampPrecision::Second {
            match &self.fractional_seconds {
                Some(Mantissa::Digits(digits)) => {
                    let nanos = self.nanoseconds.unwrap_or(0) as u64;
                    // Convert nanoseconds (9 digits precision) to the requested digit count.
                    let coefficient = if *digits <= 9 {
                        nanos / 10u64.pow(9 - *digits)
                    } else {
                        nanos * 10u64.pow(*digits - 9)
                    };
                    (*digits, coefficient)
                }
                Some(Mantissa::Arbitrary(decimal)) => {
                    if decimal.is_less_than_zero() {
                        return IonResult::illegal_operation(
                            "cannot create a timestamp with negative fractional seconds",
                        );
                    }
                    if decimal.is_greater_than_or_equal_to_one() {
                        return IonResult::illegal_operation(
                            "cannot create a timestamp with a fractional seconds >= 1.0",
                        );
                    }
                    if decimal.is_zero() && decimal.exponent >= 0 {
                        // Zero with non-negative exponent = no fractional precision
                        (0u32, 0u64)
                    } else if decimal.is_zero() {
                        // Zero with negative exponent = explicit zero precision
                        // (e.g., 0d-4 means .0000)
                        // Clamp to MAX_FRAC_DIGITS; beyond that, still zero value
                        let digits = (decimal.exponent.unsigned_abs() as u32).min(MAX_FRAC_DIGITS);
                        (digits, 0u64)
                    } else {
                        let digits = decimal.exponent.unsigned_abs() as u32;
                        if digits > MAX_FRAC_DIGITS {
                            return IonResult::illegal_operation(format!(
                                "fractional seconds precision ({} digits) exceeds maximum ({})",
                                digits, MAX_FRAC_DIGITS
                            ));
                        }
                        let coeff = decimal.coefficient().magnitude().as_u128().unwrap_or(0) as u64;
                        (digits, coeff)
                    }
                }
                None => (0u32, 0u64),
            }
        } else {
            (0u32, 0u64)
        };

        let offset_i16 = self.offset.map(|m| m as i16);

        if self.fields_are_utc {
            if let Some(offset_minutes) = offset_i16 {
                Timestamp::from_utc_fields(
                    self.precision,
                    offset_minutes,
                    self.year as u16,
                    self.month as u8,
                    self.day as u8,
                    self.hour as u8,
                    self.minute as u8,
                    self.second as u8,
                    frac_digits,
                    frac_coefficient,
                )
            } else {
                Timestamp::from_fields(
                    self.precision,
                    None,
                    self.year as u16,
                    self.month as u8,
                    self.day as u8,
                    self.hour as u8,
                    self.minute as u8,
                    self.second as u8,
                    frac_digits,
                    frac_coefficient,
                )
            }
        } else {
            Timestamp::from_fields(
                self.precision,
                offset_i16,
                self.year as u16,
                self.month as u8,
                self.day as u8,
                self.hour as u8,
                self.minute as u8,
                self.second as u8,
                frac_digits,
                frac_coefficient,
            )
        }
    }

    /// Like [Self::build], but the fields provided for each time unit are understood
    /// to be in UTC rather than in the local time of the specified offset (if there is one).
    pub(crate) fn build_utc_fields_at_offset(
        mut self,
        offset_minutes: i32,
    ) -> IonResult<Timestamp> {
        self.fields_are_utc = true;
        self.offset = Some(offset_minutes);
        self.build()
    }
}

// The type states (HasYear, HasMonth, etc.) are pub in this module, but they do not appear as types
// in the documentation, they cannot be imported, and they are not nameable from outside this crate.
#[derive(Debug, Clone)]
pub struct HasYear;
impl TimestampBuilder<HasYear> {
    pub fn with_year(year: u32) -> Self {
        TimestampBuilder {
            _state: Default::default(),
            fields_are_utc: false,
            precision: TimestampPrecision::Year,
            offset: None,
            year,
            month: 1,
            day: 1,
            hour: 0,
            minute: 0,
            second: 0,
            fractional_seconds: None,
            nanoseconds: None,
        }
    }

    pub fn with_ymd(year: u32, month: u32, day: u32) -> TimestampBuilder<HasDay> {
        Self::with_year(year).with_month(month).with_day(day)
    }

    // Libraries have conflicting opinions about whether months should be
    // 0- or 1-indexed, so Timestamp follows chrono's lead and provides
    // convenient ways to do both. Internally, it uses a 1-based representation.

    // 0-indexed month
    pub fn with_month0(self, month: u32) -> TimestampBuilder<HasMonth> {
        self.with_month(month + 1)
    }

    // 1-indexed month
    pub fn with_month(mut self, month: u32) -> TimestampBuilder<HasMonth> {
        self.precision = TimestampPrecision::Month;
        self.month = month;
        self.change_state()
    }
}

#[derive(Debug, Clone)]
pub struct HasMonth;
impl TimestampBuilder<HasMonth> {
    // Libraries have conflicting opinions about whether days should be
    // 0- or 1-indexed, so Timestamp follows chrono's lead and provides
    // convenient ways to do both. Internally, it uses a 1-based representation.

    // 0-indexed day
    pub fn with_day0(self, day: u32) -> TimestampBuilder<HasDay> {
        self.with_day(day + 1)
    }

    // 1-indexed day
    pub fn with_day(mut self, day: u32) -> TimestampBuilder<HasDay> {
        self.precision = TimestampPrecision::Day;
        self.day = day;
        self.change_state()
    }
}

#[derive(Debug, Clone)]
pub struct HasDay;
impl TimestampBuilder<HasDay> {
    pub fn with_hms(self, hour: u32, minute: u32, second: u32) -> TimestampBuilder<HasSeconds> {
        self.with_hour(hour).with_minute(minute).with_second(second)
    }

    pub fn with_hour_and_minute(mut self, hour: u32, minute: u32) -> TimestampBuilder<HasMinute> {
        self.precision = TimestampPrecision::HourAndMinute;
        self.hour = hour;
        self.minute = minute;
        self.change_state()
    }

    pub fn with_hour(mut self, hour: u32) -> TimestampBuilder<HasHour> {
        self.precision = TimestampPrecision::HourAndMinute;
        self.hour = hour;
        self.change_state()
    }
}

macro_rules! with_offset {
    () => {
        /// Sets the difference, in minutes, from UTC. A positive value indicates
        /// Eastern Hemisphere, while a negative value indicates Western Hemisphere.
        // The unit (minutes) could be seconds (which is what the chrono crate uses
        // internally), but Ion uses minutes in its binary representation, so it
        // makes sense to be consistent.
        pub fn with_offset(mut self, offset_minutes: i32) -> TimestampBuilder<HasOffset> {
            self.offset = Some(offset_minutes);
            self.change_state()
        }
    };
}

#[derive(Debug, Clone)]
pub struct HasHour;
impl TimestampBuilder<HasHour> {
    pub fn with_minute(mut self, minute: u32) -> TimestampBuilder<HasMinute> {
        self.precision = TimestampPrecision::HourAndMinute;
        self.minute = minute;
        self.change_state()
    }

    with_offset!();
}

#[derive(Debug, Clone)]
pub struct HasMinute;
impl TimestampBuilder<HasMinute> {
    pub fn with_second(mut self, second: u32) -> TimestampBuilder<HasSeconds> {
        self.precision = TimestampPrecision::Second;
        self.second = second;
        self.change_state()
    }

    with_offset!();
}

#[derive(Debug, Clone)]
pub struct HasSeconds;
impl TimestampBuilder<HasSeconds> {
    // Note that in order to create a `FractionalSecondSetter`, the user will have had to first
    // create a `SecondSetter`. Because of this, the builder's precision is already set to
    // `TimestampPrecision::Second`.
    pub fn with_nanoseconds(mut self, nanosecond: u32) -> TimestampBuilder<HasFractionalSeconds> {
        self.fractional_seconds = Some(Mantissa::Digits(9));
        self.nanoseconds = Some(nanosecond);
        self.change_state()
    }

    pub fn with_microseconds(mut self, microsecond: u32) -> TimestampBuilder<HasFractionalSeconds> {
        self.fractional_seconds = Some(Mantissa::Digits(6));
        self.nanoseconds = Some(microsecond * 1000);
        self.change_state()
    }

    pub fn with_milliseconds(mut self, millisecond: u32) -> TimestampBuilder<HasFractionalSeconds> {
        self.fractional_seconds = Some(Mantissa::Digits(3));
        self.nanoseconds = Some(millisecond * 1_000_000);
        self.change_state()
    }

    pub fn with_nanoseconds_and_precision(
        mut self,
        nanoseconds: u32,
        precision_digits: u32,
    ) -> TimestampBuilder<HasFractionalSeconds> {
        self.fractional_seconds = Some(Mantissa::Digits(precision_digits));
        self.nanoseconds = Some(nanoseconds);
        self.change_state()
    }

    pub fn with_fractional_seconds(
        mut self,
        fractional_seconds: Decimal,
    ) -> TimestampBuilder<HasFractionalSeconds> {
        self.fractional_seconds = Some(Mantissa::Arbitrary(fractional_seconds));
        self.nanoseconds = None;
        self.change_state()
    }

    with_offset!();
}

#[derive(Debug, Clone)]
pub struct HasFractionalSeconds;
impl TimestampBuilder<HasFractionalSeconds> {
    with_offset!();
}

#[derive(Debug, Clone)]
pub struct HasOffset;
// No impl for TimestampBuilder<HasOffset> because `build()` is included in TimestampBuilder<T>

#[cfg(feature = "experimental-chrono")]
impl TryInto<NaiveDateTime> for Timestamp {
    type Error = IonError;

    fn try_into(self) -> Result<NaiveDateTime, Self::Error> {
        self.try_to_naive_datetime()
    }
}

#[cfg(feature = "experimental-chrono")]
impl TryInto<DateTime<FixedOffset>> for Timestamp {
    type Error = IonError;

    fn try_into(self) -> Result<DateTime<FixedOffset>, Self::Error> {
        self.try_to_datetime_fixed_offset()
    }
}

#[cfg(feature = "experimental-chrono")]
impl From<NaiveDateTime> for Timestamp {
    fn from(date_time: NaiveDateTime) -> Self {
        Self::from_naive_datetime(date_time)
    }
}

#[cfg(feature = "experimental-chrono")]
impl From<DateTime<FixedOffset>> for Timestamp {
    fn from(fixed_offset_date_time: DateTime<FixedOffset>) -> Self {
        Self::from_fixed_offset_datetime(fixed_offset_date_time)
    }
}

#[cfg(test)]
mod timestamp_tests {
    use super::*;
    use crate::ion_data::IonEq;
    use crate::result::IonResult;
    use crate::{Decimal, Int, Timestamp, TimestampPrecision};
    #[cfg(feature = "experimental-chrono")]
    use chrono::{DateTime, FixedOffset, NaiveDate, NaiveDateTime, Timelike};
    use rstest::*;
    use std::cmp::Ordering;
    use std::io::Write;
    use std::ops::Mul;

    #[test]
    fn test_timestamps_with_same_ymd_hms_millis_at_known_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5)
            .with_hms(16, 43, 51)
            .with_milliseconds(192);
        let timestamp1 = builder.clone().with_offset(5 * 60).build()?;
        let timestamp2 = builder.with_offset(5 * 60).build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_millis_at_known_offset_are_equal_ordering() -> IonResult<()>
    {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5)
            .with_hms(16, 43, 51)
            .with_milliseconds(192);
        let timestamp1 = builder.clone().with_offset(5 * 60).build()?;
        let timestamp2 = builder.with_offset(5 * 60).build()?;
        assert!(timestamp1 == timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_millis_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5)
            .with_hms(16, 43, 51)
            .with_milliseconds(192);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_at_known_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hms(16, 43, 51);
        let timestamp1 = builder.clone().with_offset(5 * 60).build()?;
        let timestamp2 = builder.with_offset(5 * 60).build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_from_utc_and_local_hm_fields_at_same_offset_are_equal() -> IonResult<()> {
        // Builder 1 specifies its time fields in the local time of the specified offset
        let builder1 = TimestampBuilder::with_ymd(2021, 2, 5).with_hour_and_minute(11, 43);
        let timestamp1 = builder1.with_offset(-5 * 60).build()?;
        // Builder 2 specifies its time fields in UTC and expects the offset to be applied afterwards
        let builder2 = TimestampBuilder::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp2 = builder2.build_utc_fields_at_offset(-5 * 60)?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_from_utc_and_local_hms_fields_at_same_offset_are_equal() -> IonResult<()> {
        // Builder 1 specifies its time fields in the local time of the specified offset
        let builder1 = TimestampBuilder::with_ymd(2021, 2, 5).with_hms(11, 43, 51);
        let timestamp1 = builder1.with_offset(-5 * 60).build()?;
        // Builder 2 specifies its time fields in UTC and expects the offset to be applied afterwards
        let builder2 = TimestampBuilder::with_ymd(2021, 2, 5).with_hms(16, 43, 51);
        let timestamp2 = builder2.build_utc_fields_at_offset(-5 * 60)?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hms(16, 43, 51);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hm_at_known_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp1 = builder.clone().with_offset(5 * 60).build()?;
        let timestamp2 = builder.with_offset(5 * 60).build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hm_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ym_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_year(2021).with_month(2);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_year_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_year(2021);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_at_different_offsets_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5)
            .with_hms(16, 43, 51)
            .with_milliseconds(192);
        let timestamp1 = builder.clone().with_offset(5 * 60).build()?;
        let timestamp2 = builder.with_offset(4 * 60).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_known_and_unknown_offsets_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5)
            .with_hms(16, 43, 51)
            .with_milliseconds(192);
        let timestamp1 = builder.clone().with_offset(5 * 60).build()?;
        let timestamp2 = builder.build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_precisions_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hms(16, 43, 51);
        let timestamp1 = builder.clone().with_offset(5 * 60).build()?;
        let timestamp2 = builder.with_milliseconds(192).with_offset(5 * 60).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_fractional_second_precision_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hms(16, 43, 51);
        let timestamp1 = builder
            .clone()
            .with_milliseconds(192)
            .with_offset(5 * 60)
            .build()?;
        // The microseconds field has the same amount of time, but a different precision.
        let timestamp2 = builder
            .with_microseconds(193 * 1_000)
            .with_offset(5 * 60)
            .build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_fractional_seconds_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hms(16, 43, 51);
        let timestamp1 = builder
            .clone()
            .with_milliseconds(192)
            .with_offset(5 * 60)
            .build()?;
        let timestamp2 = builder.with_milliseconds(193).with_offset(5 * 60).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_seconds_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp1 = builder
            .clone()
            .with_second(12)
            .with_offset(5 * 60)
            .build()?;
        let timestamp2 = builder.with_second(13).with_offset(5 * 60).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_minutes_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5);
        let timestamp1 = builder
            .clone()
            .with_hour_and_minute(16, 42)
            .with_offset(5 * 60)
            .build()?;
        let timestamp2 = builder
            .with_hour_and_minute(16, 43)
            .with_offset(5 * 60)
            .build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_hours_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5);
        let timestamp1 = builder
            .clone()
            .with_hour_and_minute(16, 42)
            .with_offset(5 * 60)
            .build()?;
        let timestamp2 = builder
            .with_hour_and_minute(17, 42)
            .with_offset(5 * 60)
            .build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_days_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_year(2021).with_month(2);
        let timestamp1 = builder.clone().with_day(5).build()?;
        let timestamp2 = builder.with_day(6).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_months_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_year(2021);
        let timestamp1 = builder.clone().with_month(2).build()?;
        let timestamp2 = builder.with_month(3).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_years_are_not_equal() -> IonResult<()> {
        let timestamp1 = TimestampBuilder::with_year(2021).build()?;
        let timestamp2 = TimestampBuilder::with_year(2022).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[cfg(feature = "experimental-chrono")]
    #[test]
    fn test_timestamp_try_into_naive_datetime() -> IonResult<()> {
        let timestamp = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .build()?;
        let naive_datetime: NaiveDateTime = timestamp.try_into()?;
        let expected = NaiveDate::from_ymd_opt(2021, 4, 6)
            .unwrap()
            .and_hms_opt(10, 15, 0)
            .unwrap();
        assert_eq!(expected, naive_datetime);
        Ok(())
    }

    #[cfg(feature = "experimental-chrono")]
    #[test]
    fn test_timestamp_try_into_naive_datetime_fractional_seconds() -> IonResult<()> {
        let timestamp = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_milliseconds(449)
            .build()?;
        let datetime: NaiveDateTime = timestamp.try_into()?;
        let naive_datetime = NaiveDate::from_ymd_opt(2021, 4, 6)
            .unwrap()
            .and_hms_opt(10, 15, 0)
            .unwrap()
            .with_nanosecond(449000000)
            .unwrap();
        assert_eq!(datetime, naive_datetime);
        Ok(())
    }

    #[cfg(feature = "experimental-chrono")]
    #[test]
    fn test_timestamp_try_into_naive_datetime_error() -> IonResult<()> {
        let timestamp = TimestampBuilder::with_ymd(2021, 1, 1)
            .with_hms(0, 0, 0)
            .with_offset(0)
            .build()?;
        //     ^---- This timestamp has a known offset, so we cannot convert it into a NaiveDateTime
        let result: IonResult<NaiveDateTime> = timestamp.try_into();
        assert!(result.is_err());
        Ok(())
    }

    #[cfg(feature = "experimental-chrono")]
    #[test]
    fn test_timestamp_try_into_fixed_offset_datetime() -> IonResult<()> {
        let timestamp = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_offset(-5 * 60)
            .build()?;
        //                    ^-- Timestamp's offset API takes minutes
        let datetime: DateTime<FixedOffset> = timestamp.try_into()?;
        // chrono's FixedOffset takes seconds ----------v
        let expected_offset = offset_east(-5 * 60 * 60);
        let naive_datetime = NaiveDate::from_ymd_opt(2021, 4, 6)
            .unwrap()
            .and_hms_opt(10, 15, 0)
            .unwrap();
        let expected_datetime = expected_offset
            .from_local_datetime(&naive_datetime)
            .unwrap();
        assert_eq!(datetime, expected_datetime);
        Ok(())
    }

    #[cfg(feature = "experimental-chrono")]
    #[test]
    fn test_timestamp_try_into_fixed_offset_datetime_fractional_seconds() -> IonResult<()> {
        let timestamp = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_milliseconds(449)
            .with_offset(-5 * 60)
            .build()?;
        //                    ^-- Timestamp's offset API takes minutes
        let datetime: DateTime<FixedOffset> = timestamp.try_into()?;
        // chrono's FixedOffset takes seconds ----------v
        let expected_offset = offset_east(-5 * 60 * 60);
        let naive_datetime = NaiveDate::from_ymd_opt(2021, 4, 6)
            .unwrap()
            .and_hms_opt(10, 15, 0)
            .unwrap()
            .with_nanosecond(449000000)
            .unwrap();
        let expected_datetime = expected_offset
            .from_local_datetime(&naive_datetime)
            .unwrap();
        assert_eq!(datetime, expected_datetime);
        Ok(())
    }

    #[cfg(feature = "experimental-chrono")]
    #[test]
    fn test_timestamp_try_into_datetime_fixedoffset_error() -> IonResult<()> {
        let timestamp = TimestampBuilder::with_ymd(2021, 1, 1)
            .with_hms(0, 0, 0)
            .build()?;
        //     ^---- This timestamp has an unknown offset, so we cannot convert it into a DateTime<FixedOffset>
        let result: IonResult<DateTime<FixedOffset>> = timestamp.try_into();
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn test_timestamp_builder() {
        // Using individual field setters produces the same Timestamp as using setters
        // for common combinations of fields (with_ymd, with_hms).
        let timestamp1 = TimestampBuilder::with_year(2021)
            .with_month(2)
            .with_day(5)
            .with_hour(17)
            .with_minute(39)
            .with_second(51)
            .with_milliseconds(194)
            .with_offset(-4 * 60)
            .build()
            .unwrap_or_else(|e| panic!("Couldn't build timestamp: {e:?}"));

        let timestamp2 = TimestampBuilder::with_ymd(2021, 2, 5)
            .with_hms(17, 39, 51)
            .with_milliseconds(194)
            .with_offset(-4 * 60)
            .build()
            .unwrap_or_else(|e| panic!("Couldn't build timestamp: {e:?}"));

        assert_eq!(timestamp1.precision(), TimestampPrecision::Second);
        assert_eq!(timestamp1.fractional_seconds_scale(), Some(3));
        assert_eq!(timestamp1, timestamp2);

        assert!(timestamp1.ion_eq(&timestamp2));
    }

    #[test]
    fn test_timestamp_builder_without_minutes() {
        // Even though we set hour and not minute, this should still have a precision of HourAndMinute.
        let timestamp1 = TimestampBuilder::with_year(2021)
            .with_month(2)
            .with_day(5)
            .with_hour(17)
            .with_offset(60)
            .build()
            .unwrap_or_else(|e| panic!("Couldn't build timestamp: {e:?}"));

        let timestamp2 = TimestampBuilder::with_ymd(2021, 2, 5)
            .with_hour_and_minute(17, 0)
            .with_offset(60)
            .build()
            .unwrap_or_else(|e| panic!("Couldn't build timestamp: {e:?}"));

        assert_eq!(timestamp1.precision(), TimestampPrecision::HourAndMinute);
        assert_eq!(timestamp1, timestamp2)
    }

    #[test]
    fn test_timestamp_fixed_offset() -> IonResult<()> {
        let timestamp = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_milliseconds(449)
            .with_offset(-5 * 60)
            .build()?;
        //                    ^-- Timestamp's offset API takes minutes
        // expected offset in minutes
        let expected_offset = -5 * 60;

        assert_eq!(timestamp.offset().unwrap(), expected_offset);
        Ok(())
    }

    #[test]
    fn test_timestamp_precision() -> IonResult<()> {
        let timestamp = Timestamp::with_year(2021).with_month(2).build()?;
        assert_eq!(timestamp.precision(), TimestampPrecision::Month);
        Ok(())
    }

    #[test]
    fn test_timestamp_year() -> IonResult<()> {
        let timestamp_1 = TimestampBuilder::with_year(2021).with_month(2).build()?;
        assert_eq!(timestamp_1.year(), 2021);

        let timestamp_2 = TimestampBuilder::with_ymd(2021, 12, 31)
            .with_hms(10, 15, 30)
            .with_offset(-11 * 60)
            .build()?;

        assert_eq!(timestamp_2.year(), 2021);

        let timestamp_3 = TimestampBuilder::with_ymd(2021, 12, 31)
            .with_hms(15, 15, 30)
            .with_offset(10 * 60)
            .build()?;

        assert_eq!(timestamp_3.year(), 2021);

        Ok(())
    }

    #[test]
    fn test_timestamp_month() -> IonResult<()> {
        let timestamp_1 = TimestampBuilder::with_year(2021).with_month(2).build()?;
        assert_eq!(timestamp_1.month(), 2);

        let timestamp_2 = TimestampBuilder::with_ymd(2021, 1, 31)
            .with_hms(10, 15, 30)
            .with_offset(-11 * 60)
            .build()?;

        assert_eq!(timestamp_2.month(), 1);

        let timestamp_3 = TimestampBuilder::with_ymd(2021, 1, 31)
            .with_hms(15, 15, 30)
            .with_offset(10 * 60)
            .build()?;

        assert_eq!(timestamp_3.month(), 1);

        Ok(())
    }

    #[test]
    fn test_timestamp_day() -> IonResult<()> {
        let timestamp_1 = TimestampBuilder::with_year(2021).with_month(2).build()?;
        assert_eq!(timestamp_1.day(), 1);

        let timestamp_2 = TimestampBuilder::with_year(2021)
            .with_month(2)
            .with_day(4)
            .build()?;

        assert_eq!(timestamp_2.day(), 4);

        let timestamp_3 = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 30)
            .with_offset(-11 * 60)
            .build()?;

        assert_eq!(timestamp_3.day(), 6);

        let timestamp_4 = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(15, 15, 30)
            .with_offset(10 * 60)
            .build()?;

        assert_eq!(timestamp_4.day(), 6);

        Ok(())
    }

    #[rstest]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(-90).build(), 10)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(-5 * 60).build(), 10)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(5 * 60).build(), 10)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(15).build(), 10)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(30).build(), 10)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(0).build(), 10)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(0, 15, 30).with_offset(5 * 60).build(), 0)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(23, 15, 30).with_offset(-5 * 60).build(), 23)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(0, 15, 30).with_offset(23 * 60).build(), 0)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(-11 * 60).build(), 10)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(15, 15, 30).with_offset(10 * 60).build(), 15)]
    fn test_timestamp_hour(
        #[case] timestamp: IonResult<Timestamp>,
        #[case] expected_hours: u32,
    ) -> IonResult<()> {
        assert_eq!(timestamp?.hour(), expected_hours);
        Ok(())
    }

    #[rstest]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(-90).build(), 15)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(-5 * 60).build(), 15)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(5 * 60).build(), 15)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(0).build(), 15)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 0, 30).with_offset(5 * 60).build(), 0)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 59, 30).with_offset(5 * 60).build(), 59)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(-11 * 60).build(), 15)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(15, 15, 30).with_offset(10 * 60).build(), 15)]
    fn test_timestamp_minute(
        #[case] timestamp: IonResult<Timestamp>,
        #[case] expected_minutes: u32,
    ) -> IonResult<()> {
        assert_eq!(timestamp?.minute(), expected_minutes);
        Ok(())
    }

    #[test]
    fn test_timestamp_second() -> IonResult<()> {
        let timestamp = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 30)
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(timestamp.second(), 30);
        Ok(())
    }

    #[test]
    fn test_timestamp_nanoseconds() -> IonResult<()> {
        let timestamp_1 = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 30)
            .with_nanoseconds(192)
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(timestamp_1.nanoseconds(), 192);

        let timestamp_2 = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 30)
            .with_milliseconds(192)
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(timestamp_2.nanoseconds(), 192000000);

        let timestamp_3 = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 30)
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(timestamp_3.nanoseconds(), 0);

        // Big fractional coefficient (>19 digits) is rejected by Variant A
        let big_coefficient: Int = Int::from(i128::MAX).data.mul(4).into();
        let result = Timestamp::with_ymd(2023, 1, 1)
            .with_hour_and_minute(0, 0)
            .with_second(0)
            .with_fractional_seconds(Decimal::new(big_coefficient, -39))
            .build();
        assert!(result.is_err());

        // Exponent delta > 19 digits: also rejected
        let result = Timestamp::with_ymd(2023, 1, 1)
            .with_hour_and_minute(0, 0)
            .with_second(0)
            .with_fractional_seconds(Decimal::new(1i64, -50))
            .build();
        assert!(result.is_err());

        // 19 fractional digits (max allowed) should work
        let timestamp_4 = Timestamp::with_ymd(2023, 1, 1)
            .with_hour_and_minute(0, 0)
            .with_second(0)
            .with_fractional_seconds(Decimal::new(123456789u64, -9))
            .build()?;
        assert_eq!(timestamp_4.nanoseconds(), 123456789);

        Ok(())
    }

    #[test]
    fn test_timestamp_milliseconds() -> IonResult<()> {
        let timestamp_1 = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 30)
            .with_milliseconds(192)
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(timestamp_1.milliseconds(), 192);

        let timestamp_2 = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 30)
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(timestamp_2.milliseconds(), 0);
        Ok(())
    }

    #[test]
    fn test_timestamp_to_utc() -> IonResult<()> {
        let new_years_eve_nyc = TimestampBuilder::with_ymd(2022, 12, 31)
            .with_hms(23, 59, 00)
            .with_offset(-5 * 60)
            .build()?;

        let london = new_years_eve_nyc.to_utc();
        assert_eq!(london.year(), 2023);
        assert_eq!(london.month(), 1);
        assert_eq!(london.day(), 1);
        assert_eq!(london.hour(), 4);
        assert_eq!(london.minute(), 59);
        assert_eq!(london.second(), 0);
        Ok(())
    }

    #[test]
    fn test_timestamp_to_utc_year_boundary() -> IonResult<()> {
        // UTC conversion that crosses year boundary to year 0 must not panic
        let ts = TimestampBuilder::with_ymd(1, 1, 1)
            .with_hour_and_minute(0, 30)
            .with_offset(60)
            .build()?;
        let utc = ts.to_utc();
        assert_eq!(utc.year(), 0);
        assert_eq!(utc.month(), 12);
        assert_eq!(utc.day(), 31);
        assert_eq!(utc.hour(), 23);
        assert_eq!(utc.minute(), 30);
        Ok(())
    }

    #[test]
    fn test_timestamp_comparison_year_boundary_no_panic() -> IonResult<()> {
        // Comparing timestamps where UTC conversion yields year 0 must not panic
        let ts1 = TimestampBuilder::with_ymd(1, 1, 1)
            .with_hour_and_minute(0, 30)
            .with_offset(60)
            .build()?;
        let ts2 = TimestampBuilder::with_ymd(1, 1, 1)
            .with_hour_and_minute(1, 30)
            .with_offset(60)
            .build()?;
        assert!(ts1 < ts2);
        Ok(())
    }

    #[test]
    fn test_timestamp_fractional_seconds_scale() -> IonResult<()> {
        // Set fractional seconds as Decimal
        let timestamp_with_micro_seconds = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_fractional_seconds(Decimal::new(553u64, -6))
            .with_offset(-5 * 60)
            .build()?;

        assert_eq!(
            timestamp_with_micro_seconds
                .fractional_seconds_scale()
                .unwrap(),
            6
        );

        // Set fractional seconds as Decimal with 0 coefficient and non-negative exponent
        // "Fractions whose coefficient is zero and exponent is greater than -1 are ignored."
        let timestamp_with_redundant_fractional_seconds = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_fractional_seconds(Decimal::new(0, 6))
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(
            timestamp_with_redundant_fractional_seconds.precision(),
            TimestampPrecision::Second
        );
        assert_eq!(
            timestamp_with_redundant_fractional_seconds.fractional_seconds_scale(),
            None
        );

        // Set fractional seconds with milliseconds
        let timestamp_with_milliseconds = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_milliseconds(449)
            .with_offset(-5 * 60)
            .build()?;

        assert_eq!(
            timestamp_with_milliseconds
                .fractional_seconds_scale()
                .unwrap(),
            3
        );

        // Set a fractional seconds as Decimal with low precision
        let timestamp_with_seconds = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_offset(-5 * 60)
            .build()?;

        // For low precision fractional_seconds_scale should return a None
        assert_eq!(timestamp_with_seconds.fractional_seconds_scale(), None);
        Ok(())
    }

    #[rstest]
    #[case::timestamp_with_same_year(TimestampBuilder::with_year(2020).build().unwrap(), TimestampBuilder::with_year(2020).build().unwrap(), Ordering::Equal)]
    #[case::timestamp_with_different_year(TimestampBuilder::with_year(2020).build().unwrap(), TimestampBuilder::with_year(2021).build().unwrap(), Ordering::Less)]
    #[case::timestamp_with_milliseconds(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_milliseconds(449).with_offset(5 * 60).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_milliseconds(449).with_offset(5 * 60).build().unwrap(), Ordering::Equal)]
    #[case::timestamp_with_milliseconds_nanoseconds(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_milliseconds(449).with_offset(5 * 60).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_nanoseconds(449000005).with_offset(5 * 60).build().unwrap(), Ordering::Less)]
    #[case::timestamp_with_fractional_seconds(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_fractional_seconds(Decimal::new(449u64, -3)).with_offset(5 * 60).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_nanoseconds(449000000).with_offset(5 * 60).build().unwrap(), Ordering::Equal)]
    #[case::timestamp_with_different_precision(TimestampBuilder::with_year(2020).with_month(3).build().unwrap(), TimestampBuilder::with_year(2020).build().unwrap(), Ordering::Greater)]
    #[case::timestamp_with_same_offset(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_offset(-5 * 60).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_offset(-5 * 60).build().unwrap(), Ordering::Equal)]
    #[case::timestamp_with_different_offset(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_offset(5 * 60).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_offset(-5 * 60).build().unwrap(), Ordering::Less)]
    #[case::timestamp_with_unknown_offset(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_offset(-5 * 60).build().unwrap(), Ordering::Less)]
    #[case::timestamp_with_unknown_offset(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_nanoseconds(0).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).build().unwrap(), Ordering::Equal)]
    #[case::timestamp_with_unknown_offset(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_nanoseconds(449000005).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).build().unwrap(), Ordering::Greater)]
    #[case::timestamp_with_second_precison_and_year_precision(TimestampBuilder::with_ymd(2001, 1, 1).build().unwrap(), TimestampBuilder::with_ymd(2001, 1, 1).with_hms(0, 0, 0).with_fractional_seconds(Decimal::new(00000000000000000000i128, -20)).build().unwrap(), Ordering::Equal)]
    fn timestamp_ordering_tests(
        #[case] this: Timestamp,
        #[case] other: Timestamp,
        #[case] expected: Ordering,
    ) {
        assert_eq!(this.cmp(&other), expected)
    }

    #[test]
    fn ion_eq_fraction_seconds_mixed_mantissa() {
        // 1857-05-29T19:25:59.1+23:59
        // offset = 23*60 + 59 = 1439 minutes
        let t1 = TimestampBuilder::with_ymd(1857, 5, 29)
            .with_hms(19, 25, 59)
            .with_fractional_seconds(Decimal::new(1u64, -1))
            .with_offset(1439)
            .build()
            .unwrap();
        let t2 = TimestampBuilder::with_ymd(1857, 5, 29)
            .with_hms(19, 25, 59)
            .with_fractional_seconds(Decimal::new(1u64, -1))
            .with_offset(1439)
            .build()
            .unwrap();
        assert_eq!(t1, t2);
        assert!(t1.ion_eq(&t2));
    }

    #[test]
    fn ion_eq_fraction_seconds_mixed_mantissa_2() {
        // 2001-08-01T18:18:49.00600+01:01
        // offset = 61 minutes
        let t1 = TimestampBuilder::with_ymd(2001, 8, 1)
            .with_hms(18, 18, 49)
            .with_fractional_seconds(Decimal::new(600u64, -5))
            .with_offset(61)
            .build()
            .unwrap();
        let t2 = TimestampBuilder::with_ymd(2001, 8, 1)
            .with_hms(18, 18, 49)
            .with_fractional_seconds(Decimal::new(600u64, -5))
            .with_offset(61)
            .build()
            .unwrap();
        assert_eq!(t1, t2);
        assert!(t1.ion_eq(&t2));
    }

    #[rstest]
    #[case(TimestampBuilder::with_year(3030).build().unwrap(), "3030T")]
    #[case(TimestampBuilder::with_year(3030).with_month(11).build().unwrap(), "3030-11T")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).build().unwrap(), "3030-03-31T")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hour_and_minute(17, 31).build().unwrap(), "3030-03-31T17:31-00:00")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hour_and_minute(17, 31).with_offset(-420).build().unwrap(), "3030-03-31T17:31-07:00")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hour_and_minute(17, 31).build_utc_fields_at_offset(-420).unwrap(), "3030-03-31T10:31-07:00")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hms(17, 31, 57).with_offset(0).build().unwrap(), "3030-03-31T17:31:57+00:00")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hms(17, 31, 57).with_milliseconds(27).with_offset(0).build().unwrap(), "3030-03-31T17:31:57.027+00:00")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hms(17, 31, 57).with_microseconds(27).with_offset(0).build().unwrap(), "3030-03-31T17:31:57.000027+00:00")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hms(17, 31, 57).with_nanoseconds(27).with_offset(0).build().unwrap(), "3030-03-31T17:31:57.000000027+00:00")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hms(17, 31, 57).with_fractional_seconds(Decimal::new(27, -12)).with_offset(0).build().unwrap(), "3030-03-31T17:31:57.000000000027+00:00")]
    fn test_display(#[case] ts: Timestamp, #[case] expect: String) {
        let mut buf = Vec::new();
        write!(&mut buf, "{ts}").unwrap();
        assert_eq!(expect, String::from_utf8(buf).unwrap());
    }
}
