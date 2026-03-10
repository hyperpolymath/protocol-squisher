// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Atomic Types
//!
//! Atoms are the leaves of the shape tree — the indivisible primitives from which
//! all compound shapes are built. Every serialization format, database column type,
//! and programming language primitive maps to one of these.
//!
//! The design deliberately covers the union of all common type systems:
//! - Protobuf's fixed32/sfixed64/etc. map to the sized integer variants
//! - SQL's DECIMAL(p,s) maps to [`AtomKind::Decimal`]
//! - UUID and hash types map to [`AtomKind::FixedBytes`]
//! - Avro's `timestamp-millis` and `timestamp-micros` map to [`AtomKind::Timestamp`]

use serde::{Deserialize, Serialize};
use std::fmt;

/// The set of primitive atomic types that form the basis of all data shapes.
///
/// Every atom has a known, fixed information content (except [`AtomKind::String`]
/// and [`AtomKind::Bytes`], which are unbounded). This property is essential for
/// computing [`crate::information::InformationContent`].
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AtomKind {
    /// Boolean — exactly 1 bit of information.
    Bool,

    /// Unsigned 8-bit integer (0..255).
    U8,
    /// Unsigned 16-bit integer.
    U16,
    /// Unsigned 32-bit integer.
    U32,
    /// Unsigned 64-bit integer.
    U64,
    /// Unsigned 128-bit integer.
    U128,

    /// Signed 8-bit integer (-128..127).
    I8,
    /// Signed 16-bit integer.
    I16,
    /// Signed 32-bit integer.
    I32,
    /// Signed 64-bit integer.
    I64,
    /// Signed 128-bit integer.
    I128,

    /// IEEE 754 single-precision floating point.
    F32,
    /// IEEE 754 double-precision floating point.
    F64,

    /// Variable-length UTF-8 string. Unbounded information content.
    String,
    /// Variable-length byte sequence. Unbounded information content.
    Bytes,

    /// Fixed-size byte array (e.g., UUID = 16, SHA-256 = 32).
    /// The parameter is the length in bytes.
    FixedBytes(usize),

    /// Timestamp with a specific precision.
    /// Models Avro timestamp-millis, Protobuf Timestamp, SQL TIMESTAMP, etc.
    Timestamp(TimePrecision),

    /// Calendar date without time component (SQL DATE, ISO 8601 date).
    Date,

    /// Duration / time interval (Protobuf Duration, SQL INTERVAL).
    Duration,

    /// Fixed-point decimal with precision and scale.
    /// `precision` is the total number of digits; `scale` is digits after the
    /// decimal point. Models SQL DECIMAL(p,s), Avro decimal logical type.
    Decimal {
        /// Total number of significant digits.
        precision: u32,
        /// Number of digits to the right of the decimal point.
        scale: u32,
    },

    /// Enumeration with named variants that carry no associated data.
    /// For enums with associated data, use [`crate::Shape::Sum`] instead.
    Enum(Vec<std::string::String>),
}

/// Precision of a timestamp value.
///
/// Different formats store timestamps at different precisions. This matters for
/// information content: a millisecond timestamp carries fewer bits than a
/// nanosecond timestamp, and converting from nano to milli is lossy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TimePrecision {
    /// Seconds since epoch (Unix time).
    Seconds,
    /// Milliseconds since epoch (JavaScript Date, Avro timestamp-millis).
    Milliseconds,
    /// Microseconds since epoch (Avro timestamp-micros, PostgreSQL).
    Microseconds,
    /// Nanoseconds since epoch (Protobuf Timestamp, InfluxDB).
    Nanoseconds,
}

impl AtomKind {
    /// Returns the fixed bit width of this atom, or `None` if the atom is
    /// variable-length (String, Bytes).
    ///
    /// This is the foundation of information content calculation. Every fixed-size
    /// atom has a known, exact number of bits.
    pub fn bit_width(&self) -> Option<u64> {
        match self {
            AtomKind::Bool => Some(1),
            AtomKind::U8 | AtomKind::I8 => Some(8),
            AtomKind::U16 | AtomKind::I16 => Some(16),
            AtomKind::U32 | AtomKind::I32 | AtomKind::F32 => Some(32),
            AtomKind::U64 | AtomKind::I64 | AtomKind::F64 => Some(64),
            AtomKind::U128 | AtomKind::I128 => Some(128),
            AtomKind::FixedBytes(n) => Some(*n as u64 * 8),
            AtomKind::Timestamp(prec) => match prec {
                // Seconds fit in 32 bits until 2106, but we use 64 for generality
                TimePrecision::Seconds => Some(64),
                TimePrecision::Milliseconds => Some(64),
                TimePrecision::Microseconds => Some(64),
                TimePrecision::Nanoseconds => Some(64),
            },
            AtomKind::Date => Some(32),
            AtomKind::Duration => Some(64),
            AtomKind::Decimal { precision, .. } => {
                // Each decimal digit needs ~3.32 bits (log2(10))
                // Plus 1 bit for sign
                let data_bits = (*precision as f64 * std::f64::consts::LOG2_10).ceil() as u64 + 1;
                // Round up to byte boundary for practical storage
                Some(data_bits.div_ceil(8) * 8)
            },
            AtomKind::Enum(variants) => {
                if variants.is_empty() {
                    Some(0)
                } else {
                    // ceil(log2(n)) bits to distinguish n variants
                    let bits = (variants.len() as f64).log2().ceil() as u64;
                    Some(bits.max(1))
                }
            },
            AtomKind::String | AtomKind::Bytes => None,
        }
    }

    /// Returns the number of distinct values this atom can represent, or `None`
    /// if unbounded.
    pub fn cardinality(&self) -> Option<u128> {
        match self {
            AtomKind::Bool => Some(2),
            AtomKind::U8 | AtomKind::I8 => Some(256),
            AtomKind::U16 | AtomKind::I16 => Some(65_536),
            AtomKind::U32 | AtomKind::I32 => Some(4_294_967_296),
            AtomKind::F32 => Some(4_294_967_296), // 2^32 bit patterns
            AtomKind::U64 | AtomKind::I64 => Some(18_446_744_073_709_551_616),
            AtomKind::F64 => Some(18_446_744_073_709_551_616),
            AtomKind::U128 | AtomKind::I128 => None, // 2^128 overflows u128
            AtomKind::FixedBytes(n) => {
                if *n <= 15 {
                    // 2^(n*8) fits in u128 for n <= 15
                    Some(1u128 << (n * 8))
                } else {
                    None
                }
            },
            AtomKind::Timestamp(_) | AtomKind::Duration => {
                Some(18_446_744_073_709_551_616) // 2^64
            },
            AtomKind::Date => Some(4_294_967_296), // 2^32
            AtomKind::Decimal { precision, .. } => {
                // 2 * 10^precision possible values (positive + negative + zero)
                let base: u128 = 10;
                base.checked_pow(*precision)
                    .and_then(|v| v.checked_mul(2))
                    .map(|v| v + 1)
            },
            AtomKind::Enum(variants) => Some(variants.len() as u128),
            AtomKind::String | AtomKind::Bytes => None,
        }
    }

    /// Returns true if this atom can be losslessly widened to `target`.
    ///
    /// Widening preserves all information — it's a Concorde-class morphism step.
    /// For example, i32 widens to i64, f32 widens to f64, u8 widens to u16.
    pub fn can_widen_to(&self, target: &AtomKind) -> bool {
        use AtomKind::*;
        matches!(
            (self, target),
            // Unsigned widening
            (U8, U16) | (U8, U32) | (U8, U64) | (U8, U128)
            | (U16, U32) | (U16, U64) | (U16, U128)
            | (U32, U64) | (U32, U128)
            | (U64, U128)
            // Signed widening
            | (I8, I16) | (I8, I32) | (I8, I64) | (I8, I128)
            | (I16, I32) | (I16, I64) | (I16, I128)
            | (I32, I64) | (I32, I128)
            | (I64, I128)
            // Float widening
            | (F32, F64)
            // Unsigned to larger signed (u8 fits in i16, etc.)
            | (U8, I16) | (U8, I32) | (U8, I64) | (U8, I128)
            | (U16, I32) | (U16, I64) | (U16, I128)
            | (U32, I64) | (U32, I128)
            | (U64, I128)
            // Timestamp precision widening (seconds -> millis -> micros -> nanos)
            | (Timestamp(TimePrecision::Seconds), Timestamp(TimePrecision::Milliseconds))
            | (Timestamp(TimePrecision::Seconds), Timestamp(TimePrecision::Microseconds))
            | (Timestamp(TimePrecision::Seconds), Timestamp(TimePrecision::Nanoseconds))
            | (Timestamp(TimePrecision::Milliseconds), Timestamp(TimePrecision::Microseconds))
            | (Timestamp(TimePrecision::Milliseconds), Timestamp(TimePrecision::Nanoseconds))
            | (Timestamp(TimePrecision::Microseconds), Timestamp(TimePrecision::Nanoseconds))
        )
    }
}

impl fmt::Display for AtomKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AtomKind::Bool => write!(f, "bool"),
            AtomKind::U8 => write!(f, "u8"),
            AtomKind::U16 => write!(f, "u16"),
            AtomKind::U32 => write!(f, "u32"),
            AtomKind::U64 => write!(f, "u64"),
            AtomKind::U128 => write!(f, "u128"),
            AtomKind::I8 => write!(f, "i8"),
            AtomKind::I16 => write!(f, "i16"),
            AtomKind::I32 => write!(f, "i32"),
            AtomKind::I64 => write!(f, "i64"),
            AtomKind::I128 => write!(f, "i128"),
            AtomKind::F32 => write!(f, "f32"),
            AtomKind::F64 => write!(f, "f64"),
            AtomKind::String => write!(f, "string"),
            AtomKind::Bytes => write!(f, "bytes"),
            AtomKind::FixedBytes(n) => write!(f, "bytes[{}]", n),
            AtomKind::Timestamp(p) => write!(f, "timestamp<{}>", p),
            AtomKind::Date => write!(f, "date"),
            AtomKind::Duration => write!(f, "duration"),
            AtomKind::Decimal { precision, scale } => {
                write!(f, "decimal({}, {})", precision, scale)
            },
            AtomKind::Enum(variants) => {
                write!(f, "enum{{{}}}", variants.join(", "))
            },
        }
    }
}

impl fmt::Display for TimePrecision {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TimePrecision::Seconds => write!(f, "s"),
            TimePrecision::Milliseconds => write!(f, "ms"),
            TimePrecision::Microseconds => write!(f, "us"),
            TimePrecision::Nanoseconds => write!(f, "ns"),
        }
    }
}
