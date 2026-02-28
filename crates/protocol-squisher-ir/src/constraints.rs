// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! IR Constraint System
//!
//! Constraints represent validation rules and invariants that must hold
//! for values of a given type. These are crucial for compatibility analysis
//! because they determine whether transformations preserve semantics.

use serde::{Deserialize, Serialize};

/// A constraint on a type or field
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Constraint {
    // ─────────────────────────────────────────────────────────────────────
    // Numeric constraints
    // ─────────────────────────────────────────────────────────────────────
    /// Minimum value (inclusive)
    Min(NumberValue),

    /// Maximum value (inclusive)
    Max(NumberValue),

    /// Value must be in range [min, max]
    Range { min: NumberValue, max: NumberValue },

    /// Value must be a multiple of this
    MultipleOf(NumberValue),

    /// Value must be positive (> 0)
    Positive,

    /// Value must be negative (< 0)
    Negative,

    /// Value must be non-negative (>= 0)
    NonNegative,

    // ─────────────────────────────────────────────────────────────────────
    // String constraints
    // ─────────────────────────────────────────────────────────────────────
    /// Minimum length (inclusive)
    MinLength(usize),

    /// Maximum length (inclusive)
    MaxLength(usize),

    /// Length must be exactly this
    ExactLength(usize),

    /// Must match this regex pattern
    Pattern(String),

    /// Must be a valid format (email, uri, uuid, etc.)
    Format(StringFormat),

    /// Must be non-empty (length > 0)
    NonEmpty,

    // ─────────────────────────────────────────────────────────────────────
    // Collection constraints
    // ─────────────────────────────────────────────────────────────────────
    /// Minimum number of items
    MinItems(usize),

    /// Maximum number of items
    MaxItems(usize),

    /// All items must be unique
    UniqueItems,

    /// Collection must contain this value
    Contains(serde_json::Value),

    // ─────────────────────────────────────────────────────────────────────
    // Enum/choice constraints
    // ─────────────────────────────────────────────────────────────────────
    /// Value must be one of these
    OneOf(Vec<serde_json::Value>),

    /// Value must NOT be one of these
    NotOneOf(Vec<serde_json::Value>),

    // ─────────────────────────────────────────────────────────────────────
    // Relational constraints
    // ─────────────────────────────────────────────────────────────────────
    /// Value must equal another field
    EqualTo(String),

    /// Value must not equal another field
    NotEqualTo(String),

    /// Value must be less than another field
    LessThan(String),

    /// Value must be greater than another field
    GreaterThan(String),

    // ─────────────────────────────────────────────────────────────────────
    // Conditional constraints
    // ─────────────────────────────────────────────────────────────────────
    /// If condition field has value, this constraint applies
    ConditionalOn {
        field: String,
        value: serde_json::Value,
        then_constraint: Box<Constraint>,
    },

    // ─────────────────────────────────────────────────────────────────────
    // Composite constraints
    // ─────────────────────────────────────────────────────────────────────
    /// All of these constraints must hold
    AllOf(Vec<Constraint>),

    /// At least one of these constraints must hold
    AnyOf(Vec<Constraint>),

    /// Exactly one of these constraints must hold
    OneOfConstraints(Vec<Constraint>),

    /// This constraint must NOT hold
    Not(Box<Constraint>),

    // ─────────────────────────────────────────────────────────────────────
    // Custom constraints
    // ─────────────────────────────────────────────────────────────────────
    /// Custom constraint with name and parameters
    Custom {
        name: String,
        params: serde_json::Value,
    },
}

impl Constraint {
    /// Check if this constraint can be satisfied by a widened type
    ///
    /// For example, a MinLength(1) on a String can be preserved when
    /// converting to a format that supports string validation.
    pub fn is_preservable(&self) -> bool {
        match self {
            // Numeric constraints are generally preservable
            Constraint::Min(_)
            | Constraint::Max(_)
            | Constraint::Range { .. }
            | Constraint::Positive
            | Constraint::Negative
            | Constraint::NonNegative => true,

            // String constraints are format-dependent
            Constraint::MinLength(_)
            | Constraint::MaxLength(_)
            | Constraint::NonEmpty
            | Constraint::Format(_) => true,

            // Pattern constraints may not be portable
            Constraint::Pattern(_) => false,

            // Collection constraints are generally preservable
            Constraint::MinItems(_) | Constraint::MaxItems(_) | Constraint::UniqueItems => true,

            // Enum constraints are preservable if values can be converted
            Constraint::OneOf(_) | Constraint::NotOneOf(_) => true,

            // Custom constraints are not preservable by default
            Constraint::Custom { .. } => false,

            // Composite constraints depend on their children
            Constraint::AllOf(cs) | Constraint::AnyOf(cs) | Constraint::OneOfConstraints(cs) => {
                cs.iter().all(|c| c.is_preservable())
            },
            Constraint::Not(c) => c.is_preservable(),

            // Other constraints
            _ => false,
        }
    }
}

/// Numeric value that can represent integers or floats
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum NumberValue {
    Integer(i64),
    Float(f64),
}

impl NumberValue {
    pub fn as_f64(&self) -> f64 {
        match self {
            NumberValue::Integer(i) => *i as f64,
            NumberValue::Float(f) => *f,
        }
    }
}

/// Well-known string formats
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum StringFormat {
    /// RFC 5321 email address
    Email,

    /// RFC 3986 URI
    Uri,

    /// RFC 3986 URI reference
    UriReference,

    /// RFC 4122 UUID
    Uuid,

    /// ISO 8601 date-time
    DateTime,

    /// ISO 8601 date
    Date,

    /// ISO 8601 time
    Time,

    /// ISO 8601 duration
    Duration,

    /// Hostname (RFC 1123)
    Hostname,

    /// IPv4 address
    Ipv4,

    /// IPv6 address
    Ipv6,

    /// JSON Pointer (RFC 6901)
    JsonPointer,

    /// Relative JSON Pointer
    RelativeJsonPointer,

    /// Regular expression (ECMA 262)
    Regex,

    /// Base64-encoded data
    Base64,

    /// Semantic version (semver)
    Semver,

    /// Credit card number (Luhn check)
    CreditCard,

    /// Phone number (E.164)
    Phone,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constraint_serialization() {
        let c = Constraint::Range {
            min: NumberValue::Integer(0),
            max: NumberValue::Integer(100),
        };
        let json = serde_json::to_string(&c).unwrap();
        let parsed: Constraint = serde_json::from_str(&json).unwrap();
        assert_eq!(c, parsed);
    }

    #[test]
    fn test_preservability() {
        assert!(Constraint::MinLength(1).is_preservable());
        assert!(Constraint::NonNegative.is_preservable());
        assert!(!Constraint::Pattern(r"\d+".to_string()).is_preservable());
    }

    #[test]
    fn test_composite_constraint() {
        let c = Constraint::AllOf(vec![
            Constraint::Min(NumberValue::Integer(0)),
            Constraint::Max(NumberValue::Integer(100)),
        ]);
        assert!(c.is_preservable());
    }
}
