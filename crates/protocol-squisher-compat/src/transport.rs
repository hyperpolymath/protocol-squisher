// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Transport classification for schema conversions
//!
//! Defines the "class" of conversion based on fidelity and overhead.

use serde::{Deserialize, Serialize};

/// Transport class representing conversion quality
///
/// Named after travel classes to intuitively convey the trade-offs:
/// - Concorde: Premium, zero compromises
/// - BusinessClass: Minor overhead, full fidelity
/// - Economy: Moderate overhead, documented losses
/// - Wheelbarrow: It works, but barely
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum TransportClass {
    /// Zero-copy compatible, full fidelity
    ///
    /// The source and target types are structurally identical or trivially
    /// convertible (e.g., same memory layout, no transformation needed).
    Concorde,

    /// Minor overhead, full fidelity
    ///
    /// Conversion preserves all information but requires some processing
    /// (e.g., field renaming, enum variant mapping, format conversion).
    BusinessClass,

    /// Moderate overhead, documented losses
    ///
    /// Conversion loses some information but the losses are well-defined
    /// and predictable (e.g., precision loss, dropped optional fields).
    Economy,

    /// High overhead, significant losses, but works
    ///
    /// Conversion is possible but with significant compromises
    /// (e.g., type coercion, data truncation, semantic changes).
    Wheelbarrow,

    /// Conversion is not possible
    ///
    /// The types are fundamentally incompatible and no reasonable
    /// conversion exists.
    Incompatible,
}

impl TransportClass {
    /// Returns true if conversion is possible (any class except Incompatible)
    pub fn is_convertible(&self) -> bool {
        *self != TransportClass::Incompatible
    }

    /// Returns true if conversion preserves all information
    pub fn is_lossless(&self) -> bool {
        matches!(self, TransportClass::Concorde | TransportClass::BusinessClass)
    }

    /// Returns a human-readable description
    pub fn description(&self) -> &'static str {
        match self {
            TransportClass::Concorde => "Zero-copy, full fidelity",
            TransportClass::BusinessClass => "Minor overhead, full fidelity",
            TransportClass::Economy => "Moderate overhead, documented losses",
            TransportClass::Wheelbarrow => "High overhead, significant losses",
            TransportClass::Incompatible => "Not convertible",
        }
    }

    /// Combine two transport classes (takes the worse one)
    pub fn combine(self, other: TransportClass) -> TransportClass {
        std::cmp::max(self, other)
    }
}

impl Default for TransportClass {
    fn default() -> Self {
        TransportClass::Incompatible
    }
}

impl std::fmt::Display for TransportClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TransportClass::Concorde => write!(f, "Concorde"),
            TransportClass::BusinessClass => write!(f, "Business Class"),
            TransportClass::Economy => write!(f, "Economy"),
            TransportClass::Wheelbarrow => write!(f, "Wheelbarrow"),
            TransportClass::Incompatible => write!(f, "Incompatible"),
        }
    }
}

/// A loss that occurs during conversion
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ConversionLoss {
    /// What was lost
    pub kind: LossKind,
    /// Path to the affected field/type
    pub path: String,
    /// Human-readable description
    pub description: String,
    /// Severity of the loss
    pub severity: LossSeverity,
}

/// Types of losses that can occur
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum LossKind {
    /// Numeric precision loss (e.g., f64 -> f32)
    PrecisionLoss,
    /// Integer range loss (e.g., i64 -> i32)
    RangeLoss,
    /// String encoding loss
    EncodingLoss,
    /// Field dropped (not representable in target)
    FieldDropped,
    /// Constraint cannot be represented
    ConstraintDropped,
    /// Type coerced to different type
    TypeCoercion,
    /// Default value lost
    DefaultLost,
    /// Documentation/metadata lost
    MetadataLost,
    /// Enum variant dropped
    VariantDropped,
    /// Nullability changed
    NullabilityChanged,
    /// Collection type changed (e.g., Set -> List)
    CollectionTypeChanged,
    /// Ordering information lost
    OrderingLost,
    /// Validation semantics changed
    ValidationChanged,
}

impl LossKind {
    /// Returns a human-readable name
    pub fn name(&self) -> &'static str {
        match self {
            LossKind::PrecisionLoss => "Precision Loss",
            LossKind::RangeLoss => "Range Loss",
            LossKind::EncodingLoss => "Encoding Loss",
            LossKind::FieldDropped => "Field Dropped",
            LossKind::ConstraintDropped => "Constraint Dropped",
            LossKind::TypeCoercion => "Type Coercion",
            LossKind::DefaultLost => "Default Lost",
            LossKind::MetadataLost => "Metadata Lost",
            LossKind::VariantDropped => "Variant Dropped",
            LossKind::NullabilityChanged => "Nullability Changed",
            LossKind::CollectionTypeChanged => "Collection Type Changed",
            LossKind::OrderingLost => "Ordering Lost",
            LossKind::ValidationChanged => "Validation Changed",
        }
    }
}

/// Severity of a conversion loss
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum LossSeverity {
    /// Informational only, no real impact
    Info,
    /// Minor loss, unlikely to cause issues
    Minor,
    /// Moderate loss, may cause issues
    Moderate,
    /// Major loss, likely to cause issues
    Major,
    /// Critical loss, will cause issues
    Critical,
}

impl LossSeverity {
    /// Convert severity to transport class impact
    pub fn to_transport_class(&self) -> TransportClass {
        match self {
            LossSeverity::Info => TransportClass::BusinessClass,
            LossSeverity::Minor => TransportClass::Economy,
            LossSeverity::Moderate => TransportClass::Economy,
            LossSeverity::Major => TransportClass::Wheelbarrow,
            LossSeverity::Critical => TransportClass::Incompatible,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_transport_class_ordering() {
        assert!(TransportClass::Concorde < TransportClass::BusinessClass);
        assert!(TransportClass::BusinessClass < TransportClass::Economy);
        assert!(TransportClass::Economy < TransportClass::Wheelbarrow);
        assert!(TransportClass::Wheelbarrow < TransportClass::Incompatible);
    }

    #[test]
    fn test_transport_class_combine() {
        assert_eq!(
            TransportClass::Concorde.combine(TransportClass::Economy),
            TransportClass::Economy
        );
        assert_eq!(
            TransportClass::Wheelbarrow.combine(TransportClass::BusinessClass),
            TransportClass::Wheelbarrow
        );
    }

    #[test]
    fn test_is_lossless() {
        assert!(TransportClass::Concorde.is_lossless());
        assert!(TransportClass::BusinessClass.is_lossless());
        assert!(!TransportClass::Economy.is_lossless());
        assert!(!TransportClass::Wheelbarrow.is_lossless());
    }

    #[test]
    fn test_is_convertible() {
        assert!(TransportClass::Concorde.is_convertible());
        assert!(TransportClass::Wheelbarrow.is_convertible());
        assert!(!TransportClass::Incompatible.is_convertible());
    }
}
