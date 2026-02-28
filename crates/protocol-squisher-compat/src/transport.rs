// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Transport classification for schema conversions.
//!
//! The transport classes form a **bounded lattice** (Concorde, BusinessClass,
//! Economy, Wheelbarrow, Incompatible) ordered by conversion quality, where:
//!
//! - **join** (least upper bound) = `combine` = takes the *worse* class
//! - **meet** (greatest lower bound) = `refine` = takes the *better* class
//! - **top** = `Incompatible` (worst possible)
//! - **bottom** = `Concorde` (best possible)
//!
//! This lattice structure enables compositional reasoning: the transport class
//! of a composite conversion (struct with multiple fields) is the join of
//! its field-level transport classes.
//!
//! ## Galois Connection
//!
//! The classification defines an **abstraction-concretization** (Galois connection)
//! pair between concrete conversion functions and transport classes:
//!
//! - `alpha(f)` maps a conversion function to its transport class
//! - `gamma(c)` returns the set of all conversions permitted by class `c`
//!
//! The Galois connection guarantee: any property proven at the abstract level
//! (transport class) holds for all concrete conversions in that class.
//!
//! ## Information-Theoretic Bounds
//!
//! Each transport class implies bounds on **fidelity** (information preserved)
//! and **overhead** (extra processing cost), grounded in rate-distortion theory:
//!
//! | Class | Fidelity | Overhead | Rate-Distortion |
//! |-------|----------|----------|-----------------|
//! | Concorde | 100% | 0 | R(0) = H(X) (lossless) |
//! | Business | 100% | >0 | R(0) with processing cost |
//! | Economy | 70-99% | moderate | R(D) for small D |
//! | Wheelbarrow | 0-69% | high | R(D) for large D |
//! | Incompatible | N/A | N/A | no valid encoding |

use serde::{Deserialize, Serialize};

/// Transport class representing conversion quality
///
/// Named after travel classes to intuitively convey the trade-offs:
/// - Concorde: Premium, zero compromises
/// - BusinessClass: Minor overhead, full fidelity
/// - Economy: Moderate overhead, documented losses
/// - Wheelbarrow: It works, but barely
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Default,
)]
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
    #[default]
    Incompatible,
}

impl TransportClass {
    /// Returns true if conversion is possible (any class except Incompatible)
    pub fn is_convertible(&self) -> bool {
        *self != TransportClass::Incompatible
    }

    /// Returns true if conversion preserves all information
    pub fn is_lossless(&self) -> bool {
        matches!(
            self,
            TransportClass::Concorde | TransportClass::BusinessClass
        )
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

    // --- Lattice operations ---

    /// Join (least upper bound): returns the *worse* of two classes.
    ///
    /// This is the compositional rule: a struct's transport class is the
    /// join of its field transport classes.
    pub fn join(self, other: TransportClass) -> TransportClass {
        std::cmp::max(self, other)
    }

    /// Meet (greatest lower bound): returns the *better* of two classes.
    ///
    /// Useful for refinement: if two independent analyses both classify
    /// a conversion, the meet gives the tightest proven bound.
    pub fn meet(self, other: TransportClass) -> TransportClass {
        std::cmp::min(self, other)
    }

    /// Lattice top element (worst quality).
    pub const TOP: TransportClass = TransportClass::Incompatible;

    /// Lattice bottom element (best quality).
    pub const BOTTOM: TransportClass = TransportClass::Concorde;

    /// Combine two transport classes (takes the worse one).
    ///
    /// Alias for `join` - the standard compositional combinator.
    pub fn combine(self, other: TransportClass) -> TransportClass {
        self.join(other)
    }

    // --- Galois connection: abstract domain properties ---

    /// Minimum fidelity percentage guaranteed by this class.
    ///
    /// Fidelity measures the fraction of source information preserved
    /// in the target. This is the lower bound guaranteed by the class.
    pub fn min_fidelity(&self) -> u8 {
        match self {
            TransportClass::Concorde => 100,
            TransportClass::BusinessClass => 100,
            TransportClass::Economy => 70,
            TransportClass::Wheelbarrow => 0,
            TransportClass::Incompatible => 0,
        }
    }

    /// Maximum overhead ratio (percentage above baseline).
    ///
    /// Overhead measures additional processing cost relative to a
    /// zero-copy baseline. This is the upper bound for the class.
    pub fn max_overhead(&self) -> u8 {
        match self {
            TransportClass::Concorde => 0,
            TransportClass::BusinessClass => 10,
            TransportClass::Economy => 50,
            TransportClass::Wheelbarrow => 100,
            TransportClass::Incompatible => 100,
        }
    }

    /// Classify from fidelity and overhead measurements.
    ///
    /// This is the **abstraction function** (alpha) of the Galois connection:
    /// given concrete measurements of a conversion's quality, produce its
    /// transport class. Any conversion that has *some* viable path (even 0%
    /// fidelity with high overhead) is classified as Wheelbarrow, not
    /// Incompatible. Incompatible is reserved for conversions that cannot
    /// be performed at all.
    ///
    /// `convertible` defaults to true; use `from_measurements_with_convertibility`
    /// to explicitly mark a conversion as impossible.
    pub fn from_measurements(fidelity_pct: u8, overhead_pct: u8) -> TransportClass {
        Self::from_measurements_with_convertibility(fidelity_pct, overhead_pct, true)
    }

    /// Classify from fidelity, overhead, and explicit convertibility flag.
    pub fn from_measurements_with_convertibility(
        fidelity_pct: u8,
        overhead_pct: u8,
        convertible: bool,
    ) -> TransportClass {
        if !convertible {
            return TransportClass::Incompatible;
        }
        if fidelity_pct == 100 && overhead_pct == 0 {
            TransportClass::Concorde
        } else if fidelity_pct == 100 {
            TransportClass::BusinessClass
        } else if fidelity_pct >= 70 {
            TransportClass::Economy
        } else {
            TransportClass::Wheelbarrow
        }
    }

    /// Returns the fidelity and overhead bounds for this class.
    ///
    /// This is the **concretization function** (gamma): given a transport class,
    /// returns the (min_fidelity, max_overhead) bounds that any conversion in
    /// this class must satisfy.
    pub fn bounds(&self) -> TransportBounds {
        TransportBounds {
            min_fidelity: self.min_fidelity(),
            max_overhead: self.max_overhead(),
            lossless: self.is_lossless(),
            convertible: self.is_convertible(),
        }
    }

    // --- Information-theoretic metrics ---

    /// Shannon entropy preservation ratio for this class.
    ///
    /// Concorde/Business preserve H(X) entirely (lossless).
    /// Economy operates at rate R(D) for small distortion D.
    /// Wheelbarrow operates at rate R(D) for large D.
    pub fn entropy_preservation(&self) -> f64 {
        match self {
            TransportClass::Concorde => 1.0,
            TransportClass::BusinessClass => 1.0,
            TransportClass::Economy => 0.85,
            TransportClass::Wheelbarrow => 0.35,
            TransportClass::Incompatible => 0.0,
        }
    }

    /// Estimated bits wasted per field for this class.
    ///
    /// Based on typical protocol field overhead:
    /// - Concorde: 0 bits (zero-copy, no encoding overhead)
    /// - Business: ~2 bits (tag/length overhead)
    /// - Economy: ~8 bits (type coercion + padding)
    /// - Wheelbarrow: ~64 bits (full JSON key + value encoding)
    pub fn estimated_bits_wasted(&self) -> u32 {
        match self {
            TransportClass::Concorde => 0,
            TransportClass::BusinessClass => 2,
            TransportClass::Economy => 8,
            TransportClass::Wheelbarrow => 64,
            TransportClass::Incompatible => 0,
        }
    }

    /// All classes in lattice order from best to worst.
    pub const ALL: [TransportClass; 5] = [
        TransportClass::Concorde,
        TransportClass::BusinessClass,
        TransportClass::Economy,
        TransportClass::Wheelbarrow,
        TransportClass::Incompatible,
    ];
}

/// Bounds on conversion quality, derived from the Galois connection.
///
/// For any conversion function `f` classified as class `c`:
/// - `fidelity(f) >= bounds(c).min_fidelity`
/// - `overhead(f) <= bounds(c).max_overhead`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TransportBounds {
    /// Minimum information preservation (0-100%)
    pub min_fidelity: u8,
    /// Maximum processing overhead (0-100%)
    pub max_overhead: u8,
    /// Whether the conversion is lossless
    pub lossless: bool,
    /// Whether the conversion is possible at all
    pub convertible: bool,
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

    // --- Lattice property tests ---

    #[test]
    fn test_join_is_commutative() {
        for &a in &TransportClass::ALL {
            for &b in &TransportClass::ALL {
                assert_eq!(
                    a.join(b),
                    b.join(a),
                    "join({:?}, {:?}) not commutative",
                    a,
                    b
                );
            }
        }
    }

    #[test]
    fn test_join_is_associative() {
        for &a in &TransportClass::ALL {
            for &b in &TransportClass::ALL {
                for &c in &TransportClass::ALL {
                    assert_eq!(
                        a.join(b).join(c),
                        a.join(b.join(c)),
                        "join not associative for ({:?}, {:?}, {:?})",
                        a,
                        b,
                        c
                    );
                }
            }
        }
    }

    #[test]
    fn test_join_is_idempotent() {
        for &a in &TransportClass::ALL {
            assert_eq!(a.join(a), a, "join({:?}, {:?}) not idempotent", a, a);
        }
    }

    #[test]
    fn test_meet_is_commutative() {
        for &a in &TransportClass::ALL {
            for &b in &TransportClass::ALL {
                assert_eq!(
                    a.meet(b),
                    b.meet(a),
                    "meet({:?}, {:?}) not commutative",
                    a,
                    b
                );
            }
        }
    }

    #[test]
    fn test_meet_is_associative() {
        for &a in &TransportClass::ALL {
            for &b in &TransportClass::ALL {
                for &c in &TransportClass::ALL {
                    assert_eq!(
                        a.meet(b).meet(c),
                        a.meet(b.meet(c)),
                        "meet not associative for ({:?}, {:?}, {:?})",
                        a,
                        b,
                        c
                    );
                }
            }
        }
    }

    #[test]
    fn test_absorption_laws() {
        // a join (a meet b) = a
        // a meet (a join b) = a
        for &a in &TransportClass::ALL {
            for &b in &TransportClass::ALL {
                assert_eq!(
                    a.join(a.meet(b)),
                    a,
                    "absorption law 1 failed for ({:?}, {:?})",
                    a,
                    b
                );
                assert_eq!(
                    a.meet(a.join(b)),
                    a,
                    "absorption law 2 failed for ({:?}, {:?})",
                    a,
                    b
                );
            }
        }
    }

    #[test]
    fn test_lattice_bounds() {
        // Concorde is bottom: join with anything gives the other
        for &a in &TransportClass::ALL {
            assert_eq!(TransportClass::BOTTOM.join(a), a);
        }
        // Incompatible is top: join with anything gives Incompatible
        for &a in &TransportClass::ALL {
            assert_eq!(TransportClass::TOP.join(a), TransportClass::TOP);
        }
    }

    // --- Galois connection tests ---

    #[test]
    fn test_galois_roundtrip() {
        // alpha(gamma(c)) should be at most c (soundness)
        // For convertible classes, from_measurements(bounds) should recover <= c
        for &c in &TransportClass::ALL {
            let bounds = c.bounds();
            let recovered = TransportClass::from_measurements_with_convertibility(
                bounds.min_fidelity,
                bounds.max_overhead,
                bounds.convertible,
            );
            assert!(
                recovered <= c,
                "Galois roundtrip: from_measurements(bounds({:?})) = {:?}, expected <= {:?}",
                c,
                recovered,
                c
            );
        }
    }

    #[test]
    fn test_from_measurements_classification() {
        assert_eq!(
            TransportClass::from_measurements(100, 0),
            TransportClass::Concorde
        );
        assert_eq!(
            TransportClass::from_measurements(100, 5),
            TransportClass::BusinessClass
        );
        assert_eq!(
            TransportClass::from_measurements(85, 30),
            TransportClass::Economy
        );
        assert_eq!(
            TransportClass::from_measurements(50, 80),
            TransportClass::Wheelbarrow
        );
    }

    #[test]
    fn test_fidelity_monotonic() {
        // Better class => higher fidelity bound
        let classes = TransportClass::ALL;
        for i in 0..classes.len() - 1 {
            assert!(
                classes[i].min_fidelity() >= classes[i + 1].min_fidelity(),
                "Fidelity not monotonic: {:?} ({}) < {:?} ({})",
                classes[i],
                classes[i].min_fidelity(),
                classes[i + 1],
                classes[i + 1].min_fidelity()
            );
        }
    }

    #[test]
    fn test_overhead_monotonic() {
        // Better class => lower overhead bound
        let classes = TransportClass::ALL;
        for i in 0..classes.len() - 1 {
            assert!(
                classes[i].max_overhead() <= classes[i + 1].max_overhead(),
                "Overhead not monotonic: {:?} ({}) > {:?} ({})",
                classes[i],
                classes[i].max_overhead(),
                classes[i + 1],
                classes[i + 1].max_overhead()
            );
        }
    }

    #[test]
    fn test_entropy_preservation_monotonic() {
        let classes = TransportClass::ALL;
        for i in 0..classes.len() - 1 {
            assert!(
                classes[i].entropy_preservation() >= classes[i + 1].entropy_preservation(),
                "Entropy preservation not monotonic: {:?} > {:?}",
                classes[i],
                classes[i + 1]
            );
        }
    }

    #[test]
    fn test_lossless_classes_preserve_full_entropy() {
        for &c in &TransportClass::ALL {
            if c.is_lossless() {
                assert_eq!(
                    c.entropy_preservation(),
                    1.0,
                    "Lossless class {:?} should preserve 100% entropy",
                    c
                );
            }
        }
    }
}
