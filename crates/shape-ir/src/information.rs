// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Information Content and Transport Classes
//!
//! Every data shape has an information-theoretic capacity — the number of bits
//! needed to represent one instance. When converting between shapes, information
//! is either preserved, padded, lost, or destroyed.
//!
//! The transport class metaphor (borrowed from Protocol Squisher's existing
//! analysis) becomes formally grounded here:
//!
//! | Class | Meaning | Information | Reversible? |
//! |-------|---------|-------------|-------------|
//! | Concorde | Isomorphism | Preserved exactly | Yes, perfectly |
//! | Business | Embedding | Preserved + padded | Yes, with projection |
//! | Economy | Projection | Some lost | Partially, with defaults |
//! | Wheelbarrow | Best-effort | Below Shannon limit | No guarantees |
//!
//! The key insight: transport class isn't a subjective judgment — it's a
//! computable property of the morphism between two shapes. This module provides
//! the computation.

use crate::shape::Shape;
use serde::{Deserialize, Serialize};
use std::fmt;

/// Information-theoretic properties of a shape.
///
/// Computed by [`information_content`], this struct captures the fundamental
/// capacity of a data shape — how many bits it needs, whether it's bounded,
/// and how many distinct values it can represent.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InformationContent {
    /// Minimum bits needed to represent one instance of this shape.
    /// For fixed-size shapes, this equals `max_bits`.
    pub min_bits: u64,

    /// Maximum bits needed. `None` means the shape is unbounded
    /// (e.g., strings, sequences, maps).
    pub max_bits: Option<u64>,

    /// Whether every instance of this shape occupies exactly the same
    /// number of bits. True for atoms like i32, false for strings.
    pub is_fixed_size: bool,

    /// Number of distinct values this shape can represent.
    /// `None` means infinite or too large to represent in u128.
    pub cardinality: Option<u128>,
}

impl InformationContent {
    /// An empty shape carries zero information.
    pub fn zero() -> Self {
        Self {
            min_bits: 0,
            max_bits: Some(0),
            is_fixed_size: true,
            cardinality: Some(1), // Unit has exactly one inhabitant
        }
    }

    /// An unbounded shape (strings, sequences) has no maximum.
    pub fn unbounded(min_bits: u64) -> Self {
        Self {
            min_bits,
            max_bits: None,
            is_fixed_size: false,
            cardinality: None,
        }
    }

    /// A fixed-size shape with known bit width.
    pub fn fixed(bits: u64, cardinality: Option<u128>) -> Self {
        Self {
            min_bits: bits,
            max_bits: Some(bits),
            is_fixed_size: true,
            cardinality,
        }
    }
}

impl fmt::Display for InformationContent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.max_bits {
            Some(max) if max == self.min_bits => write!(f, "{} bits (fixed)", self.min_bits),
            Some(max) => write!(f, "{}-{} bits", self.min_bits, max),
            None => write!(f, "{}+ bits (unbounded)", self.min_bits),
        }
    }
}

/// Classification of a morphism's information preservation.
///
/// Transport classes are ordered: Concorde > Business > Economy > Wheelbarrow.
/// When composing morphisms, the result's class is the minimum of the inputs.
/// This reflects the fundamental principle that information loss is irreversible
/// — once you drop to Economy, no subsequent Concorde step can recover what was lost.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum TransportClass {
    /// Zero information loss — the morphism is an isomorphism.
    /// The source and target shapes carry exactly the same information.
    /// Roundtrip A->B->A is the identity.
    ///
    /// Examples: i32 <-> i32, renaming a field, reordering struct fields.
    Concorde,

    /// Lossless but padded — the target carries all source information plus extra.
    /// The morphism is an embedding (injective but not surjective).
    ///
    /// Examples: i32 -> i64 (widening), adding an optional field with default.
    Business,

    /// Lossy but recoverable with known defaults — the morphism is a projection.
    /// Some information is lost, but a reasonable inverse exists if you know
    /// what defaults to fill in.
    ///
    /// Examples: i64 -> i32 (narrowing with range check), dropping an optional field.
    Economy,

    /// Lossy, below Shannon limit — best-effort fallback.
    /// The morphism destroys information with no reasonable recovery strategy.
    ///
    /// Examples: f64 -> bool, complex struct -> flat string, schema mismatch.
    Wheelbarrow,
}

impl TransportClass {
    /// Compose two transport classes. The result is the minimum (worst) of the two.
    ///
    /// This models information loss propagation: a Concorde step followed by an
    /// Economy step yields Economy overall. You can't recover lost information
    /// by adding a lossless step.
    ///
    /// ```
    /// use shape_ir::TransportClass;
    ///
    /// assert_eq!(TransportClass::compose(TransportClass::Concorde, TransportClass::Concorde), TransportClass::Concorde);
    /// assert_eq!(TransportClass::compose(TransportClass::Business, TransportClass::Economy), TransportClass::Economy);
    /// assert_eq!(TransportClass::compose(TransportClass::Concorde, TransportClass::Wheelbarrow), TransportClass::Wheelbarrow);
    /// ```
    pub fn compose(a: TransportClass, b: TransportClass) -> TransportClass {
        // Ord is derived with Concorde < Business < Economy < Wheelbarrow,
        // but we want "worst" which is the *largest* value.
        // Since derive gives Concorde=0 < Business=1 < Economy=2 < Wheelbarrow=3,
        // max gives us the worst class.
        a.max(b)
    }

    /// Returns true if this transport class guarantees no information loss.
    pub fn is_lossless(self) -> bool {
        matches!(self, TransportClass::Concorde | TransportClass::Business)
    }

    /// Returns true if a roundtrip through this class produces the identity.
    pub fn is_isomorphism(self) -> bool {
        self == TransportClass::Concorde
    }
}

impl fmt::Display for TransportClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TransportClass::Concorde => write!(f, "Concorde (isomorphism)"),
            TransportClass::Business => write!(f, "Business (lossless, padded)"),
            TransportClass::Economy => write!(f, "Economy (lossy, recoverable)"),
            TransportClass::Wheelbarrow => write!(f, "Wheelbarrow (lossy, best-effort)"),
        }
    }
}

/// The information cost of a morphism — how much information is gained, lost,
/// or preserved during the transformation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InformationCost {
    /// Bits of information added (padding, default values, new fields).
    pub bits_added: u64,

    /// Bits of information lost (projection, narrowing, dropped fields).
    pub bits_lost: u64,

    /// Number of fields/paths that map identically (no transformation needed).
    pub identity_paths: usize,

    /// Number of transformation steps (non-identity mappings).
    pub transform_steps: usize,
}

impl InformationCost {
    /// Zero cost — a perfect identity morphism.
    pub fn zero() -> Self {
        Self {
            bits_added: 0,
            bits_lost: 0,
            identity_paths: 0,
            transform_steps: 0,
        }
    }

    /// Sum two information costs (used when composing morphisms).
    pub fn sum(&self, other: &InformationCost) -> InformationCost {
        InformationCost {
            bits_added: self.bits_added.saturating_add(other.bits_added),
            bits_lost: self.bits_lost.saturating_add(other.bits_lost),
            identity_paths: self.identity_paths + other.identity_paths,
            transform_steps: self.transform_steps + other.transform_steps,
        }
    }
}

impl fmt::Display for InformationCost {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "+{} bits, -{} bits, {} identity, {} transforms",
            self.bits_added, self.bits_lost, self.identity_paths, self.transform_steps
        )
    }
}

/// Detailed classification of a morphism based on information-theoretic metrics.
///
/// This goes beyond the four transport classes to provide quantitative measures
/// that can guide adapter generation and inform users about the nature of the
/// conversion.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MorphismMetrics {
    /// Transport class (the coarse classification).
    pub transport_class: TransportClass,

    /// Ratio of identity paths to total paths (0.0 to 1.0).
    /// Higher means more of the shape maps directly.
    pub identity_ratio: f64,

    /// Ratio of bits lost to source bits (0.0 to 1.0).
    /// 0.0 means no loss; 1.0 means everything is lost.
    pub loss_ratio: f64,

    /// Ratio of bits added to target bits (0.0 to 1.0).
    /// 0.0 means no padding; 1.0 means everything is padding.
    pub padding_ratio: f64,

    /// Net information change: bits_added - bits_lost.
    /// Positive means the target is larger; negative means the target is smaller.
    pub net_bits: i64,

    /// Whether the morphism is a pure embedding (only adds, never removes).
    pub is_pure_embedding: bool,

    /// Whether the morphism is a pure projection (only removes, never adds).
    pub is_pure_projection: bool,

    /// Estimated reversibility: what fraction of source data can be recovered
    /// from a roundtrip through target and back (0.0 to 1.0).
    pub reversibility: f64,
}

impl fmt::Display for MorphismMetrics {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} | identity: {:.0}%, loss: {:.0}%, padding: {:.0}%, net: {:+} bits, reversibility: {:.0}%",
            self.transport_class,
            self.identity_ratio * 100.0,
            self.loss_ratio * 100.0,
            self.padding_ratio * 100.0,
            self.net_bits,
            self.reversibility * 100.0,
        )
    }
}

/// Compute detailed metrics for a morphism.
///
/// Uses the source and target information content along with the morphism's
/// cost to derive quantitative measures of the conversion's fidelity.
pub fn classify_morphism(morphism: &crate::morphism::Morphism) -> MorphismMetrics {
    let source_info = information_content(&morphism.source);
    let target_info = information_content(&morphism.target);
    let cost = &morphism.information_cost;

    let total_paths = cost.identity_paths + cost.transform_steps;
    let identity_ratio = if total_paths > 0 {
        cost.identity_paths as f64 / total_paths as f64
    } else {
        1.0 // No paths means trivial identity
    };

    let source_bits = source_info.max_bits.unwrap_or(source_info.min_bits);
    let target_bits = target_info.max_bits.unwrap_or(target_info.min_bits);

    let loss_ratio = if source_bits > 0 {
        cost.bits_lost as f64 / source_bits as f64
    } else {
        0.0
    };

    let padding_ratio = if target_bits > 0 {
        cost.bits_added as f64 / target_bits as f64
    } else {
        0.0
    };

    let net_bits = cost.bits_added as i64 - cost.bits_lost as i64;

    let is_pure_embedding = cost.bits_lost == 0 && cost.bits_added > 0;
    let is_pure_projection = cost.bits_added == 0 && cost.bits_lost > 0;

    // Reversibility: fraction of source information preserved
    let reversibility = if source_bits > 0 {
        let preserved = source_bits.saturating_sub(cost.bits_lost);
        (preserved as f64 / source_bits as f64).clamp(0.0, 1.0)
    } else {
        1.0 // Empty source is perfectly reversible
    };

    MorphismMetrics {
        transport_class: morphism.transport_class,
        identity_ratio,
        loss_ratio,
        padding_ratio,
        net_bits,
        is_pure_embedding,
        is_pure_projection,
        reversibility,
    }
}

/// Compute the information content of a shape.
///
/// This is the fundamental measurement: how many bits does this shape need?
/// The computation is structural — it walks the shape tree and combines
/// information content according to the constructors.
///
/// # Rules
///
/// - **Unit**: 0 bits, cardinality 1
/// - **Atom**: Determined by [`crate::atom::AtomKind::bit_width`] and [`crate::atom::AtomKind::cardinality`]
/// - **Product**: Sum of components (both fields are present)
/// - **Sum**: Max of components + tag bits (one alternative is present)
/// - **Sequence**: Unbounded (any number of elements)
/// - **Optional**: Inner + 1 bit (presence flag)
/// - **Map**: Unbounded (any number of entries)
/// - **Dependent**: Binder + max of possible body shapes
/// - **Recursive**: Unbounded (can unfold infinitely)
/// - **Ref**: 0 bits (placeholder, resolved by context)
/// - **Annotated**: Same as inner shape (annotations are metadata)
pub fn information_content(shape: &Shape) -> InformationContent {
    match shape {
        Shape::Unit => InformationContent::zero(),

        Shape::Atom(kind) => match kind.bit_width() {
            Some(bits) => InformationContent::fixed(bits, kind.cardinality()),
            None => InformationContent::unbounded(0),
        },

        Shape::Product { left, right, .. } => {
            let left_info = information_content(left);
            let right_info = information_content(right);

            InformationContent {
                min_bits: left_info.min_bits.saturating_add(right_info.min_bits),
                max_bits: match (left_info.max_bits, right_info.max_bits) {
                    (Some(a), Some(b)) => Some(a.saturating_add(b)),
                    _ => None,
                },
                is_fixed_size: left_info.is_fixed_size && right_info.is_fixed_size,
                cardinality: match (left_info.cardinality, right_info.cardinality) {
                    (Some(a), Some(b)) => a.checked_mul(b),
                    _ => None,
                },
            }
        },

        Shape::Sum { left, right, .. } => {
            let left_info = information_content(left);
            let right_info = information_content(right);

            // A sum needs tag bits plus the larger payload
            let tag_bits = 1u64; // At least 1 bit to distinguish left vs right

            InformationContent {
                min_bits: tag_bits + left_info.min_bits.min(right_info.min_bits),
                max_bits: match (left_info.max_bits, right_info.max_bits) {
                    (Some(a), Some(b)) => Some(tag_bits + a.max(b)),
                    _ => None,
                },
                is_fixed_size: left_info.is_fixed_size
                    && right_info.is_fixed_size
                    && left_info.max_bits == right_info.max_bits,
                cardinality: match (left_info.cardinality, right_info.cardinality) {
                    (Some(a), Some(b)) => a.checked_add(b),
                    _ => None,
                },
            }
        },

        Shape::Dependent { binder, body } => {
            let binder_info = information_content(binder);
            let body_info = information_content(body);

            InformationContent {
                min_bits: binder_info.min_bits.saturating_add(body_info.min_bits),
                max_bits: match (binder_info.max_bits, body_info.max_bits) {
                    (Some(a), Some(b)) => Some(a.saturating_add(b)),
                    _ => None,
                },
                is_fixed_size: false, // Body varies with binder value
                cardinality: None,    // Depends on runtime values
            }
        },

        Shape::Recursive { .. } => {
            // Recursive types can unfold infinitely — information is unbounded
            InformationContent::unbounded(0)
        },

        Shape::Ref(_) => {
            // References are placeholders — their information content depends
            // on what they resolve to. We return zero here; resolution happens
            // at a higher level.
            InformationContent::zero()
        },

        Shape::Sequence(inner) => {
            let inner_info = information_content(inner);
            // A sequence is unbounded (0..inf elements)
            InformationContent {
                min_bits: 0, // Empty sequence
                max_bits: None,
                is_fixed_size: false,
                cardinality: match inner_info.cardinality {
                    Some(0) => Some(1), // Sequence of void = only empty sequence
                    _ => None,          // Infinite possible sequences
                },
            }
        },

        Shape::Optional(inner) => {
            let inner_info = information_content(inner);
            // Optional adds 1 bit (present/absent) to the inner shape
            InformationContent {
                min_bits: 1, // At minimum: the presence bit (when absent)
                max_bits: inner_info.max_bits.map(|b| b + 1),
                is_fixed_size: false, // Present vs absent have different sizes
                cardinality: inner_info.cardinality.and_then(|c| c.checked_add(1)),
            }
        },

        Shape::Map { key, value } => {
            let _key_info = information_content(key);
            let _value_info = information_content(value);
            // Maps are unbounded (0..inf entries)
            InformationContent {
                min_bits: 0, // Empty map
                max_bits: None,
                is_fixed_size: false,
                cardinality: None,
            }
        },

        Shape::Annotated { shape, .. } => {
            // Annotations don't change information content
            information_content(shape)
        },
    }
}
