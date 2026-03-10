// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Morphisms — Transformations Between Shapes
//!
//! A morphism is a transformation from one shape to another. It is the
//! fundamental operation in the algebra of data shape: every format conversion,
//! schema migration, API version adapter, type coercion, and memory layout
//! translation is a morphism.
//!
//! Morphisms carry three key pieces of information:
//! 1. **Steps**: The concrete sequence of transformations (rename, widen, project, etc.)
//! 2. **Transport class**: How much information is preserved (Concorde through Wheelbarrow)
//! 3. **Information cost**: Quantified bits gained and lost
//!
//! Morphisms compose: given `f: A -> B` and `g: B -> C`, we can produce
//! `g . f: A -> C`. This composition is associative and respects transport
//! classes (the composed class is the worst of the two).

use crate::atom::AtomKind;
use crate::information::{InformationCost, TransportClass};
use crate::labels::FieldPath;
use crate::shape::Shape;
use serde::{Deserialize, Serialize};
use std::fmt;

/// A transformation between two shapes.
///
/// This is the arrow in the category of data shapes. Every conversion between
/// formats, schemas, or type systems can be expressed as a morphism.
///
/// # Invariants
///
/// - `steps` describes a valid transformation from `source` to `target`
/// - `transport_class` correctly reflects the information preservation of `steps`
/// - `information_cost` accurately quantifies the bits gained and lost
///
/// These invariants are established by [`crate::compare::compare`] and
/// maintained by [`crate::compose::compose`].
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Morphism {
    /// The source shape (domain).
    pub source: Shape,

    /// The target shape (codomain).
    pub target: Shape,

    /// Classification of information preservation.
    pub transport_class: TransportClass,

    /// Quantified information cost (bits added/lost, step count).
    pub information_cost: InformationCost,

    /// The sequence of transformation steps that convert source to target.
    pub steps: Vec<MorphismStep>,
}

impl Morphism {
    /// Create an identity morphism (no transformation needed).
    pub fn identity(shape: Shape) -> Self {
        Self {
            source: shape.clone(),
            target: shape,
            transport_class: TransportClass::Concorde,
            information_cost: InformationCost::zero(),
            steps: Vec::new(),
        }
    }

    /// Returns true if this morphism is an identity (no transformation).
    pub fn is_identity(&self) -> bool {
        self.steps.is_empty() && self.transport_class == TransportClass::Concorde
    }

    /// Returns true if this morphism preserves all information (Concorde or Business).
    pub fn is_lossless(&self) -> bool {
        self.transport_class.is_lossless()
    }
}

impl fmt::Display for Morphism {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} -> {} [{}] ({} steps)",
            self.source,
            self.target,
            self.transport_class,
            self.steps.len()
        )
    }
}

/// A single step in a morphism — one atomic transformation.
///
/// Steps are the building blocks of morphisms. Each step describes a specific,
/// localized change at a particular path within the shape. Complex transformations
/// are sequences of steps.
///
/// Steps are ordered from most information-preserving (Identity) to most lossy
/// (Restructure, Reencode), reflecting the principle that simpler transformations
/// should be preferred.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum MorphismStep {
    /// Direct field mapping — the field at `path` has the same type in both
    /// shapes. No transformation needed. This is a Concorde step.
    Identity {
        /// Path to the field that maps directly.
        path: FieldPath,
    },

    /// Type widening — lossless expansion of a numeric or temporal type.
    /// The value at `path` is promoted from `from` to `to` without losing
    /// any information. This is a Business step (adds padding bits).
    ///
    /// Examples: i32 -> i64, f32 -> f64, timestamp(ms) -> timestamp(ns)
    Widen {
        /// Path to the field being widened.
        path: FieldPath,
        /// Source atom type.
        from: AtomKind,
        /// Target atom type (must be wider than `from`).
        to: AtomKind,
    },

    /// Type narrowing — lossy contraction of a numeric or temporal type.
    /// The value at `path` is truncated from `from` to `to`, potentially
    /// losing information. This is an Economy step.
    ///
    /// Examples: i64 -> i32, f64 -> f32, timestamp(ns) -> timestamp(ms)
    Narrow {
        /// Path to the field being narrowed.
        path: FieldPath,
        /// Source atom type.
        from: AtomKind,
        /// Target atom type (must be narrower than `from`).
        to: AtomKind,
    },

    /// Field added with a default value — the target has a field that the
    /// source doesn't. The morphism fills it with a default. This is a
    /// Business step (the added field is deterministic padding).
    Pad {
        /// Path where the new field appears in the target.
        path: FieldPath,
        /// Shape of the added field.
        shape: Shape,
        /// Default value to fill in.
        default: DefaultValue,
    },

    /// Field dropped — the source has a field that the target doesn't.
    /// Information is lost. This is an Economy step.
    Project {
        /// Path to the field being dropped.
        path: FieldPath,
    },

    /// Field renamed — the same data at a different path. No information
    /// change; this is a Concorde step (the data is identical, only the
    /// label changes).
    Rename {
        /// Path in the source shape.
        from: FieldPath,
        /// Path in the target shape.
        to: FieldPath,
    },

    /// Structural reorganization — fields are moved, flattened, or nested.
    /// The data may or may not be preserved depending on the specifics.
    /// Transport class depends on whether information is lost.
    Restructure {
        /// Paths in the source shape being reorganized.
        from: Vec<FieldPath>,
        /// Paths in the target shape after reorganization.
        to: Vec<FieldPath>,
    },

    /// Encoding change — the same logical value represented differently.
    /// Examples: timestamp as ISO 8601 string vs Unix epoch integer,
    /// UUID as string vs bytes, date as "YYYY-MM-DD" vs days-since-epoch.
    ///
    /// Transport class depends on whether the encoding change is reversible.
    Reencode {
        /// Path to the field being re-encoded.
        path: FieldPath,
        /// Description of the source encoding.
        from_encoding: String,
        /// Description of the target encoding.
        to_encoding: String,
    },
}

impl MorphismStep {
    /// Returns the transport class of this individual step.
    pub fn transport_class(&self) -> TransportClass {
        match self {
            MorphismStep::Identity { .. } => TransportClass::Concorde,
            MorphismStep::Widen { .. } => TransportClass::Business,
            MorphismStep::Narrow { .. } => TransportClass::Economy,
            MorphismStep::Pad { .. } => TransportClass::Business,
            MorphismStep::Project { .. } => TransportClass::Economy,
            MorphismStep::Rename { .. } => TransportClass::Concorde,
            MorphismStep::Restructure { from, to } => {
                if from.len() == to.len() {
                    TransportClass::Business // Reorganization preserves data
                } else {
                    TransportClass::Economy // Different cardinality implies loss
                }
            },
            MorphismStep::Reencode { .. } => TransportClass::Business, // Assume reversible by default
        }
    }
}

impl fmt::Display for MorphismStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MorphismStep::Identity { path } => write!(f, "identity({})", path),
            MorphismStep::Widen { path, from, to } => {
                write!(f, "widen({}: {} -> {})", path, from, to)
            },
            MorphismStep::Narrow { path, from, to } => {
                write!(f, "narrow({}: {} -> {})", path, from, to)
            },
            MorphismStep::Pad { path, default, .. } => {
                write!(f, "pad({} = {})", path, default)
            },
            MorphismStep::Project { path } => write!(f, "project({})", path),
            MorphismStep::Rename { from, to } => write!(f, "rename({} -> {})", from, to),
            MorphismStep::Restructure { from, to } => {
                let from_strs: Vec<_> = from.iter().map(|p| p.to_string()).collect();
                let to_strs: Vec<_> = to.iter().map(|p| p.to_string()).collect();
                write!(
                    f,
                    "restructure([{}] -> [{}])",
                    from_strs.join(", "),
                    to_strs.join(", ")
                )
            },
            MorphismStep::Reencode {
                path,
                from_encoding,
                to_encoding,
            } => {
                write!(
                    f,
                    "reencode({}: {} -> {})",
                    path, from_encoding, to_encoding
                )
            },
        }
    }
}

/// A default value used to fill in missing fields during a [`MorphismStep::Pad`].
///
/// Default values are format-agnostic representations of the value that should
/// be used when the source shape doesn't have a corresponding field.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum DefaultValue {
    /// No value (null / None / nil).
    Null,
    /// Boolean default.
    Bool(bool),
    /// Integer default.
    Integer(i64),
    /// Floating-point default.
    Float(f64),
    /// String default.
    String(String),
    /// Byte array default.
    Bytes(Vec<u8>),
    /// Empty collection (array, map).
    EmptyCollection,
    /// A JSON-encoded default for complex types.
    Json(String),
}

impl fmt::Display for DefaultValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DefaultValue::Null => write!(f, "null"),
            DefaultValue::Bool(v) => write!(f, "{}", v),
            DefaultValue::Integer(v) => write!(f, "{}", v),
            DefaultValue::Float(v) => write!(f, "{}", v),
            DefaultValue::String(v) => write!(f, "\"{}\"", v),
            DefaultValue::Bytes(v) => write!(f, "bytes[{}]", v.len()),
            DefaultValue::EmptyCollection => write!(f, "[]"),
            DefaultValue::Json(v) => write!(f, "{}", v),
        }
    }
}
