// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Annotations and Constraints
//!
//! Annotations attach metadata and validation constraints to shapes without
//! altering their structural identity. A shape with annotations represents the
//! same data structure as the unannotated shape, but with additional semantic
//! information that morphisms must respect.
//!
//! Constraints model validation rules found across formats:
//! - JSON Schema's `minimum`, `maximum`, `minLength`, `maxLength`, `pattern`
//! - Protobuf's field validation (via protovalidate)
//! - SQL's CHECK constraints
//! - OpenAPI's parameter validation
//!
//! When computing morphisms, constraints affect the transport class: a morphism
//! from a constrained shape to an unconstrained one may lose validation guarantees,
//! pushing it from Concorde to Business class.

use crate::linearity::Linearity;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;

/// Metadata and constraints attached to a shape via [`crate::Shape::Annotated`].
///
/// Annotations are semantically transparent for structural comparison — two
/// shapes that differ only in annotations are structurally equivalent. However,
/// annotations affect morphism transport class because they carry semantic
/// guarantees that may be lost in translation.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Annotations {
    /// Resource usage semantics for this shape.
    pub linearity: Linearity,

    /// Whether this shape explicitly allows null/nil/None values.
    /// Distinct from [`crate::Shape::Optional`], which wraps a shape.
    /// This flag models SQL's column-level NULL constraint and Protobuf's
    /// optional wrapper types.
    pub nullable: bool,

    /// Whether this shape is deprecated and should be avoided in new code.
    pub deprecated: bool,

    /// Validation constraints that values of this shape must satisfy.
    pub constraints: Vec<Constraint>,

    /// Arbitrary key-value metadata for format-specific properties that don't
    /// fit into the structured fields above.
    /// Examples: `("protobuf.field_number", "3")`, `("sql.collation", "utf8mb4")`
    pub metadata: HashMap<String, String>,
}

impl Annotations {
    /// Create default annotations (unrestricted, not nullable, no constraints).
    pub fn new() -> Self {
        Self::default()
    }

    /// Builder: set linearity.
    pub fn with_linearity(mut self, linearity: Linearity) -> Self {
        self.linearity = linearity;
        self
    }

    /// Builder: mark as nullable.
    pub fn with_nullable(mut self, nullable: bool) -> Self {
        self.nullable = nullable;
        self
    }

    /// Builder: mark as deprecated.
    pub fn with_deprecated(mut self, deprecated: bool) -> Self {
        self.deprecated = deprecated;
        self
    }

    /// Builder: add a constraint.
    pub fn with_constraint(mut self, constraint: Constraint) -> Self {
        self.constraints.push(constraint);
        self
    }

    /// Builder: add a metadata entry.
    pub fn with_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }

    /// Returns true if these annotations carry no meaningful information
    /// beyond defaults.
    pub fn is_empty(&self) -> bool {
        self.linearity == Linearity::Unrestricted
            && !self.nullable
            && !self.deprecated
            && self.constraints.is_empty()
            && self.metadata.is_empty()
    }
}

impl Default for Annotations {
    fn default() -> Self {
        Self {
            linearity: Linearity::Unrestricted,
            nullable: false,
            deprecated: false,
            constraints: Vec::new(),
            metadata: HashMap::new(),
        }
    }
}

/// A validation constraint on a shape's values.
///
/// Constraints are format-agnostic representations of validation rules. The same
/// constraint might originate from a JSON Schema `minimum`, a SQL `CHECK`, or a
/// Protobuf validation rule — the Shape IR normalizes them all.
///
/// When a morphism drops constraints, the transport class degrades because the
/// target no longer guarantees what the source promised.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Constraint {
    /// Minimum numeric value (inclusive). Maps to JSON Schema `minimum`,
    /// SQL `CHECK (col >= val)`.
    MinValue(f64),

    /// Maximum numeric value (inclusive). Maps to JSON Schema `maximum`,
    /// SQL `CHECK (col <= val)`.
    MaxValue(f64),

    /// Minimum string/bytes length. Maps to JSON Schema `minLength`,
    /// SQL `CHECK (LENGTH(col) >= val)`.
    MinLength(usize),

    /// Maximum string/bytes length. Maps to JSON Schema `maxLength`,
    /// SQL `VARCHAR(n)`.
    MaxLength(usize),

    /// Regex pattern that string values must match. Maps to JSON Schema
    /// `pattern`, protovalidate `string.pattern`.
    Pattern(String),

    /// Value must be one of the listed strings. Models JSON Schema `enum`
    /// (for string-typed enums), SQL `CHECK (col IN (...))`.
    OneOf(Vec<String>),

    /// Arbitrary named constraint for format-specific rules that don't fit
    /// the structured variants above.
    /// First element is the constraint name, second is its value.
    Custom(String, String),
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::MinValue(v) => write!(f, ">= {}", v),
            Constraint::MaxValue(v) => write!(f, "<= {}", v),
            Constraint::MinLength(v) => write!(f, "len >= {}", v),
            Constraint::MaxLength(v) => write!(f, "len <= {}", v),
            Constraint::Pattern(p) => write!(f, "~/{}/", p),
            Constraint::OneOf(vs) => write!(f, "in [{}]", vs.join(", ")),
            Constraint::Custom(k, v) => write!(f, "{}={}", k, v),
        }
    }
}
