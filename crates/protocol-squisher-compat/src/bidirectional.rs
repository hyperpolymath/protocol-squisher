// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <jonathan.jewell@open.ac.uk>

//! Bidirectional compatibility analysis.
//!
//! Transport classes are **asymmetric**: converting A->B may be Concorde
//! (safe widening) while B->A is Economy (lossy narrowing). Real-world
//! interoperability requires understanding both directions.
//!
//! This module provides:
//! - Bidirectional comparison (forward + reverse in one call)
//! - Round-trip fidelity analysis (A->B->A information preservation)
//! - Asymmetry detection (highlights where directions differ)

use crate::schema::{compare_schemas, SchemaComparison};
use crate::transport::TransportClass;
use protocol_squisher_ir::IrSchema;
use serde::{Deserialize, Serialize};

/// Result of bidirectional schema comparison.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BidirectionalResult {
    /// Forward comparison (source -> target)
    pub forward: SchemaComparison,
    /// Reverse comparison (target -> source)
    pub reverse: SchemaComparison,
    /// Forward transport class
    pub forward_class: TransportClass,
    /// Reverse transport class
    pub reverse_class: TransportClass,
    /// Whether the transport classes are symmetric (same in both directions)
    pub is_symmetric: bool,
    /// Round-trip transport class (worst of forward and reverse)
    pub round_trip_class: TransportClass,
    /// Per-type asymmetry details
    pub asymmetries: Vec<TypeAsymmetry>,
}

/// Describes an asymmetry between forward and reverse transport for a type.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeAsymmetry {
    /// Type name
    pub type_name: String,
    /// Forward (source->target) transport class
    pub forward_class: TransportClass,
    /// Reverse (target->source) transport class
    pub reverse_class: TransportClass,
    /// Direction with worse class
    pub bottleneck_direction: Direction,
    /// Additional losses incurred in the worse direction
    pub additional_losses: usize,
}

/// Which direction is the bottleneck.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Direction {
    Forward,
    Reverse,
    Symmetric,
}

impl std::fmt::Display for Direction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Direction::Forward => write!(f, "forward (source -> target)"),
            Direction::Reverse => write!(f, "reverse (target -> source)"),
            Direction::Symmetric => write!(f, "symmetric"),
        }
    }
}

/// Perform bidirectional compatibility analysis between two schemas.
pub fn bidirectional_compare(source: &IrSchema, target: &IrSchema) -> BidirectionalResult {
    let forward = compare_schemas(source, target);
    let reverse = compare_schemas(target, source);

    let forward_class = forward.class;
    let reverse_class = reverse.class;
    let is_symmetric = forward_class == reverse_class;
    let round_trip_class = forward_class.join(reverse_class);

    // Detect per-type asymmetries
    let mut asymmetries = Vec::new();
    for (type_name, fwd_cmp) in &forward.type_comparisons {
        if let Some(rev_cmp) = reverse.type_comparisons.get(type_name) {
            if fwd_cmp.class != rev_cmp.class {
                let (bottleneck_direction, additional_losses) = if fwd_cmp.class > rev_cmp.class {
                    (Direction::Forward, fwd_cmp.losses.len().saturating_sub(rev_cmp.losses.len()))
                } else {
                    (Direction::Reverse, rev_cmp.losses.len().saturating_sub(fwd_cmp.losses.len()))
                };

                asymmetries.push(TypeAsymmetry {
                    type_name: type_name.clone(),
                    forward_class: fwd_cmp.class,
                    reverse_class: rev_cmp.class,
                    bottleneck_direction,
                    additional_losses,
                });
            }
        }
    }

    BidirectionalResult {
        forward,
        reverse,
        forward_class,
        reverse_class,
        is_symmetric,
        round_trip_class,
        asymmetries,
    }
}

impl BidirectionalResult {
    /// Whether round-trip conversion preserves all information.
    pub fn is_round_trip_lossless(&self) -> bool {
        self.round_trip_class.is_lossless()
    }

    /// Whether conversion is possible in both directions.
    pub fn is_bidirectionally_convertible(&self) -> bool {
        self.forward_class.is_convertible() && self.reverse_class.is_convertible()
    }

    /// Get the number of types with asymmetric transport classes.
    pub fn asymmetry_count(&self) -> usize {
        self.asymmetries.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{
        FieldDef, FieldMetadata, IrType, PrimitiveType, StructDef, TypeDef, TypeMetadata,
    };

    fn make_schema(name: &str, field_type: PrimitiveType) -> IrSchema {
        let mut schema = IrSchema::new(name, "test");
        schema.add_type(
            "Record".to_string(),
            TypeDef::Struct(StructDef {
                name: "Record".to_string(),
                fields: vec![FieldDef {
                    name: "value".to_string(),
                    ty: IrType::Primitive(field_type),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
                metadata: TypeMetadata::default(),
            }),
        );
        schema
    }

    #[test]
    fn test_symmetric_comparison() {
        let a = make_schema("a", PrimitiveType::I64);
        let b = make_schema("b", PrimitiveType::I64);

        let result = bidirectional_compare(&a, &b);
        assert!(result.is_symmetric);
        assert_eq!(result.forward_class, TransportClass::Concorde);
        assert_eq!(result.reverse_class, TransportClass::Concorde);
        assert_eq!(result.round_trip_class, TransportClass::Concorde);
        assert!(result.is_round_trip_lossless());
        assert_eq!(result.asymmetry_count(), 0);
    }

    #[test]
    fn test_asymmetric_widening_narrowing() {
        let narrow = make_schema("narrow", PrimitiveType::I32);
        let wide = make_schema("wide", PrimitiveType::I64);

        let result = bidirectional_compare(&narrow, &wide);

        // i32->i64 should be better than i64->i32
        assert!(!result.is_symmetric);
        assert!(result.forward_class < result.reverse_class);

        // Round-trip is the worse of the two
        assert_eq!(result.round_trip_class, result.forward_class.join(result.reverse_class));
        assert!(!result.is_round_trip_lossless());
    }

    #[test]
    fn test_asymmetries_detected() {
        let narrow = make_schema("narrow", PrimitiveType::I32);
        let wide = make_schema("wide", PrimitiveType::I64);

        let result = bidirectional_compare(&narrow, &wide);
        assert!(result.asymmetry_count() > 0);

        let asym = &result.asymmetries[0];
        assert_eq!(asym.type_name, "Record");
        assert_ne!(asym.forward_class, asym.reverse_class);
    }

    #[test]
    fn test_bidirectionally_convertible() {
        let a = make_schema("a", PrimitiveType::I32);
        let b = make_schema("b", PrimitiveType::I64);

        let result = bidirectional_compare(&a, &b);
        assert!(result.is_bidirectionally_convertible());
    }

    #[test]
    fn test_incompatible_not_bidirectional() {
        let a = make_schema("a", PrimitiveType::String);
        let b = make_schema("b", PrimitiveType::Bool);

        let result = bidirectional_compare(&a, &b);
        assert!(!result.is_bidirectionally_convertible());
    }
}
