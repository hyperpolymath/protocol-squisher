// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Ephapax transport compatibility bridge for GraphQL types.
//!
//! Analyzes transport class compatibility between GraphQL-derived IR types
//! and target IR types, producing `TransportAnalysis` results.

use crate::AnalyzerError;
use protocol_squisher_ir::{ContainerType, IrType, PrimitiveType};
use serde::{Deserialize, Serialize};

/// Transport class for compatibility analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TransportClass {
    Concorde,
    Business,
    Economy,
    Wheelbarrow,
}

/// Result of a transport compatibility analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransportAnalysis {
    /// The transport class assigned to this conversion.
    pub class: TransportClass,
    /// Fidelity score (0-100) indicating data preservation accuracy.
    pub fidelity: u8,
    /// Overhead score (0-100) indicating conversion cost.
    pub overhead: u8,
    /// Source type description.
    pub source_type: String,
    /// Target type description.
    pub target_type: String,
}

impl TransportAnalysis {
    /// Whether this is a zero-copy (Concorde) conversion.
    pub fn is_zero_copy(&self) -> bool {
        self.class == TransportClass::Concorde
    }

    /// Whether this conversion is safe (Concorde or Business).
    pub fn is_safe(&self) -> bool {
        matches!(
            self.class,
            TransportClass::Concorde | TransportClass::Business
        )
    }

    /// Whether this conversion requires JSON fallback.
    pub fn requires_json_fallback(&self) -> bool {
        self.class == TransportClass::Wheelbarrow
    }
}

/// Analyze transport compatibility between two IR types.
pub fn analyze_transport_compatibility(
    source: &IrType,
    target: &IrType,
) -> Result<TransportAnalysis, AnalyzerError> {
    let (class, fidelity, overhead) = match (source, target) {
        (IrType::Primitive(s), IrType::Primitive(t)) => analyze_primitive_compatibility(s, t),
        (IrType::Container(s), IrType::Container(t)) => analyze_container_compatibility(s, t)?,
        (IrType::Reference(s), IrType::Reference(t)) if s == t => {
            (TransportClass::Concorde, 100, 0)
        },
        _ => (TransportClass::Wheelbarrow, 50, 80),
    };

    Ok(TransportAnalysis {
        class,
        fidelity,
        overhead,
        source_type: format!("{source:?}"),
        target_type: format!("{target:?}"),
    })
}

/// Analyze primitive-to-primitive transport class.
fn analyze_primitive_compatibility(
    source: &PrimitiveType,
    target: &PrimitiveType,
) -> (TransportClass, u8, u8) {
    if source == target {
        return (TransportClass::Concorde, 100, 0);
    }

    // Check safe widening.
    if is_safe_widening(source, target) {
        return (TransportClass::Business, 98, 5);
    }

    // All other cases are incompatible.
    (TransportClass::Wheelbarrow, 50, 80)
}

/// Check if a primitive type widening is safe.
fn is_safe_widening(source: &PrimitiveType, target: &PrimitiveType) -> bool {
    use PrimitiveType::*;
    matches!(
        (source, target),
        (I8, I16)
            | (I8, I32)
            | (I8, I64)
            | (I8, I128)
            | (I16, I32)
            | (I16, I64)
            | (I16, I128)
            | (I32, I64)
            | (I32, I128)
            | (I64, I128)
            | (U8, U16)
            | (U8, U32)
            | (U8, U64)
            | (U8, U128)
            | (U16, U32)
            | (U16, U64)
            | (U16, U128)
            | (U32, U64)
            | (U32, U128)
            | (U64, U128)
            | (F32, F64)
    )
}

/// Analyze container-to-container transport class.
fn analyze_container_compatibility(
    source: &ContainerType,
    target: &ContainerType,
) -> Result<(TransportClass, u8, u8), AnalyzerError> {
    match (source, target) {
        (ContainerType::Option(s), ContainerType::Option(t))
        | (ContainerType::Vec(s), ContainerType::Vec(t)) => {
            let inner = analyze_transport_compatibility(s, t)?;
            Ok((
                inner.class,
                inner.fidelity,
                inner.overhead.saturating_add(2),
            ))
        },
        (ContainerType::Map(sk, sv), ContainerType::Map(tk, tv)) => {
            let key_analysis = analyze_transport_compatibility(sk, tk)?;
            let val_analysis = analyze_transport_compatibility(sv, tv)?;
            let class = worst_transport_class(key_analysis.class, val_analysis.class);
            let fidelity = key_analysis.fidelity.min(val_analysis.fidelity);
            let overhead = key_analysis.overhead.max(val_analysis.overhead);
            Ok((class, fidelity, overhead))
        },
        _ => Ok((TransportClass::Wheelbarrow, 50, 80)),
    }
}

/// Return the worse of two transport classes.
fn worst_transport_class(a: TransportClass, b: TransportClass) -> TransportClass {
    let rank = |c: &TransportClass| match c {
        TransportClass::Concorde => 0,
        TransportClass::Business => 1,
        TransportClass::Economy => 2,
        TransportClass::Wheelbarrow => 3,
    };
    if rank(&a) >= rank(&b) {
        a
    } else {
        b
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identical_primitives_are_concorde() {
        let result = analyze_transport_compatibility(
            &IrType::Primitive(PrimitiveType::I32),
            &IrType::Primitive(PrimitiveType::I32),
        )
        .unwrap();
        assert_eq!(result.class, TransportClass::Concorde);
        assert!(result.is_zero_copy());
        assert_eq!(result.fidelity, 100);
    }

    #[test]
    fn widening_is_business() {
        let result = analyze_transport_compatibility(
            &IrType::Primitive(PrimitiveType::I32),
            &IrType::Primitive(PrimitiveType::I64),
        )
        .unwrap();
        assert_eq!(result.class, TransportClass::Business);
        assert!(result.is_safe());
    }

    #[test]
    fn incompatible_is_wheelbarrow() {
        let result = analyze_transport_compatibility(
            &IrType::Primitive(PrimitiveType::I32),
            &IrType::Primitive(PrimitiveType::String),
        )
        .unwrap();
        assert_eq!(result.class, TransportClass::Wheelbarrow);
        assert!(result.requires_json_fallback());
    }

    #[test]
    fn vec_propagates_inner_class() {
        let result = analyze_transport_compatibility(
            &IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
                PrimitiveType::I32,
            )))),
            &IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
                PrimitiveType::I64,
            )))),
        )
        .unwrap();
        assert_eq!(result.class, TransportClass::Business);
    }
}
