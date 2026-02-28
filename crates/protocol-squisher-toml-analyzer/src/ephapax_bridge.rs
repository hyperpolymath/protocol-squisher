// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Ephapax transport compatibility bridge for TOML-derived types.
//!
//! Provides the same transport analysis interface as other analyzers,
//! evaluating compatibility between TOML-inferred IR types and target types.

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
    pub class: TransportClass,
    pub fidelity: u8,
    pub overhead: u8,
    pub source_type: String,
    pub target_type: String,
}

impl TransportAnalysis {
    pub fn is_zero_copy(&self) -> bool {
        self.class == TransportClass::Concorde
    }

    pub fn is_safe(&self) -> bool {
        matches!(
            self.class,
            TransportClass::Concorde | TransportClass::Business
        )
    }

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
        (IrType::Primitive(s), IrType::Primitive(t)) => {
            analyze_primitive_compat(s, t)
        }
        (IrType::Container(s), IrType::Container(t)) => {
            analyze_container_compat(s, t)?
        }
        (IrType::Reference(s), IrType::Reference(t)) if s == t => {
            (TransportClass::Concorde, 100, 0)
        }
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

fn analyze_primitive_compat(
    source: &PrimitiveType,
    target: &PrimitiveType,
) -> (TransportClass, u8, u8) {
    if source == target {
        return (TransportClass::Concorde, 100, 0);
    }

    if is_safe_widening(source, target) {
        return (TransportClass::Business, 98, 5);
    }

    (TransportClass::Wheelbarrow, 50, 80)
}

fn is_safe_widening(source: &PrimitiveType, target: &PrimitiveType) -> bool {
    use PrimitiveType::*;
    matches!(
        (source, target),
        (I8, I16) | (I8, I32) | (I8, I64) | (I8, I128)
            | (I16, I32) | (I16, I64) | (I16, I128)
            | (I32, I64) | (I32, I128)
            | (I64, I128)
            | (U8, U16) | (U8, U32) | (U8, U64) | (U8, U128)
            | (U16, U32) | (U16, U64) | (U16, U128)
            | (U32, U64) | (U32, U128)
            | (U64, U128)
            | (F32, F64)
    )
}

fn analyze_container_compat(
    source: &ContainerType,
    target: &ContainerType,
) -> Result<(TransportClass, u8, u8), AnalyzerError> {
    match (source, target) {
        (ContainerType::Vec(s), ContainerType::Vec(t)) => {
            let inner = analyze_transport_compatibility(s, t)?;
            Ok((inner.class, inner.fidelity, inner.overhead.saturating_add(2)))
        }
        (ContainerType::Option(s), ContainerType::Option(t)) => {
            let inner = analyze_transport_compatibility(s, t)?;
            Ok((inner.class, inner.fidelity, inner.overhead))
        }
        _ => Ok((TransportClass::Wheelbarrow, 50, 80)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identical_types_concorde() {
        let result = analyze_transport_compatibility(
            &IrType::Primitive(PrimitiveType::I64),
            &IrType::Primitive(PrimitiveType::I64),
        )
        .unwrap();
        assert!(result.is_zero_copy());
    }

    #[test]
    fn widening_is_business() {
        let result = analyze_transport_compatibility(
            &IrType::Primitive(PrimitiveType::I32),
            &IrType::Primitive(PrimitiveType::I64),
        )
        .unwrap();
        assert!(result.is_safe());
        assert_eq!(result.class, TransportClass::Business);
    }

    #[test]
    fn incompatible_is_wheelbarrow() {
        let result = analyze_transport_compatibility(
            &IrType::Primitive(PrimitiveType::String),
            &IrType::Primitive(PrimitiveType::I64),
        )
        .unwrap();
        assert!(result.requires_json_fallback());
    }
}
