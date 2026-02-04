// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! Bridge between protocol-squisher IR and ephapax IR
//!
//! This module converts Rust types analyzed by syn into ephapax IR types
//! for transport class analysis.

use protocol_squisher_ephapax_ir::{IRContext, PrimitiveType, TransportClass};
use protocol_squisher_ir::IrType;
use crate::AnalyzerError;

/// Convert protocol-squisher IR type to ephapax primitive type
///
/// Returns None if the type is not a primitive or cannot be represented
/// as an ephapax primitive type.
pub fn to_ephapax_primitive(ir_type: &IrType) -> Option<PrimitiveType> {
    match ir_type {
        IrType::Primitive(prim) => {
            use protocol_squisher_ir::PrimitiveType as IrPrim;
            match prim {
                IrPrim::I8 => Some(PrimitiveType::I8),
                IrPrim::I16 => Some(PrimitiveType::I16),
                IrPrim::I32 => Some(PrimitiveType::I32),
                IrPrim::I64 => Some(PrimitiveType::I64),
                IrPrim::U8 => Some(PrimitiveType::U8),
                IrPrim::U16 => Some(PrimitiveType::U16),
                IrPrim::U32 => Some(PrimitiveType::U32),
                IrPrim::U64 => Some(PrimitiveType::U64),
                IrPrim::F32 => Some(PrimitiveType::F32),
                IrPrim::F64 => Some(PrimitiveType::F64),
                IrPrim::Bool => Some(PrimitiveType::Bool),
                IrPrim::Char => Some(PrimitiveType::Char),
                IrPrim::String => Some(PrimitiveType::String),
                // Types not yet supported in ephapax IR
                IrPrim::I128 | IrPrim::U128 | IrPrim::Bytes |
                IrPrim::DateTime | IrPrim::Date | IrPrim::Time | IrPrim::Duration |
                IrPrim::Uuid | IrPrim::Decimal | IrPrim::BigInt => None,
            }
        }
        IrType::Special(protocol_squisher_ir::SpecialType::Unit) => {
            Some(PrimitiveType::Unit)
        }
        // Containers and other complex types don't map to primitives
        _ => None,
    }
}

/// Analyze transport compatibility between two IR types
///
/// Uses the ephapax IR for proven-correct transport class analysis.
pub fn analyze_transport_compatibility(
    ctx: &IRContext,
    source: &IrType,
    target: &IrType,
) -> Result<TransportClass, AnalyzerError> {
    // For now, only handle primitive types
    let source_prim = to_ephapax_primitive(source)
        .ok_or_else(|| AnalyzerError::UnsupportedConstruct(
            "Only primitive types supported for ephapax analysis".to_string()
        ))?;

    let target_prim = to_ephapax_primitive(target)
        .ok_or_else(|| AnalyzerError::UnsupportedConstruct(
            "Only primitive types supported for ephapax analysis".to_string()
        ))?;

    Ok(ctx.analyze_compatibility(source_prim, target_prim))
}

/// Transport analysis result
#[derive(Debug, Clone)]
pub struct TransportAnalysis {
    pub class: TransportClass,
    pub fidelity: u8,
    pub overhead: u8,
    pub source_type: String,
    pub target_type: String,
}

impl TransportAnalysis {
    /// Create a new transport analysis
    pub fn new(
        ctx: &IRContext,
        source: &IrType,
        target: &IrType,
    ) -> Result<Self, AnalyzerError> {
        let class = analyze_transport_compatibility(ctx, source, target)?;

        Ok(Self {
            fidelity: ctx.get_fidelity(class),
            overhead: ctx.get_overhead(class),
            source_type: format!("{:?}", source),
            target_type: format!("{:?}", target),
            class,
        })
    }

    /// Check if this is a zero-copy path (Concorde class)
    pub fn is_zero_copy(&self) -> bool {
        matches!(self.class, TransportClass::Concorde)
    }

    /// Check if this is a safe conversion (Concorde or Business)
    pub fn is_safe(&self) -> bool {
        matches!(self.class, TransportClass::Concorde | TransportClass::Business)
    }

    /// Check if JSON fallback is required (Wheelbarrow)
    pub fn requires_json_fallback(&self) -> bool {
        matches!(self.class, TransportClass::Wheelbarrow)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::PrimitiveType as IrPrim;

    #[test]
    fn test_primitive_conversion() {
        let ir_i32 = IrType::Primitive(IrPrim::I32);
        let ephapax_type = to_ephapax_primitive(&ir_i32);
        assert_eq!(ephapax_type, Some(PrimitiveType::I32));
    }

    #[test]
    fn test_exact_match_analysis() {
        let ctx = IRContext::new();
        let i32_type = IrType::Primitive(IrPrim::I32);

        let analysis = TransportAnalysis::new(&ctx, &i32_type, &i32_type).unwrap();

        assert!(analysis.is_zero_copy());
        assert!(analysis.is_safe());
        assert!(!analysis.requires_json_fallback());
        assert_eq!(analysis.fidelity, 100);
        assert_eq!(analysis.overhead, 0);
    }

    #[test]
    fn test_safe_widening_analysis() {
        let ctx = IRContext::new();
        let i32_type = IrType::Primitive(IrPrim::I32);
        let i64_type = IrType::Primitive(IrPrim::I64);

        let analysis = TransportAnalysis::new(&ctx, &i32_type, &i64_type).unwrap();

        assert!(!analysis.is_zero_copy());
        assert!(analysis.is_safe());
        assert!(!analysis.requires_json_fallback());
        assert_eq!(analysis.fidelity, 98);
        assert_eq!(analysis.overhead, 5);
    }

    #[test]
    fn test_incompatible_types() {
        let ctx = IRContext::new();
        let i32_type = IrType::Primitive(IrPrim::I32);
        let string_type = IrType::Primitive(IrPrim::String);

        let analysis = TransportAnalysis::new(&ctx, &i32_type, &string_type).unwrap();

        assert!(!analysis.is_zero_copy());
        assert!(!analysis.is_safe());
        assert!(analysis.requires_json_fallback());
        assert_eq!(analysis.fidelity, 50);
        assert_eq!(analysis.overhead, 80);
    }
}
