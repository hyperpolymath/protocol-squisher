// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! Bridge between Python/Pydantic types and ephapax IR
//!
//! This module converts Pydantic model types into ephapax IR types
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

/// Analyze transport compatibility between Pydantic and Rust types
///
/// Uses the ephapax IR for proven-correct transport class analysis.
pub fn analyze_transport_compatibility(
    ctx: &IRContext,
    pydantic_type: &IrType,
    rust_type: &IrType,
) -> Result<TransportClass, AnalyzerError> {
    // For now, only handle primitive types
    let pydantic_prim = to_ephapax_primitive(pydantic_type)
        .ok_or_else(|| AnalyzerError::UnsupportedType(
            "Only primitive types supported for ephapax analysis".to_string()
        ))?;

    let rust_prim = to_ephapax_primitive(rust_type)
        .ok_or_else(|| AnalyzerError::UnsupportedType(
            "Only primitive types supported for ephapax analysis".to_string()
        ))?;

    Ok(ctx.analyze_compatibility(pydantic_prim, rust_prim))
}

/// Transport analysis result for Python↔Rust interop
#[derive(Debug, Clone)]
pub struct PyRustTransportAnalysis {
    pub class: TransportClass,
    pub fidelity: u8,
    pub overhead: u8,
    pub pydantic_type: String,
    pub rust_type: String,
}

impl PyRustTransportAnalysis {
    /// Create a new transport analysis for Python→Rust conversion
    pub fn new(
        ctx: &IRContext,
        pydantic_type: &IrType,
        rust_type: &IrType,
    ) -> Result<Self, AnalyzerError> {
        let class = analyze_transport_compatibility(ctx, pydantic_type, rust_type)?;

        Ok(Self {
            fidelity: ctx.get_fidelity(class),
            overhead: ctx.get_overhead(class),
            pydantic_type: format!("{:?}", pydantic_type),
            rust_type: format!("{:?}", rust_type),
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

    /// Check if PyO3 conversion is needed (not Concorde)
    pub fn needs_pyo3_conversion(&self) -> bool {
        !self.is_zero_copy()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::PrimitiveType as IrPrim;

    #[test]
    fn test_primitive_conversion() {
        let ir_i64 = IrType::Primitive(IrPrim::I64);
        let ephapax_type = to_ephapax_primitive(&ir_i64);
        assert_eq!(ephapax_type, Some(PrimitiveType::I64));
    }

    #[test]
    fn test_python_int_to_rust_i64() {
        // Python int → Rust i64 (common pattern)
        let ctx = IRContext::new();
        let py_int = IrType::Primitive(IrPrim::I64);  // Python int maps to i64
        let rust_i64 = IrType::Primitive(IrPrim::I64);

        let analysis = PyRustTransportAnalysis::new(&ctx, &py_int, &rust_i64).unwrap();

        assert!(analysis.is_zero_copy());
        assert!(analysis.is_safe());
        assert!(!analysis.requires_json_fallback());
        assert_eq!(analysis.fidelity, 100);
        assert_eq!(analysis.overhead, 0);
    }

    #[test]
    fn test_python_int_to_rust_i32() {
        // Python int → Rust i32 (potential overflow, but common)
        let ctx = IRContext::new();
        let py_int = IrType::Primitive(IrPrim::I64);  // Python int maps to i64
        let rust_i32 = IrType::Primitive(IrPrim::I32);

        let analysis = PyRustTransportAnalysis::new(&ctx, &py_int, &rust_i32).unwrap();

        // This is actually incompatible (i64 → i32 is narrowing, not widening)
        // ephapax correctly identifies this as requiring fallback
        assert!(!analysis.is_zero_copy());
        assert!(!analysis.is_safe());
        assert!(analysis.requires_json_fallback());
    }

    #[test]
    fn test_python_str_to_rust_string() {
        // Python str → Rust String (exact match)
        let ctx = IRContext::new();
        let py_str = IrType::Primitive(IrPrim::String);
        let rust_string = IrType::Primitive(IrPrim::String);

        let analysis = PyRustTransportAnalysis::new(&ctx, &py_str, &rust_string).unwrap();

        assert!(analysis.is_zero_copy());
        assert!(analysis.is_safe());
        assert!(!analysis.requires_json_fallback());
        assert!(!analysis.needs_pyo3_conversion());
    }

    #[test]
    fn test_python_float_to_rust_f64() {
        // Python float → Rust f64 (exact match)
        let ctx = IRContext::new();
        let py_float = IrType::Primitive(IrPrim::F64);
        let rust_f64 = IrType::Primitive(IrPrim::F64);

        let analysis = PyRustTransportAnalysis::new(&ctx, &py_float, &rust_f64).unwrap();

        assert!(analysis.is_zero_copy());
        assert!(!analysis.needs_pyo3_conversion());
    }

    #[test]
    fn test_python_float_to_rust_f32() {
        // Python float → Rust f32 (precision loss)
        let ctx = IRContext::new();
        let py_float = IrType::Primitive(IrPrim::F64);
        let rust_f32 = IrType::Primitive(IrPrim::F32);

        let analysis = PyRustTransportAnalysis::new(&ctx, &py_float, &rust_f32).unwrap();

        // f64 → f32 is narrowing (precision loss)
        assert!(!analysis.is_safe());
        assert!(analysis.requires_json_fallback());
    }
}
