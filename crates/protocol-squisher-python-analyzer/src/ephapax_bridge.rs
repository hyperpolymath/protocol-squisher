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
/// Supports both primitive types and containers (Option, Vec, Map, Tuple).
pub fn analyze_transport_compatibility(
    ctx: &IRContext,
    pydantic_type: &IrType,
    rust_type: &IrType,
) -> Result<TransportClass, AnalyzerError> {
    use protocol_squisher_ir::IrType;

    match (pydantic_type, rust_type) {
        // Primitive types - use ephapax analysis
        (IrType::Primitive(_), IrType::Primitive(_)) |
        (IrType::Special(_), IrType::Special(_)) => {
            let pydantic_prim = to_ephapax_primitive(pydantic_type)
                .ok_or_else(|| AnalyzerError::UnsupportedType(
                    format!("Unsupported primitive type: {:?}", pydantic_type)
                ))?;

            let rust_prim = to_ephapax_primitive(rust_type)
                .ok_or_else(|| AnalyzerError::UnsupportedType(
                    format!("Unsupported primitive type: {:?}", rust_type)
                ))?;

            Ok(ctx.analyze_compatibility(pydantic_prim, rust_prim))
        }

        // Container types - recursive analysis
        (IrType::Container(pydantic_container), IrType::Container(rust_container)) => {
            analyze_container_compatibility(ctx, pydantic_container, rust_container)
        }

        // Mismatched types (primitive vs container) - always Wheelbarrow
        _ => Ok(TransportClass::Wheelbarrow),
    }
}

/// Analyze compatibility between two container types
fn analyze_container_compatibility(
    ctx: &IRContext,
    pydantic: &protocol_squisher_ir::ContainerType,
    rust: &protocol_squisher_ir::ContainerType,
) -> Result<TransportClass, AnalyzerError> {
    use protocol_squisher_ir::ContainerType;

    match (pydantic, rust) {
        // Option<T> analysis
        (ContainerType::Option(pydantic_inner), ContainerType::Option(rust_inner)) => {
            // Option container itself is zero-overhead, propagate inner type's class
            analyze_transport_compatibility(ctx, pydantic_inner, rust_inner)
        }

        // Vec<T> / List<T> analysis
        (ContainerType::Vec(pydantic_inner), ContainerType::Vec(rust_inner)) => {
            // Vec has minor overhead even for identical types, but propagate inner class
            let inner_class = analyze_transport_compatibility(ctx, pydantic_inner, rust_inner)?;
            Ok(inner_class) // Propagate inner type's transport class
        }

        // Map<K, V> / Dict<K, V> analysis
        (ContainerType::Map(pydantic_k, pydantic_v), ContainerType::Map(rust_k, rust_v)) => {
            // Analyze both key and value types
            let key_class = analyze_transport_compatibility(ctx, pydantic_k, rust_k)?;
            let val_class = analyze_transport_compatibility(ctx, pydantic_v, rust_v)?;

            // Return the worst transport class
            Ok(worst_transport_class(key_class, val_class))
        }

        // Tuple analysis
        (ContainerType::Tuple(pydantic_elems), ContainerType::Tuple(rust_elems)) => {
            // Tuples must have same number of elements
            if pydantic_elems.len() != rust_elems.len() {
                return Ok(TransportClass::Wheelbarrow);
            }

            // Analyze each element pair and return worst class
            let mut worst_class = TransportClass::Concorde;
            for (pydantic_elem, rust_elem) in pydantic_elems.iter().zip(rust_elems.iter()) {
                let elem_class = analyze_transport_compatibility(ctx, pydantic_elem, rust_elem)?;
                worst_class = worst_transport_class(worst_class, elem_class);
            }
            Ok(worst_class)
        }

        // Mismatched container types (Vec vs Option, etc.) - always Wheelbarrow
        _ => Ok(TransportClass::Wheelbarrow),
    }
}

/// Return the worst (highest numeric value) transport class
fn worst_transport_class(a: TransportClass, b: TransportClass) -> TransportClass {
    if (a as u8) > (b as u8) {
        a
    } else {
        b
    }
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

    #[test]
    fn test_python_optional_to_rust_option_identical() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let i64_type = IrType::Primitive(IrPrim::I64);
        let py_optional = IrType::Container(ContainerType::Option(Box::new(i64_type.clone())));
        let rust_option = IrType::Container(ContainerType::Option(Box::new(i64_type)));

        let class = analyze_transport_compatibility(&ctx, &py_optional, &rust_option).unwrap();
        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_python_optional_to_rust_option_narrowing() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let py_optional = IrType::Container(ContainerType::Option(Box::new(
            IrType::Primitive(IrPrim::I64)
        )));
        let rust_option = IrType::Container(ContainerType::Option(Box::new(
            IrType::Primitive(IrPrim::I32)
        )));

        let class = analyze_transport_compatibility(&ctx, &py_optional, &rust_option).unwrap();
        assert_eq!(class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_python_list_to_rust_vec_identical() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let i64_type = IrType::Primitive(IrPrim::I64);
        let py_list = IrType::Container(ContainerType::Vec(Box::new(i64_type.clone())));
        let rust_vec = IrType::Container(ContainerType::Vec(Box::new(i64_type)));

        let class = analyze_transport_compatibility(&ctx, &py_list, &rust_vec).unwrap();
        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_python_list_to_rust_vec_narrowing() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let py_list = IrType::Container(ContainerType::Vec(Box::new(
            IrType::Primitive(IrPrim::I64)
        )));
        let rust_vec = IrType::Container(ContainerType::Vec(Box::new(
            IrType::Primitive(IrPrim::I32)
        )));

        let class = analyze_transport_compatibility(&ctx, &py_list, &rust_vec).unwrap();
        assert_eq!(class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_python_dict_to_rust_map_with_narrowing() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let py_dict = IrType::Container(ContainerType::Map(
            Box::new(IrType::Primitive(IrPrim::String)),
            Box::new(IrType::Primitive(IrPrim::I64)),
        ));
        let rust_map = IrType::Container(ContainerType::Map(
            Box::new(IrType::Primitive(IrPrim::String)),
            Box::new(IrType::Primitive(IrPrim::I32)),
        ));

        let class = analyze_transport_compatibility(&ctx, &py_dict, &rust_map).unwrap();
        assert_eq!(class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_python_tuple_to_rust_tuple_with_narrowing() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let py_tuple = IrType::Container(ContainerType::Tuple(vec![
            IrType::Primitive(IrPrim::I64),
            IrType::Primitive(IrPrim::String),
        ]));
        let rust_tuple = IrType::Container(ContainerType::Tuple(vec![
            IrType::Primitive(IrPrim::I32), // Narrowing!
            IrType::Primitive(IrPrim::String),
        ]));

        let class = analyze_transport_compatibility(&ctx, &py_tuple, &rust_tuple).unwrap();
        assert_eq!(class, TransportClass::Wheelbarrow);
    }
}
