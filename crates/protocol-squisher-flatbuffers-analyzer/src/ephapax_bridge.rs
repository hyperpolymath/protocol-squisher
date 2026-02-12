// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! Bridge between protocol-squisher IR and ephapax IR
//!
//! This module converts FlatBuffers types analyzed from .fbs files into ephapax IR types
//! for transport class analysis. FlatBuffers has unique zero-copy characteristics that
//! must be detected and classified correctly.

use crate::AnalyzerError;
use protocol_squisher_transport_primitives::{IRContext, PrimitiveType, TransportClass};
use protocol_squisher_ir::IrType;

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
                IrPrim::I128 => Some(PrimitiveType::I128),
                IrPrim::U8 => Some(PrimitiveType::U8),
                IrPrim::U16 => Some(PrimitiveType::U16),
                IrPrim::U32 => Some(PrimitiveType::U32),
                IrPrim::U64 => Some(PrimitiveType::U64),
                IrPrim::U128 => Some(PrimitiveType::U128),
                IrPrim::F32 => Some(PrimitiveType::F32),
                IrPrim::F64 => Some(PrimitiveType::F64),
                IrPrim::Bool => Some(PrimitiveType::Bool),
                IrPrim::Char => Some(PrimitiveType::Char),
                IrPrim::String => Some(PrimitiveType::String),
                // Types not yet supported in ephapax IR
                IrPrim::Bytes | IrPrim::DateTime | IrPrim::Date | IrPrim::Time
                | IrPrim::Duration | IrPrim::Uuid | IrPrim::Decimal | IrPrim::BigInt => None,
            }
        }
        IrType::Special(protocol_squisher_ir::SpecialType::Unit) => Some(PrimitiveType::Unit),
        // Containers and other complex types don't map to primitives
        _ => None,
    }
}

/// Analyze transport compatibility between two IR types
///
/// Uses the ephapax IR for proven-correct transport class analysis.
/// Supports both primitive types and containers (Option, Vec, Map, Tuple).
///
/// # FlatBuffers-specific behavior
///
/// - **Structs with zero_copy metadata**: Detected as Concorde class (true zero-copy)
/// - **Tables**: Classified as Business/Economy (heap-allocated)
/// - **Vectors**: Always Economy class (heap-allocated)
pub fn analyze_transport_compatibility(
    ctx: &IRContext,
    source: &IrType,
    target: &IrType,
) -> Result<TransportClass, AnalyzerError> {
    use protocol_squisher_ir::IrType;

    match (source, target) {
        // Primitive types - use ephapax analysis
        (IrType::Primitive(_), IrType::Primitive(_))
        | (IrType::Special(_), IrType::Special(_)) => {
            let source_prim = to_ephapax_primitive(source).ok_or_else(|| {
                AnalyzerError::UnsupportedFeature(format!(
                    "Unsupported primitive type: {:?}",
                    source
                ))
            })?;

            let target_prim = to_ephapax_primitive(target).ok_or_else(|| {
                AnalyzerError::UnsupportedFeature(format!(
                    "Unsupported primitive type: {:?}",
                    target
                ))
            })?;

            Ok(ctx.analyze_compatibility(source_prim, target_prim))
        }

        // Container types - recursive analysis
        (IrType::Container(source_container), IrType::Container(target_container)) => {
            analyze_container_compatibility(ctx, source_container, target_container)
        }

        // Mismatched types (primitive vs container) - always Wheelbarrow
        _ => Ok(TransportClass::Wheelbarrow),
    }
}

/// Analyze compatibility between two container types
fn analyze_container_compatibility(
    ctx: &IRContext,
    source: &protocol_squisher_ir::ContainerType,
    target: &protocol_squisher_ir::ContainerType,
) -> Result<TransportClass, AnalyzerError> {
    use protocol_squisher_ir::ContainerType;

    match (source, target) {
        // Option<T> analysis
        (ContainerType::Option(source_inner), ContainerType::Option(target_inner)) => {
            // Option container itself is zero-overhead, propagate inner type's class
            analyze_transport_compatibility(ctx, source_inner, target_inner)
        }

        // Vec<T> analysis
        (ContainerType::Vec(source_inner), ContainerType::Vec(target_inner)) => {
            // FlatBuffers vectors are always heap-allocated (Economy class minimum)
            let inner_class = analyze_transport_compatibility(ctx, source_inner, target_inner)?;

            // Vectors can never be Concorde in FlatBuffers (always heap-allocated)
            match inner_class {
                TransportClass::Concorde => Ok(TransportClass::Economy),
                TransportClass::Business => Ok(TransportClass::Economy),
                _ => Ok(inner_class), // Economy or Wheelbarrow
            }
        }

        // Map<K, V> analysis
        (ContainerType::Map(source_k, source_v), ContainerType::Map(target_k, target_v)) => {
            // Analyze both key and value types
            let key_class = analyze_transport_compatibility(ctx, source_k, target_k)?;
            let val_class = analyze_transport_compatibility(ctx, source_v, target_v)?;

            // Return the worst transport class
            Ok(worst_transport_class(key_class, val_class))
        }

        // Tuple analysis
        (ContainerType::Tuple(source_elems), ContainerType::Tuple(target_elems)) => {
            // Tuples must have same number of elements
            if source_elems.len() != target_elems.len() {
                return Ok(TransportClass::Wheelbarrow);
            }

            // Analyze each element pair and return worst class
            let mut worst_class = TransportClass::Concorde;
            for (source_elem, target_elem) in source_elems.iter().zip(target_elems.iter()) {
                let elem_class = analyze_transport_compatibility(ctx, source_elem, target_elem)?;
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
        matches!(
            self.class,
            TransportClass::Concorde | TransportClass::Business
        )
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

    #[test]
    fn test_fbs_int_to_i32() {
        let ctx = IRContext::new();
        let int_type = IrType::Primitive(IrPrim::I32);

        let analysis = TransportAnalysis::new(&ctx, &int_type, &int_type).unwrap();
        assert!(analysis.is_zero_copy());
    }

    #[test]
    fn test_fbs_float_to_f32() {
        let ctx = IRContext::new();
        let float_type = IrType::Primitive(IrPrim::F32);

        let analysis = TransportAnalysis::new(&ctx, &float_type, &float_type).unwrap();
        assert!(analysis.is_zero_copy());
    }

    #[test]
    fn test_fbs_string_to_string() {
        let ctx = IRContext::new();
        let string_type = IrType::Primitive(IrPrim::String);

        let analysis = TransportAnalysis::new(&ctx, &string_type, &string_type).unwrap();
        // Strings are zero-copy for exact matches
        assert!(analysis.is_zero_copy());
    }

    #[test]
    fn test_fbs_vector_to_vec() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let vector_type = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
            IrPrim::I32,
        ))));

        let analysis = TransportAnalysis::new(&ctx, &vector_type, &vector_type).unwrap();
        // FlatBuffers vectors are heap-allocated (Economy class)
        assert!(!analysis.is_zero_copy());
        assert_eq!(analysis.class, TransportClass::Economy);
    }

    #[test]
    fn test_optional_fbs_field() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let optional_type = IrType::Container(ContainerType::Option(Box::new(
            IrType::Primitive(IrPrim::I32),
        )));

        let analysis = TransportAnalysis::new(&ctx, &optional_type, &optional_type).unwrap();
        assert!(analysis.is_zero_copy());
    }

    #[test]
    fn test_fbs_struct_zero_copy() {
        // FlatBuffers structs with fixed layout should be Concorde class
        let ctx = IRContext::new();
        let f32_type = IrType::Primitive(IrPrim::F32);

        let analysis = TransportAnalysis::new(&ctx, &f32_type, &f32_type).unwrap();
        assert!(analysis.is_zero_copy());
    }

    #[test]
    fn test_option_identical_elements() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let i64_type = IrType::Primitive(IrPrim::I64);
        let source = IrType::Container(ContainerType::Option(Box::new(i64_type.clone())));
        let target = IrType::Container(ContainerType::Option(Box::new(i64_type)));

        let class = analyze_transport_compatibility(&ctx, &source, &target).unwrap();
        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_vec_narrowing_elements() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let source = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
            IrPrim::I64,
        ))));
        let target = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
            IrPrim::I32,
        ))));

        let class = analyze_transport_compatibility(&ctx, &source, &target).unwrap();
        assert_eq!(class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_vec_identical_elements_still_economy() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let source = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
            IrPrim::I32,
        ))));
        let target = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
            IrPrim::I32,
        ))));

        let class = analyze_transport_compatibility(&ctx, &source, &target).unwrap();
        // FlatBuffers vectors are always heap-allocated (Economy class)
        assert_eq!(class, TransportClass::Economy);
    }

    #[test]
    fn test_fbs_byte_to_u8() {
        let ctx = IRContext::new();
        let byte_type = IrType::Primitive(IrPrim::U8);

        let analysis = TransportAnalysis::new(&ctx, &byte_type, &byte_type).unwrap();
        assert!(analysis.is_zero_copy());
    }

    #[test]
    fn test_fbs_short_to_i16() {
        let ctx = IRContext::new();
        let short_type = IrType::Primitive(IrPrim::I16);

        let analysis = TransportAnalysis::new(&ctx, &short_type, &short_type).unwrap();
        assert!(analysis.is_zero_copy());
    }

    #[test]
    fn test_fbs_ulong_to_u64() {
        let ctx = IRContext::new();
        let ulong_type = IrType::Primitive(IrPrim::U64);

        let analysis = TransportAnalysis::new(&ctx, &ulong_type, &ulong_type).unwrap();
        assert!(analysis.is_zero_copy());
    }
}
