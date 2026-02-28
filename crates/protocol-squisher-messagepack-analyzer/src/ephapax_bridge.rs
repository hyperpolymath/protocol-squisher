// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Bridge between protocol-squisher IR and ephapax IR for MessagePack
//!
//! This module demonstrates how MessagePack's dynamic typing (schema-less format)
//! results in Wheelbarrow class transport for nearly all conversions, since
//! there's no compile-time schema to guarantee type safety.

use crate::AnalyzerError;
use protocol_squisher_ir::IrType;
use protocol_squisher_transport_primitives::{IRContext, PrimitiveType, TransportClass};

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
                IrPrim::Bytes
                | IrPrim::DateTime
                | IrPrim::Date
                | IrPrim::Time
                | IrPrim::Duration
                | IrPrim::Uuid
                | IrPrim::Decimal
                | IrPrim::BigInt => None,
            }
        },
        IrType::Special(protocol_squisher_ir::SpecialType::Unit) => Some(PrimitiveType::Unit),
        // Containers and other complex types don't map to primitives
        _ => None,
    }
}

/// Analyze transport compatibility between two IR types
///
/// For MessagePack, this almost always returns Wheelbarrow because:
/// 1. MessagePack has no compile-time schema
/// 2. Type information is dynamic (embedded in binary format)
/// 3. Any field can be any type at runtime
/// 4. No static validation is possible
///
/// This demonstrates the high-squishability end of the diversity spectrum.
pub fn analyze_transport_compatibility(
    ctx: &IRContext,
    source: &IrType,
    target: &IrType,
) -> Result<TransportClass, AnalyzerError> {
    use protocol_squisher_ir::IrType;

    // MessagePack special case: Any type always requires Wheelbarrow
    if is_any_type(source) || is_any_type(target) {
        return Ok(TransportClass::Wheelbarrow);
    }

    match (source, target) {
        // Primitive types - use ephapax analysis
        (IrType::Primitive(_), IrType::Primitive(_)) | (IrType::Special(_), IrType::Special(_)) => {
            // Even for primitives, MessagePack requires runtime validation
            // because the schema is not enforced at compile time
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

            let base_class = ctx.analyze_compatibility(source_prim, target_prim);

            // For MessagePack, even Concorde-level primitive matches
            // get downgraded to Wheelbarrow due to lack of schema enforcement
            // UNLESS both source and target explicitly validate the types
            match base_class {
                TransportClass::Concorde => {
                    // Identical types still need runtime validation in MessagePack
                    Ok(TransportClass::Wheelbarrow)
                },
                TransportClass::Business => Ok(TransportClass::Wheelbarrow),
                TransportClass::Economy => Ok(TransportClass::Wheelbarrow),
                TransportClass::Wheelbarrow => Ok(TransportClass::Wheelbarrow),
            }
        },

        // Container types - recursive analysis
        (IrType::Container(source_container), IrType::Container(target_container)) => {
            analyze_container_compatibility(ctx, source_container, target_container)
        },

        // Mismatched types (primitive vs container) - always Wheelbarrow
        _ => Ok(TransportClass::Wheelbarrow),
    }
}

/// Check if a type is the Any/Dynamic type
fn is_any_type(ty: &IrType) -> bool {
    matches!(ty, IrType::Special(protocol_squisher_ir::SpecialType::Any))
}

/// Analyze compatibility between two container types
///
/// For MessagePack, containers always result in Wheelbarrow because
/// the dynamic typing means no compile-time guarantees about element types.
fn analyze_container_compatibility(
    ctx: &IRContext,
    source: &protocol_squisher_ir::ContainerType,
    target: &protocol_squisher_ir::ContainerType,
) -> Result<TransportClass, AnalyzerError> {
    use protocol_squisher_ir::ContainerType;

    match (source, target) {
        // Option<T> analysis
        (ContainerType::Option(source_inner), ContainerType::Option(target_inner)) => {
            // Even with identical inner types, MessagePack needs runtime checks
            let _inner_class = analyze_transport_compatibility(ctx, source_inner, target_inner)?;
            // Always Wheelbarrow due to dynamic typing
            Ok(TransportClass::Wheelbarrow)
        },

        // Vec<T> analysis
        (ContainerType::Vec(source_inner), ContainerType::Vec(target_inner)) => {
            // MessagePack arrays are dynamically typed
            let _inner_class = analyze_transport_compatibility(ctx, source_inner, target_inner)?;
            // Always Wheelbarrow - array elements can be any type
            Ok(TransportClass::Wheelbarrow)
        },

        // Map<K, V> analysis
        (ContainerType::Map(source_k, source_v), ContainerType::Map(target_k, target_v)) => {
            // MessagePack maps are dynamically typed for both keys and values
            let _key_class = analyze_transport_compatibility(ctx, source_k, target_k)?;
            let _val_class = analyze_transport_compatibility(ctx, source_v, target_v)?;
            // Always Wheelbarrow - no compile-time type guarantees
            Ok(TransportClass::Wheelbarrow)
        },

        // Tuple analysis
        (ContainerType::Tuple(source_elems), ContainerType::Tuple(target_elems)) => {
            // MessagePack doesn't have native tuple support - uses arrays
            if source_elems.len() != target_elems.len() {
                return Ok(TransportClass::Wheelbarrow);
            }

            // Even with matching element counts, dynamic typing means Wheelbarrow
            Ok(TransportClass::Wheelbarrow)
        },

        // Mismatched container types - always Wheelbarrow
        _ => Ok(TransportClass::Wheelbarrow),
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
    pub fn new(ctx: &IRContext, source: &IrType, target: &IrType) -> Result<Self, AnalyzerError> {
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
    ///
    /// For MessagePack, this is always false due to dynamic typing
    pub fn is_zero_copy(&self) -> bool {
        matches!(self.class, TransportClass::Concorde)
    }

    /// Check if this is a safe conversion (Concorde or Business)
    ///
    /// For MessagePack, this is rare due to lack of schema enforcement
    pub fn is_safe(&self) -> bool {
        matches!(
            self.class,
            TransportClass::Concorde | TransportClass::Business
        )
    }

    /// Check if JSON fallback is required (Wheelbarrow)
    ///
    /// For MessagePack, this is almost always true
    pub fn requires_json_fallback(&self) -> bool {
        matches!(self.class, TransportClass::Wheelbarrow)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::PrimitiveType as IrPrim;

    #[test]
    fn test_identical_primitives_require_wheelbarrow() {
        // Even identical types need Wheelbarrow due to dynamic typing
        let ctx = IRContext::new();
        let i64_type = IrType::Primitive(IrPrim::I64);

        let analysis = TransportAnalysis::new(&ctx, &i64_type, &i64_type).unwrap();

        // MessagePack: even exact matches need runtime validation
        assert!(!analysis.is_zero_copy());
        assert!(!analysis.is_safe());
        assert!(analysis.requires_json_fallback());
        assert_eq!(analysis.class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_any_type_always_wheelbarrow() {
        let ctx = IRContext::new();
        let any_type = IrType::Special(protocol_squisher_ir::SpecialType::Any);
        let i64_type = IrType::Primitive(IrPrim::I64);

        let analysis = TransportAnalysis::new(&ctx, &any_type, &i64_type).unwrap();

        assert!(analysis.requires_json_fallback());
        assert_eq!(analysis.class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_vec_always_wheelbarrow() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let vec_i64 =
            IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(IrPrim::I64))));

        let analysis = TransportAnalysis::new(&ctx, &vec_i64, &vec_i64).unwrap();

        // Even identical Vec types need Wheelbarrow in MessagePack
        assert!(analysis.requires_json_fallback());
        assert_eq!(analysis.class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_map_always_wheelbarrow() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let map_type = IrType::Container(ContainerType::Map(
            Box::new(IrType::Primitive(IrPrim::String)),
            Box::new(IrType::Primitive(IrPrim::I64)),
        ));

        let analysis = TransportAnalysis::new(&ctx, &map_type, &map_type).unwrap();

        assert!(analysis.requires_json_fallback());
        assert_eq!(analysis.class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_option_always_wheelbarrow() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let opt_string = IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
            IrPrim::String,
        ))));

        let analysis = TransportAnalysis::new(&ctx, &opt_string, &opt_string).unwrap();

        assert!(analysis.requires_json_fallback());
        assert_eq!(analysis.class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_dynamic_array_wheelbarrow() {
        use protocol_squisher_ir::ContainerType;

        let ctx = IRContext::new();
        let dynamic_array = IrType::Container(ContainerType::Vec(Box::new(IrType::Special(
            protocol_squisher_ir::SpecialType::Any,
        ))));

        let i64_array =
            IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(IrPrim::I64))));

        let analysis = TransportAnalysis::new(&ctx, &dynamic_array, &i64_array).unwrap();

        assert!(analysis.requires_json_fallback());
        assert_eq!(analysis.class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_string_to_string_wheelbarrow() {
        // Unlike schema-based formats, MessagePack strings need runtime validation
        let ctx = IRContext::new();
        let string_type = IrType::Primitive(IrPrim::String);

        let analysis = TransportAnalysis::new(&ctx, &string_type, &string_type).unwrap();

        assert!(analysis.requires_json_fallback());
        assert_eq!(analysis.class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_fidelity_and_overhead() {
        let ctx = IRContext::new();
        let i64_type = IrType::Primitive(IrPrim::I64);

        let analysis = TransportAnalysis::new(&ctx, &i64_type, &i64_type).unwrap();

        // Wheelbarrow class has low fidelity and high overhead
        assert_eq!(analysis.fidelity, 50);
        assert_eq!(analysis.overhead, 80);
    }

    #[test]
    fn test_mismatched_types_wheelbarrow() {
        let ctx = IRContext::new();
        let i64_type = IrType::Primitive(IrPrim::I64);
        let string_type = IrType::Primitive(IrPrim::String);

        let analysis = TransportAnalysis::new(&ctx, &i64_type, &string_type).unwrap();

        assert!(analysis.requires_json_fallback());
        assert_eq!(analysis.class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_messagepack_demonstrates_high_squishability() {
        // This test demonstrates MessagePack's position on the diversity spectrum:
        // High squishability (everything needs JSON fallback) due to schema-less design

        let ctx = IRContext::new();

        // Test several different type combinations
        let test_cases = vec![
            (
                IrType::Primitive(IrPrim::I64),
                IrType::Primitive(IrPrim::I64),
            ),
            (
                IrType::Primitive(IrPrim::String),
                IrType::Primitive(IrPrim::String),
            ),
            (
                IrType::Primitive(IrPrim::Bool),
                IrType::Primitive(IrPrim::Bool),
            ),
        ];

        for (source, target) in test_cases {
            let class = analyze_transport_compatibility(&ctx, &source, &target).unwrap();
            assert_eq!(
                class,
                TransportClass::Wheelbarrow,
                "MessagePack should always use Wheelbarrow due to dynamic typing"
            );
        }
    }
}
