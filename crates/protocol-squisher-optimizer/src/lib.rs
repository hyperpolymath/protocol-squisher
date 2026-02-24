// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! # Protocol Squisher Optimizer
//!
//! Optimization layer for generating Concorde-class adapters.
//!
//! When types are compatible enough, we can do better than JSON fallback.
//! This crate detects optimization opportunities and generates efficient
//! adapter code.
//!
//! ## Optimization Levels
//!
//! - **ZeroCopy**: Types are memory-compatible, no transformation needed
//! - **DirectCast**: Simple type conversion (e.g., i32 → i64)
//! - **StructuralMatch**: Fields align, just need field-level conversion
//! - **ContainerMatch**: Same container type, optimize inner elements
//! - **Fallback**: Use JSON serialization (always works)

use protocol_squisher_compat::TransportClass;
use protocol_squisher_ir::{
    ContainerType, IrSchema, IrType, PrimitiveType, SpecialType, TypeDef, TypeId,
};
use std::collections::HashMap;

mod analysis;
pub mod ai_assist;
mod codegen;
pub mod entropy;
mod ephapax_optimizer;

pub use analysis::*;
pub use ai_assist::*;
pub use codegen::*;
pub use entropy::analyze_schema_entropy;
pub use ephapax_optimizer::*;

/// Optimization level for a type conversion
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum OptimizationLevel {
    /// Types are memory-compatible, zero transformation
    ZeroCopy,
    /// Simple cast or conversion (e.g., numeric widening)
    DirectCast,
    /// Struct fields align, convert field-by-field
    StructuralMatch,
    /// Container types match, optimize inner elements
    ContainerMatch,
    /// Must use JSON fallback
    Fallback,
}

impl OptimizationLevel {
    /// Convert to transport class equivalent
    pub fn to_transport_class(&self) -> TransportClass {
        match self {
            OptimizationLevel::ZeroCopy => TransportClass::Concorde,
            OptimizationLevel::DirectCast => TransportClass::Concorde,
            OptimizationLevel::StructuralMatch => TransportClass::BusinessClass,
            OptimizationLevel::ContainerMatch => TransportClass::BusinessClass,
            OptimizationLevel::Fallback => TransportClass::Wheelbarrow,
        }
    }

    /// Whether this optimization avoids JSON serialization
    pub fn is_optimized(&self) -> bool {
        !matches!(self, OptimizationLevel::Fallback)
    }
}

/// Describes how to convert between two types
#[derive(Debug, Clone)]
pub struct ConversionPath {
    /// Source type
    pub source: IrType,
    /// Target type
    pub target: IrType,
    /// Optimization level achieved
    pub level: OptimizationLevel,
    /// Specific conversion strategy
    pub strategy: ConversionStrategy,
    /// Nested conversions for composite types
    pub nested: Vec<ConversionPath>,
}

/// Specific strategy for type conversion
#[derive(Debug, Clone)]
pub enum ConversionStrategy {
    /// No conversion needed (identical types)
    Identity,
    /// Numeric cast (widening or narrowing)
    NumericCast { checked: bool },
    /// String encoding conversion
    StringConvert,
    /// Option wrapping/unwrapping
    OptionWrap,
    /// Container element-wise conversion
    ContainerMap,
    /// Struct field-by-field conversion
    StructConvert { field_mappings: Vec<FieldMapping> },
    /// Enum variant mapping
    EnumConvert {
        variant_mappings: Vec<VariantMapping>,
    },
    /// JSON serialization fallback
    JsonFallback,
}

/// How to map a struct field
#[derive(Debug, Clone)]
pub struct FieldMapping {
    /// Source field name
    pub source_name: String,
    /// Target field name
    pub target_name: String,
    /// Conversion for this field
    pub conversion: Box<ConversionPath>,
}

/// How to map an enum variant
#[derive(Debug, Clone)]
pub struct VariantMapping {
    /// Source variant name
    pub source_name: String,
    /// Target variant name
    pub target_name: String,
    /// Payload conversion if applicable
    pub payload_conversion: Option<Box<ConversionPath>>,
}

/// Optimizer for finding best conversion paths
#[derive(Debug, Default)]
pub struct Optimizer {
    /// Cached conversion paths
    cache: HashMap<(TypeId, TypeId), ConversionPath>,
}

impl Optimizer {
    /// Create a new optimizer
    pub fn new() -> Self {
        Self::default()
    }

    /// Find the best conversion path between two types
    pub fn find_path(
        &mut self,
        source_schema: &IrSchema,
        target_schema: &IrSchema,
        source_type: &TypeId,
        target_type: &TypeId,
    ) -> ConversionPath {
        // Check cache first
        let cache_key = (source_type.clone(), target_type.clone());
        if let Some(cached) = self.cache.get(&cache_key) {
            return cached.clone();
        }

        // Get type definitions
        let source_def = source_schema.types.get(source_type);
        let target_def = target_schema.types.get(target_type);

        let path = match (source_def, target_def) {
            (Some(src), Some(tgt)) => self.analyze_type_pair(src, tgt),
            _ => ConversionPath {
                source: IrType::Reference(source_type.clone()),
                target: IrType::Reference(target_type.clone()),
                level: OptimizationLevel::Fallback,
                strategy: ConversionStrategy::JsonFallback,
                nested: vec![],
            },
        };

        self.cache.insert(cache_key, path.clone());
        path
    }

    /// Analyze a pair of type definitions
    fn analyze_type_pair(&self, source: &TypeDef, target: &TypeDef) -> ConversionPath {
        match (source, target) {
            (TypeDef::Struct(s), TypeDef::Struct(t)) => self.analyze_struct_pair(s, t),
            (TypeDef::Enum(s), TypeDef::Enum(t)) => self.analyze_enum_pair(s, t),
            (TypeDef::Alias(s), TypeDef::Alias(t)) => self.analyze_ir_types(&s.target, &t.target),
            (TypeDef::Newtype(s), TypeDef::Newtype(t)) => self.analyze_ir_types(&s.inner, &t.inner),
            _ => ConversionPath {
                source: IrType::Special(SpecialType::Any),
                target: IrType::Special(SpecialType::Any),
                level: OptimizationLevel::Fallback,
                strategy: ConversionStrategy::JsonFallback,
                nested: vec![],
            },
        }
    }

    /// Analyze struct pair for field-level optimization
    fn analyze_struct_pair(
        &self,
        source: &protocol_squisher_ir::StructDef,
        target: &protocol_squisher_ir::StructDef,
    ) -> ConversionPath {
        let mut field_mappings = Vec::new();
        let mut worst_level = OptimizationLevel::ZeroCopy;
        let mut all_matched = true;

        // Try to match each target field with a source field
        for target_field in &target.fields {
            let source_field = source.fields.iter().find(|f| f.name == target_field.name);

            match source_field {
                Some(sf) => {
                    let field_path = self.analyze_ir_types(&sf.ty, &target_field.ty);
                    if field_path.level > worst_level {
                        worst_level = field_path.level;
                    }
                    field_mappings.push(FieldMapping {
                        source_name: sf.name.clone(),
                        target_name: target_field.name.clone(),
                        conversion: Box::new(field_path),
                    });
                },
                None if target_field.optional => {
                    // Optional field with no source - that's fine
                    field_mappings.push(FieldMapping {
                        source_name: String::new(),
                        target_name: target_field.name.clone(),
                        conversion: Box::new(ConversionPath {
                            source: IrType::Special(SpecialType::Unit),
                            target: target_field.ty.clone(),
                            level: OptimizationLevel::DirectCast,
                            strategy: ConversionStrategy::OptionWrap,
                            nested: vec![],
                        }),
                    });
                },
                None => {
                    // Required field missing - fallback
                    all_matched = false;
                    break;
                },
            }
        }

        if !all_matched {
            return ConversionPath {
                source: IrType::Reference(source.name.clone()),
                target: IrType::Reference(target.name.clone()),
                level: OptimizationLevel::Fallback,
                strategy: ConversionStrategy::JsonFallback,
                nested: vec![],
            };
        }

        // All zero-copy fields means zero-copy struct
        let level = if worst_level == OptimizationLevel::ZeroCopy
            && source.fields.len() == target.fields.len()
        {
            OptimizationLevel::ZeroCopy
        } else {
            OptimizationLevel::StructuralMatch.max(worst_level)
        };

        ConversionPath {
            source: IrType::Reference(source.name.clone()),
            target: IrType::Reference(target.name.clone()),
            level,
            strategy: ConversionStrategy::StructConvert { field_mappings },
            nested: vec![],
        }
    }

    /// Analyze enum pair for variant-level optimization
    fn analyze_enum_pair(
        &self,
        source: &protocol_squisher_ir::EnumDef,
        target: &protocol_squisher_ir::EnumDef,
    ) -> ConversionPath {
        let mut variant_mappings = Vec::new();
        let mut worst_level = OptimizationLevel::ZeroCopy;

        // Check if all source variants exist in target
        for source_variant in &source.variants {
            let target_variant = target
                .variants
                .iter()
                .find(|v| v.name == source_variant.name);

            match target_variant {
                Some(tv) => {
                    let payload_conversion = match (&source_variant.payload, &tv.payload) {
                        (None, None) => None,
                        (Some(sp), Some(tp)) => {
                            let path = self.analyze_payload_pair(sp, tp);
                            if path.level > worst_level {
                                worst_level = path.level;
                            }
                            Some(Box::new(path))
                        },
                        _ => {
                            worst_level = OptimizationLevel::Fallback;
                            None
                        },
                    };

                    variant_mappings.push(VariantMapping {
                        source_name: source_variant.name.clone(),
                        target_name: tv.name.clone(),
                        payload_conversion,
                    });
                },
                None => {
                    // Variant not found in target - fallback
                    return ConversionPath {
                        source: IrType::Reference(source.name.clone()),
                        target: IrType::Reference(target.name.clone()),
                        level: OptimizationLevel::Fallback,
                        strategy: ConversionStrategy::JsonFallback,
                        nested: vec![],
                    };
                },
            }
        }

        let level = if worst_level == OptimizationLevel::ZeroCopy
            && source.variants.len() == target.variants.len()
            && source.tag_style == target.tag_style
        {
            OptimizationLevel::ZeroCopy
        } else {
            OptimizationLevel::StructuralMatch.max(worst_level)
        };

        ConversionPath {
            source: IrType::Reference(source.name.clone()),
            target: IrType::Reference(target.name.clone()),
            level,
            strategy: ConversionStrategy::EnumConvert { variant_mappings },
            nested: vec![],
        }
    }

    /// Analyze variant payload pair
    fn analyze_payload_pair(
        &self,
        source: &protocol_squisher_ir::VariantPayload,
        target: &protocol_squisher_ir::VariantPayload,
    ) -> ConversionPath {
        use protocol_squisher_ir::VariantPayload;

        match (source, target) {
            (VariantPayload::Tuple(st), VariantPayload::Tuple(tt)) => {
                if st.len() != tt.len() {
                    return ConversionPath {
                        source: IrType::Special(SpecialType::Any),
                        target: IrType::Special(SpecialType::Any),
                        level: OptimizationLevel::Fallback,
                        strategy: ConversionStrategy::JsonFallback,
                        nested: vec![],
                    };
                }

                let mut nested = Vec::new();
                let mut worst = OptimizationLevel::ZeroCopy;

                for (s, t) in st.iter().zip(tt.iter()) {
                    let path = self.analyze_ir_types(s, t);
                    if path.level > worst {
                        worst = path.level;
                    }
                    nested.push(path);
                }

                ConversionPath {
                    source: IrType::Container(ContainerType::Tuple(st.clone())),
                    target: IrType::Container(ContainerType::Tuple(tt.clone())),
                    level: worst,
                    strategy: ConversionStrategy::ContainerMap,
                    nested,
                }
            },
            (VariantPayload::Struct(sf), VariantPayload::Struct(tf)) => {
                // Treat as inline struct
                let source_struct = protocol_squisher_ir::StructDef {
                    name: "payload".to_string(),
                    fields: sf.clone(),
                    metadata: protocol_squisher_ir::TypeMetadata::default(),
                };
                let target_struct = protocol_squisher_ir::StructDef {
                    name: "payload".to_string(),
                    fields: tf.clone(),
                    metadata: protocol_squisher_ir::TypeMetadata::default(),
                };
                self.analyze_struct_pair(&source_struct, &target_struct)
            },
            _ => ConversionPath {
                source: IrType::Special(SpecialType::Any),
                target: IrType::Special(SpecialType::Any),
                level: OptimizationLevel::Fallback,
                strategy: ConversionStrategy::JsonFallback,
                nested: vec![],
            },
        }
    }

    /// Analyze two IR types for conversion opportunities
    fn analyze_ir_types(&self, source: &IrType, target: &IrType) -> ConversionPath {
        match (source, target) {
            // Identical types - zero copy
            (s, t) if s == t => ConversionPath {
                source: s.clone(),
                target: t.clone(),
                level: OptimizationLevel::ZeroCopy,
                strategy: ConversionStrategy::Identity,
                nested: vec![],
            },

            // Primitive conversions
            (IrType::Primitive(sp), IrType::Primitive(tp)) => self.analyze_primitive_pair(sp, tp),

            // Container conversions
            (IrType::Container(sc), IrType::Container(tc)) => self.analyze_container_pair(sc, tc),

            // Type references - would need schema lookup
            (IrType::Reference(_), IrType::Reference(_)) => ConversionPath {
                source: source.clone(),
                target: target.clone(),
                level: OptimizationLevel::StructuralMatch,
                strategy: ConversionStrategy::JsonFallback,
                nested: vec![],
            },

            // Everything else - fallback
            _ => ConversionPath {
                source: source.clone(),
                target: target.clone(),
                level: OptimizationLevel::Fallback,
                strategy: ConversionStrategy::JsonFallback,
                nested: vec![],
            },
        }
    }

    /// Analyze primitive type pair
    fn analyze_primitive_pair(
        &self,
        source: &PrimitiveType,
        target: &PrimitiveType,
    ) -> ConversionPath {
        let (level, checked) = match (source, target) {
            // Same type
            (s, t) if s == t => (OptimizationLevel::ZeroCopy, false),

            // Integer widening (safe)
            (
                PrimitiveType::I8,
                PrimitiveType::I16 | PrimitiveType::I32 | PrimitiveType::I64 | PrimitiveType::I128,
            )
            | (PrimitiveType::I16, PrimitiveType::I32 | PrimitiveType::I64 | PrimitiveType::I128)
            | (PrimitiveType::I32, PrimitiveType::I64 | PrimitiveType::I128)
            | (PrimitiveType::I64, PrimitiveType::I128)
            | (
                PrimitiveType::U8,
                PrimitiveType::U16 | PrimitiveType::U32 | PrimitiveType::U64 | PrimitiveType::U128,
            )
            | (PrimitiveType::U16, PrimitiveType::U32 | PrimitiveType::U64 | PrimitiveType::U128)
            | (PrimitiveType::U32, PrimitiveType::U64 | PrimitiveType::U128)
            | (PrimitiveType::U64, PrimitiveType::U128)
            | (PrimitiveType::F32, PrimitiveType::F64) => (OptimizationLevel::DirectCast, false),

            // Integer narrowing (needs check)
            (
                PrimitiveType::I128,
                PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::I16 | PrimitiveType::I8,
            )
            | (PrimitiveType::I64, PrimitiveType::I32 | PrimitiveType::I16 | PrimitiveType::I8)
            | (PrimitiveType::I32, PrimitiveType::I16 | PrimitiveType::I8)
            | (PrimitiveType::I16, PrimitiveType::I8)
            | (
                PrimitiveType::U128,
                PrimitiveType::U64 | PrimitiveType::U32 | PrimitiveType::U16 | PrimitiveType::U8,
            )
            | (PrimitiveType::U64, PrimitiveType::U32 | PrimitiveType::U16 | PrimitiveType::U8)
            | (PrimitiveType::U32, PrimitiveType::U16 | PrimitiveType::U8)
            | (PrimitiveType::U16, PrimitiveType::U8)
            | (PrimitiveType::F64, PrimitiveType::F32) => (OptimizationLevel::DirectCast, true),

            // Unsigned to signed widening
            (
                PrimitiveType::U8,
                PrimitiveType::I16 | PrimitiveType::I32 | PrimitiveType::I64 | PrimitiveType::I128,
            )
            | (PrimitiveType::U16, PrimitiveType::I32 | PrimitiveType::I64 | PrimitiveType::I128)
            | (PrimitiveType::U32, PrimitiveType::I64 | PrimitiveType::I128)
            | (PrimitiveType::U64, PrimitiveType::I128) => (OptimizationLevel::DirectCast, false),

            // String types are compatible
            (PrimitiveType::String, PrimitiveType::String) => (OptimizationLevel::ZeroCopy, false),

            // Everything else needs fallback
            _ => (OptimizationLevel::Fallback, false),
        };

        let strategy = match level {
            OptimizationLevel::ZeroCopy => ConversionStrategy::Identity,
            OptimizationLevel::DirectCast => ConversionStrategy::NumericCast { checked },
            _ => ConversionStrategy::JsonFallback,
        };

        ConversionPath {
            source: IrType::Primitive(*source),
            target: IrType::Primitive(*target),
            level,
            strategy,
            nested: vec![],
        }
    }

    /// Analyze container type pair
    fn analyze_container_pair(
        &self,
        source: &ContainerType,
        target: &ContainerType,
    ) -> ConversionPath {
        match (source, target) {
            // Option<T> conversions
            (ContainerType::Option(s), ContainerType::Option(t)) => {
                let inner = self.analyze_ir_types(s, t);
                ConversionPath {
                    source: IrType::Container(source.clone()),
                    target: IrType::Container(target.clone()),
                    level: inner.level,
                    strategy: ConversionStrategy::ContainerMap,
                    nested: vec![inner],
                }
            },

            // Vec<T> conversions
            (ContainerType::Vec(s), ContainerType::Vec(t)) => {
                let inner = self.analyze_ir_types(s, t);
                ConversionPath {
                    source: IrType::Container(source.clone()),
                    target: IrType::Container(target.clone()),
                    level: inner.level.max(OptimizationLevel::ContainerMatch),
                    strategy: ConversionStrategy::ContainerMap,
                    nested: vec![inner],
                }
            },

            // Map conversions
            (ContainerType::Map(sk, sv), ContainerType::Map(tk, tv)) => {
                let key_path = self.analyze_ir_types(sk, tk);
                let val_path = self.analyze_ir_types(sv, tv);
                let level = key_path
                    .level
                    .max(val_path.level)
                    .max(OptimizationLevel::ContainerMatch);

                ConversionPath {
                    source: IrType::Container(source.clone()),
                    target: IrType::Container(target.clone()),
                    level,
                    strategy: ConversionStrategy::ContainerMap,
                    nested: vec![key_path, val_path],
                }
            },

            // Tuple conversions
            (ContainerType::Tuple(st), ContainerType::Tuple(tt)) if st.len() == tt.len() => {
                let mut nested = Vec::new();
                let mut worst = OptimizationLevel::ZeroCopy;

                for (s, t) in st.iter().zip(tt.iter()) {
                    let path = self.analyze_ir_types(s, t);
                    if path.level > worst {
                        worst = path.level;
                    }
                    nested.push(path);
                }

                ConversionPath {
                    source: IrType::Container(source.clone()),
                    target: IrType::Container(target.clone()),
                    level: worst,
                    strategy: ConversionStrategy::ContainerMap,
                    nested,
                }
            },

            // Everything else
            _ => ConversionPath {
                source: IrType::Container(source.clone()),
                target: IrType::Container(target.clone()),
                level: OptimizationLevel::Fallback,
                strategy: ConversionStrategy::JsonFallback,
                nested: vec![],
            },
        }
    }
}

/// Result of optimization analysis for a schema pair
#[derive(Debug, Clone)]
pub struct OptimizationResult {
    /// Overall optimization level achieved
    pub overall_level: OptimizationLevel,
    /// Transport class equivalent
    pub transport_class: TransportClass,
    /// Per-type conversion paths
    pub type_paths: HashMap<TypeId, ConversionPath>,
    /// Types that can use optimized path
    pub optimized_types: Vec<TypeId>,
    /// Types that must use fallback
    pub fallback_types: Vec<TypeId>,
}

/// Analyze two schemas and find optimization opportunities
pub fn analyze_optimization(source: &IrSchema, target: &IrSchema) -> OptimizationResult {
    let mut optimizer = Optimizer::new();
    let mut type_paths = HashMap::new();
    let mut optimized_types = Vec::new();
    let mut fallback_types = Vec::new();
    let mut worst_level = OptimizationLevel::ZeroCopy;

    // Find matching types between schemas
    for source_type_id in source.types.keys() {
        if let Some(_target_def) = target.types.get(source_type_id) {
            let path = optimizer.find_path(source, target, source_type_id, source_type_id);

            if path.level.is_optimized() {
                optimized_types.push(source_type_id.clone());
            } else {
                fallback_types.push(source_type_id.clone());
            }

            if path.level > worst_level {
                worst_level = path.level;
            }

            type_paths.insert(source_type_id.clone(), path);
        }
    }

    OptimizationResult {
        overall_level: worst_level,
        transport_class: worst_level.to_transport_class(),
        type_paths,
        optimized_types,
        fallback_types,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::*;

    fn make_primitive_type(p: PrimitiveType) -> IrType {
        IrType::Primitive(p)
    }

    #[test]
    fn test_identical_primitives_are_zero_copy() {
        let optimizer = Optimizer::new();
        let path = optimizer.analyze_ir_types(
            &make_primitive_type(PrimitiveType::I32),
            &make_primitive_type(PrimitiveType::I32),
        );
        assert_eq!(path.level, OptimizationLevel::ZeroCopy);
    }

    #[test]
    fn test_integer_widening_is_direct_cast() {
        let optimizer = Optimizer::new();
        let path = optimizer.analyze_ir_types(
            &make_primitive_type(PrimitiveType::I32),
            &make_primitive_type(PrimitiveType::I64),
        );
        assert_eq!(path.level, OptimizationLevel::DirectCast);
        assert!(matches!(
            path.strategy,
            ConversionStrategy::NumericCast { checked: false }
        ));
    }

    #[test]
    fn test_integer_narrowing_needs_check() {
        let optimizer = Optimizer::new();
        let path = optimizer.analyze_ir_types(
            &make_primitive_type(PrimitiveType::I64),
            &make_primitive_type(PrimitiveType::I32),
        );
        assert_eq!(path.level, OptimizationLevel::DirectCast);
        assert!(matches!(
            path.strategy,
            ConversionStrategy::NumericCast { checked: true }
        ));
    }

    #[test]
    fn test_incompatible_primitives_fallback() {
        let optimizer = Optimizer::new();
        let path = optimizer.analyze_ir_types(
            &make_primitive_type(PrimitiveType::String),
            &make_primitive_type(PrimitiveType::I32),
        );
        assert_eq!(path.level, OptimizationLevel::Fallback);
    }

    #[test]
    fn test_vec_optimization() {
        let optimizer = Optimizer::new();
        let path = optimizer.analyze_ir_types(
            &IrType::Container(ContainerType::Vec(Box::new(make_primitive_type(
                PrimitiveType::I32,
            )))),
            &IrType::Container(ContainerType::Vec(Box::new(make_primitive_type(
                PrimitiveType::I64,
            )))),
        );
        // Vec conversion with element widening
        assert_eq!(path.level, OptimizationLevel::ContainerMatch);
    }

    #[test]
    fn test_option_optimization() {
        let optimizer = Optimizer::new();
        let path = optimizer.analyze_ir_types(
            &IrType::Container(ContainerType::Option(Box::new(make_primitive_type(
                PrimitiveType::String,
            )))),
            &IrType::Container(ContainerType::Option(Box::new(make_primitive_type(
                PrimitiveType::String,
            )))),
        );
        assert_eq!(path.level, OptimizationLevel::ZeroCopy);
    }

    #[test]
    fn test_struct_optimization() {
        let optimizer = Optimizer::new();

        let source = StructDef {
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: make_primitive_type(PrimitiveType::I32),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: make_primitive_type(PrimitiveType::I32),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                },
            ],
            metadata: TypeMetadata::default(),
        };

        let target = StructDef {
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: make_primitive_type(PrimitiveType::I64),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: make_primitive_type(PrimitiveType::I64),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                },
            ],
            metadata: TypeMetadata::default(),
        };

        let path = optimizer.analyze_struct_pair(&source, &target);
        assert_eq!(path.level, OptimizationLevel::StructuralMatch);
        assert!(matches!(
            path.strategy,
            ConversionStrategy::StructConvert { .. }
        ));
    }

    #[test]
    fn test_optimization_level_ordering() {
        assert!(OptimizationLevel::ZeroCopy < OptimizationLevel::DirectCast);
        assert!(OptimizationLevel::DirectCast < OptimizationLevel::StructuralMatch);
        assert!(OptimizationLevel::StructuralMatch < OptimizationLevel::ContainerMatch);
        assert!(OptimizationLevel::ContainerMatch < OptimizationLevel::Fallback);
    }

    #[test]
    fn test_transport_class_mapping() {
        assert_eq!(
            OptimizationLevel::ZeroCopy.to_transport_class(),
            TransportClass::Concorde
        );
        assert_eq!(
            OptimizationLevel::DirectCast.to_transport_class(),
            TransportClass::Concorde
        );
        assert_eq!(
            OptimizationLevel::StructuralMatch.to_transport_class(),
            TransportClass::BusinessClass
        );
        assert_eq!(
            OptimizationLevel::Fallback.to_transport_class(),
            TransportClass::Wheelbarrow
        );
    }
}
