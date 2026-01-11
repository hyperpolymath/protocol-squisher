// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Schema-level compatibility analysis
//!
//! Compares entire IR schemas to determine overall compatibility.

use crate::compare::compare_types;
use crate::transport::{ConversionLoss, LossKind, LossSeverity, TransportClass};
use protocol_squisher_ir::{
    EnumDef, FieldDef, IrSchema, StructDef, TypeDef, VariantDef,
};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashSet};

/// Result of comparing two schemas
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchemaComparison {
    /// Source schema name
    pub source: String,
    /// Target schema name
    pub target: String,
    /// Overall transport class
    pub class: TransportClass,
    /// Type-by-type comparisons
    pub type_comparisons: BTreeMap<String, TypeDefComparison>,
    /// All losses across the schema
    pub all_losses: Vec<ConversionLoss>,
    /// Types only in source
    pub source_only: Vec<String>,
    /// Types only in target
    pub target_only: Vec<String>,
}

impl SchemaComparison {
    /// Check if schemas are compatible
    pub fn is_compatible(&self) -> bool {
        self.class.is_convertible()
    }

    /// Get summary statistics
    pub fn summary(&self) -> ComparisonSummary {
        let mut by_class = BTreeMap::new();
        for tc in &self.type_comparisons {
            *by_class.entry(tc.1.class).or_insert(0) += 1;
        }

        let mut by_loss_kind = BTreeMap::new();
        for loss in &self.all_losses {
            *by_loss_kind.entry(loss.kind).or_insert(0) += 1;
        }

        ComparisonSummary {
            total_types: self.type_comparisons.len(),
            types_by_class: by_class,
            total_losses: self.all_losses.len(),
            losses_by_kind: by_loss_kind,
            source_only_count: self.source_only.len(),
            target_only_count: self.target_only.len(),
        }
    }
}

/// Summary statistics for a comparison
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComparisonSummary {
    /// Total number of types compared
    pub total_types: usize,
    /// Count of types by transport class
    pub types_by_class: BTreeMap<TransportClass, usize>,
    /// Total number of losses
    pub total_losses: usize,
    /// Count of losses by kind
    pub losses_by_kind: BTreeMap<LossKind, usize>,
    /// Number of types only in source
    pub source_only_count: usize,
    /// Number of types only in target
    pub target_only_count: usize,
}

/// Comparison result for a type definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeDefComparison {
    /// Type name
    pub name: String,
    /// Transport class for this type
    pub class: TransportClass,
    /// Losses for this type
    pub losses: Vec<ConversionLoss>,
    /// Field-level comparisons (for structs)
    pub field_comparisons: Vec<FieldComparison>,
    /// Variant-level comparisons (for enums)
    pub variant_comparisons: Vec<VariantComparison>,
}

/// Comparison result for a field
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldComparison {
    /// Field name
    pub name: String,
    /// Transport class
    pub class: TransportClass,
    /// Losses
    pub losses: Vec<ConversionLoss>,
}

/// Comparison result for an enum variant
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VariantComparison {
    /// Variant name
    pub name: String,
    /// Transport class
    pub class: TransportClass,
    /// Losses
    pub losses: Vec<ConversionLoss>,
}

/// Compare two schemas
pub fn compare_schemas(source: &IrSchema, target: &IrSchema) -> SchemaComparison {
    let mut result = SchemaComparison {
        source: source.name.clone(),
        target: target.name.clone(),
        class: TransportClass::Concorde,
        type_comparisons: BTreeMap::new(),
        all_losses: Vec::new(),
        source_only: Vec::new(),
        target_only: Vec::new(),
    };

    // Find types in both, source-only, and target-only
    let source_types: HashSet<_> = source.types.keys().collect();
    let target_types: HashSet<_> = target.types.keys().collect();

    for name in source_types.difference(&target_types) {
        result.source_only.push((*name).clone());
        result.all_losses.push(ConversionLoss {
            kind: LossKind::FieldDropped,
            path: (*name).clone(),
            description: format!("Type '{name}' not in target schema"),
            severity: LossSeverity::Major,
        });
        result.class = result.class.combine(TransportClass::Wheelbarrow);
    }

    for name in target_types.difference(&source_types) {
        result.target_only.push((*name).clone());
        // Types only in target are not necessarily a problem
        // They might have defaults or be optional
    }

    // Compare types that exist in both
    for name in source_types.intersection(&target_types) {
        let source_type = source.types.get(*name).unwrap();
        let target_type = target.types.get(*name).unwrap();

        let type_cmp = compare_type_defs(source_type, target_type, name);
        result.class = result.class.combine(type_cmp.class);
        result.all_losses.extend(type_cmp.losses.clone());
        result.type_comparisons.insert((*name).clone(), type_cmp);
    }

    result
}

/// Compare two type definitions
fn compare_type_defs(source: &TypeDef, target: &TypeDef, name: &str) -> TypeDefComparison {
    match (source, target) {
        (TypeDef::Struct(src), TypeDef::Struct(tgt)) => {
            compare_structs(src, tgt, name)
        }
        (TypeDef::Enum(src), TypeDef::Enum(tgt)) => {
            compare_enums(src, tgt, name)
        }
        (TypeDef::Alias(src), TypeDef::Alias(tgt)) => {
            let cmp = compare_types(&src.target, &tgt.target, name);
            TypeDefComparison {
                name: name.to_string(),
                class: cmp.class,
                losses: cmp.losses,
                field_comparisons: vec![],
                variant_comparisons: vec![],
            }
        }
        (TypeDef::Newtype(src), TypeDef::Newtype(tgt)) => {
            let cmp = compare_types(&src.inner, &tgt.inner, name);
            TypeDefComparison {
                name: name.to_string(),
                class: cmp.class,
                losses: cmp.losses,
                field_comparisons: vec![],
                variant_comparisons: vec![],
            }
        }
        // Struct to Newtype (unwrapping)
        (TypeDef::Struct(src), TypeDef::Newtype(tgt)) if src.fields.len() == 1 => {
            let field = &src.fields[0];
            let cmp = compare_types(&field.ty, &tgt.inner, &format!("{name}.{}", field.name));
            let mut losses = cmp.losses;
            losses.push(ConversionLoss {
                kind: LossKind::MetadataLost,
                path: name.to_string(),
                description: "Struct flattened to newtype".to_string(),
                severity: LossSeverity::Minor,
            });
            TypeDefComparison {
                name: name.to_string(),
                class: cmp.class.combine(TransportClass::BusinessClass),
                losses,
                field_comparisons: vec![],
                variant_comparisons: vec![],
            }
        }
        // Newtype to Struct (wrapping)
        (TypeDef::Newtype(src), TypeDef::Struct(tgt)) if tgt.fields.len() == 1 => {
            let field = &tgt.fields[0];
            let cmp = compare_types(&src.inner, &field.ty, &format!("{name}.{}", field.name));
            let mut losses = cmp.losses;
            losses.push(ConversionLoss {
                kind: LossKind::MetadataLost,
                path: name.to_string(),
                description: "Newtype wrapped in struct".to_string(),
                severity: LossSeverity::Minor,
            });
            TypeDefComparison {
                name: name.to_string(),
                class: cmp.class.combine(TransportClass::BusinessClass),
                losses,
                field_comparisons: vec![],
                variant_comparisons: vec![],
            }
        }
        // Incompatible type kinds
        _ => TypeDefComparison {
            name: name.to_string(),
            class: TransportClass::Incompatible,
            losses: vec![ConversionLoss {
                kind: LossKind::TypeCoercion,
                path: name.to_string(),
                description: format!(
                    "Type kind mismatch: {:?} -> {:?}",
                    type_def_kind(source),
                    type_def_kind(target)
                ),
                severity: LossSeverity::Critical,
            }],
            field_comparisons: vec![],
            variant_comparisons: vec![],
        },
    }
}

/// Get a string name for a type def kind
fn type_def_kind(td: &TypeDef) -> &'static str {
    match td {
        TypeDef::Struct(_) => "Struct",
        TypeDef::Enum(_) => "Enum",
        TypeDef::Union(_) => "Union",
        TypeDef::Alias(_) => "Alias",
        TypeDef::Newtype(_) => "Newtype",
    }
}

/// Compare two struct definitions
fn compare_structs(source: &StructDef, target: &StructDef, name: &str) -> TypeDefComparison {
    let mut result = TypeDefComparison {
        name: name.to_string(),
        class: TransportClass::Concorde,
        losses: Vec::new(),
        field_comparisons: Vec::new(),
        variant_comparisons: Vec::new(),
    };

    let source_fields: BTreeMap<_, _> = source.fields.iter()
        .map(|f| (&f.name, f))
        .collect();
    let target_fields: BTreeMap<_, _> = target.fields.iter()
        .map(|f| (&f.name, f))
        .collect();

    // Check for missing fields in target
    for (field_name, field) in &source_fields {
        if !target_fields.contains_key(*field_name) {
            let severity = if field.optional {
                LossSeverity::Minor
            } else {
                LossSeverity::Major
            };
            result.losses.push(ConversionLoss {
                kind: LossKind::FieldDropped,
                path: format!("{name}.{field_name}"),
                description: format!("Field '{}' not in target", field_name),
                severity,
            });
            result.class = result.class.combine(severity.to_transport_class());
        }
    }

    // Check for new required fields in target
    for (field_name, field) in &target_fields {
        if !source_fields.contains_key(*field_name) && !field.optional {
            result.losses.push(ConversionLoss {
                kind: LossKind::FieldDropped,
                path: format!("{name}.{field_name}"),
                description: format!("Required field '{}' not in source", field_name),
                severity: LossSeverity::Major,
            });
            result.class = result.class.combine(TransportClass::Wheelbarrow);
        }
    }

    // Compare matching fields
    for (field_name, source_field) in &source_fields {
        if let Some(target_field) = target_fields.get(*field_name) {
            let field_cmp = compare_fields(source_field, target_field, name);
            result.class = result.class.combine(field_cmp.class);
            result.losses.extend(field_cmp.losses.clone());
            result.field_comparisons.push(field_cmp);
        }
    }

    result
}

/// Compare two field definitions
fn compare_fields(source: &FieldDef, target: &FieldDef, parent: &str) -> FieldComparison {
    let path = format!("{parent}.{}", source.name);
    let type_cmp = compare_types(&source.ty, &target.ty, &path);

    let mut losses = type_cmp.losses;
    let mut class = type_cmp.class;

    // Check optionality changes
    if source.optional && !target.optional {
        losses.push(ConversionLoss {
            kind: LossKind::NullabilityChanged,
            path: path.clone(),
            description: "Optional field became required".to_string(),
            severity: LossSeverity::Moderate,
        });
        class = class.combine(TransportClass::Economy);
    }

    // Check constraint compatibility
    if source.constraints.len() > target.constraints.len() {
        losses.push(ConversionLoss {
            kind: LossKind::ConstraintDropped,
            path: path.clone(),
            description: "Some constraints not represented in target".to_string(),
            severity: LossSeverity::Minor,
        });
        class = class.combine(TransportClass::BusinessClass);
    }

    FieldComparison {
        name: source.name.clone(),
        class,
        losses,
    }
}

/// Compare two enum definitions
fn compare_enums(source: &EnumDef, target: &EnumDef, name: &str) -> TypeDefComparison {
    let mut result = TypeDefComparison {
        name: name.to_string(),
        class: TransportClass::Concorde,
        losses: Vec::new(),
        field_comparisons: Vec::new(),
        variant_comparisons: Vec::new(),
    };

    let source_variants: BTreeMap<_, _> = source.variants.iter()
        .map(|v| (&v.name, v))
        .collect();
    let target_variants: BTreeMap<_, _> = target.variants.iter()
        .map(|v| (&v.name, v))
        .collect();

    // Check for missing variants in target
    for (variant_name, _) in &source_variants {
        if !target_variants.contains_key(*variant_name) {
            result.losses.push(ConversionLoss {
                kind: LossKind::VariantDropped,
                path: format!("{name}::{variant_name}"),
                description: format!("Variant '{}' not in target", variant_name),
                severity: LossSeverity::Major,
            });
            result.class = result.class.combine(TransportClass::Wheelbarrow);
        }
    }

    // Compare matching variants
    for (variant_name, source_variant) in &source_variants {
        if let Some(target_variant) = target_variants.get(*variant_name) {
            let variant_cmp = compare_variants(source_variant, target_variant, name);
            result.class = result.class.combine(variant_cmp.class);
            result.losses.extend(variant_cmp.losses.clone());
            result.variant_comparisons.push(variant_cmp);
        }
    }

    // Check tag style compatibility
    if source.tag_style != target.tag_style {
        result.losses.push(ConversionLoss {
            kind: LossKind::MetadataLost,
            path: name.to_string(),
            description: format!(
                "Tag style changed: {:?} -> {:?}",
                source.tag_style, target.tag_style
            ),
            severity: LossSeverity::Moderate,
        });
        result.class = result.class.combine(TransportClass::Economy);
    }

    result
}

/// Compare two variant definitions
fn compare_variants(source: &VariantDef, target: &VariantDef, parent: &str) -> VariantComparison {
    use protocol_squisher_ir::VariantPayload;

    let path = format!("{parent}::{}", source.name);

    match (&source.payload, &target.payload) {
        (None, None) => VariantComparison {
            name: source.name.clone(),
            class: TransportClass::Concorde,
            losses: vec![],
        },
        (Some(_), None) => VariantComparison {
            name: source.name.clone(),
            class: TransportClass::Economy,
            losses: vec![ConversionLoss {
                kind: LossKind::FieldDropped,
                path,
                description: "Variant payload dropped".to_string(),
                severity: LossSeverity::Moderate,
            }],
        },
        (None, Some(_)) => VariantComparison {
            name: source.name.clone(),
            class: TransportClass::Economy,
            losses: vec![ConversionLoss {
                kind: LossKind::DefaultLost,
                path,
                description: "Variant payload added (needs default)".to_string(),
                severity: LossSeverity::Moderate,
            }],
        },
        (Some(VariantPayload::Tuple(src)), Some(VariantPayload::Tuple(tgt))) => {
            let mut class = TransportClass::Concorde;
            let mut losses = Vec::new();

            if src.len() != tgt.len() {
                losses.push(ConversionLoss {
                    kind: LossKind::TypeCoercion,
                    path: path.clone(),
                    description: format!("Tuple length changed: {} -> {}", src.len(), tgt.len()),
                    severity: LossSeverity::Major,
                });
                class = TransportClass::Wheelbarrow;
            } else {
                for (i, (s, t)) in src.iter().zip(tgt.iter()).enumerate() {
                    let cmp = compare_types(s, t, &format!("{path}.{i}"));
                    class = class.combine(cmp.class);
                    losses.extend(cmp.losses);
                }
            }

            VariantComparison {
                name: source.name.clone(),
                class,
                losses,
            }
        },
        (Some(VariantPayload::Struct(src)), Some(VariantPayload::Struct(tgt))) => {
            // Create temporary struct defs for comparison
            let src_struct = StructDef {
                name: source.name.clone(),
                fields: src.clone(),
                metadata: Default::default(),
            };
            let tgt_struct = StructDef {
                name: target.name.clone(),
                fields: tgt.clone(),
                metadata: Default::default(),
            };
            let struct_cmp = compare_structs(&src_struct, &tgt_struct, &path);

            VariantComparison {
                name: source.name.clone(),
                class: struct_cmp.class,
                losses: struct_cmp.losses,
            }
        },
        _ => VariantComparison {
            name: source.name.clone(),
            class: TransportClass::Wheelbarrow,
            losses: vec![ConversionLoss {
                kind: LossKind::TypeCoercion,
                path,
                description: "Variant payload type changed".to_string(),
                severity: LossSeverity::Major,
            }],
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{IrType, PrimitiveType, TypeMetadata, FieldMetadata};

    fn make_struct(name: &str, fields: Vec<(&str, IrType, bool)>) -> TypeDef {
        TypeDef::Struct(StructDef {
            name: name.to_string(),
            fields: fields.into_iter().map(|(n, ty, opt)| FieldDef {
                name: n.to_string(),
                ty,
                optional: opt,
                constraints: vec![],
                metadata: FieldMetadata::default(),
            }).collect(),
            metadata: TypeMetadata::default(),
        })
    }

    #[test]
    fn test_identical_schemas() {
        let mut source = IrSchema::new("test", "test");
        source.add_type("User".to_string(), make_struct("User", vec![
            ("id", IrType::Primitive(PrimitiveType::I64), false),
            ("name", IrType::Primitive(PrimitiveType::String), false),
        ]));

        let target = source.clone();
        let cmp = compare_schemas(&source, &target);

        assert_eq!(cmp.class, TransportClass::Concorde);
        assert!(cmp.all_losses.is_empty());
    }

    #[test]
    fn test_field_widening() {
        let mut source = IrSchema::new("source", "test");
        source.add_type("User".to_string(), make_struct("User", vec![
            ("id", IrType::Primitive(PrimitiveType::I32), false),
        ]));

        let mut target = IrSchema::new("target", "test");
        target.add_type("User".to_string(), make_struct("User", vec![
            ("id", IrType::Primitive(PrimitiveType::I64), false),
        ]));

        let cmp = compare_schemas(&source, &target);
        assert_eq!(cmp.class, TransportClass::Concorde);
    }

    #[test]
    fn test_field_narrowing() {
        let mut source = IrSchema::new("source", "test");
        source.add_type("User".to_string(), make_struct("User", vec![
            ("id", IrType::Primitive(PrimitiveType::I64), false),
        ]));

        let mut target = IrSchema::new("target", "test");
        target.add_type("User".to_string(), make_struct("User", vec![
            ("id", IrType::Primitive(PrimitiveType::I32), false),
        ]));

        let cmp = compare_schemas(&source, &target);
        assert_eq!(cmp.class, TransportClass::Economy);
        assert!(!cmp.all_losses.is_empty());
    }

    #[test]
    fn test_missing_field() {
        let mut source = IrSchema::new("source", "test");
        source.add_type("User".to_string(), make_struct("User", vec![
            ("id", IrType::Primitive(PrimitiveType::I64), false),
            ("name", IrType::Primitive(PrimitiveType::String), false),
        ]));

        let mut target = IrSchema::new("target", "test");
        target.add_type("User".to_string(), make_struct("User", vec![
            ("id", IrType::Primitive(PrimitiveType::I64), false),
        ]));

        let cmp = compare_schemas(&source, &target);
        assert_eq!(cmp.class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_missing_optional_field() {
        let mut source = IrSchema::new("source", "test");
        source.add_type("User".to_string(), make_struct("User", vec![
            ("id", IrType::Primitive(PrimitiveType::I64), false),
            ("nickname", IrType::Primitive(PrimitiveType::String), true),
        ]));

        let mut target = IrSchema::new("target", "test");
        target.add_type("User".to_string(), make_struct("User", vec![
            ("id", IrType::Primitive(PrimitiveType::I64), false),
        ]));

        let cmp = compare_schemas(&source, &target);
        // Optional field dropped is less severe
        assert!(cmp.class < TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_missing_type() {
        let mut source = IrSchema::new("source", "test");
        source.add_type("User".to_string(), make_struct("User", vec![
            ("id", IrType::Primitive(PrimitiveType::I64), false),
        ]));
        source.add_type("Order".to_string(), make_struct("Order", vec![
            ("id", IrType::Primitive(PrimitiveType::I64), false),
        ]));

        let mut target = IrSchema::new("target", "test");
        target.add_type("User".to_string(), make_struct("User", vec![
            ("id", IrType::Primitive(PrimitiveType::I64), false),
        ]));

        let cmp = compare_schemas(&source, &target);
        assert!(!cmp.source_only.is_empty());
        assert!(cmp.source_only.contains(&"Order".to_string()));
    }
}
