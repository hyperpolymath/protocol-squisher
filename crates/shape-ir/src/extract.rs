// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Shape Extraction from the Canonical IR
//!
//! This module bridges the existing Protocol Squisher Canonical IR
//! ([`protocol_squisher_ir::IrSchema`]) to the universal Shape IR. Every
//! `IrSchema` produced by any of the 13 format analyzers can be converted
//! into a collection of [`Shape`]s, enabling the new shape algebra to reason
//! about data that was analyzed by the existing pipeline.
//!
//! ## Mapping overview
//!
//! | Canonical IR | Shape IR |
//! |-------------|----------|
//! | `PrimitiveType::I32` | `Shape::Atom(AtomKind::I32)` |
//! | `ContainerType::Option(T)` | `Shape::Optional(extract(T))` |
//! | `ContainerType::Vec(T)` | `Shape::Sequence(extract(T))` |
//! | `ContainerType::Map(K, V)` | `Shape::Map { key, value }` |
//! | `StructDef { fields }` | `Shape::struct_from(...)` |
//! | `EnumDef { variants }` | `Shape::enum_from(...)` or `Shape::Dependent` |
//! | `UnionDef { variants }` | `Shape::enum_from(...)` |
//! | `AliasDef { target }` | extract(target) |
//! | `NewtypeDef { inner }` | extract(inner) |
//! | `IrType::Reference(id)` | `Shape::Ref(id)` |
//! | `SpecialType::Any` | `Shape::Atom(AtomKind::String)` (Wheelbarrow) |
//! | `SpecialType::Unit` | `Shape::Unit` |

use crate::annotations::Annotations;
use crate::annotations::Constraint as ShapeConstraint;
use crate::atom::AtomKind;
use crate::shape::Shape;
use protocol_squisher_ir::{
    ContainerType, EnumDef, IrSchema, IrType, PrimitiveType, SpecialType, StructDef, TagStyle,
    TypeDef, UnionDef, VariantPayload,
};
use std::collections::BTreeMap;

/// The result of extracting shapes from an `IrSchema`.
///
/// Contains one named `Shape` for each root type in the schema, plus any
/// types referenced by those roots (transitively). The shapes use `Recursive`
/// and `Ref` for self-referential types.
#[derive(Debug, Clone)]
pub struct ExtractedShapes {
    /// Named shapes keyed by their type ID from the original schema.
    pub shapes: BTreeMap<String, Shape>,

    /// The source format identifier (e.g. "protobuf", "rust-serde").
    pub source_format: String,

    /// The schema name.
    pub schema_name: String,
}

/// Extract all root types from an `IrSchema` into `Shape`s.
///
/// Each root type is fully expanded (nested types are inlined). References
/// to other types in the schema use `Shape::Ref(type_id)`, and if the type
/// is self-referential, it is wrapped in `Shape::Recursive`.
///
/// # Examples
///
/// ```rust,ignore
/// use protocol_squisher_ir::IrSchema;
/// use shape_ir::extract::extract_schema;
///
/// let schema: IrSchema = analyzer.analyze_str(input, "example")?;
/// let extracted = extract_schema(&schema);
/// for (name, shape) in &extracted.shapes {
///     println!("{}: {}", name, shape);
/// }
/// ```
pub fn extract_schema(schema: &IrSchema) -> ExtractedShapes {
    let mut shapes = BTreeMap::new();

    // Extract each root type
    for root_id in &schema.roots {
        if let Some(type_def) = schema.types.get(root_id) {
            let shape = extract_type_def(type_def, &schema.types, root_id);
            shapes.insert(root_id.clone(), shape);
        }
    }

    // Also extract non-root types that may be referenced
    for (type_id, type_def) in &schema.types {
        if !shapes.contains_key(type_id) {
            let shape = extract_type_def(type_def, &schema.types, type_id);
            shapes.insert(type_id.clone(), shape);
        }
    }

    ExtractedShapes {
        shapes,
        source_format: schema.source_format.clone(),
        schema_name: schema.name.clone(),
    }
}

/// Extract a single `IrType` into a `Shape`.
///
/// This is the lower-level entry point for when you have a single IR type
/// rather than a complete schema.
pub fn extract_ir_type(ir_type: &IrType, type_registry: &BTreeMap<String, TypeDef>) -> Shape {
    convert_ir_type(ir_type, type_registry)
}

/// Convert a `TypeDef` to a `Shape`, wrapping in `Recursive` if the type
/// references itself.
fn extract_type_def(
    type_def: &TypeDef,
    registry: &BTreeMap<String, TypeDef>,
    type_id: &str,
) -> Shape {
    let inner = match type_def {
        TypeDef::Struct(s) => convert_struct(s, registry),
        TypeDef::Enum(e) => convert_enum(e, registry),
        TypeDef::Union(u) => convert_union(u, registry),
        TypeDef::Alias(a) => convert_ir_type(&a.target, registry),
        TypeDef::Newtype(n) => convert_ir_type(&n.inner, registry),
    };

    // If the body references its own type_id, wrap in Recursive
    if shape_references_name(&inner, type_id) {
        Shape::recursive(type_id, inner)
    } else {
        inner
    }
}

/// Convert a `StructDef` to a right-nested `Shape::Product`.
fn convert_struct(s: &StructDef, registry: &BTreeMap<String, TypeDef>) -> Shape {
    let fields: Vec<(String, Shape)> = s
        .fields
        .iter()
        .filter(|f| !f.metadata.skip) // Skip serialization-skipped fields
        .map(|f| {
            let mut shape = convert_ir_type(&f.ty, registry);

            // Wrap in Optional if the field is optional and not already optional
            if f.optional && !matches!(shape, Shape::Optional(_)) {
                shape = Shape::optional(shape);
            }

            // Attach constraints as annotations if any
            if !f.constraints.is_empty() {
                let annotations = convert_constraints(&f.constraints);
                shape = shape.annotated(annotations);
            }

            (f.name.clone(), shape)
        })
        .collect();

    if fields.is_empty() {
        Shape::Unit
    } else {
        Shape::struct_from(fields)
    }
}

/// Convert an `EnumDef` to a `Shape::Sum` or `Shape::Dependent`.
///
/// Tagged enums with an internal tag field map to `Dependent` (the tag value
/// determines the body shape). Externally tagged or untagged enums map to `Sum`.
fn convert_enum(e: &EnumDef, registry: &BTreeMap<String, TypeDef>) -> Shape {
    // For internally tagged enums, create a Dependent shape
    if let TagStyle::Internal { ref tag_field } = e.tag_style {
        let variant_names: Vec<String> = e.variants.iter().map(|v| v.name.clone()).collect();
        let binder = Shape::Atom(AtomKind::Enum(variant_names));

        // The body is a Sum of the variant payloads
        let body = convert_variants_to_sum(e, registry);

        // Wrap as Dependent: the tag field determines which variant applies
        let tag_shape =
            Shape::struct_from(vec![(tag_field.clone(), Shape::dependent(binder, body))]);
        return tag_shape;
    }

    // For external, adjacent, or untagged: standard sum
    convert_variants_to_sum(e, registry)
}

/// Convert enum variants to a right-nested `Shape::Sum`.
fn convert_variants_to_sum(e: &EnumDef, registry: &BTreeMap<String, TypeDef>) -> Shape {
    let variants: Vec<(String, Shape)> = e
        .variants
        .iter()
        .map(|v| {
            let payload = match &v.payload {
                None => Shape::Unit,
                Some(VariantPayload::Tuple(types)) => {
                    if types.len() == 1 {
                        convert_ir_type(&types[0], registry)
                    } else {
                        // Multi-element tuple: convert to a product with positional labels
                        let fields: Vec<(String, Shape)> = types
                            .iter()
                            .enumerate()
                            .map(|(i, t)| (format!("_{}", i), convert_ir_type(t, registry)))
                            .collect();
                        Shape::struct_from(fields)
                    }
                },
                Some(VariantPayload::Struct(fields)) => {
                    let shape_fields: Vec<(String, Shape)> = fields
                        .iter()
                        .map(|f| {
                            let mut shape = convert_ir_type(&f.ty, registry);
                            if f.optional && !matches!(shape, Shape::Optional(_)) {
                                shape = Shape::optional(shape);
                            }
                            (f.name.clone(), shape)
                        })
                        .collect();
                    if shape_fields.is_empty() {
                        Shape::Unit
                    } else {
                        Shape::struct_from(shape_fields)
                    }
                },
            };
            (v.name.clone(), payload)
        })
        .collect();

    if variants.is_empty() {
        Shape::Unit
    } else {
        Shape::enum_from(variants)
    }
}

/// Convert an `UnionDef` (untagged union) to a `Shape::Sum`.
fn convert_union(u: &UnionDef, registry: &BTreeMap<String, TypeDef>) -> Shape {
    let variants: Vec<(String, Shape)> = u
        .variants
        .iter()
        .enumerate()
        .map(|(i, t)| (format!("variant_{}", i), convert_ir_type(t, registry)))
        .collect();

    if variants.is_empty() {
        Shape::Unit
    } else {
        Shape::enum_from(variants)
    }
}

/// Convert an `IrType` to a `Shape`.
fn convert_ir_type(ir_type: &IrType, registry: &BTreeMap<String, TypeDef>) -> Shape {
    match ir_type {
        IrType::Primitive(p) => Shape::Atom(convert_primitive(p)),

        IrType::Container(c) => match c {
            ContainerType::Option(inner) => Shape::optional(convert_ir_type(inner, registry)),
            ContainerType::Vec(inner) => Shape::sequence(convert_ir_type(inner, registry)),
            ContainerType::Array(inner, _size) => {
                // Fixed-size arrays map to sequences (size constraint is an annotation)
                Shape::sequence(convert_ir_type(inner, registry))
            },
            ContainerType::Set(inner) => {
                // Sets map to sequences with a uniqueness annotation
                let shape = Shape::sequence(convert_ir_type(inner, registry));
                let annotations = Annotations {
                    constraints: vec![ShapeConstraint::Custom(
                        "unique_items".into(),
                        "true".into(),
                    )],
                    ..Default::default()
                };
                shape.annotated(annotations)
            },
            ContainerType::Map(key, value) => Shape::map(
                convert_ir_type(key, registry),
                convert_ir_type(value, registry),
            ),
            ContainerType::Tuple(types) => {
                if types.is_empty() {
                    Shape::Unit
                } else {
                    let fields: Vec<(String, Shape)> = types
                        .iter()
                        .enumerate()
                        .map(|(i, t)| (format!("_{}", i), convert_ir_type(t, registry)))
                        .collect();
                    Shape::struct_from(fields)
                }
            },
            ContainerType::Result(ok, err) => {
                // Result<T, E> maps to Sum("Ok", T, Sum("Err", E, Unit))
                Shape::enum_from(vec![
                    ("Ok", convert_ir_type(ok, registry)),
                    ("Err", convert_ir_type(err, registry)),
                ])
            },
        },

        IrType::Reference(type_id) => {
            // If the referenced type exists in the registry and is a simple
            // alias/newtype, inline it. Otherwise emit a Ref for later resolution.
            match registry.get(type_id.as_str()) {
                Some(TypeDef::Alias(a)) => convert_ir_type(&a.target, registry),
                Some(TypeDef::Newtype(n)) => convert_ir_type(&n.inner, registry),
                _ => Shape::Ref(type_id.clone()),
            }
        },

        IrType::Special(s) => match s {
            SpecialType::Unit => Shape::Unit,
            SpecialType::Never => Shape::Unit, // Bottom type — no inhabitants
            SpecialType::Any | SpecialType::Json => {
                // Dynamic types have no structure — Wheelbarrow territory
                Shape::Recursive {
                    var: "JSON".into(),
                    body: Box::new(Shape::enum_from(vec![
                        ("Null", Shape::Unit),
                        ("Bool", Shape::Atom(AtomKind::Bool)),
                        ("Number", Shape::Atom(AtomKind::F64)),
                        ("String", Shape::Atom(AtomKind::String)),
                        ("Array", Shape::sequence(Shape::Ref("JSON".into()))),
                        (
                            "Object",
                            Shape::map(Shape::Atom(AtomKind::String), Shape::Ref("JSON".into())),
                        ),
                    ])),
                }
            },
            SpecialType::Opaque(_) => {
                Shape::Atom(AtomKind::Bytes) // Opaque blob as raw bytes
            },
        },
    }
}

/// Convert a canonical IR `PrimitiveType` to a shape `AtomKind`.
fn convert_primitive(p: &PrimitiveType) -> AtomKind {
    match p {
        PrimitiveType::Bool => AtomKind::Bool,
        PrimitiveType::I8 => AtomKind::I8,
        PrimitiveType::I16 => AtomKind::I16,
        PrimitiveType::I32 => AtomKind::I32,
        PrimitiveType::I64 => AtomKind::I64,
        PrimitiveType::I128 => AtomKind::I128,
        PrimitiveType::U8 => AtomKind::U8,
        PrimitiveType::U16 => AtomKind::U16,
        PrimitiveType::U32 => AtomKind::U32,
        PrimitiveType::U64 => AtomKind::U64,
        PrimitiveType::U128 => AtomKind::U128,
        PrimitiveType::F32 => AtomKind::F32,
        PrimitiveType::F64 => AtomKind::F64,
        PrimitiveType::String | PrimitiveType::Char => AtomKind::String,
        PrimitiveType::Bytes => AtomKind::Bytes,
        PrimitiveType::DateTime => AtomKind::Timestamp(crate::atom::TimePrecision::Nanoseconds),
        PrimitiveType::Date => AtomKind::Date,
        PrimitiveType::Time => AtomKind::Duration, // Time-of-day approximated as duration
        PrimitiveType::Duration => AtomKind::Duration,
        PrimitiveType::Uuid => AtomKind::FixedBytes(16),
        PrimitiveType::Decimal => AtomKind::Decimal {
            precision: 38,
            scale: 18,
        },
        PrimitiveType::BigInt => AtomKind::I128, // Best available fixed approximation
    }
}

/// Convert canonical IR constraints to shape annotations.
fn convert_constraints(constraints: &[protocol_squisher_ir::Constraint]) -> Annotations {
    use protocol_squisher_ir::Constraint as IrConstraint;

    let shape_constraints: Vec<ShapeConstraint> = constraints
        .iter()
        .filter_map(|c| match c {
            IrConstraint::Min(n) => Some(ShapeConstraint::MinValue(n.as_f64())),
            IrConstraint::Max(n) => Some(ShapeConstraint::MaxValue(n.as_f64())),
            IrConstraint::Range { min, max } => {
                // No Range variant in Shape IR — emit as Custom
                Some(ShapeConstraint::Custom(
                    "range".into(),
                    format!("[{}, {}]", min.as_f64(), max.as_f64()),
                ))
            },
            IrConstraint::MinLength(n) => Some(ShapeConstraint::MinLength(*n)),
            IrConstraint::MaxLength(n) => Some(ShapeConstraint::MaxLength(*n)),
            IrConstraint::Pattern(p) => Some(ShapeConstraint::Pattern(p.clone())),
            IrConstraint::NonEmpty => Some(ShapeConstraint::MinLength(1)),
            IrConstraint::UniqueItems => Some(ShapeConstraint::Custom(
                "unique_items".into(),
                "true".into(),
            )),
            _ => None, // Other constraints don't have a direct Shape mapping yet
        })
        .collect();

    Annotations {
        constraints: shape_constraints,
        ..Default::default()
    }
}

/// Check if a shape recursively references a given name (via `Ref`).
fn shape_references_name(shape: &Shape, name: &str) -> bool {
    match shape {
        Shape::Ref(n) => n == name,
        Shape::Product { left, right, .. } => {
            shape_references_name(left, name) || shape_references_name(right, name)
        },
        Shape::Sum { left, right, .. } => {
            shape_references_name(left, name) || shape_references_name(right, name)
        },
        Shape::Dependent { binder, body } => {
            shape_references_name(binder, name) || shape_references_name(body, name)
        },
        Shape::Recursive { var, body } => {
            // If the inner recursive binds the same name, it shadows — don't recurse
            if var == name {
                false
            } else {
                shape_references_name(body, name)
            }
        },
        Shape::Sequence(inner) | Shape::Optional(inner) => shape_references_name(inner, name),
        Shape::Map { key, value } => {
            shape_references_name(key, name) || shape_references_name(value, name)
        },
        Shape::Annotated { shape, .. } => shape_references_name(shape, name),
        Shape::Unit | Shape::Atom(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TransportClass;
    use protocol_squisher_ir::*;

    /// Helper: create a simple schema with one struct type.
    fn simple_user_schema() -> IrSchema {
        let mut schema = IrSchema::new("test", "rust-serde");
        schema.add_type(
            "User".into(),
            TypeDef::Struct(StructDef {
                name: "User".into(),
                fields: vec![
                    FieldDef {
                        name: "id".into(),
                        ty: IrType::Primitive(PrimitiveType::U64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "name".into(),
                        ty: IrType::Primitive(PrimitiveType::String),
                        optional: false,
                        constraints: vec![Constraint::MinLength(1)],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "email".into(),
                        ty: IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
                            PrimitiveType::String,
                        )))),
                        optional: true,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        schema.add_root("User".into());
        schema
    }

    #[test]
    fn extract_simple_struct() {
        let schema = simple_user_schema();
        let extracted = extract_schema(&schema);

        assert_eq!(extracted.shapes.len(), 1);
        let user_shape = &extracted.shapes["User"];

        // Should be a Product (struct) with 3 fields
        let labels = user_shape.field_labels();
        assert_eq!(labels.len(), 3);
        assert_eq!(labels[0].name, "id");
        assert_eq!(labels[1].name, "name");
        assert_eq!(labels[2].name, "email");
    }

    #[test]
    fn extract_preserves_optionals() {
        let schema = simple_user_schema();
        let extracted = extract_schema(&schema);
        let user_shape = &extracted.shapes["User"];

        // The email field should be Optional
        // Walk the product chain to find "email"
        let email_shape = find_field_shape(user_shape, "email");
        assert!(
            matches!(email_shape, Some(Shape::Optional(_))),
            "email should be Optional, got {:?}",
            email_shape,
        );
    }

    #[test]
    fn extract_preserves_constraints_as_annotations() {
        let schema = simple_user_schema();
        let extracted = extract_schema(&schema);
        let user_shape = &extracted.shapes["User"];

        // The "name" field has a MinLength(1) constraint — should be annotated
        let name_shape = find_field_shape(user_shape, "name");
        assert!(
            matches!(name_shape, Some(Shape::Annotated { .. })),
            "name should be Annotated, got {:?}",
            name_shape,
        );
    }

    #[test]
    fn extract_enum_to_sum() {
        let mut schema = IrSchema::new("test", "protobuf");
        schema.add_type(
            "Status".into(),
            TypeDef::Enum(EnumDef {
                name: "Status".into(),
                variants: vec![
                    VariantDef {
                        name: "Active".into(),
                        payload: None,
                        metadata: VariantMetadata::default(),
                    },
                    VariantDef {
                        name: "Inactive".into(),
                        payload: None,
                        metadata: VariantMetadata::default(),
                    },
                    VariantDef {
                        name: "Banned".into(),
                        payload: Some(VariantPayload::Struct(vec![FieldDef {
                            name: "reason".into(),
                            ty: IrType::Primitive(PrimitiveType::String),
                            optional: false,
                            constraints: vec![],
                            metadata: FieldMetadata::default(),
                        }])),
                        metadata: VariantMetadata::default(),
                    },
                ],
                tag_style: TagStyle::External,
                metadata: TypeMetadata::default(),
            }),
        );
        schema.add_root("Status".into());

        let extracted = extract_schema(&schema);
        let status = &extracted.shapes["Status"];

        // Should be a Sum with 3 variants
        match status {
            Shape::Sum { label, .. } => assert_eq!(label.name, "Active"),
            other => panic!("Expected Sum, got {:?}", other),
        }
    }

    #[test]
    fn extract_self_referential_wraps_in_recursive() {
        let mut schema = IrSchema::new("test", "rust-serde");
        schema.add_type(
            "TreeNode".into(),
            TypeDef::Struct(StructDef {
                name: "TreeNode".into(),
                fields: vec![
                    FieldDef {
                        name: "value".into(),
                        ty: IrType::Primitive(PrimitiveType::I32),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "children".into(),
                        ty: IrType::Container(ContainerType::Vec(Box::new(IrType::Reference(
                            "TreeNode".into(),
                        )))),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        schema.add_root("TreeNode".into());

        let extracted = extract_schema(&schema);
        let tree = &extracted.shapes["TreeNode"];

        // Should be wrapped in Recursive because it references itself
        match tree {
            Shape::Recursive { var, .. } => assert_eq!(var, "TreeNode"),
            other => panic!("Expected Recursive, got {:?}", other),
        }
    }

    #[test]
    fn extract_containers() {
        let mut schema = IrSchema::new("test", "rust-serde");
        schema.add_type(
            "Containers".into(),
            TypeDef::Struct(StructDef {
                name: "Containers".into(),
                fields: vec![
                    FieldDef {
                        name: "tags".into(),
                        ty: IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
                            PrimitiveType::String,
                        )))),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "metadata".into(),
                        ty: IrType::Container(ContainerType::Map(
                            Box::new(IrType::Primitive(PrimitiveType::String)),
                            Box::new(IrType::Primitive(PrimitiveType::I64)),
                        )),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        schema.add_root("Containers".into());

        let extracted = extract_schema(&schema);
        let shape = &extracted.shapes["Containers"];

        // tags should be Sequence
        let tags = find_field_shape(shape, "tags");
        assert!(
            matches!(tags, Some(Shape::Sequence(_))),
            "tags should be Sequence, got {:?}",
            tags,
        );

        // metadata should be Map
        let meta = find_field_shape(shape, "metadata");
        assert!(
            matches!(meta, Some(Shape::Map { .. })),
            "metadata should be Map, got {:?}",
            meta,
        );
    }

    #[test]
    fn extract_any_type_is_recursive_json() {
        let mut schema = IrSchema::new("test", "json");
        schema.add_type(
            "Dynamic".into(),
            TypeDef::Struct(StructDef {
                name: "Dynamic".into(),
                fields: vec![FieldDef {
                    name: "data".into(),
                    ty: IrType::Special(SpecialType::Any),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
                metadata: TypeMetadata::default(),
            }),
        );
        schema.add_root("Dynamic".into());

        let extracted = extract_schema(&schema);
        let shape = &extracted.shapes["Dynamic"];
        let data = find_field_shape(shape, "data");

        // SpecialType::Any maps to a recursive JSON shape
        assert!(
            matches!(data, Some(Shape::Recursive { var, .. }) if var == "JSON"),
            "Any should map to Recursive JSON, got {:?}",
            data,
        );
    }

    #[test]
    fn extracted_shapes_are_comparable() {
        // Create two schemas with slightly different types and compare
        let mut schema_a = IrSchema::new("a", "rust-serde");
        schema_a.add_type(
            "Point".into(),
            TypeDef::Struct(StructDef {
                name: "Point".into(),
                fields: vec![
                    FieldDef {
                        name: "x".into(),
                        ty: IrType::Primitive(PrimitiveType::I32),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "y".into(),
                        ty: IrType::Primitive(PrimitiveType::I32),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        schema_a.add_root("Point".into());

        let mut schema_b = IrSchema::new("b", "protobuf");
        schema_b.add_type(
            "Point".into(),
            TypeDef::Struct(StructDef {
                name: "Point".into(),
                fields: vec![
                    FieldDef {
                        name: "x".into(),
                        ty: IrType::Primitive(PrimitiveType::I64), // wider
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "y".into(),
                        ty: IrType::Primitive(PrimitiveType::I64), // wider
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "z".into(),
                        ty: IrType::Primitive(PrimitiveType::I64), // extra
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        schema_b.add_root("Point".into());

        let shapes_a = extract_schema(&schema_a);
        let shapes_b = extract_schema(&schema_b);

        let m = crate::compare::compare(&shapes_a.shapes["Point"], &shapes_b.shapes["Point"]);

        // i32->i64 widening + extra field = Business
        assert_eq!(m.transport_class, TransportClass::Business);
    }

    #[test]
    fn extract_result_type() {
        let mut schema = IrSchema::new("test", "rust-serde");
        schema.add_type(
            "Outcome".into(),
            TypeDef::Struct(StructDef {
                name: "Outcome".into(),
                fields: vec![FieldDef {
                    name: "result".into(),
                    ty: IrType::Container(ContainerType::Result(
                        Box::new(IrType::Primitive(PrimitiveType::String)),
                        Box::new(IrType::Primitive(PrimitiveType::I32)),
                    )),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
                metadata: TypeMetadata::default(),
            }),
        );
        schema.add_root("Outcome".into());

        let extracted = extract_schema(&schema);
        let shape = &extracted.shapes["Outcome"];
        let result_shape = find_field_shape(shape, "result");
        // Result maps to a Sum (Ok | Err)
        assert!(
            matches!(result_shape, Some(Shape::Sum { .. })),
            "Result should map to Sum, got {:?}",
            result_shape,
        );
    }

    #[test]
    fn extract_set_with_uniqueness() {
        let mut schema = IrSchema::new("test", "rust-serde");
        schema.add_type(
            "Tags".into(),
            TypeDef::Struct(StructDef {
                name: "Tags".into(),
                fields: vec![FieldDef {
                    name: "unique_ids".into(),
                    ty: IrType::Container(ContainerType::Set(Box::new(IrType::Primitive(
                        PrimitiveType::U64,
                    )))),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
                metadata: TypeMetadata::default(),
            }),
        );
        schema.add_root("Tags".into());

        let extracted = extract_schema(&schema);
        let shape = &extracted.shapes["Tags"];
        let set_shape = find_field_shape(shape, "unique_ids");
        // Set maps to an annotated Sequence with UniqueItems
        assert!(
            matches!(set_shape, Some(Shape::Annotated { .. })),
            "Set should map to Annotated(Sequence, UniqueItems), got {:?}",
            set_shape,
        );
    }

    #[test]
    fn extract_tuple_type() {
        let mut schema = IrSchema::new("test", "rust-serde");
        schema.add_type(
            "Pair".into(),
            TypeDef::Struct(StructDef {
                name: "Pair".into(),
                fields: vec![FieldDef {
                    name: "coords".into(),
                    ty: IrType::Container(ContainerType::Tuple(vec![
                        IrType::Primitive(PrimitiveType::F64),
                        IrType::Primitive(PrimitiveType::F64),
                    ])),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
                metadata: TypeMetadata::default(),
            }),
        );
        schema.add_root("Pair".into());

        let extracted = extract_schema(&schema);
        let shape = &extracted.shapes["Pair"];
        let tuple_shape = find_field_shape(shape, "coords");
        // Tuple maps to a Product (struct_from with auto-generated labels)
        assert!(
            matches!(tuple_shape, Some(Shape::Product { .. })),
            "Tuple should map to Product, got {:?}",
            tuple_shape,
        );
    }

    /// Helper: find the shape of a named field in a product chain.
    fn find_field_shape<'a>(shape: &'a Shape, name: &str) -> Option<&'a Shape> {
        match shape {
            Shape::Product { label, left, right } => {
                if label.name == name {
                    Some(left)
                } else {
                    find_field_shape(right, name)
                }
            },
            Shape::Annotated { shape, .. } => find_field_shape(shape, name),
            Shape::Recursive { body, .. } => find_field_shape(body, name),
            _ => None,
        }
    }
}
