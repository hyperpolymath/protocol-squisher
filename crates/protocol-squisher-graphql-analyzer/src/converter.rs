// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Convert parsed GraphQL SDL into Protocol Squisher IR.
//!
//! Mapping:
//! - `type` → `StructDef`
//! - `enum` → `EnumDef`
//! - `union` → `UnionDef`
//! - `input` → `StructDef` (marked via metadata)
//! - `interface` → `StructDef` (marked via metadata)
//! - `scalar` → `TypeDef::Alias` for known scalars, reference for custom
//!
//! GraphQL primitive type mappings:
//! - `String` → `PrimitiveType::String`
//! - `Int` → `PrimitiveType::I32`
//! - `Float` → `PrimitiveType::F64`
//! - `Boolean` → `PrimitiveType::Bool`
//! - `ID` → `PrimitiveType::String`

use crate::parser::*;
use crate::AnalyzerError;
use protocol_squisher_ir::*;
use std::collections::BTreeMap;

/// Converter from parsed GraphQL to IR.
#[derive(Debug, Default)]
pub struct GraphqlConverter {}

impl GraphqlConverter {
    pub fn new() -> Self {
        Self::default()
    }

    /// Convert a parsed GraphQL schema into an `IrSchema`.
    pub fn convert(&self, parsed: &ParsedGraphql, name: &str) -> Result<IrSchema, AnalyzerError> {
        let mut schema = IrSchema::new(name, "graphql");

        // Convert enums first (other types may reference them).
        for gql_enum in &parsed.enums {
            let enum_def = self.convert_enum(gql_enum);
            schema.add_type(gql_enum.name.clone(), TypeDef::Enum(enum_def));
        }

        // Convert scalars.
        for scalar in &parsed.scalars {
            let ir_type = graphql_builtin_to_ir(&scalar.name);
            schema.add_type(
                scalar.name.clone(),
                TypeDef::Alias(AliasDef {
                    name: scalar.name.clone(),
                    target: ir_type,
                    metadata: TypeMetadata {
                        doc: Some(format!("Custom scalar: {}", scalar.name)),
                        ..Default::default()
                    },
                }),
            );
        }

        // Convert interfaces.
        for iface in &parsed.interfaces {
            let struct_def = self.convert_interface(iface);
            schema.add_type(iface.name.clone(), TypeDef::Struct(struct_def));
        }

        // Convert object types.
        for obj in &parsed.objects {
            let struct_def = self.convert_object(obj);
            schema.add_type(obj.name.clone(), TypeDef::Struct(struct_def));
            schema.add_root(obj.name.clone());
        }

        // Convert input types.
        for input in &parsed.inputs {
            let struct_def = self.convert_input(input);
            schema.add_type(input.name.clone(), TypeDef::Struct(struct_def));
        }

        // Convert unions.
        for union_def in &parsed.unions {
            let ir_union = self.convert_union(union_def);
            schema.add_type(union_def.name.clone(), TypeDef::Union(ir_union));
        }

        Ok(schema)
    }

    /// Convert a GraphQL object type to an IR struct.
    fn convert_object(&self, obj: &GraphqlObject) -> StructDef {
        let mut extra = std::collections::BTreeMap::new();
        if !obj.implements.is_empty() {
            extra.insert("graphql_implements".to_string(), obj.implements.join(", "));
        }
        for dir in &obj.directives {
            extra.insert(format!("graphql_directive_{dir}"), "true".to_string());
        }

        StructDef {
            name: obj.name.clone(),
            fields: obj.fields.iter().map(|f| self.convert_field(f)).collect(),
            metadata: TypeMetadata {
                doc: Some(format!("GraphQL type {}", obj.name)),
                extra,
                ..Default::default()
            },
        }
    }

    /// Convert a GraphQL input type to an IR struct.
    fn convert_input(&self, input: &GraphqlInput) -> StructDef {
        let mut extra = std::collections::BTreeMap::new();
        extra.insert("graphql_kind".to_string(), "input".to_string());

        StructDef {
            name: input.name.clone(),
            fields: input.fields.iter().map(|f| self.convert_field(f)).collect(),
            metadata: TypeMetadata {
                doc: Some(format!("GraphQL input {}", input.name)),
                extra,
                ..Default::default()
            },
        }
    }

    /// Convert a GraphQL interface to an IR struct.
    fn convert_interface(&self, iface: &GraphqlInterface) -> StructDef {
        let mut extra = std::collections::BTreeMap::new();
        extra.insert("graphql_kind".to_string(), "interface".to_string());

        StructDef {
            name: iface.name.clone(),
            fields: iface.fields.iter().map(|f| self.convert_field(f)).collect(),
            metadata: TypeMetadata {
                doc: Some(format!("GraphQL interface {}", iface.name)),
                extra,
                ..Default::default()
            },
        }
    }

    /// Convert a GraphQL field to an IR field definition.
    fn convert_field(&self, field: &GraphqlField) -> FieldDef {
        let (ty, optional) = convert_graphql_type(&field.field_type);

        let mut serde_hints = BTreeMap::new();
        for dir in &field.directives {
            serde_hints.insert(format!("graphql_directive_{dir}"), "true".to_string());
        }

        FieldDef {
            name: field.name.clone(),
            ty,
            optional,
            constraints: vec![],
            metadata: FieldMetadata {
                serde_hints,
                ..Default::default()
            },
        }
    }

    /// Convert a GraphQL enum to an IR enum definition.
    fn convert_enum(&self, gql_enum: &GraphqlEnum) -> EnumDef {
        EnumDef {
            name: gql_enum.name.clone(),
            variants: gql_enum
                .values
                .iter()
                .map(|v| VariantDef {
                    name: v.name.clone(),
                    payload: None,
                    metadata: VariantMetadata::default(),
                })
                .collect(),
            tag_style: TagStyle::External,
            metadata: TypeMetadata {
                doc: Some(format!("GraphQL enum {}", gql_enum.name)),
                ..Default::default()
            },
        }
    }

    /// Convert a GraphQL union to an IR union definition.
    fn convert_union(&self, union_def: &GraphqlUnion) -> UnionDef {
        UnionDef {
            name: union_def.name.clone(),
            variants: union_def
                .members
                .iter()
                .map(|m| IrType::Reference(m.clone()))
                .collect(),
            metadata: TypeMetadata {
                doc: Some(format!("GraphQL union {}", union_def.name)),
                ..Default::default()
            },
        }
    }
}

/// Convert a GraphQL type reference to an IR type and optionality flag.
///
/// Non-null types (`Type!`) produce `optional = false`.
/// Nullable types produce `optional = true`.
/// List types produce `ContainerType::Vec`.
fn convert_graphql_type(gql_type: &GraphqlType) -> (IrType, bool) {
    match gql_type {
        GraphqlType::NonNull(inner) => {
            let (ty, _) = convert_graphql_type(inner);
            (ty, false)
        },
        GraphqlType::List(inner) => {
            let (elem_ty, _) = convert_graphql_type(inner);
            (
                IrType::Container(ContainerType::Vec(Box::new(elem_ty))),
                true,
            )
        },
        GraphqlType::Named(name) => {
            let ty = graphql_builtin_to_ir(name);
            (ty, true) // GraphQL fields are nullable by default.
        },
    }
}

/// Map GraphQL built-in scalar names to IR types.
fn graphql_builtin_to_ir(name: &str) -> IrType {
    match name {
        "String" | "ID" => IrType::Primitive(PrimitiveType::String),
        "Int" => IrType::Primitive(PrimitiveType::I32),
        "Float" => IrType::Primitive(PrimitiveType::F64),
        "Boolean" => IrType::Primitive(PrimitiveType::Bool),
        other => IrType::Reference(other.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builtin_type_mappings() {
        assert!(matches!(
            graphql_builtin_to_ir("String"),
            IrType::Primitive(PrimitiveType::String)
        ));
        assert!(matches!(
            graphql_builtin_to_ir("Int"),
            IrType::Primitive(PrimitiveType::I32)
        ));
        assert!(matches!(
            graphql_builtin_to_ir("Float"),
            IrType::Primitive(PrimitiveType::F64)
        ));
        assert!(matches!(
            graphql_builtin_to_ir("Boolean"),
            IrType::Primitive(PrimitiveType::Bool)
        ));
        assert!(matches!(
            graphql_builtin_to_ir("ID"),
            IrType::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn custom_type_becomes_reference() {
        assert!(matches!(
            graphql_builtin_to_ir("DateTime"),
            IrType::Reference(_)
        ));
    }

    #[test]
    fn non_null_list_conversion() {
        let gql_type = GraphqlType::NonNull(Box::new(GraphqlType::List(Box::new(
            GraphqlType::Named("String".to_string()),
        ))));
        let (ty, optional) = convert_graphql_type(&gql_type);
        assert!(!optional);
        assert!(matches!(ty, IrType::Container(ContainerType::Vec(_))));
    }
}
