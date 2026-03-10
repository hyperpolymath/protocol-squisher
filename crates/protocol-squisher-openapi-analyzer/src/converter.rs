// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! OpenAPI schema → Protocol Squisher IR converter.
//!
//! Maps OpenAPI type definitions to IR types and schema objects to struct types.
//!
//! ## Type Mappings
//!
//! | OpenAPI Type     | Format    | IR Type       | Notes                        |
//! |------------------|-----------|---------------|------------------------------|
//! | string           |           | String        | Default text                 |
//! | string           | date      | Date          | ISO 8601 date                |
//! | string           | date-time | DateTime      | ISO 8601 datetime            |
//! | string           | uuid      | Uuid          | 128-bit identifier           |
//! | string           | byte      | Bytes         | Base64-encoded               |
//! | string           | binary    | Bytes         | Raw binary                   |
//! | integer          |           | I32           | Default integer              |
//! | integer          | int64     | I64           | 64-bit integer               |
//! | number           |           | F64           | Default number               |
//! | number           | float     | F32           | Single precision             |
//! | boolean          |           | Bool          | Boolean                      |
//! | array            |           | Vec<T>        | Typed array                  |
//! | object           |           | Struct        | Named properties             |
//! | object (map)     |           | Map<String,T> | additionalProperties         |
//! | enum             |           | Enum          | String enum                  |
//! | $ref             |           | Reference     | Cross-schema reference       |

use crate::parser::{OpenApiPrimitive, OpenApiProperty, OpenApiSchema, ParsedOpenApi, SchemaType};
use crate::AnalyzerError;
use protocol_squisher_ir::*;

/// The OpenAPI → IR converter.
#[derive(Debug, Default)]
pub struct OpenApiConverter;

impl OpenApiConverter {
    /// Convert a parsed OpenAPI spec to an IR schema.
    pub fn convert(&self, parsed: &ParsedOpenApi) -> Result<IrSchema, AnalyzerError> {
        let format_name = match parsed.spec_version {
            crate::parser::SpecVersion::OpenApi30 => "openapi-3.0",
            crate::parser::SpecVersion::OpenApi31 => "openapi-3.1",
            crate::parser::SpecVersion::Swagger20 => "swagger-2.0",
        };
        let mut schema = IrSchema::new(&parsed.title, format_name);

        for (name, api_schema) in &parsed.schemas {
            let type_def = self.convert_schema(api_schema)?;
            schema.add_type(name.clone(), type_def);
            schema.add_root(name.clone());
        }

        Ok(schema)
    }

    /// Convert a single OpenAPI schema to an IR type definition.
    fn convert_schema(&self, schema: &OpenApiSchema) -> Result<TypeDef, AnalyzerError> {
        match &schema.schema_type {
            SchemaType::Object {
                properties,
                required,
            } => {
                let fields = properties
                    .iter()
                    .map(|prop| self.convert_property(prop, required))
                    .collect::<Result<Vec<_>, _>>()?;

                let mut metadata = TypeMetadata::default();
                if let Some(desc) = &schema.description {
                    metadata.doc = Some(desc.clone());
                }

                Ok(TypeDef::Struct(StructDef {
                    name: schema.name.clone(),
                    fields,
                    metadata,
                }))
            }
            SchemaType::Enum { values } => {
                let variants = values
                    .iter()
                    .map(|v| VariantDef {
                        name: v.clone(),
                        payload: None,
                        metadata: VariantMetadata::default(),
                    })
                    .collect();

                Ok(TypeDef::Enum(EnumDef {
                    name: schema.name.clone(),
                    variants,
                    tag_style: TagStyle::default(),
                    metadata: TypeMetadata::default(),
                }))
            }
            SchemaType::Array { items } => {
                let inner = self.convert_type(items)?;
                Ok(TypeDef::Alias(AliasDef {
                    name: schema.name.clone(),
                    target: IrType::Container(ContainerType::Vec(Box::new(inner))),
                    metadata: TypeMetadata::default(),
                }))
            }
            SchemaType::Map(value_type) => {
                let inner = self.convert_type(value_type)?;
                Ok(TypeDef::Alias(AliasDef {
                    name: schema.name.clone(),
                    target: IrType::Container(ContainerType::Map(
                        Box::new(IrType::Primitive(PrimitiveType::String)),
                        Box::new(inner),
                    )),
                    metadata: TypeMetadata::default(),
                }))
            }
            SchemaType::AllOf(items) => {
                // Flatten allOf into a single struct with merged properties
                let mut all_fields = Vec::new();
                let mut all_required = Vec::new();
                for item in items {
                    match item {
                        SchemaType::Object {
                            properties,
                            required,
                        } => {
                            for prop in properties {
                                all_fields.push(self.convert_property(prop, required)?);
                            }
                            all_required.extend(required.clone());
                        }
                        SchemaType::Ref(ref_name) => {
                            // Store as metadata — the ref will be resolved at shape level
                            all_fields.push(FieldDef {
                                name: format!("_extends_{ref_name}"),
                                ty: IrType::Reference(ref_name.clone()),
                                optional: false,
                                constraints: Vec::new(),
                                metadata: FieldMetadata::default(),
                            });
                        }
                        _ => {}
                    }
                }
                Ok(TypeDef::Struct(StructDef {
                    name: schema.name.clone(),
                    fields: all_fields,
                    metadata: TypeMetadata::default(),
                }))
            }
            SchemaType::OneOf(items) => {
                // oneOf → Union type (variants are IrTypes)
                let variants: Vec<IrType> = items
                    .iter()
                    .map(|item| {
                        self.convert_type(item)
                            .unwrap_or(IrType::Primitive(PrimitiveType::String))
                    })
                    .collect();

                Ok(TypeDef::Union(UnionDef {
                    name: schema.name.clone(),
                    variants,
                    metadata: TypeMetadata::default(),
                }))
            }
            SchemaType::AnyOf(items) => {
                // anyOf → treat like oneOf (union)
                let variants: Vec<IrType> = items
                    .iter()
                    .map(|item| {
                        self.convert_type(item)
                            .unwrap_or(IrType::Primitive(PrimitiveType::String))
                    })
                    .collect();

                Ok(TypeDef::Union(UnionDef {
                    name: schema.name.clone(),
                    variants,
                    metadata: TypeMetadata::default(),
                }))
            }
            SchemaType::Primitive(prim) => {
                let ir = convert_primitive(prim, None);
                Ok(TypeDef::Alias(AliasDef {
                    name: schema.name.clone(),
                    target: ir,
                    metadata: TypeMetadata::default(),
                }))
            }
            SchemaType::Ref(ref_name) => Ok(TypeDef::Alias(AliasDef {
                name: schema.name.clone(),
                target: IrType::Reference(ref_name.clone()),
                metadata: TypeMetadata::default(),
            })),
        }
    }

    /// Convert a property to an IR field.
    fn convert_property(
        &self,
        prop: &OpenApiProperty,
        required: &[String],
    ) -> Result<FieldDef, AnalyzerError> {
        let base_type = self.convert_type_with_format(&prop.schema_type, prop.format.as_deref())?;
        let is_required = prop.required || required.contains(&prop.name);

        let ty = if !is_required {
            IrType::Container(ContainerType::Option(Box::new(base_type)))
        } else {
            base_type
        };

        let mut constraints = Vec::new();
        if is_required {
            constraints.push(Constraint::NonEmpty);
        }

        Ok(FieldDef {
            name: prop.name.clone(),
            ty,
            optional: !is_required,
            constraints,
            metadata: FieldMetadata::default(),
        })
    }

    /// Convert a schema type to an IR type, considering format hints.
    fn convert_type_with_format(
        &self,
        schema_type: &SchemaType,
        format: Option<&str>,
    ) -> Result<IrType, AnalyzerError> {
        match schema_type {
            SchemaType::Primitive(prim) => Ok(convert_primitive(prim, format)),
            _ => self.convert_type(schema_type),
        }
    }

    /// Convert a schema type to an IR type.
    #[allow(clippy::only_used_in_recursion)]
    fn convert_type(&self, schema_type: &SchemaType) -> Result<IrType, AnalyzerError> {
        match schema_type {
            SchemaType::Primitive(prim) => Ok(convert_primitive(prim, None)),
            SchemaType::Ref(name) => Ok(IrType::Reference(name.clone())),
            SchemaType::Array { items } => {
                let inner = self.convert_type(items)?;
                Ok(IrType::Container(ContainerType::Vec(Box::new(inner))))
            }
            SchemaType::Map(value_type) => {
                let inner = self.convert_type(value_type)?;
                Ok(IrType::Container(ContainerType::Map(
                    Box::new(IrType::Primitive(PrimitiveType::String)),
                    Box::new(inner),
                )))
            }
            SchemaType::Object { .. } => {
                // Inline objects become String (would need named type promotion)
                Ok(IrType::Special(SpecialType::Json))
            }
            SchemaType::Enum { .. } => Ok(IrType::Primitive(PrimitiveType::String)),
            SchemaType::AllOf(_) | SchemaType::OneOf(_) | SchemaType::AnyOf(_) => {
                Ok(IrType::Special(SpecialType::Json))
            }
        }
    }
}

/// Convert an OpenAPI primitive to an IR type, considering format hints.
fn convert_primitive(prim: &OpenApiPrimitive, format: Option<&str>) -> IrType {
    // Format hints override the base type
    if let Some(fmt) = format {
        match fmt {
            "date" => return IrType::Primitive(PrimitiveType::Date),
            "date-time" => return IrType::Primitive(PrimitiveType::DateTime),
            "uuid" => return IrType::Primitive(PrimitiveType::Uuid),
            "byte" | "binary" => return IrType::Primitive(PrimitiveType::Bytes),
            "duration" => return IrType::Primitive(PrimitiveType::Duration),
            _ => {} // Fall through to base type
        }
    }

    match prim {
        OpenApiPrimitive::String => IrType::Primitive(PrimitiveType::String),
        OpenApiPrimitive::Integer => IrType::Primitive(PrimitiveType::I32),
        OpenApiPrimitive::Long => IrType::Primitive(PrimitiveType::I64),
        OpenApiPrimitive::Number => IrType::Primitive(PrimitiveType::F64),
        OpenApiPrimitive::Float => IrType::Primitive(PrimitiveType::F32),
        OpenApiPrimitive::Boolean => IrType::Primitive(PrimitiveType::Bool),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::OpenApiParser;

    fn convert(json: &str) -> IrSchema {
        let parser = OpenApiParser;
        let parsed = parser.parse_str(json, "test").unwrap();
        OpenApiConverter.convert(&parsed).unwrap()
    }

    #[test]
    fn basic_object_mapping() {
        let schema = convert(
            r#"{
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "User": {
                    "type": "object",
                    "required": ["id", "name"],
                    "properties": {
                        "id": {"type": "integer", "format": "int64"},
                        "name": {"type": "string"},
                        "bio": {"type": "string"}
                    }
                }
            }}
        }"#,
        );
        let td = &schema.types["User"];
        match td {
            TypeDef::Struct(s) => {
                assert_eq!(s.fields.len(), 3);
                // id is required → I64
                assert!(matches!(
                    s.fields[0].ty,
                    IrType::Primitive(PrimitiveType::I64)
                ));
                assert!(!s.fields[0].optional);
                // name is required → String
                assert!(!s.fields[1].optional);
                // bio is optional → Optional<String>
                assert!(s.fields[2].optional);
                assert!(matches!(
                    s.fields[2].ty,
                    IrType::Container(ContainerType::Option(_))
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn enum_mapping() {
        let schema = convert(
            r#"{
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "Status": {
                    "type": "string",
                    "enum": ["active", "inactive", "pending"]
                }
            }}
        }"#,
        );
        match &schema.types["Status"] {
            TypeDef::Enum(e) => {
                assert_eq!(e.variants.len(), 3);
                assert_eq!(e.variants[0].name, "active");
            }
            other => panic!("Expected Enum, got {other:?}"),
        }
    }

    #[test]
    fn format_hints() {
        let schema = convert(
            r#"{
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "Event": {
                    "type": "object",
                    "required": ["id", "created_at", "uid"],
                    "properties": {
                        "id": {"type": "integer"},
                        "created_at": {"type": "string", "format": "date-time"},
                        "uid": {"type": "string", "format": "uuid"}
                    }
                }
            }}
        }"#,
        );
        match &schema.types["Event"] {
            TypeDef::Struct(s) => {
                assert!(matches!(
                    s.fields[0].ty,
                    IrType::Primitive(PrimitiveType::I32)
                ));
                assert!(matches!(
                    s.fields[1].ty,
                    IrType::Primitive(PrimitiveType::DateTime)
                ));
                assert!(matches!(
                    s.fields[2].ty,
                    IrType::Primitive(PrimitiveType::Uuid)
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn array_type_alias() {
        let schema = convert(
            r#"{
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "IdList": {
                    "type": "array",
                    "items": {"type": "integer", "format": "int64"}
                }
            }}
        }"#,
        );
        match &schema.types["IdList"] {
            TypeDef::Alias(a) => {
                assert!(matches!(
                    a.target,
                    IrType::Container(ContainerType::Vec(_))
                ));
            }
            other => panic!("Expected Alias, got {other:?}"),
        }
    }

    #[test]
    fn oneof_union() {
        let spec = serde_json::json!({
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "Shape": {
                    "oneOf": [
                        {"$ref": "#/components/schemas/Circle"},
                        {"$ref": "#/components/schemas/Square"}
                    ]
                }
            }}
        })
        .to_string();
        let schema = convert(&spec);
        match &schema.types["Shape"] {
            TypeDef::Union(u) => {
                assert_eq!(u.variants.len(), 2);
            }
            other => panic!("Expected Union, got {other:?}"),
        }
    }

    #[test]
    fn map_type() {
        let schema = convert(
            r#"{
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "Labels": {
                    "type": "object",
                    "additionalProperties": {"type": "string"}
                }
            }}
        }"#,
        );
        match &schema.types["Labels"] {
            TypeDef::Alias(a) => {
                assert!(matches!(
                    a.target,
                    IrType::Container(ContainerType::Map(_, _))
                ));
            }
            other => panic!("Expected Alias, got {other:?}"),
        }
    }

    #[test]
    fn spec_format_in_schema() {
        let schema = convert(
            r#"{
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {}}
        }"#,
        );
        assert_eq!(schema.source_format, "openapi-3.0");
    }

    #[test]
    fn swagger_format_in_schema() {
        let schema = convert(
            r#"{
            "swagger": "2.0",
            "info": {"title": "Legacy", "version": "1.0"},
            "paths": {},
            "definitions": {}
        }"#,
        );
        assert_eq!(schema.source_format, "swagger-2.0");
    }
}
