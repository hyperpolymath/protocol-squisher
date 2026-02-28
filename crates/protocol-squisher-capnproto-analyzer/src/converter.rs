// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Converter from parsed Cap'n Proto to protocol-squisher IR

use crate::parser::{
    CapnProtoEnum, CapnProtoField, CapnProtoStruct, CapnProtoUnion, ParsedCapnProto,
};
use crate::AnalyzerError;
use protocol_squisher_ir::{
    ContainerType, EnumDef, FieldDef, FieldMetadata, IrSchema, IrType, PrimitiveType, SpecialType,
    StructDef, TagStyle, TypeDef, TypeMetadata, VariantDef, VariantMetadata, VariantPayload,
};
use std::collections::BTreeMap;

/// Converter from parsed Cap'n Proto to IR
#[derive(Debug, Default)]
pub struct CapnProtoConverter {}

impl CapnProtoConverter {
    /// Create a new converter
    pub fn new() -> Self {
        Self::default()
    }

    /// Convert a parsed Cap'n Proto to IR schema
    pub fn convert(&self, parsed: &ParsedCapnProto, name: &str) -> Result<IrSchema, AnalyzerError> {
        let mut ir = IrSchema::new(name, "capnproto");
        let mut types = BTreeMap::new();

        // Convert top-level enums
        for capnp_enum in &parsed.enums {
            let enum_def = self.convert_enum(capnp_enum)?;
            types.insert(enum_def.name.clone(), TypeDef::Enum(enum_def));
        }

        // Convert top-level structs
        for capnp_struct in &parsed.structs {
            let struct_def = self.convert_struct(capnp_struct)?;
            types.insert(struct_def.name.clone(), TypeDef::Struct(struct_def));
        }

        // Convert standalone unions to enums with variants
        for capnp_union in &parsed.unions {
            let enum_def = self.convert_union_to_enum(capnp_union)?;
            types.insert(enum_def.name.clone(), TypeDef::Enum(enum_def));
        }

        // Add all types to IR
        for (type_name, type_def) in types {
            ir.add_type(type_name, type_def);
        }

        Ok(ir)
    }

    /// Convert a Cap'n Proto struct to IR struct
    fn convert_struct(&self, capnp_struct: &CapnProtoStruct) -> Result<StructDef, AnalyzerError> {
        let mut fields = capnp_struct
            .fields
            .iter()
            .map(|f| self.convert_field(f))
            .collect::<Result<Vec<_>, _>>()?;

        // Handle inline union - convert to optional variant fields
        if let Some(inline_union) = &capnp_struct.inline_union {
            let union_fields = self.convert_inline_union_to_fields(inline_union)?;
            fields.extend(union_fields);
        }

        // Add metadata for zero-copy structs
        let mut extra = BTreeMap::new();
        extra.insert("zero_copy".to_string(), "true".to_string());
        extra.insert("field_numbered".to_string(), "true".to_string());

        Ok(StructDef {
            name: capnp_struct.name.clone(),
            fields,
            metadata: TypeMetadata {
                doc: None,
                deprecated: None,
                serde_hints: BTreeMap::new(),
                extra,
            },
        })
    }

    /// Convert an inline union to variants that are added as individual fields
    ///
    /// Note: Cap'n Proto inline unions should ideally be represented as a discriminated union,
    /// but for simplicity we convert each variant to an optional field.
    /// A better approach would be to create a synthetic enum type.
    fn convert_inline_union_to_fields(
        &self,
        union: &CapnProtoUnion,
    ) -> Result<Vec<FieldDef>, AnalyzerError> {
        // For now, convert each union variant to an optional field
        // This is a simplification - real Cap'n Proto has a discriminant
        let fields: Result<Vec<FieldDef>, AnalyzerError> = union
            .variants
            .iter()
            .map(|field| -> Result<FieldDef, AnalyzerError> {
                let field_type = Self::capnp_type_to_ir(&field.field_type)?;
                Ok(FieldDef {
                    name: field.name.clone(),
                    ty: IrType::Container(ContainerType::Option(Box::new(field_type))),
                    optional: true,
                    constraints: vec![],
                    metadata: FieldMetadata {
                        doc: Some("Union variant field".to_string()),
                        default: None,
                        aliases: vec![],
                        flatten: false,
                        skip: false,
                        serde_hints: BTreeMap::new(),
                    },
                })
            })
            .collect();

        fields
    }

    /// Convert a Cap'n Proto field to IR field
    fn convert_field(&self, field: &CapnProtoField) -> Result<FieldDef, AnalyzerError> {
        let ty = self.convert_field_type(field)?;

        let mut serde_hints = BTreeMap::new();
        serde_hints.insert("field_number".to_string(), field.number.to_string());

        // Convert default value string to JSON value
        let default = field.default_value.as_ref().and_then(|v| {
            // Try to parse as JSON, or wrap as string
            serde_json::from_str(v)
                .ok()
                .or_else(|| Some(serde_json::Value::String(v.clone())))
        });

        Ok(FieldDef {
            name: field.name.clone(),
            ty,
            optional: false, // Cap'n Proto fields are not optional by default
            constraints: vec![],
            metadata: FieldMetadata {
                doc: None,
                default,
                aliases: vec![],
                flatten: false,
                skip: false,
                serde_hints,
            },
        })
    }

    /// Convert a Cap'n Proto field type string to IR type
    fn convert_field_type(&self, field: &CapnProtoField) -> Result<IrType, AnalyzerError> {
        Self::capnp_type_to_ir(&field.field_type)
    }

    /// Convert a Cap'n Proto type string to IR type
    fn capnp_type_to_ir(type_str: &str) -> Result<IrType, AnalyzerError> {
        // Handle generic types first (List(T))
        if let Some(list_inner) = extract_list_type(type_str) {
            let element_type = Self::capnp_type_to_ir(list_inner)?;
            return Ok(IrType::Container(ContainerType::Vec(Box::new(
                element_type,
            ))));
        }

        match type_str {
            // Special types
            "Void" => Ok(IrType::Special(SpecialType::Unit)),

            // Boolean
            "Bool" => Ok(IrType::Primitive(PrimitiveType::Bool)),

            // Integers
            "Int8" => Ok(IrType::Primitive(PrimitiveType::I8)),
            "UInt8" => Ok(IrType::Primitive(PrimitiveType::U8)),
            "Int16" => Ok(IrType::Primitive(PrimitiveType::I16)),
            "UInt16" => Ok(IrType::Primitive(PrimitiveType::U16)),
            "Int32" => Ok(IrType::Primitive(PrimitiveType::I32)),
            "UInt32" => Ok(IrType::Primitive(PrimitiveType::U32)),
            "Int64" => Ok(IrType::Primitive(PrimitiveType::I64)),
            "UInt64" => Ok(IrType::Primitive(PrimitiveType::U64)),

            // Floats
            "Float32" => Ok(IrType::Primitive(PrimitiveType::F32)),
            "Float64" => Ok(IrType::Primitive(PrimitiveType::F64)),

            // Text and Data
            "Text" => Ok(IrType::Primitive(PrimitiveType::String)),
            "Data" => Ok(IrType::Container(ContainerType::Vec(Box::new(
                IrType::Primitive(PrimitiveType::U8),
            )))),

            // User-defined types (structs, enums)
            type_name => Ok(IrType::Reference(type_name.to_string())),
        }
    }

    /// Convert a Cap'n Proto enum to IR enum
    fn convert_enum(&self, capnp_enum: &CapnProtoEnum) -> Result<EnumDef, AnalyzerError> {
        let variants: Vec<VariantDef> = capnp_enum
            .values
            .iter()
            .map(|v| VariantDef {
                name: to_pascal_case(&v.name),
                payload: None, // Cap'n Proto enums don't have payloads
                metadata: VariantMetadata {
                    doc: None,
                    aliases: vec![v.name.clone()],
                    serde_hints: BTreeMap::new(),
                },
            })
            .collect();

        Ok(EnumDef {
            name: capnp_enum.name.clone(),
            variants,
            tag_style: TagStyle::External,
            metadata: TypeMetadata::default(),
        })
    }

    /// Convert a Cap'n Proto union to IR enum with variants
    fn convert_union_to_enum(
        &self,
        capnp_union: &CapnProtoUnion,
    ) -> Result<EnumDef, AnalyzerError> {
        let variants: Result<Vec<VariantDef>, AnalyzerError> = capnp_union
            .variants
            .iter()
            .map(|field| -> Result<VariantDef, AnalyzerError> {
                let payload_type = Self::capnp_type_to_ir(&field.field_type)?;
                Ok(VariantDef {
                    name: to_pascal_case(&field.name),
                    payload: Some(VariantPayload::Tuple(vec![payload_type])),
                    metadata: VariantMetadata {
                        doc: None,
                        aliases: vec![field.name.clone()],
                        serde_hints: BTreeMap::new(),
                    },
                })
            })
            .collect();

        Ok(EnumDef {
            name: capnp_union.name.clone(),
            variants: variants?,
            tag_style: TagStyle::Internal {
                tag_field: "type".to_string(),
            },
            metadata: TypeMetadata::default(),
        })
    }
}

/// Extract inner type from List(T) syntax
fn extract_list_type(type_str: &str) -> Option<&str> {
    if type_str.starts_with("List(") && type_str.ends_with(')') {
        Some(&type_str[5..type_str.len() - 1])
    } else {
        None
    }
}

/// Convert snake_case or SCREAMING_CASE to PascalCase
fn to_pascal_case(s: &str) -> String {
    let mut result = String::new();
    let mut capitalize_next = true;

    for c in s.chars() {
        if c == '_' {
            capitalize_next = true;
        } else if capitalize_next {
            result.extend(c.to_uppercase());
            capitalize_next = false;
        } else {
            result.push(c.to_ascii_lowercase());
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::CapnProtoEnumValue;

    #[test]
    fn test_to_pascal_case() {
        assert_eq!(to_pascal_case("hello_world"), "HelloWorld");
        assert_eq!(to_pascal_case("active"), "Active");
        assert_eq!(to_pascal_case("user_name"), "UserName");
        assert_eq!(to_pascal_case("unknown"), "Unknown");
    }

    #[test]
    fn test_extract_list_type() {
        assert_eq!(extract_list_type("List(Int32)"), Some("Int32"));
        assert_eq!(extract_list_type("List(Text)"), Some("Text"));
        assert_eq!(extract_list_type("Int32"), None);
    }

    #[test]
    fn test_capnp_type_to_ir() {
        assert!(matches!(
            CapnProtoConverter::capnp_type_to_ir("Text").unwrap(),
            IrType::Primitive(PrimitiveType::String)
        ));
        assert!(matches!(
            CapnProtoConverter::capnp_type_to_ir("Int32").unwrap(),
            IrType::Primitive(PrimitiveType::I32)
        ));
        assert!(matches!(
            CapnProtoConverter::capnp_type_to_ir("Bool").unwrap(),
            IrType::Primitive(PrimitiveType::Bool)
        ));
        assert!(matches!(
            CapnProtoConverter::capnp_type_to_ir("Void").unwrap(),
            IrType::Special(SpecialType::Unit)
        ));
        assert!(matches!(
            CapnProtoConverter::capnp_type_to_ir("MyStruct").unwrap(),
            IrType::Reference(_)
        ));
    }

    #[test]
    fn test_convert_simple_struct() {
        let converter = CapnProtoConverter::new();

        let capnp_struct = CapnProtoStruct {
            name: "Person".to_string(),
            fields: vec![
                CapnProtoField {
                    name: "name".to_string(),
                    field_type: "Text".to_string(),
                    number: 0,
                    default_value: None,
                    annotations: vec![],
                },
                CapnProtoField {
                    name: "age".to_string(),
                    field_type: "Int32".to_string(),
                    number: 1,
                    default_value: None,
                    annotations: vec![],
                },
            ],
            inline_union: None,
            annotations: vec![],
        };

        let result = converter.convert_struct(&capnp_struct);
        assert!(result.is_ok());

        let struct_def = result.unwrap();
        assert_eq!(struct_def.name, "Person");
        assert_eq!(struct_def.fields.len(), 2);
        assert_eq!(
            struct_def.metadata.extra.get("zero_copy"),
            Some(&"true".to_string())
        );
    }

    #[test]
    fn test_convert_enum() {
        let converter = CapnProtoConverter::new();

        let capnp_enum = CapnProtoEnum {
            name: "Status".to_string(),
            values: vec![
                CapnProtoEnumValue {
                    name: "unknown".to_string(),
                    number: 0,
                    annotations: vec![],
                },
                CapnProtoEnumValue {
                    name: "active".to_string(),
                    number: 1,
                    annotations: vec![],
                },
                CapnProtoEnumValue {
                    name: "inactive".to_string(),
                    number: 2,
                    annotations: vec![],
                },
            ],
            annotations: vec![],
        };

        let result = converter.convert_enum(&capnp_enum);
        assert!(result.is_ok());

        let enum_def = result.unwrap();
        assert_eq!(enum_def.name, "Status");
        assert_eq!(enum_def.variants.len(), 3);
    }

    #[test]
    fn test_convert_list_field() {
        let converter = CapnProtoConverter::new();

        let field = CapnProtoField {
            name: "tags".to_string(),
            field_type: "List(Text)".to_string(),
            number: 0,
            default_value: None,
            annotations: vec![],
        };

        let result = converter.convert_field(&field);
        assert!(result.is_ok());

        let field_def = result.unwrap();
        assert!(matches!(
            field_def.ty,
            IrType::Container(ContainerType::Vec(_))
        ));
    }

    #[test]
    fn test_convert_data_field() {
        let converter = CapnProtoConverter::new();

        let field = CapnProtoField {
            name: "payload".to_string(),
            field_type: "Data".to_string(),
            number: 0,
            default_value: None,
            annotations: vec![],
        };

        let result = converter.convert_field(&field);
        assert!(result.is_ok());

        let field_def = result.unwrap();
        // Data should be Vec<U8>
        assert!(matches!(
            field_def.ty,
            IrType::Container(ContainerType::Vec(_))
        ));
    }

    #[test]
    fn test_field_number_metadata() {
        let converter = CapnProtoConverter::new();

        let field = CapnProtoField {
            name: "id".to_string(),
            field_type: "Int64".to_string(),
            number: 42,
            default_value: None,
            annotations: vec![],
        };

        let result = converter.convert_field(&field);
        assert!(result.is_ok());

        let field_def = result.unwrap();
        assert_eq!(
            field_def.metadata.serde_hints.get("field_number"),
            Some(&"42".to_string())
        );
    }

    #[test]
    fn test_default_value() {
        let converter = CapnProtoConverter::new();

        let field = CapnProtoField {
            name: "timeout".to_string(),
            field_type: "Int32".to_string(),
            number: 0,
            default_value: Some("30".to_string()),
            annotations: vec![],
        };

        let result = converter.convert_field(&field);
        assert!(result.is_ok());

        let field_def = result.unwrap();
        assert_eq!(
            field_def.metadata.default,
            Some(serde_json::Value::Number(30.into()))
        );
    }
}
