// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Converter from parsed Thrift to protocol-squisher IR

use crate::parser::{
    FieldModifier, ParsedThrift, ThriftEnum, ThriftException, ThriftField, ThriftStruct,
};
use crate::AnalyzerError;
use serde_json;
use protocol_squisher_ir::{
    ContainerType, EnumDef, FieldDef, FieldMetadata, IrSchema, IrType, PrimitiveType, StructDef,
    TagStyle, TypeDef, TypeMetadata, VariantDef, VariantMetadata,
};
use std::collections::BTreeMap;

/// Converter from parsed Thrift to IR
#[derive(Debug, Default)]
pub struct ThriftConverter {
    /// Type aliases from typedef declarations
    typedefs: BTreeMap<String, String>,
}

impl ThriftConverter {
    /// Create a new converter
    pub fn new() -> Self {
        Self::default()
    }

    /// Convert a parsed Thrift to IR schema
    pub fn convert(&self, parsed: &ParsedThrift, name: &str) -> Result<IrSchema, AnalyzerError> {
        let converter = Self {
            typedefs: parsed
                .typedefs
                .iter()
                .map(|td| (td.name.clone(), td.underlying_type.clone()))
                .collect(),
        };

        let mut ir = IrSchema::new(name, "thrift");
        let mut types = BTreeMap::new();

        // Convert top-level enums
        for thrift_enum in &parsed.enums {
            let enum_def = converter.convert_enum(thrift_enum)?;
            types.insert(enum_def.name.clone(), TypeDef::Enum(enum_def));
        }

        // Convert top-level structs
        for thrift_struct in &parsed.structs {
            let struct_def = converter.convert_struct(thrift_struct)?;
            types.insert(struct_def.name.clone(), TypeDef::Struct(struct_def));
        }

        // Convert top-level exceptions (as structs with metadata)
        for exception in &parsed.exceptions {
            let struct_def = converter.convert_exception(exception)?;
            types.insert(struct_def.name.clone(), TypeDef::Struct(struct_def));
        }

        // Add all types to IR
        for (type_name, type_def) in types {
            ir.add_type(type_name, type_def);
        }

        Ok(ir)
    }

    /// Convert a Thrift struct to IR struct
    fn convert_struct(&self, thrift_struct: &ThriftStruct) -> Result<StructDef, AnalyzerError> {
        let fields = thrift_struct
            .fields
            .iter()
            .map(|f| self.convert_field(f))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(StructDef {
            name: thrift_struct.name.clone(),
            fields,
            metadata: TypeMetadata {
                doc: None,
                deprecated: None,
                serde_hints: BTreeMap::new(),
                extra: BTreeMap::new(),
            },
        })
    }

    /// Convert a Thrift exception to IR struct
    fn convert_exception(
        &self,
        exception: &ThriftException,
    ) -> Result<StructDef, AnalyzerError> {
        let fields = exception
            .fields
            .iter()
            .map(|f| self.convert_field(f))
            .collect::<Result<Vec<_>, _>>()?;

        let mut extra = BTreeMap::new();
        extra.insert("is_exception".to_string(), "true".to_string());

        Ok(StructDef {
            name: exception.name.clone(),
            fields,
            metadata: TypeMetadata {
                doc: None,
                deprecated: None,
                serde_hints: BTreeMap::new(),
                extra,
            },
        })
    }

    /// Convert a Thrift field to IR field
    fn convert_field(&self, field: &ThriftField) -> Result<FieldDef, AnalyzerError> {
        let base_type = self.convert_field_type(&field.field_type)?;

        // Apply optional wrapper if needed
        let (ty, optional) = match field.modifier {
            FieldModifier::Optional => (
                IrType::Container(ContainerType::Option(Box::new(base_type))),
                true,
            ),
            FieldModifier::Required | FieldModifier::Default => (base_type, false),
        };

        // Convert default value string to JSON value
        let default_json = field.default_value.as_ref().and_then(|v| {
            // Try to parse as JSON, or wrap as string if it fails
            serde_json::from_str(v).ok().or_else(|| {
                Some(serde_json::Value::String(v.trim_matches('"').to_string()))
            })
        });

        Ok(FieldDef {
            name: field.name.clone(),
            ty,
            optional,
            constraints: vec![],
            metadata: FieldMetadata {
                doc: None,
                default: default_json,
                aliases: vec![],
                flatten: false,
                skip: false,
                serde_hints: BTreeMap::new(),
            },
        })
    }

    /// Convert a Thrift field type string to IR type
    fn convert_field_type(&self, field_type: &str) -> Result<IrType, AnalyzerError> {
        // Handle list<T>
        if field_type.starts_with("list<") {
            let inner = extract_generic_type(field_type, "list")?;
            let element_type = self.convert_field_type(&inner)?;
            return Ok(IrType::Container(ContainerType::Vec(Box::new(
                element_type,
            ))));
        }

        // Handle set<T> (represented as Vec<T> with uniqueness constraint)
        if field_type.starts_with("set<") {
            let inner = extract_generic_type(field_type, "set")?;
            let element_type = self.convert_field_type(&inner)?;
            return Ok(IrType::Container(ContainerType::Vec(Box::new(
                element_type,
            ))));
        }

        // Handle map<K, V>
        if field_type.starts_with("map<") {
            let (key_type, value_type) = extract_map_types(field_type)?;
            let key_ir = self.convert_field_type(&key_type)?;
            let value_ir = self.convert_field_type(&value_type)?;
            return Ok(IrType::Container(ContainerType::Map(
                Box::new(key_ir),
                Box::new(value_ir),
            )));
        }

        // Check if it's a typedef
        if let Some(underlying_type) = self.typedefs.get(field_type) {
            return self.convert_field_type(underlying_type);
        }

        // Regular type
        self.thrift_type_to_ir(field_type)
    }

    /// Convert a Thrift type string to IR type
    fn thrift_type_to_ir(&self, type_str: &str) -> Result<IrType, AnalyzerError> {
        match type_str {
            // Boolean
            "bool" => Ok(IrType::Primitive(PrimitiveType::Bool)),

            // Integers
            "byte" | "i8" => Ok(IrType::Primitive(PrimitiveType::I8)),
            "i16" => Ok(IrType::Primitive(PrimitiveType::I16)),
            "i32" => Ok(IrType::Primitive(PrimitiveType::I32)),
            "i64" => Ok(IrType::Primitive(PrimitiveType::I64)),

            // Floats
            "double" => Ok(IrType::Primitive(PrimitiveType::F64)),

            // String
            "string" => Ok(IrType::Primitive(PrimitiveType::String)),

            // Binary (represented as Vec<u8>)
            "binary" => Ok(IrType::Container(ContainerType::Vec(Box::new(
                IrType::Primitive(PrimitiveType::U8),
            )))),

            // User-defined types (structs, enums, exceptions)
            type_name => Ok(IrType::Reference(type_name.to_string())),
        }
    }

    /// Convert a Thrift enum to IR enum
    fn convert_enum(&self, thrift_enum: &ThriftEnum) -> Result<EnumDef, AnalyzerError> {
        let variants: Vec<VariantDef> = thrift_enum
            .values
            .iter()
            .map(|v| VariantDef {
                name: to_pascal_case(&v.name),
                payload: None, // Thrift enums don't have payloads
                metadata: VariantMetadata {
                    doc: None,
                    aliases: vec![v.name.clone()],
                    serde_hints: BTreeMap::new(),
                },
            })
            .collect();

        Ok(EnumDef {
            name: thrift_enum.name.clone(),
            variants,
            tag_style: TagStyle::External,
            metadata: TypeMetadata::default(),
        })
    }
}

/// Extract the generic type parameter from a type like "list<T>"
fn extract_generic_type(type_str: &str, container: &str) -> Result<String, AnalyzerError> {
    let prefix = format!("{}<", container);
    if let Some(start) = type_str.find(&prefix) {
        let inner_start = start + prefix.len();
        if let Some(end) = type_str.rfind('>') {
            return Ok(type_str[inner_start..end].trim().to_string());
        }
    }
    Err(AnalyzerError::ParseError(format!(
        "Invalid {} type: {}",
        container, type_str
    )))
}

/// Extract key and value types from a map type like "map<K, V>"
fn extract_map_types(type_str: &str) -> Result<(String, String), AnalyzerError> {
    if let Some(start) = type_str.find("map<") {
        let inner_start = start + 4;
        if let Some(end) = type_str.rfind('>') {
            let inner = &type_str[inner_start..end];
            let parts: Vec<&str> = inner.split(',').collect();
            if parts.len() == 2 {
                return Ok((parts[0].trim().to_string(), parts[1].trim().to_string()));
            }
        }
    }
    Err(AnalyzerError::ParseError(format!(
        "Invalid map type: {}",
        type_str
    )))
}

/// Convert SCREAMING_CASE or snake_case to PascalCase
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
    use crate::parser::ThriftEnumValue;

    #[test]
    fn test_to_pascal_case() {
        assert_eq!(to_pascal_case("HELLO_WORLD"), "HelloWorld");
        assert_eq!(to_pascal_case("ACTIVE"), "Active");
        assert_eq!(to_pascal_case("user_name"), "UserName");
        assert_eq!(to_pascal_case("STATUS_UNKNOWN"), "StatusUnknown");
    }

    #[test]
    fn test_extract_generic_type() {
        assert_eq!(
            extract_generic_type("list<string>", "list").unwrap(),
            "string"
        );
        assert_eq!(extract_generic_type("list<i32>", "list").unwrap(), "i32");
        assert_eq!(
            extract_generic_type("set<User>", "set").unwrap(),
            "User"
        );
    }

    #[test]
    fn test_extract_map_types() {
        let (key, value) = extract_map_types("map<string, i32>").unwrap();
        assert_eq!(key, "string");
        assert_eq!(value, "i32");

        let (key, value) = extract_map_types("map<i64, User>").unwrap();
        assert_eq!(key, "i64");
        assert_eq!(value, "User");
    }

    #[test]
    fn test_thrift_type_to_ir() {
        let converter = ThriftConverter::new();

        assert!(matches!(
            converter.thrift_type_to_ir("string").unwrap(),
            IrType::Primitive(PrimitiveType::String)
        ));
        assert!(matches!(
            converter.thrift_type_to_ir("i32").unwrap(),
            IrType::Primitive(PrimitiveType::I32)
        ));
        assert!(matches!(
            converter.thrift_type_to_ir("bool").unwrap(),
            IrType::Primitive(PrimitiveType::Bool)
        ));
        assert!(matches!(
            converter.thrift_type_to_ir("double").unwrap(),
            IrType::Primitive(PrimitiveType::F64)
        ));
        assert!(matches!(
            converter.thrift_type_to_ir("MyStruct").unwrap(),
            IrType::Reference(_)
        ));
    }

    #[test]
    fn test_convert_simple_struct() {
        let converter = ThriftConverter::new();

        let thrift_struct = ThriftStruct {
            name: "Person".to_string(),
            fields: vec![
                ThriftField {
                    name: "name".to_string(),
                    field_type: "string".to_string(),
                    number: 1,
                    modifier: FieldModifier::Required,
                    default_value: None,
                },
                ThriftField {
                    name: "age".to_string(),
                    field_type: "i32".to_string(),
                    number: 2,
                    modifier: FieldModifier::Required,
                    default_value: None,
                },
            ],
        };

        let result = converter.convert_struct(&thrift_struct);
        assert!(result.is_ok());

        let struct_def = result.unwrap();
        assert_eq!(struct_def.name, "Person");
        assert_eq!(struct_def.fields.len(), 2);
    }

    #[test]
    fn test_convert_enum() {
        let converter = ThriftConverter::new();

        let thrift_enum = ThriftEnum {
            name: "Status".to_string(),
            values: vec![
                ThriftEnumValue {
                    name: "UNKNOWN".to_string(),
                    number: 0,
                },
                ThriftEnumValue {
                    name: "ACTIVE".to_string(),
                    number: 1,
                },
                ThriftEnumValue {
                    name: "INACTIVE".to_string(),
                    number: 2,
                },
            ],
        };

        let result = converter.convert_enum(&thrift_enum);
        assert!(result.is_ok());

        let enum_def = result.unwrap();
        assert_eq!(enum_def.name, "Status");
        assert_eq!(enum_def.variants.len(), 3);
    }

    #[test]
    fn test_convert_list_field() {
        let converter = ThriftConverter::new();

        let field = ThriftField {
            name: "tags".to_string(),
            field_type: "list<string>".to_string(),
            number: 1,
            modifier: FieldModifier::Required,
            default_value: None,
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
    fn test_convert_map_field() {
        let converter = ThriftConverter::new();

        let field = ThriftField {
            name: "settings".to_string(),
            field_type: "map<string, string>".to_string(),
            number: 1,
            modifier: FieldModifier::Required,
            default_value: None,
        };

        let result = converter.convert_field(&field);
        assert!(result.is_ok());

        let field_def = result.unwrap();
        assert!(matches!(
            field_def.ty,
            IrType::Container(ContainerType::Map(_, _))
        ));
    }

    #[test]
    fn test_convert_optional_field() {
        let converter = ThriftConverter::new();

        let field = ThriftField {
            name: "age".to_string(),
            field_type: "i32".to_string(),
            number: 1,
            modifier: FieldModifier::Optional,
            default_value: None,
        };

        let result = converter.convert_field(&field);
        assert!(result.is_ok());

        let field_def = result.unwrap();
        assert!(field_def.optional);
        assert!(matches!(
            field_def.ty,
            IrType::Container(ContainerType::Option(_))
        ));
    }

    #[test]
    fn test_convert_field_with_default() {
        let converter = ThriftConverter::new();

        let field = ThriftField {
            name: "timeout".to_string(),
            field_type: "i32".to_string(),
            number: 1,
            modifier: FieldModifier::Default,
            default_value: Some("30".to_string()),
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
