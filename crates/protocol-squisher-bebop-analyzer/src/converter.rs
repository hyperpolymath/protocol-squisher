// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Converter from parsed Bebop to protocol-squisher IR

use crate::parser::{BebopEnum, BebopField, BebopMessage, BebopStruct, ParsedBebop};
use crate::AnalyzerError;
use protocol_squisher_ir::{
    ContainerType, EnumDef, FieldDef, FieldMetadata, IrSchema, IrType, PrimitiveType, StructDef,
    TagStyle, TypeDef, TypeMetadata, VariantDef, VariantMetadata,
};
use std::collections::BTreeMap;

/// Converter from parsed Bebop to IR
#[derive(Debug, Default)]
pub struct BebopConverter {}

impl BebopConverter {
    /// Create a new converter
    pub fn new() -> Self {
        Self::default()
    }

    /// Convert a parsed Bebop to IR schema
    pub fn convert(&self, parsed: &ParsedBebop, name: &str) -> Result<IrSchema, AnalyzerError> {
        let mut ir = IrSchema::new(name, "bebop");
        let mut types = BTreeMap::new();

        // Convert top-level enums
        for bebop_enum in &parsed.enums {
            let enum_def = self.convert_enum(bebop_enum)?;
            types.insert(enum_def.name.clone(), TypeDef::Enum(enum_def));
        }

        // Convert top-level structs
        for bebop_struct in &parsed.structs {
            let struct_def = self.convert_struct(bebop_struct)?;
            types.insert(struct_def.name.clone(), TypeDef::Struct(struct_def));
        }

        // Convert top-level messages (versioned structs)
        for message in &parsed.messages {
            let struct_def = self.convert_message(message)?;
            types.insert(struct_def.name.clone(), TypeDef::Struct(struct_def));
        }

        // Add all types to IR
        for (type_name, type_def) in types {
            ir.add_type(type_name, type_def);
        }

        Ok(ir)
    }

    /// Convert a Bebop struct to IR struct
    fn convert_struct(&self, bebop_struct: &BebopStruct) -> Result<StructDef, AnalyzerError> {
        let fields = bebop_struct
            .fields
            .iter()
            .map(|f| self.convert_field(f))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(StructDef {
            name: bebop_struct.name.clone(),
            fields,
            metadata: TypeMetadata {
                doc: None,
                deprecated: None,
                serde_hints: BTreeMap::new(),
                extra: BTreeMap::new(),
            },
        })
    }

    /// Convert a Bebop message to IR struct
    fn convert_message(&self, message: &BebopMessage) -> Result<StructDef, AnalyzerError> {
        let fields = message
            .fields
            .iter()
            .map(|f| self.convert_field(f))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(StructDef {
            name: message.name.clone(),
            fields,
            metadata: TypeMetadata {
                doc: None,
                deprecated: None,
                serde_hints: BTreeMap::new(),
                extra: BTreeMap::new(),
            },
        })
    }

    /// Convert a Bebop field to IR field
    fn convert_field(&self, field: &BebopField) -> Result<FieldDef, AnalyzerError> {
        let base_type = self.convert_field_type(field)?;

        // Apply optional wrapper if needed
        let ty = if field.optional {
            IrType::Container(ContainerType::Option(Box::new(base_type)))
        } else {
            base_type
        };

        Ok(FieldDef {
            name: field.name.clone(),
            ty,
            optional: field.optional,
            constraints: vec![],
            metadata: FieldMetadata {
                doc: None,
                default: None,
                aliases: vec![],
                flatten: false,
                skip: field.deprecated,
                serde_hints: BTreeMap::new(),
            },
        })
    }

    /// Convert a Bebop field type string to IR type
    fn convert_field_type(&self, field: &BebopField) -> Result<IrType, AnalyzerError> {
        // Handle maps first
        if let Some((key_type, value_type)) = &field.map_types {
            let key_ir = self.bebop_type_to_ir(key_type)?;
            let value_ir = self.bebop_type_to_ir(value_type)?;
            return Ok(IrType::Container(ContainerType::Map(
                Box::new(key_ir),
                Box::new(value_ir),
            )));
        }

        // Handle arrays
        if field.is_array {
            let element_type = self.bebop_type_to_ir(&field.field_type)?;
            return Ok(IrType::Container(ContainerType::Vec(Box::new(
                element_type,
            ))));
        }

        // Regular type
        self.bebop_type_to_ir(&field.field_type)
    }

    /// Convert a Bebop type string to IR type
    fn bebop_type_to_ir(&self, type_str: &str) -> Result<IrType, AnalyzerError> {
        match type_str {
            // Boolean
            "bool" => Ok(IrType::Primitive(PrimitiveType::Bool)),

            // Integers
            "byte" => Ok(IrType::Primitive(PrimitiveType::U8)),
            "int16" => Ok(IrType::Primitive(PrimitiveType::I16)),
            "uint16" => Ok(IrType::Primitive(PrimitiveType::U16)),
            "int32" => Ok(IrType::Primitive(PrimitiveType::I32)),
            "uint32" => Ok(IrType::Primitive(PrimitiveType::U32)),
            "int64" => Ok(IrType::Primitive(PrimitiveType::I64)),
            "uint64" => Ok(IrType::Primitive(PrimitiveType::U64)),

            // Floats
            "float32" => Ok(IrType::Primitive(PrimitiveType::F32)),
            "float64" => Ok(IrType::Primitive(PrimitiveType::F64)),

            // String
            "string" => Ok(IrType::Primitive(PrimitiveType::String)),

            // GUID (represented as string with constraint)
            "guid" => Ok(IrType::Primitive(PrimitiveType::Uuid)),

            // Date (represented as i64 timestamp)
            "date" => Ok(IrType::Primitive(PrimitiveType::DateTime)),

            // User-defined types (structs, enums, messages)
            type_name => Ok(IrType::Reference(type_name.to_string())),
        }
    }

    /// Convert a Bebop enum to IR enum
    fn convert_enum(&self, bebop_enum: &BebopEnum) -> Result<EnumDef, AnalyzerError> {
        let variants: Vec<VariantDef> = bebop_enum
            .values
            .iter()
            .map(|v| VariantDef {
                name: to_pascal_case(&v.name),
                payload: None, // Bebop enums don't have payloads
                metadata: VariantMetadata {
                    doc: None,
                    aliases: vec![v.name.clone()],
                    serde_hints: BTreeMap::new(),
                },
            })
            .collect();

        Ok(EnumDef {
            name: bebop_enum.name.clone(),
            variants,
            tag_style: TagStyle::External,
            metadata: TypeMetadata::default(),
        })
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
    use crate::parser::BebopEnumValue;

    #[test]
    fn test_to_pascal_case() {
        assert_eq!(to_pascal_case("hello_world"), "HelloWorld");
        assert_eq!(to_pascal_case("ACTIVE"), "Active");
        assert_eq!(to_pascal_case("user_name"), "UserName");
        assert_eq!(to_pascal_case("STATUS_UNKNOWN"), "StatusUnknown");
    }

    #[test]
    fn test_bebop_type_to_ir() {
        let converter = BebopConverter::new();

        assert!(matches!(
            converter.bebop_type_to_ir("string").unwrap(),
            IrType::Primitive(PrimitiveType::String)
        ));
        assert!(matches!(
            converter.bebop_type_to_ir("int32").unwrap(),
            IrType::Primitive(PrimitiveType::I32)
        ));
        assert!(matches!(
            converter.bebop_type_to_ir("bool").unwrap(),
            IrType::Primitive(PrimitiveType::Bool)
        ));
        assert!(matches!(
            converter.bebop_type_to_ir("guid").unwrap(),
            IrType::Primitive(PrimitiveType::Uuid)
        ));
        assert!(matches!(
            converter.bebop_type_to_ir("date").unwrap(),
            IrType::Primitive(PrimitiveType::DateTime)
        ));
        assert!(matches!(
            converter.bebop_type_to_ir("MyMessage").unwrap(),
            IrType::Reference(_)
        ));
    }

    #[test]
    fn test_convert_simple_struct() {
        let converter = BebopConverter::new();

        let bebop_struct = BebopStruct {
            name: "Person".to_string(),
            fields: vec![
                BebopField {
                    name: "name".to_string(),
                    field_type: "string".to_string(),
                    number: None,
                    optional: false,
                    deprecated: false,
                    is_array: false,
                    map_types: None,
                },
                BebopField {
                    name: "age".to_string(),
                    field_type: "int32".to_string(),
                    number: None,
                    optional: false,
                    deprecated: false,
                    is_array: false,
                    map_types: None,
                },
            ],
            readonly: false,
        };

        let result = converter.convert_struct(&bebop_struct);
        assert!(result.is_ok());

        let struct_def = result.unwrap();
        assert_eq!(struct_def.name, "Person");
        assert_eq!(struct_def.fields.len(), 2);
    }

    #[test]
    fn test_convert_enum() {
        let converter = BebopConverter::new();

        let bebop_enum = BebopEnum {
            name: "Status".to_string(),
            values: vec![
                BebopEnumValue {
                    name: "Unknown".to_string(),
                    number: 0,
                },
                BebopEnumValue {
                    name: "Active".to_string(),
                    number: 1,
                },
                BebopEnumValue {
                    name: "Inactive".to_string(),
                    number: 2,
                },
            ],
        };

        let result = converter.convert_enum(&bebop_enum);
        assert!(result.is_ok());

        let enum_def = result.unwrap();
        assert_eq!(enum_def.name, "Status");
        assert_eq!(enum_def.variants.len(), 3);
    }

    #[test]
    fn test_convert_array_field() {
        let converter = BebopConverter::new();

        let field = BebopField {
            name: "tags".to_string(),
            field_type: "string".to_string(),
            number: None,
            optional: false,
            deprecated: false,
            is_array: true,
            map_types: None,
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
        let converter = BebopConverter::new();

        let field = BebopField {
            name: "settings".to_string(),
            field_type: "map".to_string(),
            number: None,
            optional: false,
            deprecated: false,
            is_array: false,
            map_types: Some(("string".to_string(), "string".to_string())),
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
        let converter = BebopConverter::new();

        let field = BebopField {
            name: "age".to_string(),
            field_type: "int32".to_string(),
            number: None,
            optional: true,
            deprecated: false,
            is_array: false,
            map_types: None,
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
}
