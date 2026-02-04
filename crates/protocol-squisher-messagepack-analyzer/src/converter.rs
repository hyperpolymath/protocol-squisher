// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Converter from parsed JSON Schema to protocol-squisher IR

use crate::parser::{ParsedSchema, SchemaObject, SchemaType};
use crate::AnalyzerError;
use protocol_squisher_ir::*;

/// Converter from JSON Schema to IR
#[derive(Debug, Default)]
pub struct MessagePackConverter {}

impl MessagePackConverter {
    /// Create a new converter
    pub fn new() -> Self {
        Self::default()
    }

    /// Convert parsed JSON Schema to IR
    pub fn convert(
        &self,
        parsed: &ParsedSchema,
        schema_name: &str,
    ) -> Result<IrSchema, AnalyzerError> {
        let mut schema = IrSchema::new(schema_name, "messagepack");
        schema.version = "1.0.0".to_string();

        // Convert root schema to a type
        if parsed.root.schema_type == Some(SchemaType::Object) {
            let type_name = Self::capitalize(schema_name);
            let type_def = self.convert_object(&parsed.root, &type_name)?;
            schema.add_type(type_name.clone(), type_def);
            schema.add_root(type_name);
        } else {
            return Err(AnalyzerError::InvalidSchema(
                "Root schema must be an object".to_string(),
            ));
        }

        Ok(schema)
    }

    /// Convert a JSON Schema object to an IR struct
    fn convert_object(
        &self,
        obj: &SchemaObject,
        name: &str,
    ) -> Result<TypeDef, AnalyzerError> {
        let mut fields = Vec::new();

        for (field_name, field_schema) in &obj.properties {
            let field_type = self.convert_type(field_schema)?;
            let optional = !obj.required.contains(field_name);
            let constraints = self.extract_constraints(field_schema);

            let mut metadata = FieldMetadata::default();
            if let Some(desc) = &field_schema.description {
                metadata.doc = Some(desc.clone());
            }

            fields.push(FieldDef {
                name: field_name.clone(),
                ty: if optional {
                    IrType::Container(ContainerType::Option(Box::new(field_type)))
                } else {
                    field_type
                },
                optional,
                constraints,
                metadata,
            });
        }

        let mut type_metadata = TypeMetadata::default();
        if let Some(desc) = &obj.description {
            type_metadata.doc = Some(desc.clone());
        }
        type_metadata.extra.insert(
            "messagepack_dynamic".to_string(),
            "true".to_string(),
        );

        Ok(TypeDef::Struct(StructDef {
            name: name.to_string(),
            fields,
            metadata: type_metadata,
        }))
    }

    /// Convert a JSON Schema type to an IR type
    fn convert_type(&self, schema: &SchemaObject) -> Result<IrType, AnalyzerError> {
        // Handle empty schema (any type - dynamic)
        if schema.schema_type.is_none() {
            return Ok(IrType::Special(SpecialType::Any));
        }

        match schema.schema_type.unwrap() {
            SchemaType::Null => Ok(IrType::Special(SpecialType::Unit)),
            SchemaType::Boolean => Ok(IrType::Primitive(PrimitiveType::Bool)),
            SchemaType::Integer => {
                // MessagePack uses variable-length encoding, default to I64
                Ok(IrType::Primitive(PrimitiveType::I64))
            }
            SchemaType::Number => {
                // MessagePack float, default to F64
                Ok(IrType::Primitive(PrimitiveType::F64))
            }
            SchemaType::String => {
                // Check for format hints
                if let Some(format) = &schema.format {
                    match format.as_str() {
                        "date-time" => Ok(IrType::Primitive(PrimitiveType::DateTime)),
                        "date" => Ok(IrType::Primitive(PrimitiveType::Date)),
                        "time" => Ok(IrType::Primitive(PrimitiveType::Time)),
                        "uuid" => Ok(IrType::Primitive(PrimitiveType::Uuid)),
                        _ => Ok(IrType::Primitive(PrimitiveType::String)),
                    }
                } else {
                    Ok(IrType::Primitive(PrimitiveType::String))
                }
            }
            SchemaType::Array => {
                if let Some(items) = &schema.items {
                    let item_type = self.convert_type(items)?;
                    Ok(IrType::Container(ContainerType::Vec(Box::new(item_type))))
                } else {
                    // Array of any type
                    Ok(IrType::Container(ContainerType::Vec(Box::new(
                        IrType::Special(SpecialType::Any),
                    ))))
                }
            }
            SchemaType::Object => {
                if schema.properties.is_empty() {
                    // Map<String, Any> for generic objects
                    Ok(IrType::Container(ContainerType::Map(
                        Box::new(IrType::Primitive(PrimitiveType::String)),
                        Box::new(IrType::Special(SpecialType::Any)),
                    )))
                } else {
                    // Nested object - would need recursive handling
                    // For now, treat as a map
                    Ok(IrType::Container(ContainerType::Map(
                        Box::new(IrType::Primitive(PrimitiveType::String)),
                        Box::new(IrType::Special(SpecialType::Any)),
                    )))
                }
            }
        }
    }

    /// Extract constraints from JSON Schema
    fn extract_constraints(&self, schema: &SchemaObject) -> Vec<Constraint> {
        let mut constraints = Vec::new();

        // Numeric constraints
        if let Some(min) = schema.minimum {
            constraints.push(Constraint::Min(NumberValue::Float(min)));
        }
        if let Some(max) = schema.maximum {
            constraints.push(Constraint::Max(NumberValue::Float(max)));
        }

        // String constraints
        if let Some(min_len) = schema.min_length {
            constraints.push(Constraint::MinLength(min_len));
        }
        if let Some(max_len) = schema.max_length {
            constraints.push(Constraint::MaxLength(max_len));
        }
        if let Some(pattern) = &schema.pattern {
            constraints.push(Constraint::Pattern(pattern.clone()));
        }

        // Enum constraint
        if let Some(enum_values) = &schema.enum_values {
            if !enum_values.is_empty() {
                constraints.push(Constraint::OneOf(enum_values.clone()));
            }
        }

        constraints
    }

    /// Convert to PascalCase (capitalize each word)
    fn capitalize(s: &str) -> String {
        s.split(&['_', '-', ' '][..])
            .filter(|word| !word.is_empty())
            .map(|word| {
                let mut chars = word.chars();
                match chars.next() {
                    None => String::new(),
                    Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
                }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::MessagePackParser;

    #[test]
    fn test_convert_simple_object() {
        let json = r#"{
            "type": "object",
            "properties": {
                "name": { "type": "string" },
                "age": { "type": "integer" }
            }
        }"#;

        let parser = MessagePackParser::new();
        let parsed = parser.parse_str(json).unwrap();

        let converter = MessagePackConverter::new();
        let result = converter.convert(&parsed, "person");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert_eq!(ir.types.len(), 1);
        assert!(ir.types.contains_key("Person"));
    }

    #[test]
    fn test_convert_required_fields() {
        let json = r#"{
            "type": "object",
            "properties": {
                "id": { "type": "integer" },
                "name": { "type": "string" }
            },
            "required": ["id"]
        }"#;

        let parser = MessagePackParser::new();
        let parsed = parser.parse_str(json).unwrap();

        let converter = MessagePackConverter::new();
        let ir = converter.convert(&parsed, "user").unwrap();

        if let Some(TypeDef::Struct(s)) = ir.types.get("User") {
            // id is required (not wrapped in Option)
            let id_field = s.fields.iter().find(|f| f.name == "id").unwrap();
            assert!(!id_field.optional);

            // name is optional (wrapped in Option)
            let name_field = s.fields.iter().find(|f| f.name == "name").unwrap();
            assert!(name_field.optional);
        } else {
            panic!("Expected User struct");
        }
    }

    #[test]
    fn test_convert_array_field() {
        let json = r#"{
            "type": "object",
            "properties": {
                "tags": {
                    "type": "array",
                    "items": { "type": "string" }
                }
            }
        }"#;

        let parser = MessagePackParser::new();
        let parsed = parser.parse_str(json).unwrap();

        let converter = MessagePackConverter::new();
        let ir = converter.convert(&parsed, "tagged").unwrap();

        if let Some(TypeDef::Struct(s)) = ir.types.get("Tagged") {
            let tags_field = s.fields.iter().find(|f| f.name == "tags").unwrap();
            // Should be Vec<String> wrapped in Option (since not required)
            match &tags_field.ty {
                IrType::Container(ContainerType::Option(inner)) => {
                    match inner.as_ref() {
                        IrType::Container(ContainerType::Vec(item)) => {
                            match item.as_ref() {
                                IrType::Primitive(PrimitiveType::String) => {},
                                _ => panic!("Expected String item type"),
                            }
                        }
                        _ => panic!("Expected Vec container"),
                    }
                }
                _ => panic!("Expected Option wrapper"),
            }
        } else {
            panic!("Expected Tagged struct");
        }
    }

    #[test]
    fn test_convert_constraints() {
        let json = r#"{
            "type": "object",
            "properties": {
                "age": {
                    "type": "integer",
                    "minimum": 0,
                    "maximum": 150
                },
                "username": {
                    "type": "string",
                    "minLength": 3,
                    "maxLength": 20,
                    "pattern": "^[a-zA-Z0-9_]+$"
                }
            }
        }"#;

        let parser = MessagePackParser::new();
        let parsed = parser.parse_str(json).unwrap();

        let converter = MessagePackConverter::new();
        let ir = converter.convert(&parsed, "user").unwrap();

        if let Some(TypeDef::Struct(s)) = ir.types.get("User") {
            let age_field = s.fields.iter().find(|f| f.name == "age").unwrap();
            assert!(age_field.constraints.contains(&Constraint::Min(NumberValue::Float(0.0))));
            assert!(age_field.constraints.contains(&Constraint::Max(NumberValue::Float(150.0))));

            let username_field = s.fields.iter().find(|f| f.name == "username").unwrap();
            assert!(username_field.constraints.contains(&Constraint::MinLength(3)));
            assert!(username_field.constraints.contains(&Constraint::MaxLength(20)));
            assert!(username_field.constraints.iter().any(|c| matches!(c, Constraint::Pattern(_))));
        } else {
            panic!("Expected User struct");
        }
    }

    #[test]
    fn test_convert_format_hints() {
        let json = r#"{
            "type": "object",
            "properties": {
                "created_at": {
                    "type": "string",
                    "format": "date-time"
                },
                "user_id": {
                    "type": "string",
                    "format": "uuid"
                }
            }
        }"#;

        let parser = MessagePackParser::new();
        let parsed = parser.parse_str(json).unwrap();

        let converter = MessagePackConverter::new();
        let ir = converter.convert(&parsed, "record").unwrap();

        if let Some(TypeDef::Struct(s)) = ir.types.get("Record") {
            let created_field = s.fields.iter().find(|f| f.name == "created_at").unwrap();
            // Should map to DateTime type
            match &created_field.ty {
                IrType::Container(ContainerType::Option(inner)) => {
                    match inner.as_ref() {
                        IrType::Primitive(PrimitiveType::DateTime) => {},
                        _ => panic!("Expected DateTime type"),
                    }
                }
                _ => panic!("Expected Option wrapper"),
            }

            let id_field = s.fields.iter().find(|f| f.name == "user_id").unwrap();
            // Should map to Uuid type
            match &id_field.ty {
                IrType::Container(ContainerType::Option(inner)) => {
                    match inner.as_ref() {
                        IrType::Primitive(PrimitiveType::Uuid) => {},
                        _ => panic!("Expected Uuid type"),
                    }
                }
                _ => panic!("Expected Option wrapper"),
            }
        } else {
            panic!("Expected Record struct");
        }
    }

    #[test]
    fn test_dynamic_field() {
        let json = r#"{
            "type": "object",
            "properties": {
                "dynamic_field": {}
            }
        }"#;

        let parser = MessagePackParser::new();
        let parsed = parser.parse_str(json).unwrap();

        let converter = MessagePackConverter::new();
        let ir = converter.convert(&parsed, "dynamic").unwrap();

        if let Some(TypeDef::Struct(s)) = ir.types.get("Dynamic") {
            let field = s.fields.iter().find(|f| f.name == "dynamic_field").unwrap();
            // Should map to Any type (dynamic)
            match &field.ty {
                IrType::Container(ContainerType::Option(inner)) => {
                    match inner.as_ref() {
                        IrType::Special(SpecialType::Any) => {},
                        _ => panic!("Expected Any type for dynamic field"),
                    }
                }
                _ => panic!("Expected Option wrapper"),
            }
        } else {
            panic!("Expected Dynamic struct");
        }
    }

    #[test]
    fn test_messagepack_metadata() {
        let json = r#"{
            "type": "object",
            "properties": {
                "value": { "type": "string" }
            }
        }"#;

        let parser = MessagePackParser::new();
        let parsed = parser.parse_str(json).unwrap();

        let converter = MessagePackConverter::new();
        let ir = converter.convert(&parsed, "test").unwrap();

        if let Some(TypeDef::Struct(s)) = ir.types.get("Test") {
            // Should have messagepack_dynamic metadata
            assert_eq!(
                s.metadata.extra.get("messagepack_dynamic"),
                Some(&"true".to_string())
            );
        } else {
            panic!("Expected Test struct");
        }
    }
}
