// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Converter from parsed Avro to protocol-squisher IR

use crate::parser::{AvroComplexSchema, AvroField, AvroSchema, AvroType, ParsedAvro};
use crate::AnalyzerError;
use protocol_squisher_ir::{
    ContainerType, EnumDef, FieldDef, FieldMetadata, IrSchema, IrType, PrimitiveType, StructDef,
    TagStyle, TypeDef, TypeMetadata, VariantDef, VariantMetadata,
};
use std::collections::BTreeMap;

/// Converter from parsed Avro to IR
#[derive(Debug, Default)]
pub struct AvroConverter {}

#[allow(dead_code)]
impl AvroConverter {
    /// Create a new converter
    pub fn new() -> Self {
        Self::default()
    }

    /// Convert a parsed Avro schema to IR schema
    pub fn convert(&self, parsed: &ParsedAvro, name: &str) -> Result<IrSchema, AnalyzerError> {
        let mut ir = IrSchema::new(name, "avro");
        let mut types = BTreeMap::new();
        let mut nested_types = Vec::new();

        // Convert all top-level types
        for avro_type in &parsed.types {
            match avro_type {
                AvroType::Record { name, .. } => {
                    let (struct_def, mut nested) = self.convert_record_with_nested(avro_type)?;
                    types.insert(name.clone(), TypeDef::Struct(struct_def));
                    nested_types.append(&mut nested);
                }
                AvroType::Enum { name, .. } => {
                    let enum_def = self.convert_enum(avro_type)?;
                    types.insert(name.clone(), TypeDef::Enum(enum_def));
                }
                AvroType::Fixed { name, size, .. } => {
                    // Fixed types are represented as byte arrays
                    let fixed_def = self.convert_fixed(name, *size)?;
                    types.insert(name.clone(), TypeDef::Struct(fixed_def));
                }
            }
        }

        // Add nested types
        for (type_name, type_def) in nested_types {
            types.insert(type_name, type_def);
        }

        // Add all types to IR
        for (type_name, type_def) in types {
            ir.add_type(type_name, type_def);
        }

        Ok(ir)
    }

    /// Convert an Avro record to IR struct
    fn convert_record(&self, avro_type: &AvroType) -> Result<StructDef, AnalyzerError> {
        let (struct_def, _) = self.convert_record_with_nested(avro_type)?;
        Ok(struct_def)
    }

    /// Convert an Avro record to IR struct, collecting nested type definitions
    fn convert_record_with_nested(
        &self,
        avro_type: &AvroType,
    ) -> Result<(StructDef, Vec<(String, TypeDef)>), AnalyzerError> {
        if let AvroType::Record {
            name,
            doc,
            aliases,
            fields,
            ..
        } = avro_type
        {
            let mut nested_types = Vec::new();
            let mut ir_fields = Vec::new();

            for field in fields {
                let (field_def, mut field_nested) = self.convert_field_with_nested(field)?;
                ir_fields.push(field_def);
                nested_types.append(&mut field_nested);
            }

            let mut extra = BTreeMap::new();
            if !aliases.is_empty() {
                extra.insert("avro_aliases".to_string(), format!("{:?}", aliases));
            }

            let struct_def = StructDef {
                name: name.clone(),
                fields: ir_fields,
                metadata: TypeMetadata {
                    doc: doc.clone(),
                    deprecated: None,
                    serde_hints: BTreeMap::new(),
                    extra,
                },
            };

            Ok((struct_def, nested_types))
        } else {
            Err(AnalyzerError::InvalidSchema(
                "Expected record type".to_string(),
            ))
        }
    }

    /// Convert an Avro enum to IR enum
    fn convert_enum(&self, avro_type: &AvroType) -> Result<EnumDef, AnalyzerError> {
        if let AvroType::Enum {
            name,
            doc,
            aliases,
            symbols,
            default: default_symbol,
            ..
        } = avro_type
        {
            let variants: Vec<VariantDef> = symbols
                .iter()
                .map(|symbol| {
                    let is_default = default_symbol.as_ref() == Some(symbol);
                    let mut aliases_vec = Vec::new();
                    if is_default {
                        aliases_vec.push("default".to_string());
                    }

                    VariantDef {
                        name: to_pascal_case(symbol),
                        payload: None, // Avro enums don't have payloads
                        metadata: VariantMetadata {
                            doc: None,
                            aliases: aliases_vec,
                            serde_hints: BTreeMap::new(),
                        },
                    }
                })
                .collect();

            let mut extra = BTreeMap::new();
            if !aliases.is_empty() {
                extra.insert(
                    "avro_aliases".to_string(),
                    format!("{:?}", aliases),
                );
            }

            Ok(EnumDef {
                name: name.clone(),
                variants,
                tag_style: TagStyle::External, // Avro uses runtime type tags
                metadata: TypeMetadata {
                    doc: doc.clone(),
                    deprecated: None,
                    serde_hints: BTreeMap::new(),
                    extra,
                },
            })
        } else {
            Err(AnalyzerError::InvalidSchema(
                "Expected enum type".to_string(),
            ))
        }
    }

    /// Convert an Avro fixed type to IR struct with byte array
    fn convert_fixed(&self, name: &str, size: usize) -> Result<StructDef, AnalyzerError> {
        // Represent fixed as a struct with a single byte array field
        let field = FieldDef {
            name: "bytes".to_string(),
            ty: IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
                PrimitiveType::U8,
            )))),
            optional: false,
            constraints: vec![], // TODO: Add length constraint when Constraint type supports it
            metadata: FieldMetadata {
                doc: Some(format!("Fixed-size byte array of {} bytes", size)),
                default: None,
                aliases: vec![],
                flatten: false,
                skip: false,
                serde_hints: BTreeMap::new(),
            },
        };

        let mut extra = BTreeMap::new();
        extra.insert("avro_fixed_size".to_string(), size.to_string());

        Ok(StructDef {
            name: name.to_string(),
            fields: vec![field],
            metadata: TypeMetadata {
                doc: Some(format!("Avro fixed type with size {}", size)),
                deprecated: None,
                serde_hints: BTreeMap::new(),
                extra,
            },
        })
    }

    /// Convert an Avro field to IR field
    fn convert_field(&self, field: &AvroField) -> Result<FieldDef, AnalyzerError> {
        let (field_def, _) = self.convert_field_with_nested(field)?;
        Ok(field_def)
    }

    /// Convert an Avro field to IR field, collecting nested type definitions
    fn convert_field_with_nested(
        &self,
        field: &AvroField,
    ) -> Result<(FieldDef, Vec<(String, TypeDef)>), AnalyzerError> {
        let (base_type, is_optional, nested_types) = self.convert_schema_with_nested(&field.schema)?;

        // Apply optional wrapper if needed
        let ty = if is_optional {
            IrType::Container(ContainerType::Option(Box::new(base_type)))
        } else {
            base_type
        };

        let mut serde_hints = BTreeMap::new();
        if field.default.is_some() {
            serde_hints.insert("avro_default".to_string(), format!("{:?}", field.default));
        }

        let field_def = FieldDef {
            name: field.name.clone(),
            ty,
            optional: is_optional,
            constraints: vec![],
            metadata: FieldMetadata {
                doc: field.doc.clone(),
                default: field.default.clone(),
                aliases: field.aliases.clone(),
                flatten: false,
                skip: false,
                serde_hints,
            },
        };

        Ok((field_def, nested_types))
    }

    /// Convert an Avro schema to IR type
    /// Returns (type, is_optional)
    fn convert_schema(&self, schema: &AvroSchema) -> Result<(IrType, bool), AnalyzerError> {
        let (ty, opt, _) = self.convert_schema_with_nested(schema)?;
        Ok((ty, opt))
    }

    /// Convert an Avro schema to IR type, collecting nested type definitions
    /// Returns (type, is_optional, nested_types)
    fn convert_schema_with_nested(
        &self,
        schema: &AvroSchema,
    ) -> Result<(IrType, bool, Vec<(String, TypeDef)>), AnalyzerError> {
        match schema {
            // Handle optional unions (["null", "T"])
            AvroSchema::Union(_) if schema.is_optional() => {
                if let Some(inner_schema) = schema.unwrap_optional() {
                    let (inner_type, _, nested) = self.convert_schema_with_nested(inner_schema)?;
                    Ok((inner_type, true, nested))
                } else {
                    Err(AnalyzerError::InvalidSchema(
                        "Invalid optional union".to_string(),
                    ))
                }
            }

            // Handle multi-variant unions (create enum)
            AvroSchema::Union(variants) => {
                let mut all_nested = Vec::new();
                let _variant_types: Vec<IrType> = variants
                    .iter()
                    .map(|v| {
                        let (ty, _, mut nested) = self.convert_schema_with_nested(v)?;
                        all_nested.append(&mut nested);
                        Ok::<IrType, AnalyzerError>(ty)
                    })
                    .collect::<Result<Vec<_>, AnalyzerError>>()?;

                // For now, treat as an untagged enum (TODO: improve this)
                // We could create a synthetic enum type here
                Ok((
                    IrType::Special(protocol_squisher_ir::SpecialType::Any),
                    false,
                    all_nested,
                ))
            }

            // Type name reference
            AvroSchema::Name(name) => {
                let ir_type = self.avro_type_to_ir(name)?;
                Ok((ir_type, false, vec![]))
            }

            // Complex schemas
            AvroSchema::Complex(complex) => {
                let (ir_type, nested) = self.convert_complex_schema_with_nested(complex)?;
                Ok((ir_type, false, nested))
            }
        }
    }

    /// Convert an Avro type name to IR type
    fn avro_type_to_ir(&self, type_name: &str) -> Result<IrType, AnalyzerError> {
        match type_name {
            // Primitives
            "null" => Ok(IrType::Special(protocol_squisher_ir::SpecialType::Unit)),
            "boolean" => Ok(IrType::Primitive(PrimitiveType::Bool)),
            "int" => Ok(IrType::Primitive(PrimitiveType::I32)),
            "long" => Ok(IrType::Primitive(PrimitiveType::I64)),
            "float" => Ok(IrType::Primitive(PrimitiveType::F32)),
            "double" => Ok(IrType::Primitive(PrimitiveType::F64)),
            "bytes" => Ok(IrType::Container(ContainerType::Vec(Box::new(
                IrType::Primitive(PrimitiveType::U8),
            )))),
            "string" => Ok(IrType::Primitive(PrimitiveType::String)),

            // User-defined type reference
            _ => Ok(IrType::Reference(type_name.to_string())),
        }
    }

    /// Convert a complex Avro schema to IR type
    fn convert_complex_schema(
        &self,
        complex: &AvroComplexSchema,
    ) -> Result<IrType, AnalyzerError> {
        let (ty, _) = self.convert_complex_schema_with_nested(complex)?;
        Ok(ty)
    }

    /// Convert a complex Avro schema to IR type, collecting nested type definitions
    fn convert_complex_schema_with_nested(
        &self,
        complex: &AvroComplexSchema,
    ) -> Result<(IrType, Vec<(String, TypeDef)>), AnalyzerError> {
        match complex {
            AvroComplexSchema::Array { items } => {
                let (element_type, _, nested) = self.convert_schema_with_nested(items)?;
                Ok((
                    IrType::Container(ContainerType::Vec(Box::new(element_type))),
                    nested,
                ))
            }

            AvroComplexSchema::Map { values } => {
                let (value_type, _, nested) = self.convert_schema_with_nested(values)?;
                // Avro maps always have string keys
                Ok((
                    IrType::Container(ContainerType::Map(
                        Box::new(IrType::Primitive(PrimitiveType::String)),
                        Box::new(value_type),
                    )),
                    nested,
                ))
            }

            AvroComplexSchema::Record {
                name,
                doc,
                aliases,
                fields,
                ..
            } => {
                // Inline record definition - convert and add to nested types
                let mut nested_types = Vec::new();
                let mut ir_fields = Vec::new();

                for field in fields {
                    let (field_def, mut field_nested) = self.convert_field_with_nested(field)?;
                    ir_fields.push(field_def);
                    nested_types.append(&mut field_nested);
                }

                let mut extra = BTreeMap::new();
                if !aliases.is_empty() {
                    extra.insert("avro_aliases".to_string(), format!("{:?}", aliases));
                }

                let struct_def = StructDef {
                    name: name.clone(),
                    fields: ir_fields,
                    metadata: TypeMetadata {
                        doc: doc.clone(),
                        deprecated: None,
                        serde_hints: BTreeMap::new(),
                        extra,
                    },
                };

                nested_types.push((name.clone(), TypeDef::Struct(struct_def)));
                Ok((IrType::Reference(name.clone()), nested_types))
            }

            AvroComplexSchema::Enum {
                name,
                doc,
                aliases,
                symbols,
                default: default_symbol,
                ..
            } => {
                // Inline enum definition - convert and add to nested types
                let variants: Vec<VariantDef> = symbols
                    .iter()
                    .map(|symbol| {
                        let is_default = default_symbol.as_ref() == Some(symbol);
                        let mut aliases_vec = Vec::new();
                        if is_default {
                            aliases_vec.push("default".to_string());
                        }

                        VariantDef {
                            name: to_pascal_case(symbol),
                            payload: None,
                            metadata: VariantMetadata {
                                doc: None,
                                aliases: aliases_vec,
                                serde_hints: BTreeMap::new(),
                            },
                        }
                    })
                    .collect();

                let mut extra = BTreeMap::new();
                if !aliases.is_empty() {
                    extra.insert("avro_aliases".to_string(), format!("{:?}", aliases));
                }

                let enum_def = EnumDef {
                    name: name.clone(),
                    variants,
                    tag_style: TagStyle::External,
                    metadata: TypeMetadata {
                        doc: doc.clone(),
                        deprecated: None,
                        serde_hints: BTreeMap::new(),
                        extra,
                    },
                };

                Ok((
                    IrType::Reference(name.clone()),
                    vec![(name.clone(), TypeDef::Enum(enum_def))],
                ))
            }

            AvroComplexSchema::Fixed { name, size, .. } => {
                // Inline fixed definition - convert and add to nested types
                let fixed_def = self.convert_fixed(name, *size)?;
                Ok((
                    IrType::Reference(name.clone()),
                    vec![(name.clone(), TypeDef::Struct(fixed_def))],
                ))
            }
        }
    }
}

/// Convert SCREAMING_CASE or snake_case to PascalCase
fn to_pascal_case(s: &str) -> String {
    let mut result = String::new();
    let mut capitalize_next = true;

    for c in s.chars() {
        if c == '_' || c == '-' {
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
    use crate::parser::AvroParser;

    #[test]
    fn test_to_pascal_case() {
        assert_eq!(to_pascal_case("UNKNOWN"), "Unknown");
        assert_eq!(to_pascal_case("ACTIVE_USER"), "ActiveUser");
        assert_eq!(to_pascal_case("status_code"), "StatusCode");
    }

    #[test]
    fn test_convert_simple_record() {
        let json = r#"
        {
            "type": "record",
            "name": "Person",
            "fields": [
                {"name": "name", "type": "string"},
                {"name": "age", "type": "int"}
            ]
        }
        "#;

        let parser = AvroParser::new();
        let parsed = parser.parse_str(json).unwrap();

        let converter = AvroConverter::new();
        let result = converter.convert(&parsed, "person");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Person"));

        if let Some(TypeDef::Struct(s)) = ir.types.get("Person") {
            assert_eq!(s.fields.len(), 2);
            assert_eq!(s.fields[0].name, "name");
            assert_eq!(s.fields[1].name, "age");
        } else {
            panic!("Expected struct type");
        }
    }

    #[test]
    fn test_convert_optional_field() {
        let json = r#"
        {
            "type": "record",
            "name": "User",
            "fields": [
                {"name": "email", "type": ["null", "string"]}
            ]
        }
        "#;

        let parser = AvroParser::new();
        let parsed = parser.parse_str(json).unwrap();

        let converter = AvroConverter::new();
        let result = converter.convert(&parsed, "user");
        assert!(result.is_ok());

        let ir = result.unwrap();
        if let Some(TypeDef::Struct(s)) = ir.types.get("User") {
            assert!(s.fields[0].optional);
            assert!(matches!(
                s.fields[0].ty,
                IrType::Container(ContainerType::Option(_))
            ));
        }
    }

    #[test]
    fn test_convert_array() {
        let json = r#"
        {
            "type": "record",
            "name": "List",
            "fields": [
                {"name": "items", "type": {"type": "array", "items": "string"}}
            ]
        }
        "#;

        let parser = AvroParser::new();
        let parsed = parser.parse_str(json).unwrap();

        let converter = AvroConverter::new();
        let result = converter.convert(&parsed, "list");
        assert!(result.is_ok());

        let ir = result.unwrap();
        if let Some(TypeDef::Struct(s)) = ir.types.get("List") {
            assert!(matches!(
                s.fields[0].ty,
                IrType::Container(ContainerType::Vec(_))
            ));
        }
    }

    #[test]
    fn test_convert_map() {
        let json = r#"
        {
            "type": "record",
            "name": "Config",
            "fields": [
                {"name": "settings", "type": {"type": "map", "values": "int"}}
            ]
        }
        "#;

        let parser = AvroParser::new();
        let parsed = parser.parse_str(json).unwrap();

        let converter = AvroConverter::new();
        let result = converter.convert(&parsed, "config");
        assert!(result.is_ok());

        let ir = result.unwrap();
        if let Some(TypeDef::Struct(s)) = ir.types.get("Config") {
            assert!(matches!(
                s.fields[0].ty,
                IrType::Container(ContainerType::Map(_, _))
            ));
        }
    }

    #[test]
    fn test_convert_enum() {
        let json = r#"
        {
            "type": "enum",
            "name": "Status",
            "symbols": ["UNKNOWN", "ACTIVE", "INACTIVE"]
        }
        "#;

        let parser = AvroParser::new();
        let parsed = parser.parse_str(json).unwrap();

        let converter = AvroConverter::new();
        let result = converter.convert(&parsed, "status");
        assert!(result.is_ok());

        let ir = result.unwrap();
        if let Some(TypeDef::Enum(e)) = ir.types.get("Status") {
            assert_eq!(e.variants.len(), 3);
            assert_eq!(e.variants[0].name, "Unknown");
            assert_eq!(e.variants[1].name, "Active");
            assert_eq!(e.variants[2].name, "Inactive");
        } else {
            panic!("Expected enum type");
        }
    }

    #[test]
    fn test_convert_fixed() {
        let json = r#"
        {
            "type": "fixed",
            "name": "UUID",
            "size": 16
        }
        "#;

        let parser = AvroParser::new();
        let parsed = parser.parse_str(json).unwrap();

        let converter = AvroConverter::new();
        let result = converter.convert(&parsed, "uuid");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("UUID"));
    }

    #[test]
    fn test_avro_primitives() {
        let converter = AvroConverter::new();

        assert!(matches!(
            converter.avro_type_to_ir("boolean").unwrap(),
            IrType::Primitive(PrimitiveType::Bool)
        ));
        assert!(matches!(
            converter.avro_type_to_ir("int").unwrap(),
            IrType::Primitive(PrimitiveType::I32)
        ));
        assert!(matches!(
            converter.avro_type_to_ir("long").unwrap(),
            IrType::Primitive(PrimitiveType::I64)
        ));
        assert!(matches!(
            converter.avro_type_to_ir("float").unwrap(),
            IrType::Primitive(PrimitiveType::F32)
        ));
        assert!(matches!(
            converter.avro_type_to_ir("double").unwrap(),
            IrType::Primitive(PrimitiveType::F64)
        ));
        assert!(matches!(
            converter.avro_type_to_ir("string").unwrap(),
            IrType::Primitive(PrimitiveType::String)
        ));
    }
}
