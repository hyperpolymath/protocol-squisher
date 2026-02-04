// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Converter from parsed FlatBuffers to protocol-squisher IR

use crate::parser::{
    FbsEnum, FbsField, FbsStruct, FbsTable, FbsUnion, ParsedFlatBuffers,
};
use crate::AnalyzerError;
use protocol_squisher_ir::{
    ContainerType, EnumDef, FieldDef, FieldMetadata, IrSchema, IrType, PrimitiveType, StructDef,
    TagStyle, TypeDef, TypeMetadata, VariantDef, VariantMetadata,
};
use std::collections::BTreeMap;

/// Converter from parsed FlatBuffers to IR
#[derive(Debug, Default)]
pub struct FlatBuffersConverter {}

impl FlatBuffersConverter {
    /// Create a new converter
    pub fn new() -> Self {
        Self::default()
    }

    /// Convert a parsed FlatBuffers to IR schema
    pub fn convert(
        &self,
        parsed: &ParsedFlatBuffers,
        name: &str,
    ) -> Result<IrSchema, AnalyzerError> {
        let mut ir = IrSchema::new(name, "flatbuffers");
        let mut types = BTreeMap::new();

        // Convert top-level enums
        for fbs_enum in &parsed.enums {
            let enum_def = self.convert_enum(fbs_enum)?;
            types.insert(enum_def.name.clone(), TypeDef::Enum(enum_def));
        }

        // Convert top-level unions
        for fbs_union in &parsed.unions {
            let enum_def = self.convert_union(fbs_union)?;
            types.insert(enum_def.name.clone(), TypeDef::Enum(enum_def));
        }

        // Convert top-level structs (zero-copy, fixed layout)
        for fbs_struct in &parsed.structs {
            let struct_def = self.convert_struct(fbs_struct)?;
            types.insert(struct_def.name.clone(), TypeDef::Struct(struct_def));
        }

        // Convert top-level tables (heap-allocated, flexible)
        for fbs_table in &parsed.tables {
            let struct_def = self.convert_table(fbs_table)?;
            types.insert(struct_def.name.clone(), TypeDef::Struct(struct_def));
        }

        // Add all types to IR
        for (type_name, type_def) in types {
            ir.add_type(type_name, type_def);
        }

        Ok(ir)
    }

    /// Convert a FlatBuffers struct to IR struct
    /// Structs have fixed layout and support zero-copy access (Concorde class)
    fn convert_struct(&self, fbs_struct: &FbsStruct) -> Result<StructDef, AnalyzerError> {
        let fields = fbs_struct
            .fields
            .iter()
            .map(|f| self.convert_field(f))
            .collect::<Result<Vec<_>, _>>()?;

        let mut extra = BTreeMap::new();
        // Mark as zero-copy struct for transport analysis
        extra.insert("zero_copy".to_string(), "true".to_string());
        extra.insert("layout".to_string(), "fixed".to_string());

        Ok(StructDef {
            name: fbs_struct.name.clone(),
            fields,
            metadata: TypeMetadata {
                doc: Some("FlatBuffers struct with fixed layout (zero-copy)".to_string()),
                deprecated: None,
                serde_hints: BTreeMap::new(),
                extra,
            },
        })
    }

    /// Convert a FlatBuffers table to IR struct
    /// Tables are heap-allocated and support optional fields (Business/Economy class)
    fn convert_table(&self, fbs_table: &FbsTable) -> Result<StructDef, AnalyzerError> {
        let fields = fbs_table
            .fields
            .iter()
            .map(|f| self.convert_field(f))
            .collect::<Result<Vec<_>, _>>()?;

        let mut extra = BTreeMap::new();
        // Mark as heap-allocated table
        extra.insert("heap_allocated".to_string(), "true".to_string());
        extra.insert("layout".to_string(), "flexible".to_string());

        Ok(StructDef {
            name: fbs_table.name.clone(),
            fields,
            metadata: TypeMetadata {
                doc: Some("FlatBuffers table (heap-allocated, flexible)".to_string()),
                deprecated: None,
                serde_hints: BTreeMap::new(),
                extra,
            },
        })
    }

    /// Convert a FlatBuffers field to IR field
    fn convert_field(&self, field: &FbsField) -> Result<FieldDef, AnalyzerError> {
        let base_type = self.convert_field_type(field)?;

        // FlatBuffers fields are optional by default in tables (unless marked required)
        // Structs have all required fields
        let ty = if !field.required && !field.is_vector {
            IrType::Container(ContainerType::Option(Box::new(base_type)))
        } else {
            base_type
        };

        let mut serde_hints = BTreeMap::new();
        let default_json = if let Some(ref default) = field.default_value {
            serde_hints.insert("default".to_string(), default.clone());
            // Try to parse default value as JSON, fallback to string
            serde_json::from_str(default).ok().or_else(|| {
                Some(serde_json::Value::String(default.clone()))
            })
        } else {
            None
        };

        Ok(FieldDef {
            name: field.name.clone(),
            ty,
            optional: !field.required,
            constraints: vec![],
            metadata: FieldMetadata {
                doc: None,
                default: default_json,
                aliases: vec![],
                flatten: false,
                skip: field.deprecated,
                serde_hints,
            },
        })
    }

    /// Convert a FlatBuffers field type to IR type
    fn convert_field_type(&self, field: &FbsField) -> Result<IrType, AnalyzerError> {
        // Handle vectors
        if field.is_vector {
            let element_type = self.fbs_type_to_ir(&field.field_type)?;
            return Ok(IrType::Container(ContainerType::Vec(Box::new(
                element_type,
            ))));
        }

        // Regular type
        self.fbs_type_to_ir(&field.field_type)
    }

    /// Convert a FlatBuffers type string to IR type
    fn fbs_type_to_ir(&self, type_str: &str) -> Result<IrType, AnalyzerError> {
        match type_str {
            // Boolean
            "bool" => Ok(IrType::Primitive(PrimitiveType::Bool)),

            // Integers (signed)
            "byte" => Ok(IrType::Primitive(PrimitiveType::I8)),
            "short" => Ok(IrType::Primitive(PrimitiveType::I16)),
            "int" => Ok(IrType::Primitive(PrimitiveType::I32)),
            "long" => Ok(IrType::Primitive(PrimitiveType::I64)),

            // Integers (unsigned)
            "ubyte" => Ok(IrType::Primitive(PrimitiveType::U8)),
            "ushort" => Ok(IrType::Primitive(PrimitiveType::U16)),
            "uint" => Ok(IrType::Primitive(PrimitiveType::U32)),
            "ulong" => Ok(IrType::Primitive(PrimitiveType::U64)),

            // Floats
            "float" => Ok(IrType::Primitive(PrimitiveType::F32)),
            "double" => Ok(IrType::Primitive(PrimitiveType::F64)),

            // String
            "string" => Ok(IrType::Primitive(PrimitiveType::String)),

            // User-defined types (tables, structs, enums)
            type_name => Ok(IrType::Reference(type_name.to_string())),
        }
    }

    /// Convert a FlatBuffers enum to IR enum
    fn convert_enum(&self, fbs_enum: &FbsEnum) -> Result<EnumDef, AnalyzerError> {
        let variants: Vec<VariantDef> = fbs_enum
            .values
            .iter()
            .map(|v| VariantDef {
                name: to_pascal_case(&v.name),
                payload: None, // FlatBuffers enums don't have payloads
                metadata: VariantMetadata {
                    doc: None,
                    aliases: vec![v.name.clone()],
                    serde_hints: BTreeMap::new(),
                },
            })
            .collect();

        let mut extra = BTreeMap::new();
        extra.insert("base_type".to_string(), fbs_enum.base_type.clone());

        Ok(EnumDef {
            name: fbs_enum.name.clone(),
            variants,
            tag_style: TagStyle::External,
            metadata: TypeMetadata {
                doc: Some(format!("FlatBuffers enum (base: {})", fbs_enum.base_type)),
                deprecated: None,
                serde_hints: BTreeMap::new(),
                extra,
            },
        })
    }

    /// Convert a FlatBuffers union to IR enum
    fn convert_union(&self, fbs_union: &FbsUnion) -> Result<EnumDef, AnalyzerError> {
        use protocol_squisher_ir::VariantPayload;

        let variants: Vec<VariantDef> = fbs_union
            .variants
            .iter()
            .map(|variant_name| VariantDef {
                name: variant_name.clone(),
                payload: Some(VariantPayload::Tuple(vec![IrType::Reference(
                    variant_name.clone(),
                )])),
                metadata: VariantMetadata {
                    doc: None,
                    aliases: vec![],
                    serde_hints: BTreeMap::new(),
                },
            })
            .collect();

        Ok(EnumDef {
            name: fbs_union.name.clone(),
            variants,
            tag_style: TagStyle::External,
            metadata: TypeMetadata {
                doc: Some("FlatBuffers union (discriminated)".to_string()),
                deprecated: None,
                serde_hints: BTreeMap::new(),
                extra: BTreeMap::new(),
            },
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
    use crate::parser::FbsEnumValue;

    #[test]
    fn test_to_pascal_case() {
        assert_eq!(to_pascal_case("hello_world"), "HelloWorld");
        assert_eq!(to_pascal_case("RED"), "Red");
        assert_eq!(to_pascal_case("user_name"), "UserName");
        assert_eq!(to_pascal_case("COLOR_BLUE"), "ColorBlue");
    }

    #[test]
    fn test_fbs_type_to_ir() {
        let converter = FlatBuffersConverter::new();

        assert!(matches!(
            converter.fbs_type_to_ir("string").unwrap(),
            IrType::Primitive(PrimitiveType::String)
        ));
        assert!(matches!(
            converter.fbs_type_to_ir("int").unwrap(),
            IrType::Primitive(PrimitiveType::I32)
        ));
        assert!(matches!(
            converter.fbs_type_to_ir("bool").unwrap(),
            IrType::Primitive(PrimitiveType::Bool)
        ));
        assert!(matches!(
            converter.fbs_type_to_ir("float").unwrap(),
            IrType::Primitive(PrimitiveType::F32)
        ));
        assert!(matches!(
            converter.fbs_type_to_ir("MyTable").unwrap(),
            IrType::Reference(_)
        ));
    }

    #[test]
    fn test_convert_simple_table() {
        let converter = FlatBuffersConverter::new();

        let fbs_table = FbsTable {
            name: "Person".to_string(),
            fields: vec![
                FbsField {
                    name: "name".to_string(),
                    field_type: "string".to_string(),
                    required: false,
                    deprecated: false,
                    is_vector: false,
                    default_value: None,
                },
                FbsField {
                    name: "age".to_string(),
                    field_type: "int".to_string(),
                    required: false,
                    deprecated: false,
                    is_vector: false,
                    default_value: None,
                },
            ],
        };

        let result = converter.convert_table(&fbs_table);
        assert!(result.is_ok());

        let struct_def = result.unwrap();
        assert_eq!(struct_def.name, "Person");
        assert_eq!(struct_def.fields.len(), 2);
    }

    #[test]
    fn test_convert_struct_zero_copy() {
        let converter = FlatBuffersConverter::new();

        let fbs_struct = FbsStruct {
            name: "Vec3".to_string(),
            fields: vec![
                FbsField {
                    name: "x".to_string(),
                    field_type: "float".to_string(),
                    required: true,
                    deprecated: false,
                    is_vector: false,
                    default_value: None,
                },
                FbsField {
                    name: "y".to_string(),
                    field_type: "float".to_string(),
                    required: true,
                    deprecated: false,
                    is_vector: false,
                    default_value: None,
                },
                FbsField {
                    name: "z".to_string(),
                    field_type: "float".to_string(),
                    required: true,
                    deprecated: false,
                    is_vector: false,
                    default_value: None,
                },
            ],
        };

        let result = converter.convert_struct(&fbs_struct);
        assert!(result.is_ok());

        let struct_def = result.unwrap();
        assert_eq!(struct_def.name, "Vec3");
        assert_eq!(struct_def.fields.len(), 3);
        assert_eq!(
            struct_def.metadata.extra.get("zero_copy"),
            Some(&"true".to_string())
        );
    }

    #[test]
    fn test_convert_enum() {
        let converter = FlatBuffersConverter::new();

        let fbs_enum = FbsEnum {
            name: "Color".to_string(),
            base_type: "byte".to_string(),
            values: vec![
                FbsEnumValue {
                    name: "Red".to_string(),
                    number: 0,
                },
                FbsEnumValue {
                    name: "Green".to_string(),
                    number: 1,
                },
                FbsEnumValue {
                    name: "Blue".to_string(),
                    number: 2,
                },
            ],
        };

        let result = converter.convert_enum(&fbs_enum);
        assert!(result.is_ok());

        let enum_def = result.unwrap();
        assert_eq!(enum_def.name, "Color");
        assert_eq!(enum_def.variants.len(), 3);
    }

    #[test]
    fn test_convert_vector_field() {
        let converter = FlatBuffersConverter::new();

        let field = FbsField {
            name: "tags".to_string(),
            field_type: "string".to_string(),
            required: false,
            deprecated: false,
            is_vector: true,
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
    fn test_convert_optional_field() {
        let converter = FlatBuffersConverter::new();

        let field = FbsField {
            name: "age".to_string(),
            field_type: "int".to_string(),
            required: false,
            deprecated: false,
            is_vector: false,
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
    fn test_convert_required_field() {
        let converter = FlatBuffersConverter::new();

        let field = FbsField {
            name: "id".to_string(),
            field_type: "int".to_string(),
            required: true,
            deprecated: false,
            is_vector: false,
            default_value: None,
        };

        let result = converter.convert_field(&field);
        assert!(result.is_ok());

        let field_def = result.unwrap();
        assert!(!field_def.optional);
        assert!(matches!(field_def.ty, IrType::Primitive(_)));
    }
}
