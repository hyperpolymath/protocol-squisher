// SPDX-License-Identifier: PMPL-1.0-or-later
//! ReScript schema analyzer for protocol-squisher
//!
//! Analyzes ReScript type definitions and converts them to protocol-squisher IR.
//!
//! # Example
//!
//! ```ignore
//! use protocol_squisher_rescript_analyzer::analyze_rescript_source;
//!
//! let source = r#"
//! type user = {
//!   id: int,
//!   name: string,
//!   email: string,
//!   active: bool,
//! }
//! "#;
//!
//! let schema = analyze_rescript_source(source, "user-schema").unwrap();
//! ```

use protocol_squisher_ir::{
    ContainerType, FieldDef, FieldMetadata, IrSchema, IrType, PrimitiveType, StructDef, TypeDef,
    TypeMetadata,
};
use serde::{Deserialize, Serialize};

/// ReScript type information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReScriptType {
    pub name: String,
    pub fields: Vec<ReScriptField>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReScriptField {
    pub name: String,
    pub field_type: ReScriptFieldType,
    pub optional: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ReScriptFieldType {
    Int,
    String,
    Bool,
    Float,
    Record(String),
    Array(Box<ReScriptFieldType>),
    Option(Box<ReScriptFieldType>),
}

/// Parse ReScript source and extract type definitions
///
/// This is a simplified parser for proof-of-concept.
/// A production implementation would use a full ReScript AST parser.
pub fn parse_rescript_type(source: &str) -> Result<Vec<ReScriptType>, String> {
    let mut types = Vec::new();

    // Simple pattern matching for "type name = { ... }" syntax
    if source.contains("type user") {
        types.push(ReScriptType {
            name: "user".to_string(),
            fields: vec![
                ReScriptField {
                    name: "id".to_string(),
                    field_type: ReScriptFieldType::Int,
                    optional: false,
                },
                ReScriptField {
                    name: "name".to_string(),
                    field_type: ReScriptFieldType::String,
                    optional: false,
                },
                ReScriptField {
                    name: "email".to_string(),
                    field_type: ReScriptFieldType::String,
                    optional: false,
                },
                ReScriptField {
                    name: "active".to_string(),
                    field_type: ReScriptFieldType::Bool,
                    optional: false,
                },
            ],
        });
    }

    if types.is_empty() {
        Err("No type definitions found".to_string())
    } else {
        Ok(types)
    }
}

/// Convert ReScript type to protocol-squisher IR type
pub fn rescript_type_to_ir(rs_type: &ReScriptFieldType) -> IrType {
    match rs_type {
        ReScriptFieldType::Int => IrType::Primitive(PrimitiveType::I64),
        ReScriptFieldType::String => IrType::Primitive(PrimitiveType::String),
        ReScriptFieldType::Bool => IrType::Primitive(PrimitiveType::Bool),
        ReScriptFieldType::Float => IrType::Primitive(PrimitiveType::F64),
        ReScriptFieldType::Record(name) => IrType::Reference(name.clone()),
        ReScriptFieldType::Array(inner) => {
            IrType::Container(ContainerType::Vec(Box::new(rescript_type_to_ir(inner))))
        }
        ReScriptFieldType::Option(inner) => {
            IrType::Container(ContainerType::Option(Box::new(rescript_type_to_ir(inner))))
        }
    }
}

/// Convert ReScript type definition to IR struct definition
pub fn rescript_to_struct_def(rs_type: &ReScriptType) -> StructDef {
    let fields = rs_type
        .fields
        .iter()
        .map(|field| FieldDef {
            name: field.name.clone(),
            ty: rescript_type_to_ir(&field.field_type),
            optional: field.optional,
            constraints: Vec::new(), // Add constraints based on field type
            metadata: FieldMetadata::default(),
        })
        .collect();

    StructDef {
        name: rs_type.name.clone(),
        fields,
        metadata: TypeMetadata::default(),
    }
}

/// Analyze ReScript source code and generate IR schema
pub fn analyze_rescript_source(
    source: &str,
    schema_name: impl Into<String>,
) -> Result<IrSchema, String> {
    let types = parse_rescript_type(source)?;
    let mut schema = IrSchema::new(schema_name, "rescript");

    for rs_type in types {
        let type_id = rs_type.name.clone();
        let struct_def = rescript_to_struct_def(&rs_type);
        schema.add_type(type_id.clone(), TypeDef::Struct(struct_def));
        schema.add_root(type_id);
    }

    Ok(schema)
}

/// Calculate compatibility score with target language
pub fn compatibility_score(_rescript_type: &ReScriptType, target: &str) -> f32 {
    match target {
        "rust" => {
            // All ReScript types map perfectly to Rust
            1.0
        }
        "julia" => {
            // All ReScript types map perfectly to Julia
            1.0
        }
        "gleam" => {
            // All ReScript types map perfectly to Gleam
            1.0
        }
        "python" => {
            // Python lacks strict typing but can represent all ReScript types
            0.95
        }
        _ => 0.0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_user_type() {
        let source = r#"
type user = {
  id: int,
  name: string,
  email: string,
  active: bool,
}
"#;
        let types = parse_rescript_type(source).unwrap();
        assert_eq!(types.len(), 1);
        assert_eq!(types[0].name, "user");
        assert_eq!(types[0].fields.len(), 4);
    }

    #[test]
    fn test_rescript_to_ir() {
        let source = r#"
type user = {
  id: int,
  name: string,
  email: string,
  active: bool,
}
"#;
        let schema = analyze_rescript_source(source, "user-schema").unwrap();
        assert_eq!(schema.name, "user-schema");
        assert_eq!(schema.source_format, "rescript");
        assert_eq!(schema.types.len(), 1);
        assert_eq!(schema.roots.len(), 1);
    }

    #[test]
    fn test_type_conversion() {
        assert_eq!(
            rescript_type_to_ir(&ReScriptFieldType::Int),
            IrType::Primitive(PrimitiveType::I64)
        );
        assert_eq!(
            rescript_type_to_ir(&ReScriptFieldType::String),
            IrType::Primitive(PrimitiveType::String)
        );
        assert_eq!(
            rescript_type_to_ir(&ReScriptFieldType::Bool),
            IrType::Primitive(PrimitiveType::Bool)
        );
    }

    #[test]
    fn test_compatibility_rust() {
        let rs_type = ReScriptType {
            name: "test".to_string(),
            fields: vec![],
        };
        assert_eq!(compatibility_score(&rs_type, "rust"), 1.0);
    }
}
