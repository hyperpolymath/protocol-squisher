// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Avro schema JSON parser
//!
//! Parses Avro schema definitions from JSON into intermediate structures
//! that can be converted to protocol-squisher IR.

use crate::AnalyzerError;
use serde::{Deserialize, Serialize};
use std::path::Path;

/// Parsed Avro schema representation
#[derive(Debug, Clone)]
pub struct ParsedAvro {
    /// All named types defined in the schema
    pub types: Vec<AvroType>,
}

/// Avro type definition
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
#[serde(rename_all = "lowercase")]
pub enum AvroType {
    /// Record type (struct)
    Record {
        name: String,
        #[serde(default)]
        namespace: Option<String>,
        #[serde(default)]
        doc: Option<String>,
        #[serde(default)]
        aliases: Vec<String>,
        fields: Vec<AvroField>,
    },
    /// Enum type
    Enum {
        name: String,
        #[serde(default)]
        namespace: Option<String>,
        #[serde(default)]
        doc: Option<String>,
        #[serde(default)]
        aliases: Vec<String>,
        symbols: Vec<String>,
        #[serde(default)]
        default: Option<String>,
    },
    /// Fixed-size bytes
    Fixed {
        name: String,
        #[serde(default)]
        namespace: Option<String>,
        #[serde(default)]
        doc: Option<String>,
        #[serde(default)]
        aliases: Vec<String>,
        size: usize,
    },
}

/// Avro field in a record
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AvroField {
    /// Field name
    pub name: String,
    /// Field schema (can be a type name string or inline schema)
    #[serde(rename = "type")]
    pub schema: AvroSchema,
    /// Optional documentation
    #[serde(default)]
    pub doc: Option<String>,
    /// Default value for the field (schema evolution)
    #[serde(default)]
    pub default: Option<serde_json::Value>,
    /// Aliases for the field (schema evolution)
    #[serde(default)]
    pub aliases: Vec<String>,
}

/// Avro schema can be a type name, primitive, or complex type
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum AvroSchema {
    /// Type name reference (e.g., "string", "MyRecord")
    Name(String),
    /// Array of union types (e.g., ["null", "string"])
    Union(Vec<AvroSchema>),
    /// Complex type definition
    Complex(Box<AvroComplexSchema>),
}

/// Complex Avro schema types
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
#[serde(rename_all = "lowercase")]
pub enum AvroComplexSchema {
    /// Array type
    Array { items: AvroSchema },
    /// Map type (keys are always strings in Avro)
    Map { values: AvroSchema },
    /// Inline record definition
    Record {
        name: String,
        #[serde(default)]
        namespace: Option<String>,
        #[serde(default)]
        doc: Option<String>,
        #[serde(default)]
        aliases: Vec<String>,
        fields: Vec<AvroField>,
    },
    /// Inline enum definition
    Enum {
        name: String,
        #[serde(default)]
        namespace: Option<String>,
        #[serde(default)]
        doc: Option<String>,
        #[serde(default)]
        aliases: Vec<String>,
        symbols: Vec<String>,
        #[serde(default)]
        default: Option<String>,
    },
    /// Inline fixed definition
    Fixed {
        name: String,
        #[serde(default)]
        namespace: Option<String>,
        #[serde(default)]
        doc: Option<String>,
        #[serde(default)]
        aliases: Vec<String>,
        size: usize,
    },
}

/// Parser for Avro schema files
#[derive(Debug, Default)]
pub struct AvroParser {}

impl AvroParser {
    /// Create a new parser
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse an Avro schema file
    pub fn parse_file(&self, path: &Path) -> Result<ParsedAvro, AnalyzerError> {
        let content = std::fs::read_to_string(path)?;
        self.parse_str(&content)
    }

    /// Parse Avro schema content from a JSON string
    pub fn parse_str(&self, content: &str) -> Result<ParsedAvro, AnalyzerError> {
        // Parse as generic JSON first to determine top-level type
        let value: serde_json::Value = serde_json::from_str(content)?;

        let mut types = Vec::new();

        // Handle different top-level schema types
        match &value {
            serde_json::Value::Object(obj) if obj.contains_key("type") => {
                // Single type definition
                let avro_type: AvroType = serde_json::from_value(value.clone()).map_err(|e| {
                    AnalyzerError::ParseError(format!("Invalid Avro schema: {}", e))
                })?;
                types.push(avro_type);
            },
            serde_json::Value::Array(_) => {
                // Multiple type definitions (protocol)
                let avro_types: Vec<AvroType> = serde_json::from_value(value).map_err(|e| {
                    AnalyzerError::ParseError(format!("Invalid Avro protocol: {}", e))
                })?;
                types.extend(avro_types);
            },
            _ => {
                return Err(AnalyzerError::InvalidSchema(
                    "Expected Avro schema object or array".to_string(),
                ));
            },
        }

        Ok(ParsedAvro { types })
    }
}

impl AvroSchema {
    /// Check if this schema represents an optional field (union with null)
    pub fn is_optional(&self) -> bool {
        if let AvroSchema::Union(variants) = self {
            if variants.len() == 2 {
                return variants
                    .iter()
                    .any(|v| matches!(v, AvroSchema::Name(name) if name == "null"));
            }
        }
        false
    }

    /// Get the non-null type from an optional union
    pub fn unwrap_optional(&self) -> Option<&AvroSchema> {
        if let AvroSchema::Union(variants) = self {
            if variants.len() == 2 {
                for variant in variants {
                    if !matches!(variant, AvroSchema::Name(name) if name == "null") {
                        return Some(variant);
                    }
                }
            }
        }
        None
    }

    /// Check if this is a primitive type
    pub fn is_primitive(&self) -> bool {
        if let AvroSchema::Name(name) = self {
            matches!(
                name.as_str(),
                "null" | "boolean" | "int" | "long" | "float" | "double" | "bytes" | "string"
            )
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_record() {
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
        let result = parser.parse_str(json);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.types.len(), 1);

        assert!(
            matches!(&parsed.types[0], AvroType::Record { .. }),
            "Expected record type"
        );
        let AvroType::Record { name, fields, .. } = &parsed.types[0] else {
            unreachable!("asserted record");
        };
        assert_eq!(name, "Person");
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[0].name, "name");
        assert_eq!(fields[1].name, "age");
    }

    #[test]
    fn test_parse_optional_field() {
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
        let result = parser.parse_str(json);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        if let AvroType::Record { fields, .. } = &parsed.types[0] {
            assert!(fields[0].schema.is_optional());
        }
    }

    #[test]
    fn test_parse_array() {
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
        let result = parser.parse_str(json);
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_map() {
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
        let result = parser.parse_str(json);
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_enum() {
        let json = r#"
        {
            "type": "enum",
            "name": "Status",
            "symbols": ["UNKNOWN", "ACTIVE", "INACTIVE"]
        }
        "#;

        let parser = AvroParser::new();
        let result = parser.parse_str(json);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert!(
            matches!(&parsed.types[0], AvroType::Enum { .. }),
            "Expected enum type"
        );
        let AvroType::Enum { name, symbols, .. } = &parsed.types[0] else {
            unreachable!("asserted enum");
        };
        assert_eq!(name, "Status");
        assert_eq!(symbols.len(), 3);
    }

    #[test]
    fn test_parse_fixed() {
        let json = r#"
        {
            "type": "fixed",
            "name": "UUID",
            "size": 16
        }
        "#;

        let parser = AvroParser::new();
        let result = parser.parse_str(json);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert!(
            matches!(&parsed.types[0], AvroType::Fixed { .. }),
            "Expected fixed type"
        );
        let AvroType::Fixed { name, size, .. } = &parsed.types[0] else {
            unreachable!("asserted fixed");
        };
        assert_eq!(name, "UUID");
        assert_eq!(*size, 16);
    }

    #[test]
    fn test_is_optional() {
        let optional = AvroSchema::Union(vec![
            AvroSchema::Name("null".to_string()),
            AvroSchema::Name("string".to_string()),
        ]);
        assert!(optional.is_optional());

        let not_optional = AvroSchema::Name("string".to_string());
        assert!(!not_optional.is_optional());

        let complex_union = AvroSchema::Union(vec![
            AvroSchema::Name("string".to_string()),
            AvroSchema::Name("int".to_string()),
            AvroSchema::Name("boolean".to_string()),
        ]);
        assert!(!complex_union.is_optional());
    }

    #[test]
    fn test_unwrap_optional() {
        let optional = AvroSchema::Union(vec![
            AvroSchema::Name("null".to_string()),
            AvroSchema::Name("string".to_string()),
        ]);
        let unwrapped = optional.unwrap_optional();
        assert!(unwrapped.is_some());
        assert!(matches!(unwrapped.unwrap(), AvroSchema::Name(name) if name == "string"));
    }

    #[test]
    fn test_is_primitive() {
        assert!(AvroSchema::Name("string".to_string()).is_primitive());
        assert!(AvroSchema::Name("int".to_string()).is_primitive());
        assert!(AvroSchema::Name("null".to_string()).is_primitive());
        assert!(!AvroSchema::Name("MyRecord".to_string()).is_primitive());
    }
}
