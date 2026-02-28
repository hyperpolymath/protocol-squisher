// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! JSON Schema parser for MessagePack type inference
//!
//! Since MessagePack is schema-less, we accept JSON Schema as a proxy
//! for type information. This allows us to infer types and constraints
//! that would be used in MessagePack serialization.

use crate::AnalyzerError;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::Path;

/// Parsed JSON Schema representation
#[derive(Debug, Clone, Default)]
pub struct ParsedSchema {
    /// Root schema object
    pub root: SchemaObject,
    /// Named definitions (for $ref support)
    pub definitions: HashMap<String, SchemaObject>,
}

/// Top-level JSON Schema document with optional named-definition sections.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct SchemaDocument {
    #[serde(flatten)]
    root: SchemaObject,
    #[serde(default)]
    definitions: HashMap<String, SchemaObject>,
    #[serde(rename = "$defs", default)]
    defs: HashMap<String, SchemaObject>,
}

/// JSON Schema object
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SchemaObject {
    /// Schema type (object, array, string, etc.)
    #[serde(rename = "type")]
    pub schema_type: Option<SchemaType>,

    /// Object properties (for type: object)
    #[serde(default)]
    pub properties: HashMap<String, Box<SchemaObject>>,

    /// Required properties (for type: object)
    #[serde(default)]
    pub required: Vec<String>,

    /// Array items (for type: array)
    pub items: Option<Box<SchemaObject>>,

    /// Enum values (for constrained strings/integers)
    #[serde(rename = "enum")]
    pub enum_values: Option<Vec<serde_json::Value>>,

    /// Minimum value (for numbers)
    pub minimum: Option<f64>,

    /// Maximum value (for numbers)
    pub maximum: Option<f64>,

    /// Minimum length (for strings/arrays)
    #[serde(rename = "minLength")]
    pub min_length: Option<usize>,

    /// Maximum length (for strings/arrays)
    #[serde(rename = "maxLength")]
    pub max_length: Option<usize>,

    /// Pattern (for strings)
    pub pattern: Option<String>,

    /// Description
    pub description: Option<String>,

    /// Format hint (e.g., "date-time", "uuid")
    pub format: Option<String>,

    /// Additional properties flag
    #[serde(rename = "additionalProperties")]
    pub additional_properties: Option<bool>,
}

/// JSON Schema type enum
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum SchemaType {
    Null,
    Boolean,
    Integer,
    Number,
    String,
    Array,
    Object,
}

/// Parser for JSON Schema files
#[derive(Debug, Default)]
pub struct MessagePackParser {}

impl MessagePackParser {
    /// Create a new parser
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse a JSON Schema file
    pub fn parse_file(&self, path: &Path) -> Result<ParsedSchema, AnalyzerError> {
        let content = std::fs::read_to_string(path)?;
        self.parse_str(&content)
    }

    /// Parse JSON Schema content from a string
    pub fn parse_str(&self, content: &str) -> Result<ParsedSchema, AnalyzerError> {
        let mut document: SchemaDocument = serde_json::from_str(content)
            .map_err(|e| AnalyzerError::ParseError(format!("JSON parse error: {}", e)))?;
        let mut definitions = document.definitions;
        definitions.extend(document.defs.drain());

        Ok(ParsedSchema {
            root: document.root,
            definitions,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_object() {
        let json = r#"{
            "type": "object",
            "properties": {
                "name": { "type": "string" },
                "age": { "type": "integer" }
            }
        }"#;

        let parser = MessagePackParser::new();
        let result = parser.parse_str(json);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.root.schema_type, Some(SchemaType::Object));
        assert_eq!(parsed.root.properties.len(), 2);
    }

    #[test]
    fn test_parse_required_fields() {
        let json = r#"{
            "type": "object",
            "properties": {
                "id": { "type": "integer" },
                "name": { "type": "string" }
            },
            "required": ["id", "name"]
        }"#;

        let parser = MessagePackParser::new();
        let result = parser.parse_str(json);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.root.required.len(), 2);
        assert!(parsed.root.required.contains(&"id".to_string()));
        assert!(parsed.root.required.contains(&"name".to_string()));
    }

    #[test]
    fn test_parse_array_field() {
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
        let result = parser.parse_str(json);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        let tags = parsed.root.properties.get("tags").unwrap();
        assert_eq!(tags.schema_type, Some(SchemaType::Array));
        assert!(tags.items.is_some());
    }

    #[test]
    fn test_parse_constraints() {
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
                    "maxLength": 20
                }
            }
        }"#;

        let parser = MessagePackParser::new();
        let result = parser.parse_str(json);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        let age = parsed.root.properties.get("age").unwrap();
        assert_eq!(age.minimum, Some(0.0));
        assert_eq!(age.maximum, Some(150.0));

        let username = parsed.root.properties.get("username").unwrap();
        assert_eq!(username.min_length, Some(3));
        assert_eq!(username.max_length, Some(20));
    }

    #[test]
    fn test_parse_enum() {
        let json = r#"{
            "type": "object",
            "properties": {
                "status": {
                    "type": "string",
                    "enum": ["draft", "published", "archived"]
                }
            }
        }"#;

        let parser = MessagePackParser::new();
        let result = parser.parse_str(json);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        let status = parsed.root.properties.get("status").unwrap();
        assert!(status.enum_values.is_some());
        assert_eq!(status.enum_values.as_ref().unwrap().len(), 3);
    }

    #[test]
    fn test_parse_nested_object() {
        let json = r#"{
            "type": "object",
            "properties": {
                "address": {
                    "type": "object",
                    "properties": {
                        "street": { "type": "string" },
                        "city": { "type": "string" }
                    }
                }
            }
        }"#;

        let parser = MessagePackParser::new();
        let result = parser.parse_str(json);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        let address = parsed.root.properties.get("address").unwrap();
        assert_eq!(address.schema_type, Some(SchemaType::Object));
        assert_eq!(address.properties.len(), 2);
    }

    #[test]
    fn test_parse_format_hints() {
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
        let result = parser.parse_str(json);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        let created_at = parsed.root.properties.get("created_at").unwrap();
        assert_eq!(created_at.format.as_ref().unwrap(), "date-time");

        let user_id = parsed.root.properties.get("user_id").unwrap();
        assert_eq!(user_id.format.as_ref().unwrap(), "uuid");
    }

    #[test]
    fn test_parse_empty_schema() {
        // Empty schema means any type is allowed (dynamic)
        let json = "{}";

        let parser = MessagePackParser::new();
        let result = parser.parse_str(json);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert!(parsed.root.schema_type.is_none());
    }

    #[test]
    fn test_parse_all_primitive_types() {
        let json = r#"{
            "type": "object",
            "properties": {
                "null_field": { "type": "null" },
                "bool_field": { "type": "boolean" },
                "int_field": { "type": "integer" },
                "number_field": { "type": "number" },
                "string_field": { "type": "string" }
            }
        }"#;

        let parser = MessagePackParser::new();
        let result = parser.parse_str(json);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.root.properties.len(), 5);
    }

    #[test]
    fn test_parse_definitions_and_defs() {
        let json = r#"{
            "type": "object",
            "definitions": {
                "LegacyUserId": { "type": "string" }
            },
            "$defs": {
                "OrderId": { "type": "integer" }
            }
        }"#;

        let parser = MessagePackParser::new();
        let parsed = parser.parse_str(json).unwrap();

        assert_eq!(parsed.definitions.len(), 2);
        assert!(parsed.definitions.contains_key("LegacyUserId"));
        assert!(parsed.definitions.contains_key("OrderId"));
    }
}
