// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Types representing parsed JSON Schema structure

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// A parsed JSON Schema document
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct JsonSchema {
    /// Schema version URI
    #[serde(rename = "$schema", default)]
    pub schema: Option<String>,

    /// Schema ID
    #[serde(rename = "$id", default)]
    pub id: Option<String>,

    /// Title of the schema
    #[serde(default)]
    pub title: Option<String>,

    /// Description
    #[serde(default)]
    pub description: Option<String>,

    /// Type constraint
    #[serde(rename = "type", default)]
    pub schema_type: Option<SchemaType>,

    /// Properties for object types
    #[serde(default)]
    pub properties: BTreeMap<String, Box<JsonSchema>>,

    /// Additional properties constraint
    #[serde(rename = "additionalProperties", default)]
    pub additional_properties: Option<AdditionalProperties>,

    /// Required property names
    #[serde(default)]
    pub required: Vec<String>,

    /// Items schema for array types
    #[serde(default)]
    pub items: Option<Box<JsonSchema>>,

    /// Prefix items for tuple validation (draft-2020-12)
    #[serde(rename = "prefixItems", default)]
    pub prefix_items: Option<Vec<JsonSchema>>,

    /// Minimum items for arrays
    #[serde(rename = "minItems", default)]
    pub min_items: Option<u64>,

    /// Maximum items for arrays
    #[serde(rename = "maxItems", default)]
    pub max_items: Option<u64>,

    /// Unique items constraint
    #[serde(rename = "uniqueItems", default)]
    pub unique_items: Option<bool>,

    /// Enum values
    #[serde(rename = "enum", default)]
    pub enum_values: Option<Vec<serde_json::Value>>,

    /// Const value
    #[serde(rename = "const", default)]
    pub const_value: Option<serde_json::Value>,

    /// Minimum value for numbers
    #[serde(default)]
    pub minimum: Option<f64>,

    /// Maximum value for numbers
    #[serde(default)]
    pub maximum: Option<f64>,

    /// Exclusive minimum (draft-04/06/07 style - boolean or number)
    #[serde(rename = "exclusiveMinimum", default)]
    pub exclusive_minimum: Option<serde_json::Value>,

    /// Exclusive maximum (draft-04/06/07 style - boolean or number)
    #[serde(rename = "exclusiveMaximum", default)]
    pub exclusive_maximum: Option<serde_json::Value>,

    /// Multiple of constraint
    #[serde(rename = "multipleOf", default)]
    pub multiple_of: Option<f64>,

    /// Minimum string length
    #[serde(rename = "minLength", default)]
    pub min_length: Option<u64>,

    /// Maximum string length
    #[serde(rename = "maxLength", default)]
    pub max_length: Option<u64>,

    /// Pattern (regex) for strings
    #[serde(default)]
    pub pattern: Option<String>,

    /// Format hint for strings
    #[serde(default)]
    pub format: Option<String>,

    /// Content encoding (e.g., base64)
    #[serde(rename = "contentEncoding", default)]
    pub content_encoding: Option<String>,

    /// Content media type
    #[serde(rename = "contentMediaType", default)]
    pub content_media_type: Option<String>,

    /// Reference to another schema
    #[serde(rename = "$ref", default)]
    pub ref_uri: Option<String>,

    /// Definitions (draft-04/06/07)
    #[serde(default)]
    pub definitions: BTreeMap<String, JsonSchema>,

    /// Definitions (draft-2019-09+)
    #[serde(rename = "$defs", default)]
    pub defs: BTreeMap<String, JsonSchema>,

    /// All of (schema composition)
    #[serde(rename = "allOf", default)]
    pub all_of: Option<Vec<JsonSchema>>,

    /// Any of (schema composition)
    #[serde(rename = "anyOf", default)]
    pub any_of: Option<Vec<JsonSchema>>,

    /// One of (schema composition)
    #[serde(rename = "oneOf", default)]
    pub one_of: Option<Vec<JsonSchema>>,

    /// Not (schema negation)
    #[serde(default)]
    pub not: Option<Box<JsonSchema>>,

    /// If condition
    #[serde(rename = "if", default)]
    pub if_schema: Option<Box<JsonSchema>>,

    /// Then consequence
    #[serde(rename = "then", default)]
    pub then_schema: Option<Box<JsonSchema>>,

    /// Else alternative
    #[serde(rename = "else", default)]
    pub else_schema: Option<Box<JsonSchema>>,

    /// Default value
    #[serde(default)]
    pub default: Option<serde_json::Value>,

    /// Examples
    #[serde(default)]
    pub examples: Option<Vec<serde_json::Value>>,

    /// Read only
    #[serde(rename = "readOnly", default)]
    pub read_only: Option<bool>,

    /// Write only
    #[serde(rename = "writeOnly", default)]
    pub write_only: Option<bool>,

    /// Deprecated flag
    #[serde(default)]
    pub deprecated: Option<bool>,

    /// Property names schema
    #[serde(rename = "propertyNames", default)]
    pub property_names: Option<Box<JsonSchema>>,

    /// Minimum properties
    #[serde(rename = "minProperties", default)]
    pub min_properties: Option<u64>,

    /// Maximum properties
    #[serde(rename = "maxProperties", default)]
    pub max_properties: Option<u64>,

    /// Pattern properties
    #[serde(rename = "patternProperties", default)]
    pub pattern_properties: BTreeMap<String, JsonSchema>,

    /// Dependent required
    #[serde(rename = "dependentRequired", default)]
    pub dependent_required: BTreeMap<String, Vec<String>>,

    /// Dependent schemas
    #[serde(rename = "dependentSchemas", default)]
    pub dependent_schemas: BTreeMap<String, JsonSchema>,

    /// Contains schema for arrays
    #[serde(default)]
    pub contains: Option<Box<JsonSchema>>,

    /// Min contains
    #[serde(rename = "minContains", default)]
    pub min_contains: Option<u64>,

    /// Max contains
    #[serde(rename = "maxContains", default)]
    pub max_contains: Option<u64>,
}

/// JSON Schema type constraint
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(untagged)]
pub enum SchemaType {
    /// Single type
    Single(SingleType),
    /// Multiple types (union)
    Multiple(Vec<SingleType>),
}

/// Single JSON Schema type
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum SingleType {
    String,
    Number,
    Integer,
    Boolean,
    Array,
    Object,
    Null,
}

/// Additional properties constraint
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum AdditionalProperties {
    /// Boolean: true allows any, false disallows
    Bool(bool),
    /// Schema for additional properties
    Schema(Box<JsonSchema>),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_object() {
        let json = r#"{
            "type": "object",
            "properties": {
                "name": { "type": "string" }
            },
            "required": ["name"]
        }"#;

        let schema: JsonSchema = serde_json::from_str(json).unwrap();
        assert_eq!(
            schema.schema_type,
            Some(SchemaType::Single(SingleType::Object))
        );
        assert!(schema.properties.contains_key("name"));
        assert_eq!(schema.required, vec!["name"]);
    }

    #[test]
    fn test_parse_multi_type() {
        let json = r#"{
            "type": ["string", "null"]
        }"#;

        let schema: JsonSchema = serde_json::from_str(json).unwrap();
        let Some(SchemaType::Multiple(types)) = schema.schema_type else {
            unreachable!("schema type should be a multi-type union");
        };
        assert_eq!(types.len(), 2);
        assert!(types.contains(&SingleType::String));
        assert!(types.contains(&SingleType::Null));
    }

    #[test]
    fn test_parse_with_constraints() {
        let json = r#"{
            "type": "integer",
            "minimum": 0,
            "maximum": 100,
            "multipleOf": 5
        }"#;

        let schema: JsonSchema = serde_json::from_str(json).unwrap();
        assert_eq!(schema.minimum, Some(0.0));
        assert_eq!(schema.maximum, Some(100.0));
        assert_eq!(schema.multiple_of, Some(5.0));
    }

    #[test]
    fn test_parse_string_constraints() {
        let json = r#"{
            "type": "string",
            "minLength": 1,
            "maxLength": 255,
            "pattern": "^[a-z]+$",
            "format": "email"
        }"#;

        let schema: JsonSchema = serde_json::from_str(json).unwrap();
        assert_eq!(schema.min_length, Some(1));
        assert_eq!(schema.max_length, Some(255));
        assert_eq!(schema.pattern, Some("^[a-z]+$".to_string()));
        assert_eq!(schema.format, Some("email".to_string()));
    }

    #[test]
    fn test_parse_with_refs() {
        let json = r##"{
            "$defs": {
                "Address": {
                    "type": "object",
                    "properties": {
                        "street": { "type": "string" }
                    }
                }
            },
            "type": "object",
            "properties": {
                "home": { "$ref": "#/$defs/Address" }
            }
        }"##;

        let schema: JsonSchema = serde_json::from_str(json).unwrap();
        assert!(schema.defs.contains_key("Address"));
        let home = schema.properties.get("home").unwrap();
        assert_eq!(home.ref_uri, Some("#/$defs/Address".to_string()));
    }

    #[test]
    fn test_parse_enum() {
        let json = r#"{
            "type": "string",
            "enum": ["red", "green", "blue"]
        }"#;

        let schema: JsonSchema = serde_json::from_str(json).unwrap();
        let values = schema.enum_values.unwrap();
        assert_eq!(values.len(), 3);
    }

    #[test]
    fn test_parse_oneof() {
        let json = r#"{
            "oneOf": [
                { "type": "string" },
                { "type": "number" }
            ]
        }"#;

        let schema: JsonSchema = serde_json::from_str(json).unwrap();
        let one_of = schema.one_of.unwrap();
        assert_eq!(one_of.len(), 2);
    }
}
