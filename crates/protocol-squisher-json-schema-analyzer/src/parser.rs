// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! JSON Schema parser

use crate::{AnalyzerError, JsonSchema, SchemaVersion};

/// Parser for JSON Schema documents
#[derive(Debug, Default)]
pub struct JsonSchemaParser {
    /// Whether to be strict about schema validation
    pub strict: bool,
}

impl JsonSchemaParser {
    /// Create a new parser
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a strict parser that rejects unknown fields
    pub fn strict() -> Self {
        Self { strict: true }
    }

    /// Parse a JSON string into a JsonSchema
    pub fn parse_str(&self, json: &str) -> Result<JsonSchema, AnalyzerError> {
        let schema: JsonSchema = serde_json::from_str(json)?;
        self.validate(&schema)?;
        Ok(schema)
    }

    /// Parse a serde_json::Value into a JsonSchema
    pub fn parse_value(&self, value: serde_json::Value) -> Result<JsonSchema, AnalyzerError> {
        let schema: JsonSchema = serde_json::from_value(value)?;
        self.validate(&schema)?;
        Ok(schema)
    }

    /// Detect the schema version
    pub fn detect_version(&self, schema: &JsonSchema) -> SchemaVersion {
        schema
            .schema
            .as_ref()
            .map(|s| SchemaVersion::from_schema_uri(s))
            .unwrap_or(SchemaVersion::Unknown)
    }

    /// Validate the parsed schema
    fn validate(&self, schema: &JsonSchema) -> Result<(), AnalyzerError> {
        // Basic validation - ensure the schema has some useful content
        if schema.schema_type.is_none()
            && schema.properties.is_empty()
            && schema.ref_uri.is_none()
            && schema.all_of.is_none()
            && schema.any_of.is_none()
            && schema.one_of.is_none()
            && schema.enum_values.is_none()
            && schema.const_value.is_none()
        {
            // This could be a valid "accept anything" schema, so only warn in strict mode
            if self.strict {
                return Err(AnalyzerError::InvalidSchema(
                    "Schema has no type information".to_string(),
                ));
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_basic_schema() {
        let parser = JsonSchemaParser::new();
        let json = r#"{"type": "string"}"#;
        let result = parser.parse_str(json);
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_with_schema_version() {
        let parser = JsonSchemaParser::new();
        let json = r#"{
            "$schema": "https://json-schema.org/draft/2020-12/schema",
            "type": "object"
        }"#;
        let schema = parser.parse_str(json).unwrap();
        assert_eq!(parser.detect_version(&schema), SchemaVersion::Draft202012);
    }

    #[test]
    fn test_parse_draft07() {
        let parser = JsonSchemaParser::new();
        let json = r#"{
            "$schema": "http://json-schema.org/draft-07/schema#",
            "type": "object"
        }"#;
        let schema = parser.parse_str(json).unwrap();
        assert_eq!(parser.detect_version(&schema), SchemaVersion::Draft07);
    }

    #[test]
    fn test_parse_invalid_json() {
        let parser = JsonSchemaParser::new();
        let result = parser.parse_str("not valid json");
        assert!(result.is_err());
    }

    #[test]
    fn test_strict_mode_empty_schema() {
        let parser = JsonSchemaParser::strict();
        let result = parser.parse_str("{}");
        assert!(result.is_err());
    }

    #[test]
    fn test_non_strict_empty_schema() {
        let parser = JsonSchemaParser::new();
        let result = parser.parse_str("{}");
        assert!(result.is_ok());
    }
}
