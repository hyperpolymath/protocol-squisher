// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: Copyright (c) 2025 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! JSON Schema analyzer for protocol-squisher
//!
//! Converts JSON Schema definitions to the protocol-squisher IR format.
//! Supports JSON Schema draft-07, draft-2019-09, and draft-2020-12.
//!
//! # Example
//!
//! ```rust,no_run
//! use protocol_squisher_json_schema_analyzer::JsonSchemaAnalyzer;
//!
//! let schema_json = r#"
//! {
//!   "$schema": "https://json-schema.org/draft/2020-12/schema",
//!   "type": "object",
//!   "properties": {
//!     "name": { "type": "string" },
//!     "age": { "type": "integer", "minimum": 0 }
//!   },
//!   "required": ["name"]
//! }
//! "#;
//!
//! let analyzer = JsonSchemaAnalyzer::new();
//! let ir_schema = analyzer.analyze_str(schema_json, "Person").unwrap();
//! ```

mod converter;
mod parser;
mod types;

pub use converter::SchemaConverter;
pub use parser::JsonSchemaParser;
pub use types::*;

use protocol_squisher_ir::IrSchema;
use thiserror::Error;

/// Errors that can occur during JSON Schema analysis
#[derive(Debug, Error)]
pub enum AnalyzerError {
    /// Failed to parse JSON
    #[error("JSON parse error: {0}")]
    JsonParse(#[from] serde_json::Error),

    /// Invalid schema structure
    #[error("Invalid schema: {0}")]
    InvalidSchema(String),

    /// Unsupported schema feature
    #[error("Unsupported feature: {0}")]
    UnsupportedFeature(String),

    /// Reference resolution error
    #[error("Reference error: {0}")]
    ReferenceError(String),

    /// IO error
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// JSON Schema draft version
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SchemaVersion {
    /// JSON Schema draft-04
    Draft04,
    /// JSON Schema draft-06
    Draft06,
    /// JSON Schema draft-07
    Draft07,
    /// JSON Schema draft-2019-09
    Draft201909,
    /// JSON Schema draft-2020-12
    Draft202012,
    /// Unknown version
    Unknown,
}

impl SchemaVersion {
    /// Detect schema version from $schema URI
    pub fn from_schema_uri(uri: &str) -> Self {
        if uri.contains("draft-04") {
            Self::Draft04
        } else if uri.contains("draft-06") {
            Self::Draft06
        } else if uri.contains("draft-07") {
            Self::Draft07
        } else if uri.contains("draft/2019-09") {
            Self::Draft201909
        } else if uri.contains("draft/2020-12") {
            Self::Draft202012
        } else {
            Self::Unknown
        }
    }
}

/// Main analyzer for JSON Schema files
#[derive(Debug, Default)]
pub struct JsonSchemaAnalyzer {
    /// Parser for JSON Schema documents
    parser: JsonSchemaParser,
    /// Converter from parsed schema to IR
    converter: SchemaConverter,
}

impl JsonSchemaAnalyzer {
    /// Create a new JSON Schema analyzer
    pub fn new() -> Self {
        Self::default()
    }

    /// Analyze a JSON Schema from a string
    pub fn analyze_str(&self, json: &str, schema_name: &str) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_str(json)?;
        self.converter.convert(&parsed, schema_name)
    }

    /// Analyze a JSON Schema from a file path
    pub fn analyze_file(&self, path: &std::path::Path) -> Result<IrSchema, AnalyzerError> {
        let content = std::fs::read_to_string(path)?;
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("schema"); // SAFETY: fallback to "schema" when file has no stem
        self.analyze_str(&content, name)
    }

    /// Analyze a JSON Schema from a serde_json::Value
    pub fn analyze_value(
        &self,
        value: serde_json::Value,
        schema_name: &str,
    ) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_value(value)?;
        self.converter.convert(&parsed, schema_name)
    }
}

impl protocol_squisher_ir::SchemaAnalyzer for JsonSchemaAnalyzer {
    type Error = AnalyzerError;

    fn analyzer_name(&self) -> &str {
        "json-schema"
    }

    fn supported_extensions(&self) -> &[&str] {
        &["json"]
    }

    fn analyze_file(&self, path: &std::path::Path) -> Result<IrSchema, Self::Error> {
        self.analyze_file(path)
    }

    fn analyze_str(&self, content: &str, name: &str) -> Result<IrSchema, Self::Error> {
        self.analyze_str(content, name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_schema_analyzer_trait() {
        use protocol_squisher_ir::SchemaAnalyzer;

        let analyzer = JsonSchemaAnalyzer::new();
        assert_eq!(analyzer.analyzer_name(), "json-schema");
        assert_eq!(analyzer.supported_extensions(), &["json"]);

        let schema = r#"{
            "type": "object",
            "properties": {
                "name": { "type": "string" }
            }
        }"#;
        let ir = SchemaAnalyzer::analyze_str(&analyzer, schema, "Ping").unwrap();
        assert!(ir.types.contains_key("Ping"));
    }

    #[test]
    fn test_schema_version_detection() {
        assert_eq!(
            SchemaVersion::from_schema_uri("https://json-schema.org/draft-04/schema#"),
            SchemaVersion::Draft04
        );
        assert_eq!(
            SchemaVersion::from_schema_uri("https://json-schema.org/draft-07/schema#"),
            SchemaVersion::Draft07
        );
        assert_eq!(
            SchemaVersion::from_schema_uri("https://json-schema.org/draft/2019-09/schema"),
            SchemaVersion::Draft201909
        );
        assert_eq!(
            SchemaVersion::from_schema_uri("https://json-schema.org/draft/2020-12/schema"),
            SchemaVersion::Draft202012
        );
    }

    #[test]
    fn test_simple_object_schema() {
        let schema = r#"{
            "$schema": "https://json-schema.org/draft/2020-12/schema",
            "type": "object",
            "title": "Person",
            "properties": {
                "name": { "type": "string" },
                "age": { "type": "integer" }
            },
            "required": ["name"]
        }"#;

        let analyzer = JsonSchemaAnalyzer::new();
        let result = analyzer.analyze_str(schema, "Person");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert_eq!(ir.name, "Person");
        assert!(ir.types.contains_key("Person"));
    }

    #[test]
    fn test_string_with_constraints() {
        let schema = r#"{
            "type": "object",
            "properties": {
                "email": {
                    "type": "string",
                    "format": "email",
                    "minLength": 5,
                    "maxLength": 100
                }
            }
        }"#;

        let analyzer = JsonSchemaAnalyzer::new();
        let result = analyzer.analyze_str(schema, "Contact");
        assert!(result.is_ok());
    }

    #[test]
    fn test_numeric_constraints() {
        let schema = r#"{
            "type": "object",
            "properties": {
                "quantity": {
                    "type": "integer",
                    "minimum": 1,
                    "maximum": 100
                },
                "price": {
                    "type": "number",
                    "exclusiveMinimum": 0
                }
            }
        }"#;

        let analyzer = JsonSchemaAnalyzer::new();
        let result = analyzer.analyze_str(schema, "Product");
        assert!(result.is_ok());
    }

    #[test]
    fn test_array_schema() {
        let schema = r#"{
            "type": "object",
            "properties": {
                "tags": {
                    "type": "array",
                    "items": { "type": "string" },
                    "minItems": 1,
                    "maxItems": 10,
                    "uniqueItems": true
                }
            }
        }"#;

        let analyzer = JsonSchemaAnalyzer::new();
        let result = analyzer.analyze_str(schema, "TaggedItem");
        assert!(result.is_ok());
    }

    #[test]
    fn test_enum_schema() {
        let schema = r#"{
            "type": "object",
            "properties": {
                "status": {
                    "type": "string",
                    "enum": ["pending", "active", "completed"]
                }
            }
        }"#;

        let analyzer = JsonSchemaAnalyzer::new();
        let result = analyzer.analyze_str(schema, "Task");
        assert!(result.is_ok());
    }

    #[test]
    fn test_nested_object() {
        let schema = r#"{
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

        let analyzer = JsonSchemaAnalyzer::new();
        let result = analyzer.analyze_str(schema, "Customer");
        assert!(result.is_ok());
    }

    #[test]
    fn test_ref_schema() {
        let schema = r##"{
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
                "billing": { "$ref": "#/$defs/Address" },
                "shipping": { "$ref": "#/$defs/Address" }
            }
        }"##;

        let analyzer = JsonSchemaAnalyzer::new();
        let result = analyzer.analyze_str(schema, "Order");
        assert!(result.is_ok());
    }

    #[test]
    fn test_oneof_schema() {
        let schema = r#"{
            "type": "object",
            "properties": {
                "payment": {
                    "oneOf": [
                        {
                            "type": "object",
                            "properties": {
                                "cardNumber": { "type": "string" }
                            },
                            "required": ["cardNumber"]
                        },
                        {
                            "type": "object",
                            "properties": {
                                "bankAccount": { "type": "string" }
                            },
                            "required": ["bankAccount"]
                        }
                    ]
                }
            }
        }"#;

        let analyzer = JsonSchemaAnalyzer::new();
        let result = analyzer.analyze_str(schema, "Checkout");
        assert!(result.is_ok());
    }
}
