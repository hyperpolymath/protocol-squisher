// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! MessagePack schema analyzer for protocol-squisher
//!
//! Converts JSON Schema or TypeScript interfaces to the protocol-squisher IR format
//! with ephapax transport class analysis. MessagePack is a schema-less binary
//! serialization format with dynamic typing, making it similar to JSON but more efficient.
//!
//! # Features
//!
//! - **Schema-less format**: No compile-time schema like Bebop/FlatBuffers
//! - **Dynamic typing**: Type information embedded in binary format
//! - **JSON Schema support**: Accepts JSON Schema as proxy for type information
//! - **TypeScript support**: Can parse TypeScript interfaces for type info
//! - **Transport analysis**: Shows high squishability (Wheelbarrow class) due to dynamic typing
//!
//! # Quick Start
//!
//! ```rust,no_run
//! use protocol_squisher_messagepack_analyzer::MessagePackAnalyzer;
//! use std::path::Path;
//!
//! let analyzer = MessagePackAnalyzer::new();
//!
//! // Analyze from JSON Schema file
//! let schema = analyzer.analyze_file(Path::new("schema.json")).unwrap();
//!
//! // Analyze from JSON Schema string
//! let json_schema = r#"{
//!     "type": "object",
//!     "properties": {
//!         "id": { "type": "integer" },
//!         "name": { "type": "string" }
//!     },
//!     "required": ["id", "name"]
//! }"#;
//! let schema = analyzer.analyze_str(json_schema, "user").unwrap();
//!
//! // Access types
//! for (name, type_def) in &schema.types {
//!     println!("Found type: {}", name);
//! }
//! ```
//!
//! # MessagePack Type Mappings (from JSON Schema)
//!
//! | JSON Schema | MessagePack | IR Type | Transport Class |
//! |-------------|-------------|---------|-----------------|
//! | `null` | nil | `Option<T>` | Wheelbarrow (dynamic) |
//! | `boolean` | bool | `Bool` | Wheelbarrow (dynamic) |
//! | `integer` | int | `I64` | Wheelbarrow (dynamic) |
//! | `number` | float | `F64` | Wheelbarrow (dynamic) |
//! | `string` | str | `String` | Wheelbarrow (dynamic) |
//! | `array` | array | `Vec<Dynamic>` | Wheelbarrow (dynamic) |
//! | `object` | map | `Map<String, Dynamic>` | Wheelbarrow (dynamic) |
//!
//! # Why Wheelbarrow Class?
//!
//! MessagePack has no compile-time schema, so all type checking happens at runtime:
//! - Fields can change types between messages
//! - No static validation possible
//! - Requires JSON-like fallback for type safety
//! - High flexibility but maximum overhead for type conversions
//!
//! This makes MessagePack ideal for demonstrating the diversity spectrum's
//! schema-less end, contrasting with Bebop/FlatBuffers' schema-based approach.

mod converter;
mod ephapax_bridge;
mod parser;

pub use converter::MessagePackConverter;
pub use ephapax_bridge::{analyze_transport_compatibility, TransportAnalysis};
pub use parser::MessagePackParser;

use protocol_squisher_ir::IrSchema;
use std::path::Path;
use thiserror::Error;

/// Errors that can occur during MessagePack analysis
#[derive(Debug, Error)]
pub enum AnalyzerError {
    /// Failed to parse JSON Schema
    #[error("JSON Schema parse error: {0}")]
    ParseError(String),

    /// Invalid JSON Schema structure
    #[error("Invalid JSON Schema: {0}")]
    InvalidSchema(String),

    /// Unsupported JSON Schema feature
    #[error("Unsupported feature: {0}")]
    UnsupportedFeature(String),

    /// IO error
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    /// JSON parsing error
    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),
}

/// Main analyzer for MessagePack schemas (JSON Schema format)
#[derive(Debug, Default)]
pub struct MessagePackAnalyzer {
    /// Parser for JSON Schema files
    parser: MessagePackParser,
    /// Converter from parsed schema to IR
    converter: MessagePackConverter,
}

impl MessagePackAnalyzer {
    /// Create a new MessagePack analyzer
    pub fn new() -> Self {
        Self::default()
    }

    /// Analyze a JSON Schema file from a path
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_file(path)?;
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("schema");
        self.converter.convert(&parsed, name)
    }

    /// Analyze JSON Schema content from a string
    pub fn analyze_str(&self, content: &str, name: &str) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_str(content)?;
        self.converter.convert(&parsed, name)
    }
}

impl protocol_squisher_ir::SchemaAnalyzer for MessagePackAnalyzer {
    type Error = AnalyzerError;

    fn analyzer_name(&self) -> &str {
        "messagepack"
    }

    fn supported_extensions(&self) -> &[&str] {
        &["msgpack"]
    }

    fn analyze_file(&self, path: &Path) -> Result<IrSchema, Self::Error> {
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

        let analyzer = MessagePackAnalyzer::new();
        assert_eq!(analyzer.analyzer_name(), "messagepack");
        assert_eq!(analyzer.supported_extensions(), &["msgpack"]);

        let json_schema = r#"{
            "type": "object",
            "properties": {
                "msg": { "type": "string" }
            }
        }"#;
        let ir = SchemaAnalyzer::analyze_str(&analyzer, json_schema, "ping").unwrap();
        assert!(ir.types.contains_key("Ping"));
    }

    #[test]
    fn test_simple_object() {
        let json_schema = r#"{
            "type": "object",
            "properties": {
                "name": { "type": "string" },
                "age": { "type": "integer" }
            }
        }"#;

        let analyzer = MessagePackAnalyzer::new();
        let result = analyzer.analyze_str(json_schema, "person");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Person"));
    }

    #[test]
    fn test_required_fields() {
        let json_schema = r#"{
            "type": "object",
            "properties": {
                "id": { "type": "integer" },
                "name": { "type": "string" }
            },
            "required": ["id"]
        }"#;

        let analyzer = MessagePackAnalyzer::new();
        let result = analyzer.analyze_str(json_schema, "user");
        assert!(result.is_ok());
    }

    #[test]
    fn test_array_field() {
        let json_schema = r#"{
            "type": "object",
            "properties": {
                "name": { "type": "string" },
                "tags": {
                    "type": "array",
                    "items": { "type": "string" }
                }
            }
        }"#;

        let analyzer = MessagePackAnalyzer::new();
        let result = analyzer.analyze_str(json_schema, "tagged");
        assert!(result.is_ok());
    }

    #[test]
    fn test_nested_object() {
        let json_schema = r#"{
            "type": "object",
            "properties": {
                "name": { "type": "string" },
                "address": {
                    "type": "object",
                    "properties": {
                        "street": { "type": "string" },
                        "city": { "type": "string" }
                    }
                }
            }
        }"#;

        let analyzer = MessagePackAnalyzer::new();
        let result = analyzer.analyze_str(json_schema, "person");
        assert!(result.is_ok());
    }

    #[test]
    fn test_all_json_schema_types() {
        let json_schema = r#"{
            "type": "object",
            "properties": {
                "bool_field": { "type": "boolean" },
                "int_field": { "type": "integer" },
                "number_field": { "type": "number" },
                "string_field": { "type": "string" },
                "null_field": { "type": "null" }
            }
        }"#;

        let analyzer = MessagePackAnalyzer::new();
        let result = analyzer.analyze_str(json_schema, "alltypes");
        assert!(result.is_ok());

        let ir = result.unwrap();
        let all_types = ir.types.get("Alltypes").unwrap();

        assert!(
            matches!(all_types, protocol_squisher_ir::TypeDef::Struct(_)),
            "Expected struct type"
        );
        let protocol_squisher_ir::TypeDef::Struct(s) = all_types else {
            unreachable!("asserted struct");
        };
        assert_eq!(s.fields.len(), 5);
    }

    #[test]
    fn test_dynamic_typing_characteristic() {
        // MessagePack is schema-less - this test verifies we handle
        // the lack of compile-time type constraints properly
        let json_schema = r#"{
            "type": "object",
            "properties": {
                "dynamic_field": {}
            }
        }"#;

        let analyzer = MessagePackAnalyzer::new();
        let result = analyzer.analyze_str(json_schema, "dynamic");
        assert!(result.is_ok());
    }

    #[test]
    fn test_optional_field() {
        let json_schema = r#"{
            "type": "object",
            "properties": {
                "required_name": { "type": "string" },
                "optional_age": { "type": "integer" }
            },
            "required": ["required_name"]
        }"#;

        let analyzer = MessagePackAnalyzer::new();
        let result = analyzer.analyze_str(json_schema, "person");
        assert!(result.is_ok());
    }

    #[test]
    fn test_enum_values() {
        let json_schema = r#"{
            "type": "object",
            "properties": {
                "status": {
                    "type": "string",
                    "enum": ["draft", "published", "archived"]
                }
            }
        }"#;

        let analyzer = MessagePackAnalyzer::new();
        let result = analyzer.analyze_str(json_schema, "post");
        assert!(result.is_ok());
    }

    #[test]
    fn test_number_constraints() {
        let json_schema = r#"{
            "type": "object",
            "properties": {
                "age": {
                    "type": "integer",
                    "minimum": 0,
                    "maximum": 150
                }
            }
        }"#;

        let analyzer = MessagePackAnalyzer::new();
        let result = analyzer.analyze_str(json_schema, "person");
        assert!(result.is_ok());
    }

    #[test]
    fn test_string_constraints() {
        let json_schema = r#"{
            "type": "object",
            "properties": {
                "username": {
                    "type": "string",
                    "minLength": 3,
                    "maxLength": 20,
                    "pattern": "^[a-zA-Z0-9_]+$"
                }
            }
        }"#;

        let analyzer = MessagePackAnalyzer::new();
        let result = analyzer.analyze_str(json_schema, "user");
        assert!(result.is_ok());
    }
}
