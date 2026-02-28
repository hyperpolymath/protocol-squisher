// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Apache Avro schema analyzer for protocol-squisher
//!
//! Converts Avro schema definitions (.avsc JSON files) to the protocol-squisher IR format
//! with ephapax transport class analysis. Avro is a schema-based serialization format
//! with strong schema evolution support.
//!
//! # Features
//!
//! - **Schema evolution**: Reader/writer schema compatibility
//! - **Union types**: Tagged unions with runtime type checking
//! - **Name-based fields**: No field numbers required
//! - **Compact encoding**: Space-efficient binary format
//! - **Dynamic typing**: Schema provided with data
//! - **Transport analysis**: Ephapax-powered compatibility checking
//!
//! # Quick Start
//!
//! ```rust,no_run
//! use protocol_squisher_avro_analyzer::AvroAnalyzer;
//! use std::path::Path;
//!
//! let analyzer = AvroAnalyzer::new();
//!
//! // Analyze from file
//! let schema = analyzer.analyze_file(Path::new("schema.avsc"));
//!
//! // Analyze from JSON string
//! let avro_json = r#"
//! {
//!   "type": "record",
//!   "name": "User",
//!   "fields": [
//!     {"name": "id", "type": "long"},
//!     {"name": "name", "type": "string"}
//!   ]
//! }
//! "#;
//! let schema = analyzer.analyze_str(avro_json, "user");
//!
//! // Access types
//! if let Ok(schema) = schema {
//!     for (name, _type_def) in &schema.types {
//!         println!("Found type: {}", name);
//!     }
//! }
//! ```
//!
//! # Avro Type Mappings
//!
//! | Avro | IR Type | Transport Class | Notes |
//! |------|---------|-----------------|-------|
//! | `null` | `Unit` | Special | Often used in unions |
//! | `boolean` | `Bool` | Concorde | Zero-copy compatible |
//! | `int` | `I32` | Concorde | 32-bit signed |
//! | `long` | `I64` | Concorde | 64-bit signed |
//! | `float` | `F32` | Concorde | 32-bit float |
//! | `double` | `F64` | Concorde | 64-bit float |
//! | `bytes` | `Vec<U8>` | Economy | Heap allocation |
//! | `string` | `String` | Economy | Heap allocation |
//! | `array` | `Vec<T>` | Economy+ | Depends on element type |
//! | `map` | `Map<String,V>` | Economy+ | Keys always strings |
//! | `union` | `Enum` | Business+ | Runtime type tag |
//! | `record` | `Struct` | Varies | Depends on fields |
//! | `enum` | `Enum` | Concorde | Simple variants |
//! | `fixed` | `[u8; N]` | Concorde | Fixed-size bytes |
//!
//! # Schema Evolution Patterns
//!
//! Avro's schema evolution creates opportunities for squishing:
//!
//! - **Optional fields**: `["null", "T"]` unions can often be required
//! - **Default values**: Suggest backward compatibility constraints
//! - **Union bloat**: Runtime type tags add overhead
//! - **Name aliases**: Multiple names for same field
//!
//! These patterns are captured in the IR metadata for squishability analysis.

mod converter;
mod ephapax_bridge;
mod parser;

pub use converter::AvroConverter;
pub use ephapax_bridge::{analyze_transport_compatibility, TransportAnalysis};
pub use parser::AvroParser;

use protocol_squisher_ir::IrSchema;
use std::path::Path;
use thiserror::Error;

/// Errors that can occur during Avro analysis
#[derive(Debug, Error)]
pub enum AnalyzerError {
    /// Failed to parse Avro schema JSON
    #[error("Avro parse error: {0}")]
    ParseError(String),

    /// Invalid Avro schema structure
    #[error("Invalid Avro schema: {0}")]
    InvalidSchema(String),

    /// Unsupported Avro feature
    #[error("Unsupported feature: {0}")]
    UnsupportedFeature(String),

    /// IO error
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    /// JSON parsing error
    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),
}

/// Main analyzer for Avro schema files
#[derive(Debug, Default)]
pub struct AvroAnalyzer {
    /// Parser for Avro JSON schemas
    parser: AvroParser,
    /// Converter from parsed Avro to IR
    converter: AvroConverter,
}

impl AvroAnalyzer {
    /// Create a new Avro analyzer
    pub fn new() -> Self {
        Self::default()
    }

    /// Analyze an Avro schema file from a path
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_file(path)?;
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("schema");
        self.converter.convert(&parsed, name)
    }

    /// Analyze Avro schema content from a JSON string
    pub fn analyze_str(&self, content: &str, name: &str) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_str(content)?;
        self.converter.convert(&parsed, name)
    }
}

impl protocol_squisher_ir::SchemaAnalyzer for AvroAnalyzer {
    type Error = AnalyzerError;

    fn analyzer_name(&self) -> &str {
        "avro"
    }

    fn supported_extensions(&self) -> &[&str] {
        &["avsc", "avro"]
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
        let analyzer = AvroAnalyzer::new();
        assert_eq!(analyzer.analyzer_name(), "avro");
        assert!(analyzer.supported_extensions().contains(&"avsc"));
    }

    #[test]
    fn test_simple_record() {
        let avro_json = r#"
        {
            "type": "record",
            "name": "Person",
            "fields": [
                {"name": "name", "type": "string"},
                {"name": "age", "type": "int"}
            ]
        }
        "#;

        let analyzer = AvroAnalyzer::new();
        let result = analyzer.analyze_str(avro_json, "person");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Person"));
    }

    #[test]
    fn test_optional_field() {
        let avro_json = r#"
        {
            "type": "record",
            "name": "User",
            "fields": [
                {"name": "id", "type": "long"},
                {"name": "email", "type": ["null", "string"]}
            ]
        }
        "#;

        let analyzer = AvroAnalyzer::new();
        let result = analyzer.analyze_str(avro_json, "user");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("User"));
    }

    #[test]
    fn test_array_field() {
        let avro_json = r#"
        {
            "type": "record",
            "name": "TaggedItem",
            "fields": [
                {"name": "name", "type": "string"},
                {"name": "tags", "type": {"type": "array", "items": "string"}}
            ]
        }
        "#;

        let analyzer = AvroAnalyzer::new();
        let result = analyzer.analyze_str(avro_json, "tagged");
        assert!(result.is_ok());
    }

    #[test]
    fn test_map_field() {
        let avro_json = r#"
        {
            "type": "record",
            "name": "Config",
            "fields": [
                {"name": "settings", "type": {"type": "map", "values": "string"}}
            ]
        }
        "#;

        let analyzer = AvroAnalyzer::new();
        let result = analyzer.analyze_str(avro_json, "config");
        assert!(result.is_ok());
    }

    #[test]
    fn test_enum_type() {
        let avro_json = r#"
        {
            "type": "enum",
            "name": "Status",
            "symbols": ["UNKNOWN", "ACTIVE", "INACTIVE"]
        }
        "#;

        let analyzer = AvroAnalyzer::new();
        let result = analyzer.analyze_str(avro_json, "status");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Status"));
    }

    #[test]
    fn test_fixed_type() {
        let avro_json = r#"
        {
            "type": "record",
            "name": "Message",
            "fields": [
                {"name": "id", "type": {"type": "fixed", "name": "UUID", "size": 16}}
            ]
        }
        "#;

        let analyzer = AvroAnalyzer::new();
        let result = analyzer.analyze_str(avro_json, "message");
        assert!(result.is_ok());
    }

    #[test]
    fn test_nested_record() {
        let avro_json = r#"
        {
            "type": "record",
            "name": "User",
            "fields": [
                {"name": "name", "type": "string"},
                {"name": "address", "type": {
                    "type": "record",
                    "name": "Address",
                    "fields": [
                        {"name": "street", "type": "string"},
                        {"name": "city", "type": "string"}
                    ]
                }}
            ]
        }
        "#;

        let analyzer = AvroAnalyzer::new();
        let result = analyzer.analyze_str(avro_json, "user");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("User"));
        assert!(ir.types.contains_key("Address"));
    }

    #[test]
    fn test_union_types() {
        let avro_json = r#"
        {
            "type": "record",
            "name": "Response",
            "fields": [
                {"name": "data", "type": ["string", "int", "boolean"]}
            ]
        }
        "#;

        let analyzer = AvroAnalyzer::new();
        let result = analyzer.analyze_str(avro_json, "response");
        assert!(result.is_ok());
    }
}
