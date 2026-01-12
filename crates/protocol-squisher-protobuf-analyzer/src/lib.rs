// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Protobuf schema analyzer for protocol-squisher
//!
//! Converts Protocol Buffer definitions (.proto files) to the protocol-squisher
//! IR format. Supports both proto2 and proto3 syntax.
//!
//! # Example
//!
//! ```rust,no_run
//! use protocol_squisher_protobuf_analyzer::ProtobufAnalyzer;
//! use std::path::Path;
//!
//! let analyzer = ProtobufAnalyzer::new();
//! let ir_schema = analyzer.analyze_file(Path::new("schema.proto")).unwrap();
//! ```

mod converter;
mod parser;

pub use converter::ProtoConverter;
pub use parser::ProtoParser;

use protocol_squisher_ir::IrSchema;
use std::path::Path;
use thiserror::Error;

/// Errors that can occur during Protobuf analysis
#[derive(Debug, Error)]
pub enum AnalyzerError {
    /// Failed to parse protobuf file
    #[error("Protobuf parse error: {0}")]
    ParseError(String),

    /// Invalid protobuf structure
    #[error("Invalid protobuf: {0}")]
    InvalidProto(String),

    /// Unsupported protobuf feature
    #[error("Unsupported feature: {0}")]
    UnsupportedFeature(String),

    /// IO error
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Protobuf syntax version
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ProtoSyntax {
    /// Proto2 syntax (explicit optional/required)
    Proto2,
    /// Proto3 syntax (implicit optional, no required)
    #[default]
    Proto3,
}

/// Main analyzer for Protobuf files
#[derive(Debug, Default)]
pub struct ProtobufAnalyzer {
    /// Parser for protobuf files
    parser: ProtoParser,
    /// Converter from parsed proto to IR
    converter: ProtoConverter,
}

impl ProtobufAnalyzer {
    /// Create a new Protobuf analyzer
    pub fn new() -> Self {
        Self::default()
    }

    /// Analyze a protobuf file from a path
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_file(path)?;
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("schema");
        self.converter.convert(&parsed, name)
    }

    /// Analyze protobuf content from a string
    pub fn analyze_str(&self, content: &str, name: &str) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_str(content)?;
        self.converter.convert(&parsed, name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_message() {
        let proto = r#"
            syntax = "proto3";

            message Person {
                string name = 1;
                int32 age = 2;
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "person");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Person"));
    }

    #[test]
    fn test_nested_message() {
        let proto = r#"
            syntax = "proto3";

            message Person {
                string name = 1;
                Address address = 2;

                message Address {
                    string street = 1;
                    string city = 2;
                }
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "person");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Person"));
        assert!(ir.types.contains_key("Person_Address"));
    }

    #[test]
    fn test_enum() {
        let proto = r#"
            syntax = "proto3";

            enum Status {
                UNKNOWN = 0;
                ACTIVE = 1;
                INACTIVE = 2;
            }

            message Task {
                string title = 1;
                Status status = 2;
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "task");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Status"));
        assert!(ir.types.contains_key("Task"));
    }

    #[test]
    fn test_repeated_field() {
        let proto = r#"
            syntax = "proto3";

            message TaggedItem {
                string name = 1;
                repeated string tags = 2;
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "tagged");
        assert!(result.is_ok());
    }

    #[test]
    fn test_map_field() {
        let proto = r#"
            syntax = "proto3";

            message Config {
                map<string, string> settings = 1;
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "config");
        assert!(result.is_ok());
    }

    #[test]
    fn test_oneof() {
        let proto = r#"
            syntax = "proto3";

            message Payment {
                oneof method {
                    string card_number = 1;
                    string bank_account = 2;
                }
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "payment");
        assert!(result.is_ok());
    }

    #[test]
    fn test_proto2_syntax() {
        let proto = r#"
            syntax = "proto2";

            message Person {
                required string name = 1;
                optional int32 age = 2;
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "person");
        assert!(result.is_ok());
    }

    #[test]
    fn test_optional_field_proto3() {
        let proto = r#"
            syntax = "proto3";

            message Person {
                string name = 1;
                optional int32 age = 2;
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "person");
        assert!(result.is_ok());
    }
}
