// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Protobuf schema analyzer for protocol-squisher
//!
//! Converts Protocol Buffer definitions (.proto files) to the protocol-squisher
//! IR format with ephapax transport class analysis. Supports both proto2 and proto3 syntax.
//!
//! # Features
//!
//! - **Proto2 and Proto3**: Full support for both syntax versions
//! - **All field types**: Scalar types, messages, enums, repeated, maps, oneofs
//! - **Nested types**: Messages and enums can be nested with automatic flattening
//! - **Transport analysis**: Ephapax-powered compatibility checking between types
//! - **Zero-copy detection**: Identifies when data can be transferred without serialization
//!
//! # Quick Start
//!
//! ```rust,no_run
//! use protocol_squisher_protobuf_analyzer::ProtobufAnalyzer;
//! use std::path::Path;
//!
//! let analyzer = ProtobufAnalyzer::new();
//!
//! // Analyze from file
//! let schema = analyzer.analyze_file(Path::new("schema.proto")).unwrap();
//!
//! // Analyze from string
//! let proto = r#"
//!     syntax = "proto3";
//!     message User {
//!         int32 id = 1;
//!         string name = 2;
//!     }
//! "#;
//! let schema = analyzer.analyze_str(proto, "user").unwrap();
//!
//! // Access types
//! for (name, type_def) in &schema.types {
//!     println!("Found type: {}", name);
//! }
//! ```
//!
//! # Transport Class Analysis
//!
//! Use the ephapax bridge to check type compatibility:
//!
//! ```rust,no_run
//! use protocol_squisher_protobuf_analyzer::{ProtobufAnalyzer, TransportAnalysis};
//! use protocol_squisher_ephapax_ir::IRContext;
//! use protocol_squisher_ir::{IrType, PrimitiveType};
//!
//! let ctx = IRContext::new();
//! let source_type = IrType::Primitive(PrimitiveType::I32);
//! let target_type = IrType::Primitive(PrimitiveType::I64);
//!
//! let analysis = TransportAnalysis::new(&ctx, &source_type, &target_type).unwrap();
//!
//! if analysis.is_zero_copy() {
//!     println!("Zero-copy path available!");
//! } else if analysis.is_safe() {
//!     println!("Safe widening (i32 -> i64)");
//! }
//! ```
//!
//! # Protobuf Type Mappings
//!
//! | Protobuf | IR Type | Transport Compatible With |
//! |----------|---------|---------------------------|
//! | `int32` | `I32` | `I32`, `I64`, `I128` (widening) |
//! | `int64` | `I64` | `I64`, `I128` (widening) |
//! | `string` | `String` | `String` only |
//! | `repeated T` | `Vec<T>` | `Vec<T>` with compatible T |
//! | `map<K,V>` | `Map<K,V>` | `Map<K,V>` with compatible K,V |
//!
//! # Examples
//!
//! See the `examples/` directory for complete working examples:
//! - `analyze_proto` - Basic schema analysis
//! - `transport_analysis` - Field compatibility checking
//! - `complex_schema` - Nested types, oneofs, maps

mod converter;
mod parser;
mod ephapax_bridge;

pub use converter::ProtoConverter;
pub use parser::ProtoParser;
pub use ephapax_bridge::{TransportAnalysis, analyze_transport_compatibility, to_ephapax_primitive};

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

    #[test]
    fn test_complex_nested_types() {
        let proto = r#"
            syntax = "proto3";

            message Company {
                string name = 1;
                repeated Employee employees = 2;

                message Employee {
                    string name = 1;
                    int32 id = 2;
                    Address address = 3;

                    message Address {
                        string street = 1;
                        string city = 2;
                    }
                }
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "company");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Company"));
        assert!(ir.types.contains_key("Company_Employee"));
        assert!(ir.types.contains_key("Company_Employee_Address"));
    }

    #[test]
    fn test_all_protobuf_types() {
        let proto = r#"
            syntax = "proto3";

            message AllTypes {
                double double_field = 1;
                float float_field = 2;
                int32 int32_field = 3;
                int64 int64_field = 4;
                uint32 uint32_field = 5;
                uint64 uint64_field = 6;
                sint32 sint32_field = 7;
                sint64 sint64_field = 8;
                fixed32 fixed32_field = 9;
                fixed64 fixed64_field = 10;
                sfixed32 sfixed32_field = 11;
                sfixed64 sfixed64_field = 12;
                bool bool_field = 13;
                string string_field = 14;
                bytes bytes_field = 15;
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "alltypes");
        assert!(result.is_ok());

        let ir = result.unwrap();
        let all_types = ir.types.get("AllTypes").unwrap();

        if let protocol_squisher_ir::TypeDef::Struct(s) = all_types {
            assert_eq!(s.fields.len(), 15);
        } else {
            panic!("Expected struct type");
        }
    }

    #[test]
    fn test_multiple_messages() {
        let proto = r#"
            syntax = "proto3";

            message User {
                string username = 1;
                string email = 2;
            }

            message Post {
                string title = 1;
                string content = 2;
                string author_username = 3;
            }

            message Comment {
                string text = 1;
                string author_username = 2;
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "schema");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert_eq!(ir.types.len(), 3);
        assert!(ir.types.contains_key("User"));
        assert!(ir.types.contains_key("Post"));
        assert!(ir.types.contains_key("Comment"));
    }

    #[test]
    fn test_nested_enum() {
        let proto = r#"
            syntax = "proto3";

            message Task {
                string title = 1;
                Priority priority = 2;

                enum Priority {
                    UNKNOWN = 0;
                    LOW = 1;
                    MEDIUM = 2;
                    HIGH = 3;
                }
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "task");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Task"));
        assert!(ir.types.contains_key("Task_Priority"));
    }

    #[test]
    fn test_complex_map() {
        let proto = r#"
            syntax = "proto3";

            message UserPreferences {
                map<string, int32> counters = 1;
                map<string, string> labels = 2;
                map<int32, bool> flags = 3;
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "prefs");
        assert!(result.is_ok());

        let ir = result.unwrap();
        let prefs = ir.types.get("UserPreferences").unwrap();

        if let protocol_squisher_ir::TypeDef::Struct(s) = prefs {
            assert_eq!(s.fields.len(), 3);

            // Check that all fields are map types
            for field in &s.fields {
                if let protocol_squisher_ir::IrType::Container(
                    protocol_squisher_ir::ContainerType::Map(_, _)
                ) = &field.ty {
                    // OK
                } else {
                    panic!("Expected map type for field {}", field.name);
                }
            }
        } else {
            panic!("Expected struct type");
        }
    }

    #[test]
    fn test_multiple_oneofs() {
        let proto = r#"
            syntax = "proto3";

            message SearchQuery {
                oneof query_type {
                    string text_query = 1;
                    int32 id_query = 2;
                }

                oneof result_format {
                    bool json_format = 3;
                    bool xml_format = 4;
                }
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "search");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("SearchQuery"));
        assert!(ir.types.contains_key("SearchQuery_QueryType"));
        assert!(ir.types.contains_key("SearchQuery_ResultFormat"));
    }

    #[test]
    fn test_with_comments() {
        let proto = r#"
            syntax = "proto3";

            // User account information
            message User {
                // Unique user ID
                int32 id = 1;
                /* Username for login
                   Must be unique */
                string username = 2;
                string email = 3;  // Contact email
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "user");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("User"));
    }

    #[test]
    fn test_package_declaration() {
        let proto = r#"
            syntax = "proto3";
            package com.example.api;

            message Request {
                string id = 1;
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "api");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Request"));
    }

    #[test]
    fn test_transport_analysis_integration() {
        use crate::ephapax_bridge::TransportAnalysis;
        use protocol_squisher_ephapax_ir::IRContext;
        use protocol_squisher_ir::{IrType, PrimitiveType};

        let proto = r#"
            syntax = "proto3";

            message Data {
                int32 value = 1;
            }
        "#;

        let analyzer = ProtobufAnalyzer::new();
        let result = analyzer.analyze_str(proto, "data").unwrap();

        // Get the field type for the int32 field
        let data_type = result.types.get("Data").unwrap();
        if let protocol_squisher_ir::TypeDef::Struct(s) = data_type {
            let field = s.fields.first().unwrap();

            // The field type is I32 (since proto3 fields are non-optional by default)
            // Test transport analysis
            let ctx = IRContext::new();
            let target_type = IrType::Primitive(PrimitiveType::I32);

            // In proto3, non-optional fields are just the primitive type
            let analysis = TransportAnalysis::new(&ctx, &field.ty, &target_type).unwrap();

            // Should be zero-copy for I32 -> I32
            assert!(analysis.is_zero_copy(),
                "Expected zero-copy but got class {:?} for types {:?} -> {:?}",
                analysis.class, field.ty, target_type);
            assert!(analysis.is_safe());
        }
    }
}
