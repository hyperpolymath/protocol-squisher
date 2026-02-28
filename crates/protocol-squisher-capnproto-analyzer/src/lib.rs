// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Cap'n Proto schema analyzer for protocol-squisher
//!
//! Converts Cap'n Proto schema definitions to the protocol-squisher IR format with
//! ephapax transport class analysis. Cap'n Proto is a zero-copy serialization format
//! designed for extreme performance and RPC capabilities.
//!
//! # Features
//!
//! - **Zero-copy access**: Direct memory mapping without deserialization
//! - **Schema-based**: Clean .capnp schema definitions
//! - **Field numbering**: Explicit field numbers for versioning
//! - **RPC support**: Interface definitions (data types only in this analyzer)
//! - **Transport analysis**: Ephapax-powered zero-copy detection
//! - **Packing**: Efficient wire format with bit-level packing
//!
//! # Quick Start
//!
//! ```rust,no_run
//! use protocol_squisher_capnproto_analyzer::CapnProtoAnalyzer;
//! use std::path::Path;
//!
//! let analyzer = CapnProtoAnalyzer::new();
//!
//! // Analyze from file
//! let schema = analyzer.analyze_file(Path::new("schema.capnp"));
//!
//! // Analyze from string
//! let capnp = r#"
//!     struct User {
//!         id @0 :Int64;
//!         name @1 :Text;
//!     }
//! "#;
//! let schema = analyzer.analyze_str(capnp, "user");
//!
//! // Access types
//! if let Ok(schema) = schema {
//!     for (name, _type_def) in &schema.types {
//!         println!("Found type: {}", name);
//!     }
//! }
//! ```
//!
//! # Cap'n Proto Type Mappings
//!
//! | Cap'n Proto | IR Type | Transport Class |
//! |-------------|---------|-----------------|
//! | `Void` | `Unit` | Concorde (zero-copy) |
//! | `Bool` | `Bool` | Concorde |
//! | `Int8`/`UInt8` | `I8`/`U8` | Concorde |
//! | `Int16`/`UInt16` | `I16`/`U16` | Concorde |
//! | `Int32`/`UInt32` | `I32`/`U32` | Concorde |
//! | `Int64`/`UInt64` | `I64`/`U64` | Concorde |
//! | `Float32` | `F32` | Concorde |
//! | `Float64` | `F64` | Concorde |
//! | `Text` | `String` | Economy (pointer) |
//! | `Data` | `Vec<U8>` | Economy (pointer) |
//! | `List(T)` | `Vec<T>` | Economy (pointer) |
//! | `struct` | Struct | Concorde (fixed layout with zero_copy metadata) |
//! | `enum` | Enum | Concorde |
//! | `union` | Enum with variants | Economy (discriminant + payload) |
//!
//! # Key Differences from FlatBuffers
//!
//! - **Field numbers**: Cap'n Proto requires explicit `@N` field numbers for versioning
//! - **Pointer indirection**: Text/Data/List are pointers (not inline like FlatBuffers)
//! - **Unions**: Cap'n Proto has first-class union support
//! - **Interfaces**: RPC interfaces (we skip these and focus on data types)
//! - **Generics**: Cap'n Proto supports generic types `List(T)`, `Pair(K,V)`

mod converter;
mod ephapax_bridge;
mod parser;

pub use converter::CapnProtoConverter;
pub use ephapax_bridge::{analyze_transport_compatibility, TransportAnalysis};
pub use parser::CapnProtoParser;

use protocol_squisher_ir::IrSchema;
use std::path::Path;
use thiserror::Error;

/// Errors that can occur during Cap'n Proto analysis
#[derive(Debug, Error)]
pub enum AnalyzerError {
    /// Failed to parse Cap'n Proto file
    #[error("Cap'n Proto parse error: {0}")]
    ParseError(String),

    /// Invalid Cap'n Proto structure
    #[error("Invalid Cap'n Proto: {0}")]
    InvalidCapnProto(String),

    /// Unsupported Cap'n Proto feature
    #[error("Unsupported feature: {0}")]
    UnsupportedFeature(String),

    /// IO error
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Main analyzer for Cap'n Proto files
#[derive(Debug, Default)]
pub struct CapnProtoAnalyzer {
    /// Parser for Cap'n Proto files
    parser: CapnProtoParser,
    /// Converter from parsed Cap'n Proto to IR
    converter: CapnProtoConverter,
}

impl CapnProtoAnalyzer {
    /// Create a new Cap'n Proto analyzer
    pub fn new() -> Self {
        Self::default()
    }

    /// Analyze a Cap'n Proto file from a path
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_file(path)?;
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("schema");
        self.converter.convert(&parsed, name)
    }

    /// Analyze Cap'n Proto content from a string
    pub fn analyze_str(&self, content: &str, name: &str) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_str(content)?;
        self.converter.convert(&parsed, name)
    }
}

impl protocol_squisher_ir::SchemaAnalyzer for CapnProtoAnalyzer {
    type Error = AnalyzerError;

    fn analyzer_name(&self) -> &str {
        "capnproto"
    }

    fn supported_extensions(&self) -> &[&str] {
        &["capnp"]
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

        let analyzer = CapnProtoAnalyzer::new();
        assert_eq!(analyzer.analyzer_name(), "capnproto");
        assert_eq!(analyzer.supported_extensions(), &["capnp"]);

        let capnp = r#"
            struct Ping {
                msg @0 :Text;
            }
        "#;
        let ir = SchemaAnalyzer::analyze_str(&analyzer, capnp, "ping").unwrap();
        assert!(ir.types.contains_key("Ping"));
    }

    #[test]
    fn test_simple_struct() {
        let capnp = r#"
            struct Person {
                name @0 :Text;
                age @1 :Int32;
            }
        "#;

        let analyzer = CapnProtoAnalyzer::new();
        let result = analyzer.analyze_str(capnp, "person");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Person"));
    }

    #[test]
    fn test_enum() {
        let capnp = r#"
            enum Status {
                unknown @0;
                active @1;
                inactive @2;
            }

            struct Task {
                title @0 :Text;
                status @1 :Status;
            }
        "#;

        let analyzer = CapnProtoAnalyzer::new();
        let result = analyzer.analyze_str(capnp, "task");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Status"));
        assert!(ir.types.contains_key("Task"));
    }

    #[test]
    fn test_list_field() {
        let capnp = r#"
            struct TaggedItem {
                name @0 :Text;
                tags @1 :List(Text);
            }
        "#;

        let analyzer = CapnProtoAnalyzer::new();
        let result = analyzer.analyze_str(capnp, "tagged");
        assert!(result.is_ok());
    }

    #[test]
    fn test_union_field() {
        let capnp = r#"
            struct Message {
                union {
                    text @0 :Text;
                    number @1 :Int64;
                }
            }
        "#;

        let analyzer = CapnProtoAnalyzer::new();
        let result = analyzer.analyze_str(capnp, "message");
        assert!(result.is_ok());
    }

    #[test]
    fn test_all_capnproto_types() {
        let capnp = r#"
            struct AllTypes {
                voidField @0 :Void;
                boolField @1 :Bool;
                int8Field @2 :Int8;
                uint8Field @3 :UInt8;
                int16Field @4 :Int16;
                uint16Field @5 :UInt16;
                int32Field @6 :Int32;
                uint32Field @7 :UInt32;
                int64Field @8 :Int64;
                uint64Field @9 :UInt64;
                float32Field @10 :Float32;
                float64Field @11 :Float64;
                textField @12 :Text;
                dataField @13 :Data;
            }
        "#;

        let analyzer = CapnProtoAnalyzer::new();
        let result = analyzer.analyze_str(capnp, "alltypes");
        assert!(result.is_ok());

        let ir = result.unwrap();
        let all_types = ir.types.get("AllTypes").unwrap();

        assert!(
            matches!(all_types, protocol_squisher_ir::TypeDef::Struct(_)),
            "Expected struct type"
        );
        let protocol_squisher_ir::TypeDef::Struct(s) = all_types else {
            unreachable!("asserted struct");
        };
        assert_eq!(s.fields.len(), 14);
    }

    #[test]
    fn test_multiple_definitions() {
        let capnp = r#"
            struct User {
                username @0 :Text;
                email @1 :Text;
            }

            struct Post {
                title @0 :Text;
                content @1 :Text;
                authorUsername @2 :Text;
            }

            enum PostStatus {
                draft @0;
                published @1;
                archived @2;
            }
        "#;

        let analyzer = CapnProtoAnalyzer::new();
        let result = analyzer.analyze_str(capnp, "schema");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert_eq!(ir.types.len(), 3);
        assert!(ir.types.contains_key("User"));
        assert!(ir.types.contains_key("Post"));
        assert!(ir.types.contains_key("PostStatus"));
    }

    #[test]
    fn test_nested_struct() {
        let capnp = r#"
            struct Address {
                street @0 :Text;
                city @1 :Text;
            }

            struct Person {
                name @0 :Text;
                address @1 :Address;
            }
        "#;

        let analyzer = CapnProtoAnalyzer::new();
        let result = analyzer.analyze_str(capnp, "nested");
        assert!(result.is_ok());
    }

    #[test]
    fn test_generic_list() {
        let capnp = r#"
            struct Numbers {
                integers @0 :List(Int32);
                floats @1 :List(Float64);
            }
        "#;

        let analyzer = CapnProtoAnalyzer::new();
        let result = analyzer.analyze_str(capnp, "numbers");
        assert!(result.is_ok());
    }

    #[test]
    fn test_data_field() {
        let capnp = r#"
            struct BinaryData {
                id @0 :Int64;
                payload @1 :Data;
            }
        "#;

        let analyzer = CapnProtoAnalyzer::new();
        let result = analyzer.analyze_str(capnp, "binary");
        assert!(result.is_ok());
    }

    #[test]
    fn test_void_field() {
        let capnp = r#"
            struct Event {
                timestamp @0 :Int64;
                marker @1 :Void;
            }
        "#;

        let analyzer = CapnProtoAnalyzer::new();
        let result = analyzer.analyze_str(capnp, "event");
        assert!(result.is_ok());
    }
}
