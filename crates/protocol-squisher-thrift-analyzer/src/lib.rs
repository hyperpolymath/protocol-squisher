// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Apache Thrift IDL analyzer for protocol-squisher
//!
//! Converts Thrift IDL definitions to the protocol-squisher IR format with
//! ephapax transport class analysis. Thrift is an enterprise RPC framework
//! with IDL-based schemas designed for cross-language service development.
//!
//! # Features
//!
//! - **IDL syntax**: C-style interface definition language
//! - **All field types**: Structs, enums, exceptions, typedefs
//! - **Field modifiers**: Required/optional/default field semantics
//! - **Versioning**: Field numbers for schema evolution
//! - **Transport analysis**: Ephapax-powered compatibility checking
//!
//! # Quick Start
//!
//! ```rust,no_run
//! use protocol_squisher_thrift_analyzer::ThriftAnalyzer;
//! use std::path::Path;
//!
//! let analyzer = ThriftAnalyzer::new();
//!
//! // Analyze from file
//! let schema = analyzer.analyze_file(Path::new("schema.thrift"));
//!
//! // Analyze from string
//! let thrift = r#"
//!     struct User {
//!         1: required i64 id
//!         2: required string name
//!         3: optional string email
//!     }
//! "#;
//! let schema = analyzer.analyze_str(thrift, "user");
//!
//! // Access types
//! if let Ok(schema) = schema {
//!     for (name, _type_def) in &schema.types {
//!         println!("Found type: {}", name);
//!     }
//! }
//! ```
//!
//! # Thrift Type Mappings
//!
//! | Thrift | IR Type | Transport Compatible With |
//! |--------|---------|---------------------------|
//! | `bool` | `Bool` | `Bool` only |
//! | `byte`/`i8` | `I8` | `I8`, `I16`, `I32`, `I64`, `I128` (widening) |
//! | `i16` | `I16` | `I16`, `I32`, `I64`, `I128` (widening) |
//! | `i32` | `I32` | `I32`, `I64`, `I128` (widening) |
//! | `i64` | `I64` | `I64`, `I128` (widening) |
//! | `double` | `F64` | `F64` only |
//! | `string` | `String` | `String` only |
//! | `binary` | `Vec<U8>` | `Vec<U8>` only |
//! | `list<T>` | `Vec<T>` | `Vec<T>` with compatible T |
//! | `set<T>` | `Vec<T>` | `Vec<T>` (with uniqueness constraint) |
//! | `map<K,V>` | `Map<K,V>` | `Map<K,V>` with compatible K,V |

mod converter;
mod ephapax_bridge;
mod parser;

pub use converter::ThriftConverter;
pub use ephapax_bridge::{analyze_transport_compatibility, TransportAnalysis};
pub use parser::ThriftParser;

use protocol_squisher_ir::IrSchema;
use std::path::Path;
use thiserror::Error;

/// Errors that can occur during Thrift analysis
#[derive(Debug, Error)]
pub enum AnalyzerError {
    /// Failed to parse thrift file
    #[error("Thrift parse error: {0}")]
    ParseError(String),

    /// Invalid thrift structure
    #[error("Invalid thrift: {0}")]
    InvalidThrift(String),

    /// Unsupported thrift feature
    #[error("Unsupported feature: {0}")]
    UnsupportedFeature(String),

    /// IO error
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Main analyzer for Thrift files
#[derive(Debug, Default)]
pub struct ThriftAnalyzer {
    /// Parser for thrift files
    parser: ThriftParser,
    /// Converter from parsed thrift to IR
    converter: ThriftConverter,
}

impl ThriftAnalyzer {
    /// Create a new Thrift analyzer
    pub fn new() -> Self {
        Self::default()
    }

    /// Analyze a thrift file from a path
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_file(path)?;
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("schema");
        self.converter.convert(&parsed, name)
    }

    /// Analyze thrift content from a string
    pub fn analyze_str(&self, content: &str, name: &str) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_str(content)?;
        self.converter.convert(&parsed, name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_struct() {
        let thrift = r#"
            struct Person {
                1: required string name
                2: required i32 age
            }
        "#;

        let analyzer = ThriftAnalyzer::new();
        let result = analyzer.analyze_str(thrift, "person");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Person"));
    }

    #[test]
    fn test_enum() {
        let thrift = r#"
            enum Status {
                UNKNOWN = 0
                ACTIVE = 1
                INACTIVE = 2
            }

            struct Task {
                1: required string title
                2: required Status status
            }
        "#;

        let analyzer = ThriftAnalyzer::new();
        let result = analyzer.analyze_str(thrift, "task");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Status"));
        assert!(ir.types.contains_key("Task"));
    }

    #[test]
    fn test_list_field() {
        let thrift = r#"
            struct TaggedItem {
                1: required string name
                2: required list<string> tags
            }
        "#;

        let analyzer = ThriftAnalyzer::new();
        let result = analyzer.analyze_str(thrift, "tagged");
        assert!(result.is_ok());
    }

    #[test]
    fn test_map_field() {
        let thrift = r#"
            struct Config {
                1: required map<string, string> settings
            }
        "#;

        let analyzer = ThriftAnalyzer::new();
        let result = analyzer.analyze_str(thrift, "config");
        if let Err(e) = &result {
            eprintln!("Error: {:?}", e);
        }
        assert!(result.is_ok());
    }

    #[test]
    fn test_optional_field() {
        let thrift = r#"
            struct Person {
                1: required string name
                2: optional i32 age
            }
        "#;

        let analyzer = ThriftAnalyzer::new();
        let result = analyzer.analyze_str(thrift, "person");
        assert!(result.is_ok());
    }

    #[test]
    fn test_default_value() {
        let thrift = r#"
            struct Config {
                1: i32 timeout = 30
                2: string host = "localhost"
            }
        "#;

        let analyzer = ThriftAnalyzer::new();
        let result = analyzer.analyze_str(thrift, "config");
        assert!(result.is_ok());
    }

    #[test]
    fn test_all_thrift_types() {
        let thrift = r#"
            struct AllTypes {
                1: required bool bool_field
                2: required byte byte_field
                3: required i16 int16_field
                4: required i32 int32_field
                5: required i64 int64_field
                6: required double double_field
                7: required string string_field
                8: required binary binary_field
            }
        "#;

        let analyzer = ThriftAnalyzer::new();
        let result = analyzer.analyze_str(thrift, "alltypes");
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
        assert_eq!(s.fields.len(), 8);
    }

    #[test]
    fn test_multiple_definitions() {
        let thrift = r#"
            struct User {
                1: required string username
                2: required string email
            }

            struct Post {
                1: required string title
                2: required string content
                3: required string author_username
            }

            enum PostStatus {
                DRAFT = 0
                PUBLISHED = 1
                ARCHIVED = 2
            }
        "#;

        let analyzer = ThriftAnalyzer::new();
        let result = analyzer.analyze_str(thrift, "schema");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert_eq!(ir.types.len(), 3);
        assert!(ir.types.contains_key("User"));
        assert!(ir.types.contains_key("Post"));
        assert!(ir.types.contains_key("PostStatus"));
    }

    #[test]
    fn test_exception() {
        let thrift = r#"
            exception UserNotFound {
                1: required string message
                2: optional i64 user_id
            }
        "#;

        let analyzer = ThriftAnalyzer::new();
        let result = analyzer.analyze_str(thrift, "exceptions");
        assert!(result.is_ok());
    }

    #[test]
    fn test_typedef() {
        let thrift = r#"
            typedef i64 UserId

            struct User {
                1: required UserId id
                2: required string name
            }
        "#;

        let analyzer = ThriftAnalyzer::new();
        let result = analyzer.analyze_str(thrift, "user");
        assert!(result.is_ok());
    }

    #[test]
    fn test_const_declaration() {
        let thrift = r#"
            const i32 MAX_USERS = 1000

            struct UserLimit {
                1: required i32 current_count
            }
        "#;

        let analyzer = ThriftAnalyzer::new();
        let result = analyzer.analyze_str(thrift, "limits");
        assert!(result.is_ok());
    }
}
