// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Bebop schema analyzer for protocol-squisher
//!
//! Converts Bebop schema definitions to the protocol-squisher IR format with
//! ephapax transport class analysis. Bebop is a modern, high-performance
//! schema-based serialization format designed for simplicity and speed.
//!
//! # Features
//!
//! - **Modern syntax**: Clean, readable schema definitions
//! - **All field types**: Structs, messages, enums, arrays, maps
//! - **High performance**: Designed for minimal overhead
//! - **Transport analysis**: Ephapax-powered compatibility checking
//! - **Zero-copy potential**: Can identify when data can be transferred without serialization
//!
//! # Quick Start
//!
//! ```rust,no_run
//! use protocol_squisher_bebop_analyzer::BebopAnalyzer;
//! use std::path::Path;
//!
//! let analyzer = BebopAnalyzer::new();
//!
//! // Analyze from file
//! let schema = analyzer.analyze_file(Path::new("schema.bop"));
//!
//! // Analyze from string
//! let bebop = r#"
//!     struct User {
//!         int32 id;
//!         string name;
//!     }
//! "#;
//! let schema = analyzer.analyze_str(bebop, "user");
//!
//! // Access types
//! if let Ok(schema) = schema {
//!     for (name, _type_def) in &schema.types {
//!         println!("Found type: {}", name);
//!     }
//! }
//! ```
//!
//! # Bebop Type Mappings
//!
//! | Bebop | IR Type | Transport Compatible With |
//! |-------|---------|---------------------------|
//! | `int32` | `I32` | `I32`, `I64`, `I128` (widening) |
//! | `int64` | `I64` | `I64`, `I128` (widening) |
//! | `string` | `String` | `String` only |
//! | `array[T]` | `Vec<T>` | `Vec<T>` with compatible T |
//! | `map[K, V]` | `Map<K,V>` | `Map<K,V>` with compatible K,V |

mod converter;
mod ephapax_bridge;
mod parser;

pub use converter::BebopConverter;
pub use ephapax_bridge::{analyze_transport_compatibility, TransportAnalysis};
pub use parser::BebopParser;

use protocol_squisher_ir::IrSchema;
use std::path::Path;
use thiserror::Error;

/// Errors that can occur during Bebop analysis
#[derive(Debug, Error)]
pub enum AnalyzerError {
    /// Failed to parse bebop file
    #[error("Bebop parse error: {0}")]
    ParseError(String),

    /// Invalid bebop structure
    #[error("Invalid bebop: {0}")]
    InvalidBebop(String),

    /// Unsupported bebop feature
    #[error("Unsupported feature: {0}")]
    UnsupportedFeature(String),

    /// IO error
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Main analyzer for Bebop files
#[derive(Debug, Default)]
pub struct BebopAnalyzer {
    /// Parser for bebop files
    parser: BebopParser,
    /// Converter from parsed bebop to IR
    converter: BebopConverter,
}

impl BebopAnalyzer {
    /// Create a new Bebop analyzer
    pub fn new() -> Self {
        Self::default()
    }

    /// Analyze a bebop file from a path
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_file(path)?;
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("schema");
        self.converter.convert(&parsed, name)
    }

    /// Analyze bebop content from a string
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
        let bebop = r#"
            struct Person {
                string name;
                int32 age;
            }
        "#;

        let analyzer = BebopAnalyzer::new();
        let result = analyzer.analyze_str(bebop, "person");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Person"));
    }

    #[test]
    fn test_enum() {
        let bebop = r#"
            enum Status {
                Unknown = 0;
                Active = 1;
                Inactive = 2;
            }

            struct Task {
                string title;
                Status status;
            }
        "#;

        let analyzer = BebopAnalyzer::new();
        let result = analyzer.analyze_str(bebop, "task");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Status"));
        assert!(ir.types.contains_key("Task"));
    }

    #[test]
    fn test_array_field() {
        let bebop = r#"
            struct TaggedItem {
                string name;
                array[string] tags;
            }
        "#;

        let analyzer = BebopAnalyzer::new();
        let result = analyzer.analyze_str(bebop, "tagged");
        assert!(result.is_ok());
    }

    #[test]
    fn test_map_field() {
        let bebop = r#"
            struct Config {
                map[string, string] settings;
            }
        "#;

        let analyzer = BebopAnalyzer::new();
        let result = analyzer.analyze_str(bebop, "config");
        assert!(result.is_ok());
    }

    #[test]
    fn test_optional_field() {
        let bebop = r#"
            struct Person {
                string name;
                int32? age;
            }
        "#;

        let analyzer = BebopAnalyzer::new();
        let result = analyzer.analyze_str(bebop, "person");
        assert!(result.is_ok());
    }

    #[test]
    fn test_message_with_deprecation() {
        let bebop = r#"
            message User {
                1 -> int32 id;
                2 -> string name;
                3 -> deprecated string old_field;
            }
        "#;

        let analyzer = BebopAnalyzer::new();
        let result = analyzer.analyze_str(bebop, "user");
        assert!(result.is_ok());
    }

    #[test]
    fn test_all_bebop_types() {
        let bebop = r#"
            struct AllTypes {
                bool bool_field;
                byte byte_field;
                int16 int16_field;
                uint16 uint16_field;
                int32 int32_field;
                uint32 uint32_field;
                int64 int64_field;
                uint64 uint64_field;
                float32 float32_field;
                float64 float64_field;
                string string_field;
                guid guid_field;
                date date_field;
            }
        "#;

        let analyzer = BebopAnalyzer::new();
        let result = analyzer.analyze_str(bebop, "alltypes");
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
        assert_eq!(s.fields.len(), 13);
    }

    #[test]
    fn test_multiple_definitions() {
        let bebop = r#"
            struct User {
                string username;
                string email;
            }

            struct Post {
                string title;
                string content;
                string author_username;
            }

            enum PostStatus {
                Draft = 0;
                Published = 1;
                Archived = 2;
            }
        "#;

        let analyzer = BebopAnalyzer::new();
        let result = analyzer.analyze_str(bebop, "schema");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert_eq!(ir.types.len(), 3);
        assert!(ir.types.contains_key("User"));
        assert!(ir.types.contains_key("Post"));
        assert!(ir.types.contains_key("PostStatus"));
    }

    #[test]
    fn test_readonly_message() {
        let bebop = r#"
            readonly message Config {
                1 -> string api_key;
                2 -> string base_url;
            }
        "#;

        let analyzer = BebopAnalyzer::new();
        let result = analyzer.analyze_str(bebop, "config");
        assert!(result.is_ok());
    }
}
