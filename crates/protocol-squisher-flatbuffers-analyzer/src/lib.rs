// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! FlatBuffers schema analyzer for protocol-squisher
//!
//! Converts FlatBuffers schema definitions to the protocol-squisher IR format with
//! ephapax transport class analysis. FlatBuffers is a zero-copy serialization format
//! designed for performance-critical applications.
//!
//! # Features
//!
//! - **Zero-copy access**: Direct memory mapping without deserialization
//! - **Schema-based**: Clean .fbs schema definitions
//! - **Type safety**: Tables, structs, enums, unions
//! - **Performance**: Optimized for speed and memory efficiency
//! - **Transport analysis**: Ephapax-powered zero-copy detection
//!
//! # Quick Start
//!
//! ```rust,no_run
//! use protocol_squisher_flatbuffers_analyzer::FlatBuffersAnalyzer;
//! use std::path::Path;
//!
//! let analyzer = FlatBuffersAnalyzer::new();
//!
//! // Analyze from file
//! let schema = analyzer.analyze_file(Path::new("schema.fbs"));
//!
//! // Analyze from string
//! let fbs = r#"
//!     table User {
//!         id: int;
//!         name: string;
//!     }
//!     root_type User;
//! "#;
//! let schema = analyzer.analyze_str(fbs, "user");
//!
//! // Access types
//! if let Ok(schema) = schema {
//!     for (name, _type_def) in &schema.types {
//!         println!("Found type: {}", name);
//!     }
//! }
//! ```
//!
//! # FlatBuffers Type Mappings
//!
//! | FlatBuffers | IR Type | Transport Class |
//! |-------------|---------|-----------------|
//! | `bool` | `Bool` | Concorde (zero-copy) |
//! | `byte`/`ubyte` | `I8`/`U8` | Concorde |
//! | `short`/`ushort` | `I16`/`U16` | Concorde |
//! | `int`/`uint` | `I32`/`U32` | Concorde |
//! | `long`/`ulong` | `I64`/`U64` | Concorde |
//! | `float` | `F32` | Concorde |
//! | `double` | `F64` | Concorde |
//! | `string` | `String` | Economy (heap) |
//! | `[T]` | `Vec<T>` | Economy (heap) |
//! | `struct` | Struct | Concorde (fixed layout, zero-copy) |
//! | `table` | Struct | Business/Economy (heap-allocated) |
//!
//! # Key Differences from Bebop
//!
//! - **Zero-copy structs**: FlatBuffers `struct` types have fixed layout and support true zero-copy access
//! - **Tables vs Structs**: Tables are heap-allocated (like Bebop structs), structs are stack-allocated
//! - **Root type**: FlatBuffers requires a `root_type` declaration
//! - **Unions**: FlatBuffers supports discriminated unions
//! - **Backwards compatibility**: Tables support optional fields and schema evolution

mod converter;
mod ephapax_bridge;
mod parser;

pub use converter::FlatBuffersConverter;
pub use ephapax_bridge::{analyze_transport_compatibility, TransportAnalysis};
pub use parser::FlatBuffersParser;

use protocol_squisher_ir::IrSchema;
use std::path::Path;
use thiserror::Error;

/// Errors that can occur during FlatBuffers analysis
#[derive(Debug, Error)]
pub enum AnalyzerError {
    /// Failed to parse FlatBuffers file
    #[error("FlatBuffers parse error: {0}")]
    ParseError(String),

    /// Invalid FlatBuffers structure
    #[error("Invalid FlatBuffers: {0}")]
    InvalidFlatBuffers(String),

    /// Unsupported FlatBuffers feature
    #[error("Unsupported feature: {0}")]
    UnsupportedFeature(String),

    /// IO error
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Main analyzer for FlatBuffers files
#[derive(Debug, Default)]
pub struct FlatBuffersAnalyzer {
    /// Parser for FlatBuffers files
    parser: FlatBuffersParser,
    /// Converter from parsed FlatBuffers to IR
    converter: FlatBuffersConverter,
}

impl FlatBuffersAnalyzer {
    /// Create a new FlatBuffers analyzer
    pub fn new() -> Self {
        Self::default()
    }

    /// Analyze a FlatBuffers file from a path
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_file(path)?;
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("schema");
        self.converter.convert(&parsed, name)
    }

    /// Analyze FlatBuffers content from a string
    pub fn analyze_str(&self, content: &str, name: &str) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_str(content)?;
        self.converter.convert(&parsed, name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_table() {
        let fbs = r#"
            table Person {
                name: string;
                age: int;
            }
        "#;

        let analyzer = FlatBuffersAnalyzer::new();
        let result = analyzer.analyze_str(fbs, "person");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Person"));
    }

    #[test]
    fn test_struct_zero_copy() {
        let fbs = r#"
            struct Vec3 {
                x: float;
                y: float;
                z: float;
            }
        "#;

        let analyzer = FlatBuffersAnalyzer::new();
        let result = analyzer.analyze_str(fbs, "vec3");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Vec3"));
    }

    #[test]
    fn test_enum() {
        let fbs = r#"
            enum Color: byte {
                Red = 0,
                Green = 1,
                Blue = 2
            }

            table Pixel {
                color: Color;
            }
        "#;

        let analyzer = FlatBuffersAnalyzer::new();
        let result = analyzer.analyze_str(fbs, "pixel");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("Color"));
        assert!(ir.types.contains_key("Pixel"));
    }

    #[test]
    fn test_vector_field() {
        let fbs = r#"
            table TaggedItem {
                name: string;
                tags: [string];
            }
        "#;

        let analyzer = FlatBuffersAnalyzer::new();
        let result = analyzer.analyze_str(fbs, "tagged");
        assert!(result.is_ok());
    }

    #[test]
    fn test_optional_field() {
        let fbs = r#"
            table Person {
                name: string (required);
                age: int;
            }
        "#;

        let analyzer = FlatBuffersAnalyzer::new();
        let result = analyzer.analyze_str(fbs, "person");
        assert!(result.is_ok());
    }

    #[test]
    fn test_deprecated_field() {
        let fbs = r#"
            table User {
                id: int;
                name: string;
                old_field: string (deprecated);
            }
        "#;

        let analyzer = FlatBuffersAnalyzer::new();
        let result = analyzer.analyze_str(fbs, "user");
        assert!(result.is_ok());
    }

    #[test]
    fn test_all_flatbuffers_types() {
        let fbs = r#"
            table AllTypes {
                bool_field: bool;
                byte_field: byte;
                ubyte_field: ubyte;
                short_field: short;
                ushort_field: ushort;
                int_field: int;
                uint_field: uint;
                long_field: long;
                ulong_field: ulong;
                float_field: float;
                double_field: double;
                string_field: string;
            }
        "#;

        let analyzer = FlatBuffersAnalyzer::new();
        let result = analyzer.analyze_str(fbs, "alltypes");
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
        assert_eq!(s.fields.len(), 12);
    }

    #[test]
    fn test_multiple_definitions() {
        let fbs = r#"
            table User {
                username: string;
                email: string;
            }

            table Post {
                title: string;
                content: string;
                author_username: string;
            }

            enum PostStatus: byte {
                Draft = 0,
                Published = 1,
                Archived = 2
            }
        "#;

        let analyzer = FlatBuffersAnalyzer::new();
        let result = analyzer.analyze_str(fbs, "schema");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert_eq!(ir.types.len(), 3);
        assert!(ir.types.contains_key("User"));
        assert!(ir.types.contains_key("Post"));
        assert!(ir.types.contains_key("PostStatus"));
    }

    #[test]
    fn test_nested_table() {
        let fbs = r#"
            table Address {
                street: string;
                city: string;
            }

            table Person {
                name: string;
                address: Address;
            }
        "#;

        let analyzer = FlatBuffersAnalyzer::new();
        let result = analyzer.analyze_str(fbs, "nested");
        assert!(result.is_ok());
    }

    #[test]
    fn test_union() {
        let fbs = r#"
            table Vec2 {
                x: float;
                y: float;
            }

            table Vec3 {
                x: float;
                y: float;
                z: float;
            }

            union Geometry {
                Vec2,
                Vec3
            }

            table Shape {
                geometry: Geometry;
            }
        "#;

        let analyzer = FlatBuffersAnalyzer::new();
        let result = analyzer.analyze_str(fbs, "union");
        assert!(result.is_ok());
    }
}
