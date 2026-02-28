// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! GraphQL SDL schema analyzer for Protocol Squisher.
//!
//! Parses GraphQL Schema Definition Language files and converts them to
//! the protocol-squisher IR for transport class analysis and adapter
//! generation.
//!
//! ## Type Mappings
//!
//! | GraphQL      | IR Type           | Notes                          |
//! |-------------|-------------------|--------------------------------|
//! | String      | String            | Direct mapping                 |
//! | Int         | I32               | GraphQL Int is 32-bit signed   |
//! | Float       | F64               | GraphQL Float is double        |
//! | Boolean     | Bool              | Direct mapping                 |
//! | ID          | String            | Serialized as string           |
//! | [Type]      | Vec<T>            | List type                      |
//! | Type!       | non-optional      | Non-null modifier              |
//! | enum        | EnumDef           | Variant enum                   |
//! | union       | UnionDef          | Tagged union                   |
//! | type        | StructDef         | Object type                    |
//! | input       | StructDef         | Input type (marked in metadata)|
//! | interface   | StructDef         | Interface (marked in metadata) |

pub mod converter;
pub mod ephapax_bridge;
pub mod parser;

use converter::GraphqlConverter;
pub use ephapax_bridge::{analyze_transport_compatibility, TransportAnalysis};
use parser::GraphqlParser;
use protocol_squisher_ir::IrSchema;
use std::path::Path;

/// Errors from the GraphQL analyzer.
#[derive(Debug, thiserror::Error)]
pub enum AnalyzerError {
    /// Failed to parse the GraphQL SDL.
    #[error("GraphQL parse error: {0}")]
    ParseError(String),

    /// Invalid or unsupported GraphQL construct.
    #[error("Invalid GraphQL schema: {0}")]
    InvalidGraphql(String),

    /// Unsupported GraphQL feature.
    #[error("Unsupported GraphQL feature: {0}")]
    UnsupportedFeature(String),

    /// IO error reading a file.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Main GraphQL schema analyzer.
#[derive(Debug, Default)]
pub struct GraphqlAnalyzer {
    parser: GraphqlParser,
    converter: GraphqlConverter,
}

impl GraphqlAnalyzer {
    pub fn new() -> Self {
        Self::default()
    }

    /// Analyze a GraphQL SDL file and produce an IR schema.
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_file(path)?;
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("graphql");
        self.converter.convert(&parsed, name)
    }

    /// Analyze a GraphQL SDL string and produce an IR schema.
    pub fn analyze_str(&self, content: &str, name: &str) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_str(content)?;
        self.converter.convert(&parsed, name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::TypeDef;

    fn analyzer() -> GraphqlAnalyzer {
        GraphqlAnalyzer::new()
    }

    #[test]
    fn simple_object_type() {
        let sdl = r#"
            type User {
                id: ID!
                name: String!
                age: Int
            }
        "#;
        let schema = analyzer().analyze_str(sdl, "test").unwrap();
        assert!(schema.types.contains_key("User"));
        match &schema.types["User"] {
            TypeDef::Struct(s) => {
                assert_eq!(s.fields.len(), 3);
                assert!(!s.fields[0].optional); // id: ID!
                assert!(!s.fields[1].optional); // name: String!
                assert!(s.fields[2].optional); // age: Int (nullable)
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn enum_type() {
        let sdl = r#"
            enum Status {
                ACTIVE
                INACTIVE
                PENDING
            }
        "#;
        let schema = analyzer().analyze_str(sdl, "test").unwrap();
        assert!(schema.types.contains_key("Status"));
        match &schema.types["Status"] {
            TypeDef::Enum(e) => {
                assert_eq!(e.variants.len(), 3);
                assert_eq!(e.variants[0].name, "ACTIVE");
            }
            other => panic!("Expected Enum, got {other:?}"),
        }
    }

    #[test]
    fn union_type() {
        let sdl = r#"
            type User {
                id: ID!
            }
            type Post {
                id: ID!
            }
            union SearchResult = User | Post
        "#;
        let schema = analyzer().analyze_str(sdl, "test").unwrap();
        assert!(schema.types.contains_key("SearchResult"));
        match &schema.types["SearchResult"] {
            TypeDef::Union(u) => {
                assert_eq!(u.variants.len(), 2);
            }
            other => panic!("Expected Union, got {other:?}"),
        }
    }

    #[test]
    fn input_type() {
        let sdl = r#"
            input CreateUserInput {
                name: String!
                email: String!
            }
        "#;
        let schema = analyzer().analyze_str(sdl, "test").unwrap();
        assert!(schema.types.contains_key("CreateUserInput"));
        match &schema.types["CreateUserInput"] {
            TypeDef::Struct(s) => {
                assert_eq!(s.fields.len(), 2);
                assert!(s.metadata.extra.get("graphql_kind").map(|v| v.as_str() == "input").unwrap_or(false));
            }
            other => panic!("Expected Struct for input, got {other:?}"),
        }
    }

    #[test]
    fn list_fields() {
        let sdl = r#"
            type Article {
                tags: [String!]!
                comments: [String]
            }
        "#;
        let schema = analyzer().analyze_str(sdl, "test").unwrap();
        match &schema.types["Article"] {
            TypeDef::Struct(s) => {
                assert!(!s.fields[0].optional); // tags: [String!]!
                assert!(s.fields[1].optional); // comments: [String]
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn interface_type() {
        let sdl = r#"
            interface Node {
                id: ID!
            }
        "#;
        let schema = analyzer().analyze_str(sdl, "test").unwrap();
        assert!(schema.types.contains_key("Node"));
        match &schema.types["Node"] {
            TypeDef::Struct(s) => {
                assert!(s.metadata.extra.get("graphql_kind").map(|v| v.as_str() == "interface").unwrap_or(false));
            }
            other => panic!("Expected Struct for interface, got {other:?}"),
        }
    }

    #[test]
    fn scalar_type() {
        let sdl = r#"
            scalar DateTime
        "#;
        let schema = analyzer().analyze_str(sdl, "test").unwrap();
        assert!(schema.types.contains_key("DateTime"));
        match &schema.types["DateTime"] {
            TypeDef::Alias(alias_def) => {
                assert_eq!(alias_def.name, "DateTime");
            }
            other => panic!("Expected Alias for scalar, got {other:?}"),
        }
    }

    #[test]
    fn multiple_types() {
        let sdl = r#"
            enum Role {
                ADMIN
                USER
            }

            type User {
                id: ID!
                name: String!
                role: Role!
            }

            type Post {
                id: ID!
                title: String!
                author: User!
            }
        "#;
        let schema = analyzer().analyze_str(sdl, "test").unwrap();
        assert_eq!(schema.types.len(), 3); // Role, User, Post
        assert!(schema.roots.contains(&"User".to_string()));
        assert!(schema.roots.contains(&"Post".to_string()));
    }

    #[test]
    fn comments_are_stripped() {
        let sdl = r#"
            # This is a comment
            type User {
                id: ID! # inline comment
                name: String!
            }
        "#;
        let schema = analyzer().analyze_str(sdl, "test").unwrap();
        match &schema.types["User"] {
            TypeDef::Struct(s) => assert_eq!(s.fields.len(), 2),
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn nested_type_references() {
        let sdl = r#"
            type Address {
                street: String!
                city: String!
            }

            type User {
                name: String!
                address: Address
            }
        "#;
        let schema = analyzer().analyze_str(sdl, "test").unwrap();
        match &schema.types["User"] {
            TypeDef::Struct(s) => {
                let addr_field = s.fields.iter().find(|f| f.name == "address").unwrap();
                assert!(addr_field.optional);
                assert!(matches!(addr_field.ty, protocol_squisher_ir::IrType::Reference(_)));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn transport_analysis_for_identical_types() {
        let result = analyze_transport_compatibility(
            &protocol_squisher_ir::IrType::Primitive(protocol_squisher_ir::PrimitiveType::I32),
            &protocol_squisher_ir::IrType::Primitive(protocol_squisher_ir::PrimitiveType::I32),
        )
        .unwrap();
        assert!(result.is_zero_copy());
    }

    #[test]
    fn graphql_schema_to_json_roundtrip() {
        let sdl = r#"
            type User {
                id: ID!
                name: String!
            }
        "#;
        let schema = analyzer().analyze_str(sdl, "test").unwrap();
        let json = schema.to_json().expect("serialize");
        let restored = IrSchema::from_json(&json).expect("deserialize");
        assert_eq!(restored.types.len(), schema.types.len());
    }
}
