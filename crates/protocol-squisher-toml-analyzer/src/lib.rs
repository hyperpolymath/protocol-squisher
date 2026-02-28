// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! TOML schema analyzer for Protocol Squisher.
//!
//! Infers structural types from TOML documents and converts them to
//! the protocol-squisher IR for transport class analysis.
//!
//! ## Type Inference
//!
//! | TOML Value      | IR Type           | Notes                         |
//! |----------------|-------------------|-------------------------------|
//! | String         | String            | Direct mapping                |
//! | Integer        | I64               | TOML integers are 64-bit      |
//! | Float          | F64               | TOML floats are 64-bit        |
//! | Boolean        | Bool              | Direct mapping                |
//! | DateTime       | DateTime          | ISO 8601 format               |
//! | Table          | StructDef         | Named struct from table keys  |
//! | Array          | Vec<T>            | Inferred from first element   |
//! | Array of Tables| Vec<StructDef>    | Nested struct array           |

pub mod converter;
pub mod ephapax_bridge;
pub mod parser;

use converter::TomlConverter;
pub use ephapax_bridge::{analyze_transport_compatibility, TransportAnalysis};
use parser::TomlParser;
use protocol_squisher_ir::IrSchema;
use std::path::Path;

/// Errors from the TOML analyzer.
#[derive(Debug, thiserror::Error)]
pub enum AnalyzerError {
    /// Failed to parse the TOML document.
    #[error("TOML parse error: {0}")]
    ParseError(String),

    /// Invalid TOML structure.
    #[error("Invalid TOML structure: {0}")]
    InvalidToml(String),

    /// IO error reading a file.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Main TOML schema analyzer.
#[derive(Debug, Default)]
pub struct TomlAnalyzer {
    parser: TomlParser,
    converter: TomlConverter,
}

impl TomlAnalyzer {
    pub fn new() -> Self {
        Self::default()
    }

    /// Analyze a TOML file and produce an IR schema.
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_file(path)?;
        self.converter.convert(&parsed, &parsed.name)
    }

    /// Analyze a TOML string and produce an IR schema.
    pub fn analyze_str(&self, content: &str, name: &str) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_str(content, name)?;
        self.converter.convert(&parsed, name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{IrType, PrimitiveType, TypeDef};

    fn analyzer() -> TomlAnalyzer {
        TomlAnalyzer::new()
    }

    #[test]
    fn basic_table() {
        let toml = r#"
            name = "protocol-squisher"
            version = "1.0.0"
            debug = true
            port = 8080
        "#;
        let schema = analyzer().analyze_str(toml, "config").unwrap();
        assert!(schema.types.contains_key("Config"));
        match &schema.types["Config"] {
            TypeDef::Struct(s) => {
                assert_eq!(s.fields.len(), 4);
                let name_field = s.fields.iter().find(|f| f.name == "name").unwrap();
                assert!(matches!(name_field.ty, IrType::Primitive(PrimitiveType::String)));
                let port_field = s.fields.iter().find(|f| f.name == "port").unwrap();
                assert!(matches!(port_field.ty, IrType::Primitive(PrimitiveType::I64)));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn nested_table() {
        let toml = r#"
            [server]
            host = "localhost"
            port = 8080
        "#;
        let schema = analyzer().analyze_str(toml, "app").unwrap();
        assert!(schema.types.contains_key("App"));
        assert!(schema.types.contains_key("App_Server"));
        match &schema.types["App_Server"] {
            TypeDef::Struct(s) => {
                assert_eq!(s.fields.len(), 2);
            }
            other => panic!("Expected Struct for server, got {other:?}"),
        }
    }

    #[test]
    fn arrays() {
        let toml = r#"
            tags = ["web", "api", "rust"]
        "#;
        let schema = analyzer().analyze_str(toml, "test").unwrap();
        match &schema.types["Test"] {
            TypeDef::Struct(s) => {
                let tags_field = s.fields.iter().find(|f| f.name == "tags").unwrap();
                assert!(matches!(
                    tags_field.ty,
                    IrType::Container(protocol_squisher_ir::ContainerType::Vec(_))
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn array_of_tables() {
        let toml = r#"
            [[servers]]
            host = "alpha"
            port = 8080

            [[servers]]
            host = "beta"
            port = 9090
        "#;
        let schema = analyzer().analyze_str(toml, "infra").unwrap();
        match &schema.types["Infra"] {
            TypeDef::Struct(s) => {
                let servers_field = s.fields.iter().find(|f| f.name == "servers").unwrap();
                assert!(matches!(
                    servers_field.ty,
                    IrType::Container(protocol_squisher_ir::ContainerType::Vec(_))
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn mixed_types() {
        let toml = r#"
            title = "Example"
            enabled = true
            threshold = 0.75
            max_retries = 3
        "#;
        let schema = analyzer().analyze_str(toml, "settings").unwrap();
        match &schema.types["Settings"] {
            TypeDef::Struct(s) => {
                assert_eq!(s.fields.len(), 4);
                let bool_field = s.fields.iter().find(|f| f.name == "enabled").unwrap();
                assert!(matches!(bool_field.ty, IrType::Primitive(PrimitiveType::Bool)));
                let float_field = s.fields.iter().find(|f| f.name == "threshold").unwrap();
                assert!(matches!(float_field.ty, IrType::Primitive(PrimitiveType::F64)));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn inline_table() {
        let toml = r#"
            point = { x = 1, y = 2 }
        "#;
        let schema = analyzer().analyze_str(toml, "geo").unwrap();
        assert!(schema.types.contains_key("Geo_Point"));
    }

    #[test]
    fn dotted_keys() {
        let toml = r#"
            [database]
            host = "db.example.com"
            port = 5432
            name = "mydb"
        "#;
        let schema = analyzer().analyze_str(toml, "config").unwrap();
        assert!(schema.types.contains_key("Config_Database"));
        match &schema.types["Config_Database"] {
            TypeDef::Struct(s) => {
                assert_eq!(s.fields.len(), 3);
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn empty_array_defaults_to_string_vec() {
        let toml = r#"
            tags = []
        "#;
        let schema = analyzer().analyze_str(toml, "empty").unwrap();
        match &schema.types["Empty"] {
            TypeDef::Struct(s) => {
                let field = &s.fields[0];
                match &field.ty {
                    IrType::Container(protocol_squisher_ir::ContainerType::Vec(inner)) => {
                        assert!(matches!(**inner, IrType::Primitive(PrimitiveType::String)));
                    }
                    other => panic!("Expected Vec, got {other:?}"),
                }
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn schema_json_roundtrip() {
        let toml = r#"
            name = "test"
            count = 42
        "#;
        let schema = analyzer().analyze_str(toml, "roundtrip").unwrap();
        let json = schema.to_json().expect("serialize");
        let restored = IrSchema::from_json(&json).expect("deserialize");
        assert_eq!(restored.types.len(), schema.types.len());
    }

    #[test]
    fn transport_analysis() {
        let result = analyze_transport_compatibility(
            &IrType::Primitive(PrimitiveType::I64),
            &IrType::Primitive(PrimitiveType::I64),
        )
        .unwrap();
        assert!(result.is_zero_copy());
    }
}
