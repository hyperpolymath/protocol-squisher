// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! SQL DDL schema analyzer for Protocol Squisher — Phase 3 domain extractor.
//!
//! Parses SQL CREATE TABLE statements and converts them to the
//! protocol-squisher IR, enabling database schemas to be treated as
//! universal data shapes alongside serialization formats.
//!
//! This is the first non-serialization domain extractor, bridging
//! the gap between database schemas and the shape algebra.
//!
//! ## Type Mappings
//!
//! | SQL Type               | IR Type       | Notes                      |
//! |------------------------|---------------|----------------------------|
//! | INTEGER, INT           | I32           | 32-bit signed integer      |
//! | BIGINT, BIGSERIAL      | I64           | 64-bit signed integer      |
//! | SMALLINT, TINYINT      | I16           | 16-bit signed integer      |
//! | REAL, FLOAT            | F32           | Single precision           |
//! | DOUBLE PRECISION       | F64           | Double precision           |
//! | DECIMAL, NUMERIC       | Decimal       | Arbitrary precision        |
//! | BOOLEAN                | Bool          | Boolean                    |
//! | TEXT, VARCHAR, CHAR     | String        | Text types                 |
//! | BYTEA, BLOB, BINARY    | Bytes         | Binary data                |
//! | DATE                   | Date          | Calendar date              |
//! | TIMESTAMP, TIMESTAMPTZ | DateTime      | Date + time                |
//! | UUID                   | Uuid          | 128-bit identifier         |
//! | JSON, JSONB            | Special(Json) | JSON document              |
//!
//! ## Nullability
//!
//! Columns without NOT NULL become `Optional<T>` in the IR. Primary key
//! columns are always non-optional regardless of NOT NULL declaration.

#![forbid(unsafe_code)]
pub mod converter;
pub mod ephapax_bridge;
pub mod parser;

use converter::SqlConverter;
pub use ephapax_bridge::{analyze_transport_compatibility, TransportAnalysis};
use parser::SqlParser;
use protocol_squisher_ir::IrSchema;
use std::path::Path;

/// Errors from the SQL analyzer.
#[derive(Debug, thiserror::Error)]
pub enum AnalyzerError {
    /// Failed to parse the SQL DDL.
    #[error("SQL parse error: {0}")]
    ParseError(String),

    /// Invalid or unsupported SQL construct.
    #[error("Invalid SQL schema: {0}")]
    InvalidSql(String),

    /// IO error reading a file.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Main SQL DDL schema analyzer.
#[derive(Debug, Default)]
pub struct SqlAnalyzer {
    parser: SqlParser,
    converter: SqlConverter,
}

impl SqlAnalyzer {
    /// Create a new SQL analyzer.
    pub fn new() -> Self {
        Self::default()
    }

    /// Analyze a SQL file and produce an IR schema.
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_file(path)?;
        self.converter.convert(&parsed)
    }

    /// Analyze a SQL string and produce an IR schema.
    pub fn analyze_str(&self, content: &str, name: &str) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_str(content, name)?;
        self.converter.convert(&parsed)
    }
}

impl protocol_squisher_ir::SchemaAnalyzer for SqlAnalyzer {
    type Error = AnalyzerError;

    fn analyzer_name(&self) -> &str {
        "sql"
    }

    fn supported_extensions(&self) -> &[&str] {
        &["sql", "ddl"]
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
    use protocol_squisher_ir::{IrType, PrimitiveType, SchemaAnalyzer, TypeDef};

    fn analyzer() -> SqlAnalyzer {
        SqlAnalyzer::new()
    }

    #[test]
    fn simple_table() {
        let sql = "CREATE TABLE users (
            id INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            email TEXT,
            active BOOLEAN NOT NULL DEFAULT TRUE
        );";
        let schema = analyzer().analyze_str(sql, "test").unwrap();
        assert!(schema.types.contains_key("users"));
        match &schema.types["users"] {
            TypeDef::Struct(s) => {
                assert_eq!(s.fields.len(), 4);
                assert!(!s.fields[0].optional); // id is PK
                assert!(!s.fields[1].optional); // name NOT NULL
                assert!(s.fields[2].optional); // email nullable
                assert!(!s.fields[3].optional); // active NOT NULL
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn postgres_schema() {
        let sql = "CREATE TABLE events (
            id BIGSERIAL PRIMARY KEY,
            payload JSONB NOT NULL,
            created_at TIMESTAMPTZ NOT NULL DEFAULT now(),
            tags TEXT[] NOT NULL
        );";
        let schema = analyzer().analyze_str(sql, "events_db").unwrap();
        assert_eq!(schema.source_format, "sql-postgresql");
        match &schema.types["events"] {
            TypeDef::Struct(s) => {
                assert!(matches!(
                    s.fields[0].ty,
                    IrType::Primitive(PrimitiveType::I64)
                ));
                assert!(matches!(s.fields[1].ty, IrType::Special(_)));
                assert!(matches!(
                    s.fields[2].ty,
                    IrType::Primitive(PrimitiveType::DateTime)
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn multi_table_schema() {
        let sql = "
            CREATE TABLE users (
                id INTEGER PRIMARY KEY,
                name TEXT NOT NULL
            );
            CREATE TABLE posts (
                id INTEGER PRIMARY KEY,
                user_id INTEGER NOT NULL,
                title TEXT NOT NULL,
                body TEXT NOT NULL,
                FOREIGN KEY (user_id) REFERENCES users(id)
            );
        ";
        let schema = analyzer().analyze_str(sql, "blog").unwrap();
        assert_eq!(schema.types.len(), 2);
        assert!(schema.types.contains_key("users"));
        assert!(schema.types.contains_key("posts"));
        // Foreign key metadata should be present
        match &schema.types["posts"] {
            TypeDef::Struct(s) => {
                assert!(s.metadata.extra.get("foreign_keys").is_some());
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn schema_analyzer_trait() {
        let a = SqlAnalyzer::new();
        assert_eq!(a.analyzer_name(), "sql");
        assert_eq!(a.supported_extensions(), &["sql", "ddl"]);

        let sql = "CREATE TABLE ping (msg TEXT NOT NULL);";
        let ir = SchemaAnalyzer::analyze_str(&a, sql, "ping").unwrap();
        assert!(ir.types.contains_key("ping"));
    }

    #[test]
    fn schema_json_roundtrip() {
        let sql = "CREATE TABLE t (id INTEGER PRIMARY KEY, name TEXT NOT NULL);";
        let schema = analyzer().analyze_str(sql, "roundtrip").unwrap();
        let json = schema.to_json().expect("serialize");
        let restored = IrSchema::from_json(&json).expect("deserialize");
        assert_eq!(restored.types.len(), schema.types.len());
    }

    #[test]
    fn transport_analysis_identical() {
        let result = analyze_transport_compatibility(
            &IrType::Primitive(PrimitiveType::I32),
            &IrType::Primitive(PrimitiveType::I32),
        )
        .unwrap();
        assert!(result.is_zero_copy());
    }

    #[test]
    fn shape_extraction_from_sql() {
        // End-to-end: SQL → IR → Shape
        let sql = "CREATE TABLE products (
            id INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            price REAL NOT NULL,
            description TEXT
        );";
        let schema = analyzer().analyze_str(sql, "shop").unwrap();
        let shapes = shape_ir::extract::extract_schema(&schema);
        assert!(shapes.shapes.contains_key("products"));

        // Verify shape properties
        let product_shape = &shapes.shapes["products"];
        let labels = product_shape.field_labels();
        assert_eq!(labels.len(), 4);
        assert_eq!(labels[0].name, "id");
        assert_eq!(labels[1].name, "name");
    }

    #[test]
    fn cross_domain_comparison() {
        // SQL schema vs Protobuf-like struct — this is the Phase 3 killer feature
        let sql = "CREATE TABLE users (
            id INTEGER NOT NULL,
            name TEXT NOT NULL,
            email TEXT
        );";
        let sql_schema = analyzer().analyze_str(sql, "sql_users").unwrap();
        let sql_shapes = shape_ir::extract::extract_schema(&sql_schema);
        let sql_shape = &sql_shapes.shapes["users"];

        // Build an equivalent shape manually (as if from Protobuf)
        let proto_shape = shape_ir::Shape::struct_from(vec![
            ("id", shape_ir::Shape::Atom(shape_ir::AtomKind::I32)),
            ("name", shape_ir::Shape::Atom(shape_ir::AtomKind::String)),
            (
                "email",
                shape_ir::Shape::optional(shape_ir::Shape::Atom(shape_ir::AtomKind::String)),
            ),
        ]);

        // Compare across domains — should be Concorde (isomorphic!)
        let morphism = shape_ir::compare::compare(sql_shape, &proto_shape);
        assert_eq!(
            morphism.transport_class,
            shape_ir::TransportClass::Concorde,
            "SQL and Protobuf with same structure should be isomorphic"
        );
    }
}
