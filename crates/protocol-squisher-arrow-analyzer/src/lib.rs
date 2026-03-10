// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Apache Arrow schema analyzer for Protocol Squisher — Phase 3 domain extractor.
//!
//! Analyzes Apache Arrow columnar memory layouts and converts them to the
//! protocol-squisher IR, enabling columnar data schemas to be treated as
//! universal data shapes alongside serialization formats and database schemas.
//!
//! This is the "memory layouts" domain extractor, completing Phase 3's
//! coverage of non-serialization data domains.
//!
//! ## Type Mappings
//!
//! | Arrow DataType          | IR Type         | Notes                       |
//! |-------------------------|-----------------|-----------------------------|
//! | Boolean                 | Bool            | 1-bit boolean               |
//! | Int8–Int64, UInt8–UInt64| I8–I64, U8–U64  | Width-preserving            |
//! | Float16/Float32         | F32             | Single precision            |
//! | Float64                 | F64             | Double precision            |
//! | Utf8 / LargeUtf8        | String          | Variable-length text        |
//! | Binary / LargeBinary    | Bytes           | Variable-length binary      |
//! | Date32 / Date64         | Date            | Calendar date               |
//! | Timestamp               | DateTime        | Date + time                 |
//! | Time32 / Time64         | Time            | Time of day                 |
//! | Duration                | Duration        | Time interval               |
//! | Decimal128 / Decimal256 | Decimal         | Arbitrary precision         |
//! | List / LargeList        | Vec<T>          | Variable-length sequence    |
//! | FixedSizeList(n)        | Array<T, n>     | Fixed-length array          |
//! | Map                     | Map<K, V>       | Key-value mapping           |
//!
//! ## Nullability
//!
//! Nullable Arrow fields become `Optional<T>` in the IR. Non-nullable
//! fields get `NonEmpty` constraints.

pub mod converter;
pub mod ephapax_bridge;
pub mod parser;

use converter::ArrowConverter;
pub use ephapax_bridge::{analyze_transport_compatibility, TransportAnalysis};
use parser::ArrowParser;
use protocol_squisher_ir::IrSchema;
use std::path::Path;

/// Errors from the Arrow analyzer.
#[derive(Debug, thiserror::Error)]
pub enum AnalyzerError {
    /// Failed to parse the Arrow schema.
    #[error("Arrow parse error: {0}")]
    ParseError(String),

    /// Invalid or unsupported Arrow construct.
    #[error("Invalid Arrow schema: {0}")]
    InvalidSchema(String),

    /// IO error reading a file.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Main Apache Arrow schema analyzer.
#[derive(Debug, Default)]
pub struct ArrowAnalyzer {
    parser: ArrowParser,
    converter: ArrowConverter,
}

impl ArrowAnalyzer {
    /// Create a new Arrow analyzer.
    pub fn new() -> Self {
        Self::default()
    }

    /// Analyze an Arrow schema JSON file and produce an IR schema.
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_file(path)?;
        self.converter.convert(&parsed)
    }

    /// Analyze an Arrow schema JSON string and produce an IR schema.
    pub fn analyze_str(&self, content: &str, name: &str) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_str(content, name)?;
        self.converter.convert(&parsed)
    }

    /// Analyze directly from an `arrow_schema::Schema` object.
    pub fn analyze_schema(
        &self,
        schema: &arrow_schema::Schema,
        name: &str,
    ) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.from_arrow_schema(schema, name);
        self.converter.convert(&parsed)
    }
}

impl protocol_squisher_ir::SchemaAnalyzer for ArrowAnalyzer {
    type Error = AnalyzerError;

    fn analyzer_name(&self) -> &str {
        "arrow"
    }

    fn supported_extensions(&self) -> &[&str] {
        &["arrow.json", "arrow-schema.json"]
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
    use arrow_schema::{DataType, Field, Schema, TimeUnit};
    use protocol_squisher_ir::{IrType, PrimitiveType, SchemaAnalyzer, TypeDef};

    fn analyzer() -> ArrowAnalyzer {
        ArrowAnalyzer::new()
    }

    fn schema_json(fields: Vec<Field>) -> String {
        serde_json::to_string(&Schema::new(fields)).unwrap()
    }

    #[test]
    fn simple_schema() {
        let json = schema_json(vec![
            Field::new("id", DataType::Int32, false),
            Field::new("name", DataType::Utf8, false),
            Field::new("email", DataType::Utf8, true),
            Field::new("active", DataType::Boolean, false),
        ]);
        let schema = analyzer().analyze_str(&json, "users").unwrap();
        assert!(schema.types.contains_key("users"));
        match &schema.types["users"] {
            TypeDef::Struct(s) => {
                assert_eq!(s.fields.len(), 4);
                assert!(!s.fields[0].optional); // id non-nullable
                assert!(!s.fields[1].optional); // name non-nullable
                assert!(s.fields[2].optional); // email nullable
                assert!(!s.fields[3].optional); // active non-nullable
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn columnar_analytics_schema() {
        let json = schema_json(vec![
            Field::new("event_id", DataType::Int64, false),
            Field::new("timestamp", DataType::Timestamp(TimeUnit::Microsecond, None), false),
            Field::new("value", DataType::Float64, false),
            Field::new("tags", DataType::List(Box::new(Field::new("item", DataType::Utf8, false)).into()), true),
        ]);
        let schema = analyzer().analyze_str(&json, "events").unwrap();
        assert_eq!(schema.source_format, "arrow-ipc");
        match &schema.types["events"] {
            TypeDef::Struct(s) => {
                assert!(matches!(s.fields[0].ty, IrType::Primitive(PrimitiveType::I64)));
                assert!(matches!(s.fields[1].ty, IrType::Primitive(PrimitiveType::DateTime)));
                assert!(matches!(s.fields[2].ty, IrType::Primitive(PrimitiveType::F64)));
                // tags is nullable → Optional<Vec<String>>
                assert!(s.fields[3].optional);
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn schema_analyzer_trait() {
        let a = ArrowAnalyzer::new();
        assert_eq!(a.analyzer_name(), "arrow");
        assert_eq!(a.supported_extensions(), &["arrow.json", "arrow-schema.json"]);

        let json = schema_json(vec![Field::new("x", DataType::Int32, false)]);
        let ir = SchemaAnalyzer::analyze_str(&a, &json, "ping").unwrap();
        assert!(ir.types.contains_key("ping"));
    }

    #[test]
    fn schema_json_roundtrip() {
        let json = schema_json(vec![
            Field::new("id", DataType::Int32, false),
            Field::new("name", DataType::Utf8, false),
        ]);
        let schema = analyzer().analyze_str(&json, "roundtrip").unwrap();
        let json_out = schema.to_json().expect("serialize");
        let restored = IrSchema::from_json(&json_out).expect("deserialize");
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
    fn direct_schema_analysis() {
        let arrow = Schema::new(vec![
            Field::new("a", DataType::Float32, false),
            Field::new("b", DataType::Float64, false),
        ]);
        let ir = analyzer().analyze_schema(&arrow, "direct").unwrap();
        assert!(ir.types.contains_key("direct"));
        match &ir.types["direct"] {
            TypeDef::Struct(s) => {
                assert!(matches!(s.fields[0].ty, IrType::Primitive(PrimitiveType::F32)));
                assert!(matches!(s.fields[1].ty, IrType::Primitive(PrimitiveType::F64)));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn fixed_size_list_and_map() {
        let json = schema_json(vec![
            Field::new(
                "coords",
                DataType::FixedSizeList(Box::new(Field::new("item", DataType::Float64, false)).into(), 3),
                false,
            ),
            Field::new(
                "meta",
                DataType::Map(
                    Box::new(Field::new(
                        "entries",
                        DataType::Struct(
                            vec![
                                Field::new("key", DataType::Utf8, false),
                                Field::new("value", DataType::Utf8, true),
                            ].into(),
                        ),
                        false,
                    )).into(),
                    false,
                ),
                false,
            ),
        ]);
        let schema = analyzer().analyze_str(&json, "complex").unwrap();
        match &schema.types["complex"] {
            TypeDef::Struct(s) => {
                assert!(matches!(
                    s.fields[0].ty,
                    IrType::Container(protocol_squisher_ir::ContainerType::Array(_, 3))
                ));
                assert!(matches!(
                    s.fields[1].ty,
                    IrType::Container(protocol_squisher_ir::ContainerType::Map(_, _))
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn shape_extraction_from_arrow() {
        // End-to-end: Arrow → IR → Shape
        let json = schema_json(vec![
            Field::new("id", DataType::Int32, false),
            Field::new("name", DataType::Utf8, false),
            Field::new("price", DataType::Float32, false),
            Field::new("description", DataType::Utf8, true),
        ]);
        let schema = analyzer().analyze_str(&json, "products").unwrap();
        let shapes = shape_ir::extract::extract_schema(&schema);
        assert!(shapes.shapes.contains_key("products"));

        let product_shape = &shapes.shapes["products"];
        let labels = product_shape.field_labels();
        assert_eq!(labels.len(), 4);
        assert_eq!(labels[0].name, "id");
        assert_eq!(labels[1].name, "name");
    }

    #[test]
    fn cross_domain_arrow_vs_sql_shape() {
        // Arrow columnar layout vs SQL DDL — the Phase 3 cross-domain promise
        let json = schema_json(vec![
            Field::new("id", DataType::Int32, false),
            Field::new("name", DataType::Utf8, false),
            Field::new("email", DataType::Utf8, true),
        ]);
        let arrow_schema = analyzer().analyze_str(&json, "users").unwrap();
        let arrow_shapes = shape_ir::extract::extract_schema(&arrow_schema);
        let arrow_shape = &arrow_shapes.shapes["users"];

        // Build equivalent shape manually (as if from SQL)
        let sql_shape = shape_ir::Shape::struct_from(vec![
            ("id", shape_ir::Shape::Atom(shape_ir::AtomKind::I32)),
            ("name", shape_ir::Shape::Atom(shape_ir::AtomKind::String)),
            (
                "email",
                shape_ir::Shape::optional(shape_ir::Shape::Atom(shape_ir::AtomKind::String)),
            ),
        ]);

        // Compare across domains — should be Concorde (isomorphic!)
        let morphism = shape_ir::compare::compare(arrow_shape, &sql_shape);
        assert_eq!(
            morphism.transport_class,
            shape_ir::TransportClass::Concorde,
            "Arrow and SQL with same structure should be isomorphic"
        );
    }

    #[test]
    fn cross_domain_arrow_widening() {
        // Arrow Int32 vs target Int64 — should be Business (safe widening)
        let json = schema_json(vec![
            Field::new("value", DataType::Int32, false),
        ]);
        let arrow_schema = analyzer().analyze_str(&json, "narrow").unwrap();
        let arrow_shapes = shape_ir::extract::extract_schema(&arrow_schema);
        let arrow_shape = &arrow_shapes.shapes["narrow"];

        let wide_shape = shape_ir::Shape::struct_from(vec![
            ("value", shape_ir::Shape::Atom(shape_ir::AtomKind::I64)),
        ]);

        let morphism = shape_ir::compare::compare(arrow_shape, &wide_shape);
        assert_eq!(
            morphism.transport_class,
            shape_ir::TransportClass::Business,
            "Arrow I32 → I64 should be Business (safe widening)"
        );
    }
}
