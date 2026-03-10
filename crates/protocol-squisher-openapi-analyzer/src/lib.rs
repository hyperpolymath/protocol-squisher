// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! OpenAPI/Swagger schema analyzer for Protocol Squisher — Phase 3 domain extractor.
//!
//! Parses OpenAPI 3.x and Swagger 2.0 specifications and converts their
//! `components.schemas` (or `definitions`) to the protocol-squisher IR,
//! enabling API contracts to be treated as universal data shapes alongside
//! serialization formats and database schemas.
//!
//! This is the second non-serialization domain extractor, bridging
//! API contracts into the shape algebra.
//!
//! ## Type Mappings
//!
//! | OpenAPI Type     | Format    | IR Type       | Notes                        |
//! |------------------|-----------|---------------|------------------------------|
//! | string           |           | String        | Default text                 |
//! | string           | date-time | DateTime      | ISO 8601 datetime            |
//! | string           | uuid      | Uuid          | 128-bit identifier           |
//! | integer          |           | I32           | Default integer              |
//! | integer          | int64     | I64           | 64-bit integer               |
//! | number           |           | F64           | Default number               |
//! | number           | float     | F32           | Single precision             |
//! | boolean          |           | Bool          | Boolean                      |
//! | array            |           | Vec<T>        | Typed array                  |
//! | object           |           | Struct        | Named properties             |
//! | enum             |           | Enum          | String enum                  |
//!
//! ## Requiredness
//!
//! Properties not listed in `required` become `Optional<T>` in the IR.

pub mod converter;
pub mod ephapax_bridge;
pub mod parser;

use converter::OpenApiConverter;
pub use ephapax_bridge::{analyze_transport_compatibility, TransportAnalysis};
use parser::OpenApiParser;
use protocol_squisher_ir::IrSchema;
use std::path::Path;

/// Errors from the OpenAPI analyzer.
#[derive(Debug, thiserror::Error)]
pub enum AnalyzerError {
    /// Failed to parse the OpenAPI specification.
    #[error("OpenAPI parse error: {0}")]
    ParseError(String),

    /// Invalid or unsupported OpenAPI construct.
    #[error("Invalid OpenAPI schema: {0}")]
    InvalidSchema(String),

    /// IO error reading a file.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Main OpenAPI/Swagger schema analyzer.
#[derive(Debug, Default)]
pub struct OpenApiAnalyzer {
    parser: OpenApiParser,
    converter: OpenApiConverter,
}

impl OpenApiAnalyzer {
    /// Create a new OpenAPI analyzer.
    pub fn new() -> Self {
        Self::default()
    }

    /// Analyze an OpenAPI file (JSON or YAML) and produce an IR schema.
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_file(path)?;
        self.converter.convert(&parsed)
    }

    /// Analyze an OpenAPI string and produce an IR schema.
    pub fn analyze_str(&self, content: &str, name: &str) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_str(content, name)?;
        self.converter.convert(&parsed)
    }
}

impl protocol_squisher_ir::SchemaAnalyzer for OpenApiAnalyzer {
    type Error = AnalyzerError;

    fn analyzer_name(&self) -> &str {
        "openapi"
    }

    fn supported_extensions(&self) -> &[&str] {
        &["openapi.json", "openapi.yaml", "swagger.json"]
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

    fn analyzer() -> OpenApiAnalyzer {
        OpenApiAnalyzer::new()
    }

    fn petstore_json() -> String {
        serde_json::json!({
            "openapi": "3.0.3",
            "info": {"title": "Petstore", "version": "1.0"},
            "paths": {},
            "components": {
                "schemas": {
                    "Pet": {
                        "type": "object",
                        "required": ["id", "name"],
                        "properties": {
                            "id": {"type": "integer", "format": "int64"},
                            "name": {"type": "string"},
                            "tag": {"type": "string"}
                        }
                    },
                    "Pets": {
                        "type": "array",
                        "items": {"$ref": "#/components/schemas/Pet"}
                    },
                    "Error": {
                        "type": "object",
                        "required": ["code", "message"],
                        "properties": {
                            "code": {"type": "integer"},
                            "message": {"type": "string"}
                        }
                    }
                }
            }
        })
        .to_string()
    }

    #[test]
    fn petstore_basic() {
        let schema = analyzer().analyze_str(&petstore_json(), "petstore").unwrap();
        assert_eq!(schema.types.len(), 3);
        assert!(schema.types.contains_key("Pet"));
        assert!(schema.types.contains_key("Pets"));
        assert!(schema.types.contains_key("Error"));
    }

    #[test]
    fn petstore_pet_fields() {
        let schema = analyzer().analyze_str(&petstore_json(), "petstore").unwrap();
        match &schema.types["Pet"] {
            TypeDef::Struct(s) => {
                assert_eq!(s.fields.len(), 3);
                // id: required int64
                assert!(!s.fields[0].optional);
                assert!(matches!(
                    s.fields[0].ty,
                    IrType::Primitive(PrimitiveType::I64)
                ));
                // name: required string
                assert!(!s.fields[1].optional);
                // tag: optional string
                assert!(s.fields[2].optional);
                assert!(matches!(
                    s.fields[2].ty,
                    IrType::Container(protocol_squisher_ir::ContainerType::Option(_))
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn petstore_list_alias() {
        let schema = analyzer().analyze_str(&petstore_json(), "petstore").unwrap();
        match &schema.types["Pets"] {
            TypeDef::Alias(a) => {
                assert!(matches!(
                    a.target,
                    IrType::Container(protocol_squisher_ir::ContainerType::Vec(_))
                ));
            }
            other => panic!("Expected Alias, got {other:?}"),
        }
    }

    #[test]
    fn format_hints_datetime_uuid() {
        let spec = r#"{
            "openapi": "3.0.3",
            "info": {"title": "Events", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "Event": {
                    "type": "object",
                    "required": ["id", "timestamp", "uid"],
                    "properties": {
                        "id": {"type": "integer"},
                        "timestamp": {"type": "string", "format": "date-time"},
                        "uid": {"type": "string", "format": "uuid"}
                    }
                }
            }}
        }"#;
        let schema = analyzer().analyze_str(spec, "events").unwrap();
        match &schema.types["Event"] {
            TypeDef::Struct(s) => {
                assert!(matches!(
                    s.fields[1].ty,
                    IrType::Primitive(PrimitiveType::DateTime)
                ));
                assert!(matches!(
                    s.fields[2].ty,
                    IrType::Primitive(PrimitiveType::Uuid)
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn enum_type() {
        let spec = r#"{
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "Color": {
                    "type": "string",
                    "enum": ["red", "green", "blue"]
                }
            }}
        }"#;
        let schema = analyzer().analyze_str(spec, "colors").unwrap();
        match &schema.types["Color"] {
            TypeDef::Enum(e) => {
                assert_eq!(e.variants.len(), 3);
            }
            other => panic!("Expected Enum, got {other:?}"),
        }
    }

    #[test]
    fn oneof_union() {
        let spec = serde_json::json!({
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "Shape": {
                    "oneOf": [
                        {"$ref": "#/components/schemas/Circle"},
                        {"$ref": "#/components/schemas/Rect"}
                    ]
                }
            }}
        })
        .to_string();
        let schema = analyzer().analyze_str(&spec, "shapes").unwrap();
        match &schema.types["Shape"] {
            TypeDef::Union(u) => {
                assert_eq!(u.variants.len(), 2);
                assert!(matches!(&u.variants[0], IrType::Reference(name) if name == "Circle"));
            }
            other => panic!("Expected Union, got {other:?}"),
        }
    }

    #[test]
    fn schema_analyzer_trait() {
        let a = OpenApiAnalyzer::new();
        assert_eq!(a.analyzer_name(), "openapi");

        let spec = r#"{
            "openapi": "3.0.3",
            "info": {"title": "Ping", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "Ping": {
                    "type": "object",
                    "required": ["msg"],
                    "properties": {"msg": {"type": "string"}}
                }
            }}
        }"#;
        let ir = SchemaAnalyzer::analyze_str(&a, spec, "ping").unwrap();
        assert!(ir.types.contains_key("Ping"));
    }

    #[test]
    fn schema_json_roundtrip() {
        let schema = analyzer().analyze_str(&petstore_json(), "roundtrip").unwrap();
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
    fn shape_extraction_from_openapi() {
        // End-to-end: OpenAPI → IR → Shape
        let spec = r#"{
            "openapi": "3.0.3",
            "info": {"title": "Shop", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "Product": {
                    "type": "object",
                    "required": ["id", "name", "price"],
                    "properties": {
                        "id": {"type": "integer"},
                        "name": {"type": "string"},
                        "price": {"type": "number", "format": "float"},
                        "description": {"type": "string"}
                    }
                }
            }}
        }"#;
        let schema = analyzer().analyze_str(spec, "shop").unwrap();
        let shapes = shape_ir::extract::extract_schema(&schema);
        assert!(shapes.shapes.contains_key("Product"));

        let product_shape = &shapes.shapes["Product"];
        let labels = product_shape.field_labels();
        assert_eq!(labels.len(), 4);
        assert_eq!(labels[0].name, "id");
    }

    #[test]
    fn cross_domain_openapi_vs_sql() {
        // OpenAPI schema vs SQL schema — the Phase 3 killer feature
        let openapi_spec = r#"{
            "openapi": "3.0.3",
            "info": {"title": "Users API", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "User": {
                    "type": "object",
                    "required": ["id", "name"],
                    "properties": {
                        "id": {"type": "integer"},
                        "name": {"type": "string"},
                        "email": {"type": "string"}
                    }
                }
            }}
        }"#;

        let openapi_schema = analyzer().analyze_str(openapi_spec, "api").unwrap();
        let openapi_shapes = shape_ir::extract::extract_schema(&openapi_schema);
        let openapi_shape = &openapi_shapes.shapes["User"];

        // Build the same shape as if from a SQL table
        let sql_shape = shape_ir::Shape::struct_from(vec![
            ("id", shape_ir::Shape::Atom(shape_ir::AtomKind::I32)),
            ("name", shape_ir::Shape::Atom(shape_ir::AtomKind::String)),
            (
                "email",
                shape_ir::Shape::optional(shape_ir::Shape::Atom(shape_ir::AtomKind::String)),
            ),
        ]);

        // Compare across domains — should be Concorde (isomorphic!)
        let morphism = shape_ir::compare::compare(openapi_shape, &sql_shape);
        assert_eq!(
            morphism.transport_class,
            shape_ir::TransportClass::Concorde,
            "OpenAPI and SQL with same structure should be isomorphic"
        );
    }

    #[test]
    fn yaml_input() {
        let yaml = r#"
openapi: "3.0.3"
info:
  title: YAML API
  version: "1.0"
paths: {}
components:
  schemas:
    Item:
      type: object
      required:
        - name
      properties:
        name:
          type: string
        count:
          type: integer
"#;
        let schema = analyzer().analyze_str(yaml, "yaml_test").unwrap();
        assert!(schema.types.contains_key("Item"));
        match &schema.types["Item"] {
            TypeDef::Struct(s) => {
                assert_eq!(s.fields.len(), 2);
                assert!(!s.fields[0].optional); // name required
                assert!(s.fields[1].optional); // count not required
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }
}
