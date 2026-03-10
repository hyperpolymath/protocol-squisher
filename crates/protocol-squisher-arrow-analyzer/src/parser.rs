// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Apache Arrow schema parser for Protocol Squisher.
//!
//! Provides two entry points:
//! - `from_arrow_schema`: Direct conversion from an `arrow_schema::Schema`
//! - `parse_str`: Parses Arrow IPC JSON schema format (as produced by
//!   `arrow_schema::Schema::to_json()`)
//!
//! Arrow schemas are flat — a list of named, typed fields — which maps
//! directly to a single IR struct per schema.

use crate::AnalyzerError;
use arrow_schema::{DataType, Field, Schema};
use std::path::Path;

/// A parsed Arrow schema with metadata.
#[derive(Debug, Clone)]
pub struct ParsedArrowSchema {
    /// Schema name (from metadata or file stem).
    pub name: String,
    /// The Arrow fields comprising this schema.
    pub fields: Vec<ParsedArrowField>,
    /// Schema-level metadata key-value pairs.
    pub metadata: Vec<(String, String)>,
}

/// A single field extracted from an Arrow schema.
#[derive(Debug, Clone)]
pub struct ParsedArrowField {
    /// Field name.
    pub name: String,
    /// Arrow data type.
    pub data_type: DataType,
    /// Whether the field is nullable.
    pub nullable: bool,
    /// Field-level metadata.
    pub metadata: Vec<(String, String)>,
}

/// Arrow schema parser.
#[derive(Debug, Default)]
pub struct ArrowParser;

impl ArrowParser {
    /// Parse an Arrow IPC JSON schema from a file.
    pub fn parse_file(&self, path: &Path) -> Result<ParsedArrowSchema, AnalyzerError> {
        let content = std::fs::read_to_string(path)?;
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("arrow_schema")
            .to_string();
        self.parse_str(&content, &name)
    }

    /// Parse an Arrow IPC JSON schema from a string.
    ///
    /// The input should be the JSON representation of an Arrow schema,
    /// as produced by `Schema::to_json()`.
    pub fn parse_str(
        &self,
        content: &str,
        name: &str,
    ) -> Result<ParsedArrowSchema, AnalyzerError> {
        let schema: Schema = serde_json::from_str(content)
            .map_err(|e| AnalyzerError::ParseError(format!("Invalid Arrow schema JSON: {e}")))?;
        Ok(self.from_arrow_schema(&schema, name))
    }

    /// Convert directly from an `arrow_schema::Schema`.
    pub fn from_arrow_schema(&self, schema: &Schema, name: &str) -> ParsedArrowSchema {
        let fields = schema
            .fields()
            .iter()
            .map(|f| self.convert_field(f))
            .collect();

        let metadata = schema
            .metadata()
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();

        ParsedArrowSchema {
            name: name.to_string(),
            fields,
            metadata,
        }
    }

    /// Convert a single Arrow field to our parsed representation.
    fn convert_field(&self, field: &Field) -> ParsedArrowField {
        let metadata = field
            .metadata()
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();

        ParsedArrowField {
            name: field.name().clone(),
            data_type: field.data_type().clone(),
            nullable: field.is_nullable(),
            metadata,
        }
    }
}

/// Helper to create an Arrow `Schema` for testing.
#[cfg(test)]
pub fn test_schema(fields: Vec<Field>) -> Schema {
    Schema::new(fields)
}

/// Helper to create an Arrow `Schema` with metadata for testing.
#[cfg(test)]
pub fn test_schema_with_metadata(
    fields: Vec<Field>,
    metadata: std::collections::HashMap<String, String>,
) -> Schema {
    Schema::new_with_metadata(fields, metadata)
}

#[cfg(test)]
mod tests {
    use super::*;
    use arrow_schema::{Field, TimeUnit};

    #[test]
    fn parse_simple_schema() {
        let schema = test_schema(vec![
            Field::new("id", DataType::Int32, false),
            Field::new("name", DataType::Utf8, false),
            Field::new("email", DataType::Utf8, true),
        ]);
        let parser = ArrowParser;
        let parsed = parser.from_arrow_schema(&schema, "users");
        assert_eq!(parsed.name, "users");
        assert_eq!(parsed.fields.len(), 3);
        assert_eq!(parsed.fields[0].name, "id");
        assert!(!parsed.fields[0].nullable);
        assert!(parsed.fields[2].nullable);
    }

    #[test]
    fn parse_temporal_types() {
        let schema = test_schema(vec![
            Field::new("created_at", DataType::Timestamp(TimeUnit::Microsecond, None), false),
            Field::new("birthday", DataType::Date32, false),
            Field::new("duration", DataType::Duration(TimeUnit::Millisecond), false),
        ]);
        let parser = ArrowParser;
        let parsed = parser.from_arrow_schema(&schema, "temporal");
        assert_eq!(parsed.fields.len(), 3);
        assert!(matches!(parsed.fields[0].data_type, DataType::Timestamp(..)));
        assert!(matches!(parsed.fields[1].data_type, DataType::Date32));
    }

    #[test]
    fn parse_nested_types() {
        let inner = Field::new("item", DataType::Int64, false);
        let schema = test_schema(vec![
            Field::new("tags", DataType::List(Box::new(inner).into()), false),
            Field::new(
                "address",
                DataType::Struct(
                    vec![
                        Field::new("street", DataType::Utf8, false),
                        Field::new("city", DataType::Utf8, false),
                    ]
                    .into(),
                ),
                true,
            ),
        ]);
        let parser = ArrowParser;
        let parsed = parser.from_arrow_schema(&schema, "nested");
        assert_eq!(parsed.fields.len(), 2);
        assert!(matches!(parsed.fields[0].data_type, DataType::List(_)));
        assert!(matches!(parsed.fields[1].data_type, DataType::Struct(_)));
    }

    #[test]
    fn parse_schema_metadata() {
        let mut meta = std::collections::HashMap::new();
        meta.insert("version".into(), "1.0".into());
        let schema = test_schema_with_metadata(
            vec![Field::new("x", DataType::Float64, false)],
            meta,
        );
        let parser = ArrowParser;
        let parsed = parser.from_arrow_schema(&schema, "with_meta");
        assert_eq!(parsed.metadata.len(), 1);
        assert_eq!(parsed.metadata[0].0, "version");
    }

    #[test]
    fn roundtrip_through_json() {
        let schema = test_schema(vec![
            Field::new("id", DataType::Int32, false),
            Field::new("value", DataType::Float64, true),
        ]);
        let json_str = serde_json::to_string(&schema).unwrap();
        let parser = ArrowParser;
        let parsed = parser.parse_str(&json_str, "roundtrip").unwrap();
        assert_eq!(parsed.fields.len(), 2);
        assert_eq!(parsed.fields[0].name, "id");
    }

    #[test]
    fn map_type() {
        let schema = test_schema(vec![Field::new(
            "labels",
            DataType::Map(
                Box::new(Field::new(
                    "entries",
                    DataType::Struct(
                        vec![
                            Field::new("key", DataType::Utf8, false),
                            Field::new("value", DataType::Utf8, true),
                        ]
                        .into(),
                    ),
                    false,
                ))
                .into(),
                false,
            ),
            false,
        )]);
        let parser = ArrowParser;
        let parsed = parser.from_arrow_schema(&schema, "map_test");
        assert_eq!(parsed.fields.len(), 1);
        assert!(matches!(parsed.fields[0].data_type, DataType::Map(..)));
    }
}
