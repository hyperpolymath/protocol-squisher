// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! OpenAPI/Swagger specification parser.
//!
//! Parses OpenAPI 3.x and Swagger 2.0 JSON/YAML files, extracting the
//! `components.schemas` (OAS3) or `definitions` (Swagger 2.0) section
//! which contains the reusable type definitions.
//!
//! This is a pragmatic parser focused on data shapes, not full API
//! routing or request/response semantics.

use crate::AnalyzerError;
use serde_json::Value;
use std::collections::BTreeMap;

/// A parsed OpenAPI specification (data-shape-relevant parts).
#[derive(Debug, Clone)]
pub struct ParsedOpenApi {
    /// Spec title (from info.title).
    pub title: String,
    /// OpenAPI version string ("3.0.x", "3.1.x", "2.0").
    pub spec_version: SpecVersion,
    /// Named schema definitions.
    pub schemas: BTreeMap<String, OpenApiSchema>,
}

/// OpenAPI specification version.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecVersion {
    /// OpenAPI 3.0.x
    OpenApi30,
    /// OpenAPI 3.1.x
    OpenApi31,
    /// Swagger 2.0
    Swagger20,
}

/// A single schema definition from the OpenAPI spec.
#[derive(Debug, Clone)]
pub struct OpenApiSchema {
    /// Schema name.
    pub name: String,
    /// The schema type.
    pub schema_type: SchemaType,
    /// Description, if any.
    pub description: Option<String>,
    /// Whether this schema is nullable.
    pub nullable: bool,
}

/// OpenAPI schema type variants.
#[derive(Debug, Clone)]
pub enum SchemaType {
    /// Object with named properties.
    Object {
        /// Property definitions.
        properties: Vec<OpenApiProperty>,
        /// Names of required properties.
        required: Vec<String>,
    },
    /// String enum.
    Enum {
        /// Possible values.
        values: Vec<String>,
    },
    /// Array of items.
    Array {
        /// Element type.
        items: Box<SchemaType>,
    },
    /// Primitive type.
    Primitive(OpenApiPrimitive),
    /// Reference to another schema ($ref).
    Ref(String),
    /// allOf composition (intersection/inheritance).
    AllOf(Vec<SchemaType>),
    /// oneOf composition (tagged union).
    OneOf(Vec<SchemaType>),
    /// anyOf composition (union).
    AnyOf(Vec<SchemaType>),
    /// Map with string keys and typed values.
    Map(Box<SchemaType>),
}

/// A property within an object schema.
#[derive(Debug, Clone)]
pub struct OpenApiProperty {
    /// Property name.
    pub name: String,
    /// Property type.
    pub schema_type: SchemaType,
    /// Whether this property is required.
    pub required: bool,
    /// Description, if any.
    pub description: Option<String>,
    /// Format hint (e.g., "date-time", "uuid", "email").
    pub format: Option<String>,
}

/// OpenAPI primitive types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OpenApiPrimitive {
    /// string type.
    String,
    /// integer type (default: int32).
    Integer,
    /// integer with int64 format.
    Long,
    /// number type (default: double).
    Number,
    /// number with float format.
    Float,
    /// boolean type.
    Boolean,
}

/// The OpenAPI parser.
#[derive(Debug, Default)]
pub struct OpenApiParser;

impl OpenApiParser {
    /// Parse an OpenAPI file (JSON or YAML).
    pub fn parse_file(&self, path: &std::path::Path) -> Result<ParsedOpenApi, AnalyzerError> {
        let content = std::fs::read_to_string(path)?;
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("openapi");
        self.parse_str(&content, name)
    }

    /// Parse an OpenAPI string (JSON or YAML).
    pub fn parse_str(&self, content: &str, name: &str) -> Result<ParsedOpenApi, AnalyzerError> {
        // Try JSON first, then YAML
        let value: Value = match serde_json::from_str(content) {
            Ok(v) => v,
            Err(_) => serde_yaml::from_str(content).map_err(|e| {
                AnalyzerError::ParseError(format!("Failed to parse as JSON or YAML: {e}"))
            })?,
        };

        self.parse_value(&value, name)
    }

    /// Parse from a serde_json::Value.
    fn parse_value(&self, value: &Value, name: &str) -> Result<ParsedOpenApi, AnalyzerError> {
        let spec_version = detect_spec_version(value)?;
        let title = value
            .pointer("/info/title")
            .and_then(|v| v.as_str())
            .unwrap_or(name)
            .to_string();

        // Extract schema definitions based on spec version
        let schemas_value = match spec_version {
            SpecVersion::OpenApi30 | SpecVersion::OpenApi31 => {
                value.pointer("/components/schemas")
            }
            SpecVersion::Swagger20 => value.pointer("/definitions"),
        };

        let mut schemas = BTreeMap::new();
        if let Some(Value::Object(map)) = schemas_value {
            for (schema_name, schema_value) in map {
                let schema = parse_schema(schema_name, schema_value)?;
                schemas.insert(schema_name.clone(), schema);
            }
        }

        Ok(ParsedOpenApi {
            title,
            spec_version,
            schemas,
        })
    }
}

/// Detect the OpenAPI specification version.
fn detect_spec_version(value: &Value) -> Result<SpecVersion, AnalyzerError> {
    // OpenAPI 3.x has "openapi" field
    if let Some(version) = value.get("openapi").and_then(|v| v.as_str()) {
        if version.starts_with("3.1") {
            return Ok(SpecVersion::OpenApi31);
        }
        if version.starts_with("3.") {
            return Ok(SpecVersion::OpenApi30);
        }
    }

    // Swagger 2.0 has "swagger" field
    if let Some(version) = value.get("swagger").and_then(|v| v.as_str()) {
        if version.starts_with("2.") {
            return Ok(SpecVersion::Swagger20);
        }
    }

    Err(AnalyzerError::ParseError(
        "Cannot detect OpenAPI/Swagger version: missing 'openapi' or 'swagger' field".into(),
    ))
}

/// Parse a single schema definition.
fn parse_schema(name: &str, value: &Value) -> Result<OpenApiSchema, AnalyzerError> {
    let description = value.get("description").and_then(|v| v.as_str()).map(String::from);
    let nullable = value.get("nullable").and_then(|v| v.as_bool()).unwrap_or(false);
    let schema_type = parse_schema_type(value)?;

    Ok(OpenApiSchema {
        name: name.to_string(),
        schema_type,
        description,
        nullable,
    })
}

/// Parse a schema type from a JSON value.
fn parse_schema_type(value: &Value) -> Result<SchemaType, AnalyzerError> {
    // $ref
    if let Some(ref_str) = value.get("$ref").and_then(|v| v.as_str()) {
        return Ok(SchemaType::Ref(extract_ref_name(ref_str)));
    }

    // allOf
    if let Some(Value::Array(items)) = value.get("allOf") {
        let types: Result<Vec<_>, _> = items.iter().map(parse_schema_type).collect();
        return Ok(SchemaType::AllOf(types?));
    }

    // oneOf
    if let Some(Value::Array(items)) = value.get("oneOf") {
        let types: Result<Vec<_>, _> = items.iter().map(parse_schema_type).collect();
        return Ok(SchemaType::OneOf(types?));
    }

    // anyOf
    if let Some(Value::Array(items)) = value.get("anyOf") {
        let types: Result<Vec<_>, _> = items.iter().map(parse_schema_type).collect();
        return Ok(SchemaType::AnyOf(types?));
    }

    // enum (string enums)
    if let Some(Value::Array(vals)) = value.get("enum") {
        let values: Vec<String> = vals
            .iter()
            .filter_map(|v| v.as_str().map(String::from))
            .collect();
        if !values.is_empty() {
            return Ok(SchemaType::Enum { values });
        }
    }

    let type_str = value.get("type").and_then(|v| v.as_str()).unwrap_or("object");
    let format_str = value.get("format").and_then(|v| v.as_str());

    match type_str {
        "object" => {
            // Check for additionalProperties (map type)
            if let Some(additional) = value.get("additionalProperties") {
                if additional.is_object() || additional.is_boolean() {
                    let value_type = if additional.is_object() {
                        parse_schema_type(additional)?
                    } else {
                        SchemaType::Primitive(OpenApiPrimitive::String)
                    };
                    // If there are no named properties, this is a pure map
                    if value.get("properties").is_none() {
                        return Ok(SchemaType::Map(Box::new(value_type)));
                    }
                }
            }

            parse_object_type(value)
        }
        "array" => {
            let items = value
                .get("items")
                .map(parse_schema_type)
                .transpose()?
                .unwrap_or(SchemaType::Primitive(OpenApiPrimitive::String));
            Ok(SchemaType::Array {
                items: Box::new(items),
            })
        }
        "string" => Ok(SchemaType::Primitive(OpenApiPrimitive::String)),
        "integer" => {
            let prim = match format_str {
                Some("int64") => OpenApiPrimitive::Long,
                _ => OpenApiPrimitive::Integer,
            };
            Ok(SchemaType::Primitive(prim))
        }
        "number" => {
            let prim = match format_str {
                Some("float") => OpenApiPrimitive::Float,
                _ => OpenApiPrimitive::Number,
            };
            Ok(SchemaType::Primitive(prim))
        }
        "boolean" => Ok(SchemaType::Primitive(OpenApiPrimitive::Boolean)),
        _ => Ok(SchemaType::Primitive(OpenApiPrimitive::String)),
    }
}

/// Parse an object type with properties.
fn parse_object_type(value: &Value) -> Result<SchemaType, AnalyzerError> {
    let required: Vec<String> = value
        .get("required")
        .and_then(|v| v.as_array())
        .map(|arr| {
            arr.iter()
                .filter_map(|v| v.as_str().map(String::from))
                .collect()
        })
        .unwrap_or_default();

    let mut properties = Vec::new();
    if let Some(Value::Object(props)) = value.get("properties") {
        for (prop_name, prop_value) in props {
            let schema_type = parse_schema_type(prop_value)?;
            let description = prop_value
                .get("description")
                .and_then(|v| v.as_str())
                .map(String::from);
            let format = prop_value
                .get("format")
                .and_then(|v| v.as_str())
                .map(String::from);

            properties.push(OpenApiProperty {
                name: prop_name.clone(),
                schema_type,
                required: required.contains(prop_name),
                description,
                format,
            });
        }
    }

    Ok(SchemaType::Object {
        properties,
        required,
    })
}

/// Extract the schema name from a $ref string.
/// `"#/components/schemas/User"` → `"User"`
/// `"#/definitions/User"` → `"User"`
fn extract_ref_name(ref_str: &str) -> String {
    ref_str
        .rsplit('/')
        .next()
        .unwrap_or(ref_str)
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(json: &str) -> ParsedOpenApi {
        let parser = OpenApiParser;
        parser.parse_str(json, "test").expect("parsing should succeed")
    }

    #[test]
    fn detect_openapi_30() {
        let spec = r#"{
            "openapi": "3.0.3",
            "info": {"title": "Test API", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {}}
        }"#;
        let parsed = parse(spec);
        assert_eq!(parsed.spec_version, SpecVersion::OpenApi30);
        assert_eq!(parsed.title, "Test API");
    }

    #[test]
    fn detect_swagger_20() {
        let spec = r#"{
            "swagger": "2.0",
            "info": {"title": "Legacy API", "version": "1.0"},
            "paths": {},
            "definitions": {}
        }"#;
        let parsed = parse(spec);
        assert_eq!(parsed.spec_version, SpecVersion::Swagger20);
    }

    #[test]
    fn parse_object_schema() {
        let spec = r#"{
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {
                "schemas": {
                    "User": {
                        "type": "object",
                        "required": ["id", "name"],
                        "properties": {
                            "id": {"type": "integer", "format": "int64"},
                            "name": {"type": "string"},
                            "email": {"type": "string", "format": "email"},
                            "active": {"type": "boolean"}
                        }
                    }
                }
            }
        }"#;
        let parsed = parse(spec);
        assert!(parsed.schemas.contains_key("User"));
        let user = &parsed.schemas["User"];
        match &user.schema_type {
            SchemaType::Object {
                properties,
                required,
            } => {
                assert_eq!(properties.len(), 4);
                assert_eq!(required, &["id", "name"]);
                assert!(properties[0].required); // id
                assert!(properties[1].required); // name
            }
            other => panic!("Expected Object, got {other:?}"),
        }
    }

    #[test]
    fn parse_enum_schema() {
        let spec = r#"{
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {
                "schemas": {
                    "Status": {
                        "type": "string",
                        "enum": ["active", "inactive", "pending"]
                    }
                }
            }
        }"#;
        let parsed = parse(spec);
        let status = &parsed.schemas["Status"];
        match &status.schema_type {
            SchemaType::Enum { values } => {
                assert_eq!(values.len(), 3);
                assert_eq!(values[0], "active");
            }
            other => panic!("Expected Enum, got {other:?}"),
        }
    }

    #[test]
    fn parse_array_schema() {
        let spec = serde_json::json!({
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {
                "schemas": {
                    "UserList": {
                        "type": "array",
                        "items": {"$ref": "#/components/schemas/User"}
                    }
                }
            }
        })
        .to_string();
        let parsed = parse(&spec);
        let list = &parsed.schemas["UserList"];
        match &list.schema_type {
            SchemaType::Array { items } => {
                assert!(matches!(items.as_ref(), SchemaType::Ref(name) if name == "User"));
            }
            other => panic!("Expected Array, got {other:?}"),
        }
    }

    #[test]
    fn parse_ref_resolution() {
        assert_eq!(
            extract_ref_name("#/components/schemas/User"),
            "User"
        );
        assert_eq!(extract_ref_name("#/definitions/Order"), "Order");
    }

    #[test]
    fn parse_yaml_format() {
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
      properties:
        name:
          type: string
"#;
        let parser = OpenApiParser;
        let parsed = parser.parse_str(yaml, "yaml_test").expect("parsing should succeed");
        assert!(parsed.schemas.contains_key("Item"));
    }

    #[test]
    fn parse_allof_composition() {
        let spec = serde_json::json!({
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {
                "schemas": {
                    "Employee": {
                        "allOf": [
                            {"$ref": "#/components/schemas/Person"},
                            {
                                "type": "object",
                                "properties": {
                                    "department": {"type": "string"}
                                }
                            }
                        ]
                    }
                }
            }
        })
        .to_string();
        let parsed = parse(&spec);
        let emp = &parsed.schemas["Employee"];
        assert!(matches!(&emp.schema_type, SchemaType::AllOf(items) if items.len() == 2));
    }

    #[test]
    fn parse_map_type() {
        let spec = r#"{
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {
                "schemas": {
                    "Metadata": {
                        "type": "object",
                        "additionalProperties": {"type": "string"}
                    }
                }
            }
        }"#;
        let parsed = parse(spec);
        let meta = &parsed.schemas["Metadata"];
        assert!(matches!(&meta.schema_type, SchemaType::Map(_)));
    }

    #[test]
    fn parse_multiple_schemas() {
        let spec = r#"{
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {
                "schemas": {
                    "User": {"type": "object", "properties": {"id": {"type": "integer"}}},
                    "Order": {"type": "object", "properties": {"total": {"type": "number"}}},
                    "Status": {"type": "string", "enum": ["ok", "error"]}
                }
            }
        }"#;
        let parsed = parse(spec);
        assert_eq!(parsed.schemas.len(), 3);
    }
}
