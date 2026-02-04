// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! FlatBuffers file parser using regex-based parsing

use crate::AnalyzerError;
use regex::Regex;
use std::path::Path;

/// Parsed FlatBuffers file representation
#[derive(Debug, Clone, Default)]
pub struct ParsedFlatBuffers {
    /// Top-level tables
    pub tables: Vec<FbsTable>,
    /// Top-level structs (zero-copy, fixed layout)
    pub structs: Vec<FbsStruct>,
    /// Top-level enums
    pub enums: Vec<FbsEnum>,
    /// Top-level unions
    pub unions: Vec<FbsUnion>,
    /// Root type declaration
    pub root_type: Option<String>,
}

/// Parsed FlatBuffers table (heap-allocated, flexible)
#[derive(Debug, Clone, Default)]
pub struct FbsTable {
    /// Table name
    pub name: String,
    /// Fields
    pub fields: Vec<FbsField>,
}

/// Parsed FlatBuffers struct (zero-copy, fixed layout)
#[derive(Debug, Clone, Default)]
pub struct FbsStruct {
    /// Struct name
    pub name: String,
    /// Fields
    pub fields: Vec<FbsField>,
}

/// Parsed FlatBuffers field
#[derive(Debug, Clone)]
pub struct FbsField {
    /// Field name
    pub name: String,
    /// Field type
    pub field_type: String,
    /// Whether the field is required (default: optional for tables)
    pub required: bool,
    /// Whether the field is deprecated
    pub deprecated: bool,
    /// Whether the field is a vector
    pub is_vector: bool,
    /// Default value (if specified)
    pub default_value: Option<String>,
}

/// Parsed FlatBuffers enum
#[derive(Debug, Clone, Default)]
pub struct FbsEnum {
    /// Enum name
    pub name: String,
    /// Underlying type (default: byte)
    pub base_type: String,
    /// Enum values
    pub values: Vec<FbsEnumValue>,
}

/// Parsed FlatBuffers enum value
#[derive(Debug, Clone)]
pub struct FbsEnumValue {
    /// Value name
    pub name: String,
    /// Value number
    pub number: i64,
}

/// Parsed FlatBuffers union
#[derive(Debug, Clone, Default)]
pub struct FbsUnion {
    /// Union name
    pub name: String,
    /// Union variants (table/struct names)
    pub variants: Vec<String>,
}

/// Parser for FlatBuffers files
#[derive(Debug, Default)]
pub struct FlatBuffersParser {}

impl FlatBuffersParser {
    /// Create a new parser
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse a FlatBuffers file
    pub fn parse_file(&self, path: &Path) -> Result<ParsedFlatBuffers, AnalyzerError> {
        let content = std::fs::read_to_string(path)?;
        self.parse_str(&content)
    }

    /// Parse FlatBuffers content from a string
    pub fn parse_str(&self, content: &str) -> Result<ParsedFlatBuffers, AnalyzerError> {
        let mut parsed = ParsedFlatBuffers::default();

        // Remove comments
        let content = remove_comments(content);

        // Parse enums
        parsed.enums = parse_enums(&content)?;

        // Parse unions
        parsed.unions = parse_unions(&content)?;

        // Parse structs
        parsed.structs = parse_structs(&content)?;

        // Parse tables
        parsed.tables = parse_tables(&content)?;

        // Parse root_type
        parsed.root_type = parse_root_type(&content);

        Ok(parsed)
    }
}

/// Remove single-line and multi-line comments
fn remove_comments(content: &str) -> String {
    let mut result = String::new();
    let mut chars = content.chars().peekable();
    let mut in_string = false;

    while let Some(c) = chars.next() {
        if c == '"' && !in_string {
            in_string = true;
            result.push(c);
        } else if c == '"' && in_string {
            in_string = false;
            result.push(c);
        } else if !in_string && c == '/' {
            if chars.peek() == Some(&'/') {
                // Single-line comment - skip to end of line
                chars.next();
                while let Some(&nc) = chars.peek() {
                    if nc == '\n' {
                        break;
                    }
                    chars.next();
                }
            } else if chars.peek() == Some(&'*') {
                // Multi-line comment - skip to */
                chars.next();
                while let Some(c1) = chars.next() {
                    if c1 == '*' && chars.peek() == Some(&'/') {
                        chars.next();
                        break;
                    }
                }
            } else {
                result.push(c);
            }
        } else {
            result.push(c);
        }
    }

    result
}

/// Parse all enums in the content
fn parse_enums(content: &str) -> Result<Vec<FbsEnum>, AnalyzerError> {
    let enum_regex = Regex::new(r"enum\s+(\w+)\s*:\s*(\w+)\s*\{([^}]+)\}").unwrap();
    let mut enums = Vec::new();

    for cap in enum_regex.captures_iter(content) {
        let name = cap[1].to_string();
        let base_type = cap[2].to_string();
        let body = &cap[3];

        let values = parse_enum_values(body)?;

        enums.push(FbsEnum {
            name,
            base_type,
            values,
        });
    }

    Ok(enums)
}

/// Parse enum values from the enum body
fn parse_enum_values(body: &str) -> Result<Vec<FbsEnumValue>, AnalyzerError> {
    let value_regex = Regex::new(r"(\w+)\s*=\s*(-?\d+)").unwrap();
    let mut values = Vec::new();

    for cap in value_regex.captures_iter(body) {
        let name = cap[1].to_string();
        let number = cap[2]
            .parse::<i64>()
            .map_err(|e| AnalyzerError::ParseError(format!("Invalid enum value: {}", e)))?;

        values.push(FbsEnumValue { name, number });
    }

    Ok(values)
}

/// Parse all unions in the content
fn parse_unions(content: &str) -> Result<Vec<FbsUnion>, AnalyzerError> {
    let union_regex = Regex::new(r"union\s+(\w+)\s*\{([^}]+)\}").unwrap();
    let mut unions = Vec::new();

    for cap in union_regex.captures_iter(content) {
        let name = cap[1].to_string();
        let body = &cap[2];

        let variants = body
            .split(',')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect();

        unions.push(FbsUnion { name, variants });
    }

    Ok(unions)
}

/// Parse all structs in the content
fn parse_structs(content: &str) -> Result<Vec<FbsStruct>, AnalyzerError> {
    let struct_regex = Regex::new(r"struct\s+(\w+)\s*\{([^}]+)\}").unwrap();
    let mut structs = Vec::new();

    for cap in struct_regex.captures_iter(content) {
        let name = cap[1].to_string();
        let body = &cap[2];

        let fields = parse_fields(body)?;

        structs.push(FbsStruct { name, fields });
    }

    Ok(structs)
}

/// Parse all tables in the content
fn parse_tables(content: &str) -> Result<Vec<FbsTable>, AnalyzerError> {
    let table_regex = Regex::new(r"table\s+(\w+)\s*\{([^}]+)\}").unwrap();
    let mut tables = Vec::new();

    for cap in table_regex.captures_iter(content) {
        let name = cap[1].to_string();
        let body = &cap[2];

        let fields = parse_fields(body)?;

        tables.push(FbsTable { name, fields });
    }

    Ok(tables)
}

/// Parse fields from a table or struct body
fn parse_fields(body: &str) -> Result<Vec<FbsField>, AnalyzerError> {
    let mut fields = Vec::new();

    for line in body.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        if let Some(field) = parse_field(line)? {
            fields.push(field);
        }
    }

    Ok(fields)
}

/// Parse a single field
fn parse_field(line: &str) -> Result<Option<FbsField>, AnalyzerError> {
    let line = line.trim();

    // Skip empty lines and comments
    if line.is_empty() || line.starts_with("//") {
        return Ok(None);
    }

    // Remove trailing semicolon
    let line = line.trim_end_matches(';').trim();

    // Parse field: name: type (attributes)
    let field_regex = Regex::new(r"(\w+)\s*:\s*(\[?\w+\]?)\s*(\([^)]*\))?").unwrap();

    if let Some(cap) = field_regex.captures(line) {
        let name = cap[1].to_string();
        let type_str = cap[2].to_string();
        let attributes = cap.get(3).map(|m| m.as_str()).unwrap_or("");

        // Check if vector type
        let is_vector = type_str.starts_with('[') && type_str.ends_with(']');
        let field_type = if is_vector {
            type_str.trim_start_matches('[').trim_end_matches(']').to_string()
        } else {
            type_str
        };

        // Parse attributes
        let required = attributes.contains("required");
        let deprecated = attributes.contains("deprecated");
        let default_value = parse_default_value(attributes);

        Ok(Some(FbsField {
            name,
            field_type,
            required,
            deprecated,
            is_vector,
            default_value,
        }))
    } else {
        Err(AnalyzerError::ParseError(format!(
            "Invalid field format: {}",
            line
        )))
    }
}

/// Parse default value from attributes
fn parse_default_value(attributes: &str) -> Option<String> {
    let default_regex = Regex::new(r"default\s*:\s*([^,\)]+)").unwrap();
    default_regex
        .captures(attributes)
        .map(|cap| cap[1].trim().to_string())
}

/// Parse root_type declaration
fn parse_root_type(content: &str) -> Option<String> {
    let root_regex = Regex::new(r"root_type\s+(\w+)\s*;").unwrap();
    root_regex
        .captures(content)
        .map(|cap| cap[1].to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_table() {
        let fbs = r#"
            table Person {
                name: string;
                age: int;
            }
        "#;

        let parser = FlatBuffersParser::new();
        let result = parser.parse_str(fbs);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.tables.len(), 1);
        assert_eq!(parsed.tables[0].name, "Person");
        assert_eq!(parsed.tables[0].fields.len(), 2);
    }

    #[test]
    fn test_parse_struct() {
        let fbs = r#"
            struct Vec3 {
                x: float;
                y: float;
                z: float;
            }
        "#;

        let parser = FlatBuffersParser::new();
        let result = parser.parse_str(fbs);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.structs.len(), 1);
        assert_eq!(parsed.structs[0].name, "Vec3");
        assert_eq!(parsed.structs[0].fields.len(), 3);
    }

    #[test]
    fn test_parse_enum() {
        let fbs = r#"
            enum Color: byte {
                Red = 0,
                Green = 1,
                Blue = 2
            }
        "#;

        let parser = FlatBuffersParser::new();
        let result = parser.parse_str(fbs);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.enums.len(), 1);
        assert_eq!(parsed.enums[0].name, "Color");
        assert_eq!(parsed.enums[0].base_type, "byte");
        assert_eq!(parsed.enums[0].values.len(), 3);
    }

    #[test]
    fn test_parse_vector_field() {
        let fbs = r#"
            table List {
                items: [int];
            }
        "#;

        let parser = FlatBuffersParser::new();
        let result = parser.parse_str(fbs);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert!(parsed.tables[0].fields[0].is_vector);
    }

    #[test]
    fn test_parse_required_field() {
        let fbs = r#"
            table User {
                name: string (required);
            }
        "#;

        let parser = FlatBuffersParser::new();
        let result = parser.parse_str(fbs);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert!(parsed.tables[0].fields[0].required);
    }

    #[test]
    fn test_parse_deprecated_field() {
        let fbs = r#"
            table User {
                old_field: string (deprecated);
            }
        "#;

        let parser = FlatBuffersParser::new();
        let result = parser.parse_str(fbs);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert!(parsed.tables[0].fields[0].deprecated);
    }

    #[test]
    fn test_parse_root_type() {
        let fbs = r#"
            table User {
                name: string;
            }
            root_type User;
        "#;

        let parser = FlatBuffersParser::new();
        let result = parser.parse_str(fbs);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.root_type, Some("User".to_string()));
    }

    #[test]
    fn test_parse_union() {
        let fbs = r#"
            union Geometry {
                Vec2,
                Vec3
            }
        "#;

        let parser = FlatBuffersParser::new();
        let result = parser.parse_str(fbs);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.unions.len(), 1);
        assert_eq!(parsed.unions[0].name, "Geometry");
        assert_eq!(parsed.unions[0].variants.len(), 2);
    }
}
