// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Cap'n Proto file parser using regex-based parsing

use crate::AnalyzerError;
use regex::Regex;
use std::path::Path;

/// Parsed Cap'n Proto file representation
#[derive(Debug, Clone, Default)]
pub struct ParsedCapnProto {
    /// Top-level structs
    pub structs: Vec<CapnProtoStruct>,
    /// Top-level enums
    pub enums: Vec<CapnProtoEnum>,
    /// Top-level unions (standalone)
    pub unions: Vec<CapnProtoUnion>,
}

/// Parsed Cap'n Proto struct
#[derive(Debug, Clone, Default)]
pub struct CapnProtoStruct {
    /// Struct name
    pub name: String,
    /// Fields
    pub fields: Vec<CapnProtoField>,
    /// Inline union (if present)
    pub inline_union: Option<CapnProtoUnion>,
    /// Annotations
    pub annotations: Vec<String>,
}

/// Parsed Cap'n Proto field
#[derive(Debug, Clone)]
pub struct CapnProtoField {
    /// Field name
    pub name: String,
    /// Field type
    pub field_type: String,
    /// Field number (@N)
    pub number: u32,
    /// Default value (if specified)
    pub default_value: Option<String>,
    /// Annotations
    pub annotations: Vec<String>,
}

/// Parsed Cap'n Proto enum
#[derive(Debug, Clone, Default)]
pub struct CapnProtoEnum {
    /// Enum name
    pub name: String,
    /// Enum values
    pub values: Vec<CapnProtoEnumValue>,
    /// Annotations
    pub annotations: Vec<String>,
}

/// Parsed Cap'n Proto enum value
#[derive(Debug, Clone)]
pub struct CapnProtoEnumValue {
    /// Value name
    pub name: String,
    /// Value number (@N)
    pub number: u32,
    /// Annotations
    pub annotations: Vec<String>,
}

/// Parsed Cap'n Proto union
#[derive(Debug, Clone, Default)]
pub struct CapnProtoUnion {
    /// Union name (if named, otherwise empty for inline unions)
    pub name: String,
    /// Union variants (fields)
    pub variants: Vec<CapnProtoField>,
}

/// Parser for Cap'n Proto files
#[derive(Debug, Default)]
pub struct CapnProtoParser {}

impl CapnProtoParser {
    /// Create a new parser
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse a Cap'n Proto file
    pub fn parse_file(&self, path: &Path) -> Result<ParsedCapnProto, AnalyzerError> {
        let content = std::fs::read_to_string(path)?;
        self.parse_str(&content)
    }

    /// Parse Cap'n Proto content from a string
    pub fn parse_str(&self, content: &str) -> Result<ParsedCapnProto, AnalyzerError> {
        let mut parsed = ParsedCapnProto::default();

        // Remove comments
        let content = remove_comments(content);

        // Parse enums
        parsed.enums = parse_enums(&content)?;

        // Parse structs (including inline unions)
        parsed.structs = parse_structs(&content)?;

        // Parse standalone unions
        parsed.unions = parse_unions(&content)?;

        Ok(parsed)
    }
}

/// Remove single-line comments (# style)
fn remove_comments(content: &str) -> String {
    let mut result = String::new();
    let mut in_string = false;

    for line in content.lines() {
        let mut cleaned_line = String::new();
        let mut chars = line.chars().peekable();

        while let Some(c) = chars.next() {
            if c == '"' {
                in_string = !in_string;
                cleaned_line.push(c);
            } else if !in_string && c == '#' {
                // Comment - skip rest of line
                break;
            } else {
                cleaned_line.push(c);
            }
        }

        if !cleaned_line.trim().is_empty() {
            result.push_str(&cleaned_line);
            result.push('\n');
        }
    }

    result
}

/// Parse all enums in the content
fn parse_enums(content: &str) -> Result<Vec<CapnProtoEnum>, AnalyzerError> {
    // SAFETY: constant regex pattern, compile-time verified
    let enum_regex = Regex::new(r"enum\s+(\w+)\s*\{([^}]+)\}").unwrap();
    let mut enums = Vec::new();

    for cap in enum_regex.captures_iter(content) {
        let name = cap[1].to_string();
        let body = &cap[2];

        let values = parse_enum_values(body)?;

        enums.push(CapnProtoEnum {
            name,
            values,
            annotations: vec![],
        });
    }

    Ok(enums)
}

/// Parse enum values from the enum body
fn parse_enum_values(body: &str) -> Result<Vec<CapnProtoEnumValue>, AnalyzerError> {
    // SAFETY: constant regex pattern, compile-time verified
    let value_regex = Regex::new(r"(\w+)\s+@(\d+)").unwrap();
    let mut values = Vec::new();

    for cap in value_regex.captures_iter(body) {
        let name = cap[1].to_string();
        let number = cap[2].parse::<u32>()
            .map_err(|e| AnalyzerError::ParseError(format!("Invalid enum value number: {}", e)))?;

        values.push(CapnProtoEnumValue {
            name,
            number,
            annotations: vec![],
        });
    }

    Ok(values)
}

/// Parse all structs in the content
fn parse_structs(content: &str) -> Result<Vec<CapnProtoStruct>, AnalyzerError> {
    // Use a more robust approach - find struct keyword and manually parse braces
    let mut structs = Vec::new();
    let lines: Vec<&str> = content.lines().collect();
    let mut i = 0;

    while i < lines.len() {
        let line = lines[i].trim();
        if line.starts_with("struct ") {
            // Parse struct name (handle both "struct Name {" on same line or separate lines)
            let name = if let Some(name_end) = line.find('{') {
                line[7..name_end].trim().to_string()
            } else {
                // Name is on this line, brace on next
                let name = line[7..].trim().to_string();
                i += 1;
                if i >= lines.len() {
                    break;
                }
                name
            };

            // Now find the opening brace
            while i < lines.len() && !lines[i].contains('{') {
                i += 1;
            }
            if i >= lines.len() {
                break;
            }

            // Count braces starting after the opening brace
            let mut brace_count = 1;
            let mut body_lines = Vec::new();
            i += 1;

            while i < lines.len() && brace_count > 0 {
                let body_line = lines[i];
                for c in body_line.chars() {
                    if c == '{' {
                        brace_count += 1;
                    } else if c == '}' {
                        brace_count -= 1;
                        if brace_count == 0 {
                            break;
                        }
                    }
                }
                if brace_count > 0 {
                    body_lines.push(body_line);
                }
                i += 1;
            }

            let body = body_lines.join("\n");

            // Check for inline union
            let inline_union = parse_inline_union(&body)?;

            // Parse regular fields (excluding union body)
            let fields = parse_struct_fields(&body, inline_union.is_some())?;

            structs.push(CapnProtoStruct {
                name,
                fields,
                inline_union,
                annotations: vec![],
            });
        } else {
            i += 1;
        }
    }

    Ok(structs)
}

/// Parse inline union from struct body
fn parse_inline_union(body: &str) -> Result<Option<CapnProtoUnion>, AnalyzerError> {
    // SAFETY: constant regex pattern, compile-time verified
    let union_regex = Regex::new(r"union\s*\{([^}]+)\}").unwrap();

    if let Some(cap) = union_regex.captures(body) {
        let union_body = &cap[1];
        let variants = parse_union_fields(union_body)?;

        Ok(Some(CapnProtoUnion {
            name: String::new(), // Inline unions are unnamed
            variants,
        }))
    } else {
        Ok(None)
    }
}

/// Parse struct fields from the struct body
fn parse_struct_fields(body: &str, has_inline_union: bool) -> Result<Vec<CapnProtoField>, AnalyzerError> {
    let mut fields = Vec::new();

    // Remove inline union from body if present
    let body = if has_inline_union {
        // SAFETY: constant regex pattern, compile-time verified
        let union_regex = Regex::new(r"union\s*\{[^}]+\}").unwrap();
        union_regex.replace(body, "").to_string()
    } else {
        body.to_string()
    };

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
fn parse_field(line: &str) -> Result<Option<CapnProtoField>, AnalyzerError> {
    let line = line.trim();

    // Skip empty lines
    if line.is_empty() || line.starts_with('#') {
        return Ok(None);
    }

    // Remove trailing semicolon
    let line = line.trim_end_matches(';').trim();

    // Field format: name @N :Type
    // or: name @N :Type = defaultValue
    // SAFETY: constant regex pattern, compile-time verified
    let field_regex = Regex::new(r"(\w+)\s+@(\d+)\s*:\s*([^=;]+)(?:\s*=\s*(.+))?").unwrap();

    if let Some(cap) = field_regex.captures(line) {
        let name = cap[1].to_string();
        let number = cap[2].parse::<u32>()
            .map_err(|e| AnalyzerError::ParseError(format!("Invalid field number: {}", e)))?;
        let field_type = cap[3].trim().to_string();
        let default_value = cap.get(4).map(|m| m.as_str().trim().to_string());

        Ok(Some(CapnProtoField {
            name,
            field_type,
            number,
            default_value,
            annotations: vec![],
        }))
    } else {
        Ok(None)
    }
}

/// Parse standalone unions
fn parse_unions(content: &str) -> Result<Vec<CapnProtoUnion>, AnalyzerError> {
    // Standalone unions have format: union UnionName { ... }
    // SAFETY: constant regex pattern, compile-time verified
    let union_regex = Regex::new(r"union\s+(\w+)\s*\{([^}]+)\}").unwrap();
    let mut unions = Vec::new();

    for cap in union_regex.captures_iter(content) {
        let name = cap[1].to_string();
        let body = &cap[2];

        let variants = parse_union_fields(body)?;

        unions.push(CapnProtoUnion { name, variants });
    }

    Ok(unions)
}

/// Parse union fields
fn parse_union_fields(body: &str) -> Result<Vec<CapnProtoField>, AnalyzerError> {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_struct() {
        let capnp = r#"
            struct Person {
                name @0 :Text;
                age @1 :Int32;
            }
        "#;

        let parser = CapnProtoParser::new();
        let result = parser.parse_str(capnp);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.structs.len(), 1);
        assert_eq!(parsed.structs[0].name, "Person");
        assert_eq!(parsed.structs[0].fields.len(), 2);
    }

    #[test]
    fn test_parse_enum() {
        let capnp = r#"
            enum Status {
                unknown @0;
                active @1;
                inactive @2;
            }
        "#;

        let parser = CapnProtoParser::new();
        let result = parser.parse_str(capnp);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.enums.len(), 1);
        assert_eq!(parsed.enums[0].name, "Status");
        assert_eq!(parsed.enums[0].values.len(), 3);
    }

    #[test]
    fn test_parse_inline_union() {
        let capnp = r#"
            struct Message {
                id @0 :Int64;
                union {
                    text @1 :Text;
                    number @2 :Int64;
                }
            }
        "#;

        let parser = CapnProtoParser::new();
        let result = parser.parse_str(capnp);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.structs.len(), 1);
        assert!(parsed.structs[0].inline_union.is_some());

        let union_variants = &parsed.structs[0].inline_union.as_ref().unwrap().variants;
        assert_eq!(union_variants.len(), 2);
    }

    #[test]
    fn test_parse_list_type() {
        let capnp = r#"
            struct TaggedItem {
                name @0 :Text;
                tags @1 :List(Text);
            }
        "#;

        let parser = CapnProtoParser::new();
        let result = parser.parse_str(capnp);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.structs[0].fields.len(), 2);
        assert_eq!(parsed.structs[0].fields[1].field_type, "List(Text)");
    }

    #[test]
    fn test_parse_default_value() {
        let capnp = r#"
            struct Config {
                timeout @0 :Int32 = 30;
                enabled @1 :Bool = true;
            }
        "#;

        let parser = CapnProtoParser::new();
        let result = parser.parse_str(capnp);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.structs[0].fields[0].default_value, Some("30".to_string()));
        assert_eq!(parsed.structs[0].fields[1].default_value, Some("true".to_string()));
    }

    #[test]
    fn test_parse_multiple_types() {
        let capnp = r#"
            struct User {
                username @0 :Text;
                email @1 :Text;
            }

            enum Role {
                user @0;
                admin @1;
            }

            struct Post {
                title @0 :Text;
                author @1 :User;
            }
        "#;

        let parser = CapnProtoParser::new();
        let result = parser.parse_str(capnp);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.structs.len(), 2);
        assert_eq!(parsed.enums.len(), 1);
    }

    #[test]
    fn test_parse_comments() {
        let capnp = r#"
            # This is a comment
            struct Person {
                name @0 :Text; # Field comment
                age @1 :Int32;
            }
        "#;

        let parser = CapnProtoParser::new();
        let result = parser.parse_str(capnp);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.structs.len(), 1);
        assert_eq!(parsed.structs[0].fields.len(), 2);
    }

    #[test]
    fn test_parse_void_type() {
        let capnp = r#"
            struct Event {
                timestamp @0 :Int64;
                marker @1 :Void;
            }
        "#;

        let parser = CapnProtoParser::new();
        let result = parser.parse_str(capnp);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.structs[0].fields[1].field_type, "Void");
    }

    #[test]
    fn test_parse_data_type() {
        let capnp = r#"
            struct BinaryData {
                id @0 :Int64;
                payload @1 :Data;
            }
        "#;

        let parser = CapnProtoParser::new();
        let result = parser.parse_str(capnp);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.structs[0].fields[1].field_type, "Data");
    }
}
