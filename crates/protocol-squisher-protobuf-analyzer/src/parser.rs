// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Protobuf file parser using regex-based parsing

use crate::{AnalyzerError, ProtoSyntax};
use regex::Regex;
use std::path::Path;

/// Parsed protobuf file representation
#[derive(Debug, Clone, Default)]
pub struct ParsedProto {
    /// Detected syntax version
    pub syntax: ProtoSyntax,
    /// Package name
    pub package: Option<String>,
    /// Top-level messages
    pub messages: Vec<ProtoMessage>,
    /// Top-level enums
    pub enums: Vec<ProtoEnum>,
}

/// Parsed protobuf message
#[derive(Debug, Clone, Default)]
pub struct ProtoMessage {
    /// Message name
    pub name: String,
    /// Fields
    pub fields: Vec<ProtoField>,
    /// Nested messages
    pub nested_messages: Vec<ProtoMessage>,
    /// Nested enums
    pub nested_enums: Vec<ProtoEnum>,
    /// Oneof groups
    pub oneofs: Vec<ProtoOneof>,
}

/// Parsed protobuf field
#[derive(Debug, Clone)]
pub struct ProtoField {
    /// Field name
    pub name: String,
    /// Field type
    pub field_type: String,
    /// Field number
    pub number: i32,
    /// Field label (optional, required, repeated)
    pub label: FieldLabel,
    /// Map key type (if map field)
    pub map_key_type: Option<String>,
    /// Map value type (if map field)
    pub map_value_type: Option<String>,
}

/// Field label (modifier)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum FieldLabel {
    /// Optional field (proto2) or implicit (proto3)
    #[default]
    Optional,
    /// Required field (proto2 only)
    Required,
    /// Repeated field (array)
    Repeated,
}

/// Parsed protobuf enum
#[derive(Debug, Clone, Default)]
pub struct ProtoEnum {
    /// Enum name
    pub name: String,
    /// Enum values
    pub values: Vec<ProtoEnumValue>,
}

/// Parsed protobuf enum value
#[derive(Debug, Clone)]
pub struct ProtoEnumValue {
    /// Value name
    pub name: String,
    /// Value number
    pub number: i32,
}

/// Parsed protobuf oneof
#[derive(Debug, Clone, Default)]
pub struct ProtoOneof {
    /// Oneof name
    pub name: String,
    /// Fields in the oneof
    pub fields: Vec<ProtoField>,
}

/// Parser for protobuf files
#[derive(Debug, Default)]
pub struct ProtoParser {}

impl ProtoParser {
    /// Create a new parser
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse a protobuf file
    pub fn parse_file(&self, path: &Path) -> Result<ParsedProto, AnalyzerError> {
        let content = std::fs::read_to_string(path)?;
        self.parse_str(&content)
    }

    /// Parse protobuf content from a string
    pub fn parse_str(&self, content: &str) -> Result<ParsedProto, AnalyzerError> {
        let mut parsed = ParsedProto::default();

        // Remove comments
        let content = remove_comments(content);

        // Detect syntax
        parsed.syntax = detect_syntax(&content);

        // Parse package
        parsed.package = parse_package(&content);

        // Parse top-level enums
        parsed.enums = parse_enums(&content, 0)?;

        // Parse top-level messages
        parsed.messages = parse_messages(&content, parsed.syntax)?;

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
                while let Some(nc) = chars.next() {
                    if nc == '*' && chars.peek() == Some(&'/') {
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

fn compile_regex(pattern: &str) -> Result<Regex, AnalyzerError> {
    Regex::new(pattern).map_err(|e| {
        AnalyzerError::ParseError(format!("Internal parser regex error for '{pattern}': {e}"))
    })
}

/// Detect the protobuf syntax version
fn detect_syntax(content: &str) -> ProtoSyntax {
    let Ok(syntax_re) = Regex::new(r#"syntax\s*=\s*"(proto[23])"\s*;"#) else {
        return ProtoSyntax::Proto2;
    };

    if let Some(caps) = syntax_re.captures(content) {
        match caps.get(1).map(|m| m.as_str()) {
            Some("proto3") => ProtoSyntax::Proto3,
            Some("proto2") => ProtoSyntax::Proto2,
            _ => ProtoSyntax::Proto2,
        }
    } else {
        // Default to proto2 if no syntax specified
        ProtoSyntax::Proto2
    }
}

/// Parse package declaration
fn parse_package(content: &str) -> Option<String> {
    let Ok(package_re) = Regex::new(r"package\s+([\w.]+)\s*;") else {
        return None;
    };
    package_re
        .captures(content)
        .and_then(|caps| caps.get(1))
        .map(|m| m.as_str().to_string())
}

/// Parse enum definitions at a given nesting level
fn parse_enums(content: &str, _depth: usize) -> Result<Vec<ProtoEnum>, AnalyzerError> {
    let mut enums = Vec::new();

    // Match enum blocks
    let enum_re = compile_regex(r"enum\s+(\w+)\s*\{([^}]*)\}")?;

    for caps in enum_re.captures_iter(content) {
        let name = caps.get(1).map(|m| m.as_str()).unwrap_or("").to_string();
        let body = caps.get(2).map(|m| m.as_str()).unwrap_or("");

        let values = parse_enum_values(body)?;

        enums.push(ProtoEnum { name, values });
    }

    Ok(enums)
}

/// Parse enum values
fn parse_enum_values(body: &str) -> Result<Vec<ProtoEnumValue>, AnalyzerError> {
    let mut values = Vec::new();

    // Match enum value definitions: NAME = NUMBER;
    let value_re = compile_regex(r"(\w+)\s*=\s*(-?\d+)")?;

    for caps in value_re.captures_iter(body) {
        let name = caps.get(1).map(|m| m.as_str()).unwrap_or("").to_string();
        let number: i32 = caps
            .get(2)
            .map(|m| m.as_str())
            .unwrap_or("0")
            .parse()
            .unwrap_or(0);

        values.push(ProtoEnumValue { name, number });
    }

    Ok(values)
}

/// Parse message definitions
fn parse_messages(content: &str, syntax: ProtoSyntax) -> Result<Vec<ProtoMessage>, AnalyzerError> {
    let mut messages = Vec::new();

    // Find message blocks with balanced braces
    let message_start_re = compile_regex(r"message\s+(\w+)\s*\{")?;

    for caps in message_start_re.captures_iter(content) {
        let name = caps.get(1).map(|m| m.as_str()).unwrap_or("").to_string();
        let Some(full_match) = caps.get(0) else {
            continue;
        };
        let start_pos = full_match.end() - 1; // Position of opening brace

        if let Some(body) = extract_brace_content(content, start_pos) {
            let message = parse_message_body(&name, &body, syntax)?;
            messages.push(message);
        }
    }

    Ok(messages)
}

/// Extract content between balanced braces
fn extract_brace_content(content: &str, start: usize) -> Option<String> {
    let bytes = content.as_bytes();
    if start >= bytes.len() || bytes[start] != b'{' {
        return None;
    }

    let mut depth = 0;
    let mut end = start;

    for (i, &b) in bytes[start..].iter().enumerate() {
        if b == b'{' {
            depth += 1;
        } else if b == b'}' {
            depth -= 1;
            if depth == 0 {
                end = start + i;
                break;
            }
        }
    }

    if depth == 0 {
        Some(content[start + 1..end].to_string())
    } else {
        None
    }
}

/// Parse a message body
fn parse_message_body(
    name: &str,
    body: &str,
    syntax: ProtoSyntax,
) -> Result<ProtoMessage, AnalyzerError> {
    let mut message = ProtoMessage {
        name: name.to_string(),
        ..Default::default()
    };

    // Parse nested enums
    message.nested_enums = parse_enums(body, 1)?;

    // Parse nested messages (recursively)
    message.nested_messages = parse_messages(body, syntax)?;

    // Parse oneof groups
    message.oneofs = parse_oneofs(body, syntax)?;

    // Parse fields (excluding oneof fields)
    message.fields = parse_fields(body, syntax)?;

    Ok(message)
}

/// Parse oneof groups
fn parse_oneofs(body: &str, syntax: ProtoSyntax) -> Result<Vec<ProtoOneof>, AnalyzerError> {
    let mut oneofs = Vec::new();

    let oneof_start_re = compile_regex(r"oneof\s+(\w+)\s*\{")?;

    for caps in oneof_start_re.captures_iter(body) {
        let name = caps.get(1).map(|m| m.as_str()).unwrap_or("").to_string();
        let Some(full_match) = caps.get(0) else {
            continue;
        };
        let start_pos = full_match.end() - 1;

        if let Some(oneof_body) = extract_brace_content(body, start_pos) {
            let fields = parse_oneof_fields(&oneof_body, syntax)?;
            oneofs.push(ProtoOneof { name, fields });
        }
    }

    Ok(oneofs)
}

/// Parse fields inside a oneof
fn parse_oneof_fields(body: &str, _syntax: ProtoSyntax) -> Result<Vec<ProtoField>, AnalyzerError> {
    let mut fields = Vec::new();

    // Oneof fields don't have labels
    let field_re = compile_regex(r"(\w+)\s+(\w+)\s*=\s*(\d+)")?;

    for caps in field_re.captures_iter(body) {
        let field_type = caps.get(1).map(|m| m.as_str()).unwrap_or("").to_string();
        let name = caps.get(2).map(|m| m.as_str()).unwrap_or("").to_string();
        let number: i32 = caps
            .get(3)
            .map(|m| m.as_str())
            .unwrap_or("0")
            .parse()
            .unwrap_or(0);

        fields.push(ProtoField {
            name,
            field_type,
            number,
            label: FieldLabel::Optional,
            map_key_type: None,
            map_value_type: None,
        });
    }

    Ok(fields)
}

/// Parse regular fields
fn parse_fields(body: &str, syntax: ProtoSyntax) -> Result<Vec<ProtoField>, AnalyzerError> {
    let mut fields = Vec::new();

    // Remove nested message, enum, and oneof blocks to avoid parsing their contents as fields
    let cleaned = remove_nested_blocks(body);

    // Match map fields: map<KeyType, ValueType> name = number;
    let map_re = compile_regex(r"map\s*<\s*(\w+)\s*,\s*(\w+)\s*>\s+(\w+)\s*=\s*(\d+)")?;
    for caps in map_re.captures_iter(&cleaned) {
        let key_type = caps.get(1).map(|m| m.as_str()).unwrap_or("").to_string();
        let value_type = caps.get(2).map(|m| m.as_str()).unwrap_or("").to_string();
        let name = caps.get(3).map(|m| m.as_str()).unwrap_or("").to_string();
        let number: i32 = caps
            .get(4)
            .map(|m| m.as_str())
            .unwrap_or("0")
            .parse()
            .unwrap_or(0);

        fields.push(ProtoField {
            name,
            field_type: "map".to_string(),
            number,
            label: FieldLabel::Repeated,
            map_key_type: Some(key_type),
            map_value_type: Some(value_type),
        });
    }

    // Match regular fields with potential labels
    let field_pattern = match syntax {
        ProtoSyntax::Proto2 => {
            // Proto2: (optional|required|repeated)? type name = number;
            r"(optional|required|repeated)?\s*(\w+)\s+(\w+)\s*=\s*(\d+)"
        },
        ProtoSyntax::Proto3 => {
            // Proto3: (optional|repeated)? type name = number;
            r"(optional|repeated)?\s*(\w+)\s+(\w+)\s*=\s*(\d+)"
        },
    };

    let field_re = compile_regex(field_pattern)?;

    for caps in field_re.captures_iter(&cleaned) {
        let label_str = caps.get(1).map(|m| m.as_str()).unwrap_or("");
        let field_type = caps.get(2).map(|m| m.as_str()).unwrap_or("").to_string();
        let name = caps.get(3).map(|m| m.as_str()).unwrap_or("").to_string();
        let number: i32 = caps
            .get(4)
            .map(|m| m.as_str())
            .unwrap_or("0")
            .parse()
            .unwrap_or(0);

        // Skip if this is a map field (already handled)
        if field_type == "map" {
            continue;
        }

        // Skip keyword-like types that aren't actually fields
        if [
            "message",
            "enum",
            "oneof",
            "option",
            "reserved",
            "extensions",
        ]
        .contains(&field_type.as_str())
        {
            continue;
        }

        let label = match label_str {
            "required" => FieldLabel::Required,
            "repeated" => FieldLabel::Repeated,
            "optional" => FieldLabel::Optional,
            _ => {
                // Default depends on syntax
                match syntax {
                    ProtoSyntax::Proto2 => FieldLabel::Optional, // Proto2 defaults to optional
                    ProtoSyntax::Proto3 => FieldLabel::Required, // Proto3 fields have implicit presence (required)
                }
            },
        };

        fields.push(ProtoField {
            name,
            field_type,
            number,
            label,
            map_key_type: None,
            map_value_type: None,
        });
    }

    Ok(fields)
}

/// Remove nested message, enum, and oneof blocks
fn remove_nested_blocks(content: &str) -> String {
    let mut result = content.to_string();
    let Ok(message_re) = Regex::new(r"message\s+\w+\s*\{[^{}]*\}") else {
        return result;
    };
    let Ok(oneof_re) = Regex::new(r"oneof\s+\w+\s*\{[^{}]*\}") else {
        return result;
    };

    // Remove message blocks
    loop {
        let new_result = message_re.replace_all(&result, "").to_string();
        if new_result == result {
            break;
        }
        result = new_result;
    }

    // Remove enum blocks
    let Ok(enum_re) = Regex::new(r"enum\s+\w+\s*\{[^{}]*\}") else {
        return result;
    };
    result = enum_re.replace_all(&result, "").to_string();

    // Remove oneof blocks
    loop {
        let new_result = oneof_re.replace_all(&result, "").to_string();
        if new_result == result {
            break;
        }
        result = new_result;
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_detect_syntax_proto3() {
        let content = r#"syntax = "proto3";"#;
        assert_eq!(detect_syntax(content), ProtoSyntax::Proto3);
    }

    #[test]
    fn test_detect_syntax_proto2() {
        let content = r#"syntax = "proto2";"#;
        assert_eq!(detect_syntax(content), ProtoSyntax::Proto2);
    }

    #[test]
    fn test_parse_package() {
        let content = "package com.example.test;";
        assert_eq!(parse_package(content), Some("com.example.test".to_string()));
    }

    #[test]
    fn test_parse_simple_message() {
        let content = r#"
            syntax = "proto3";
            message Person {
                string name = 1;
                int32 age = 2;
            }
        "#;

        let parser = ProtoParser::new();
        let result = parser.parse_str(content).unwrap();

        assert_eq!(result.syntax, ProtoSyntax::Proto3);
        assert_eq!(result.messages.len(), 1);
        assert_eq!(result.messages[0].name, "Person");
        assert_eq!(result.messages[0].fields.len(), 2);
    }

    #[test]
    fn test_parse_enum() {
        let content = r#"
            syntax = "proto3";
            enum Status {
                UNKNOWN = 0;
                ACTIVE = 1;
                INACTIVE = 2;
            }
        "#;

        let parser = ProtoParser::new();
        let result = parser.parse_str(content).unwrap();

        assert_eq!(result.enums.len(), 1);
        assert_eq!(result.enums[0].name, "Status");
        assert_eq!(result.enums[0].values.len(), 3);
    }

    #[test]
    fn test_parse_repeated_field() {
        let content = r#"
            syntax = "proto3";
            message TaggedItem {
                string name = 1;
                repeated string tags = 2;
            }
        "#;

        let parser = ProtoParser::new();
        let result = parser.parse_str(content).unwrap();

        let tags_field = result.messages[0]
            .fields
            .iter()
            .find(|f| f.name == "tags")
            .unwrap();
        assert_eq!(tags_field.label, FieldLabel::Repeated);
    }

    #[test]
    fn test_parse_map_field() {
        let content = r#"
            syntax = "proto3";
            message Config {
                map<string, string> settings = 1;
            }
        "#;

        let parser = ProtoParser::new();
        let result = parser.parse_str(content).unwrap();

        let settings_field = result.messages[0]
            .fields
            .iter()
            .find(|f| f.name == "settings")
            .unwrap();
        assert_eq!(settings_field.field_type, "map");
        assert_eq!(settings_field.map_key_type, Some("string".to_string()));
        assert_eq!(settings_field.map_value_type, Some("string".to_string()));
    }

    #[test]
    fn test_parse_oneof() {
        let content = r#"
            syntax = "proto3";
            message Payment {
                oneof method {
                    string card_number = 1;
                    string bank_account = 2;
                }
            }
        "#;

        let parser = ProtoParser::new();
        let result = parser.parse_str(content).unwrap();

        assert_eq!(result.messages[0].oneofs.len(), 1);
        assert_eq!(result.messages[0].oneofs[0].name, "method");
        assert_eq!(result.messages[0].oneofs[0].fields.len(), 2);
    }

    #[test]
    fn test_remove_comments() {
        let content = r#"
            // Single line comment
            message Test {
                /* Multi-line
                   comment */
                string name = 1;
            }
        "#;

        let cleaned = remove_comments(content);
        assert!(!cleaned.contains("Single line"));
        assert!(!cleaned.contains("Multi-line"));
        assert!(cleaned.contains("message Test"));
        assert!(cleaned.contains("string name"));
    }
}
