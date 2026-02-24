// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Bebop file parser using regex-based parsing

use crate::AnalyzerError;
use regex::Regex;
use std::path::Path;

/// Parsed bebop file representation
#[derive(Debug, Clone, Default)]
pub struct ParsedBebop {
    /// Top-level structs
    pub structs: Vec<BebopStruct>,
    /// Top-level messages
    pub messages: Vec<BebopMessage>,
    /// Top-level enums
    pub enums: Vec<BebopEnum>,
}

/// Parsed bebop struct (unversioned)
#[derive(Debug, Clone, Default)]
pub struct BebopStruct {
    /// Struct name
    pub name: String,
    /// Fields
    pub fields: Vec<BebopField>,
    /// Whether this is a readonly struct
    pub readonly: bool,
}

/// Parsed bebop message (versioned)
#[derive(Debug, Clone, Default)]
pub struct BebopMessage {
    /// Message name
    pub name: String,
    /// Fields (with explicit field numbers)
    pub fields: Vec<BebopField>,
    /// Whether this is a readonly message
    pub readonly: bool,
}

/// Parsed bebop field
#[derive(Debug, Clone)]
pub struct BebopField {
    /// Field name
    pub name: String,
    /// Field type
    pub field_type: String,
    /// Field number (for messages)
    pub number: Option<i32>,
    /// Whether the field is optional
    pub optional: bool,
    /// Whether the field is deprecated
    pub deprecated: bool,
    /// Whether the field is an array
    pub is_array: bool,
    /// Whether the field is a map (and key/value types)
    pub map_types: Option<(String, String)>,
}

/// Parsed bebop enum
#[derive(Debug, Clone, Default)]
pub struct BebopEnum {
    /// Enum name
    pub name: String,
    /// Enum values
    pub values: Vec<BebopEnumValue>,
}

/// Parsed bebop enum value
#[derive(Debug, Clone)]
pub struct BebopEnumValue {
    /// Value name
    pub name: String,
    /// Value number
    pub number: i32,
}

/// Parser for bebop files
#[derive(Debug, Default)]
pub struct BebopParser {}

impl BebopParser {
    /// Create a new parser
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse a bebop file
    pub fn parse_file(&self, path: &Path) -> Result<ParsedBebop, AnalyzerError> {
        let content = std::fs::read_to_string(path)?;
        self.parse_str(&content)
    }

    /// Parse bebop content from a string
    pub fn parse_str(&self, content: &str) -> Result<ParsedBebop, AnalyzerError> {
        let mut parsed = ParsedBebop::default();

        // Remove comments
        let content = remove_comments(content);

        // Parse enums
        parsed.enums = parse_enums(&content)?;

        // Parse structs
        parsed.structs = parse_structs(&content)?;

        // Parse messages
        parsed.messages = parse_messages(&content)?;

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
fn parse_enums(content: &str) -> Result<Vec<BebopEnum>, AnalyzerError> {
    // SAFETY: constant regex pattern, compile-time verified
    let enum_regex = Regex::new(r"enum\s+(\w+)\s*\{([^}]+)\}").unwrap();
    let mut enums = Vec::new();

    for cap in enum_regex.captures_iter(content) {
        let name = cap[1].to_string();
        let body = &cap[2];

        let values = parse_enum_values(body)?;

        enums.push(BebopEnum { name, values });
    }

    Ok(enums)
}

/// Parse enum values from the enum body
fn parse_enum_values(body: &str) -> Result<Vec<BebopEnumValue>, AnalyzerError> {
    // SAFETY: constant regex pattern, compile-time verified
    let value_regex = Regex::new(r"(\w+)\s*=\s*(\d+)").unwrap();
    let mut values = Vec::new();

    for cap in value_regex.captures_iter(body) {
        let name = cap[1].to_string();
        let number = cap[2].parse::<i32>()
            .map_err(|e| AnalyzerError::ParseError(format!("Invalid enum value: {}", e)))?;

        values.push(BebopEnumValue { name, number });
    }

    Ok(values)
}

/// Parse all structs in the content
fn parse_structs(content: &str) -> Result<Vec<BebopStruct>, AnalyzerError> {
    // SAFETY: constant regex pattern, compile-time verified
    let struct_regex = Regex::new(r"(readonly\s+)?struct\s+(\w+)\s*\{([^}]+)\}").unwrap();
    let mut structs = Vec::new();

    for cap in struct_regex.captures_iter(content) {
        let readonly = cap.get(1).is_some();
        let name = cap[2].to_string();
        let body = &cap[3];

        let fields = parse_struct_fields(body)?;

        structs.push(BebopStruct {
            name,
            fields,
            readonly,
        });
    }

    Ok(structs)
}

/// Parse struct fields from the struct body
fn parse_struct_fields(body: &str) -> Result<Vec<BebopField>, AnalyzerError> {
    let mut fields = Vec::new();

    for line in body.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        let field = parse_field(line, false)?;
        if let Some(field) = field {
            fields.push(field);
        }
    }

    Ok(fields)
}

/// Parse all messages in the content
fn parse_messages(content: &str) -> Result<Vec<BebopMessage>, AnalyzerError> {
    // SAFETY: constant regex pattern, compile-time verified
    let message_regex = Regex::new(r"(readonly\s+)?message\s+(\w+)\s*\{([^}]+)\}").unwrap();
    let mut messages = Vec::new();

    for cap in message_regex.captures_iter(content) {
        let readonly = cap.get(1).is_some();
        let name = cap[2].to_string();
        let body = &cap[3];

        let fields = parse_message_fields(body)?;

        messages.push(BebopMessage {
            name,
            fields,
            readonly,
        });
    }

    Ok(messages)
}

/// Parse message fields from the message body
fn parse_message_fields(body: &str) -> Result<Vec<BebopField>, AnalyzerError> {
    let mut fields = Vec::new();

    for line in body.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        let field = parse_field(line, true)?;
        if let Some(field) = field {
            fields.push(field);
        }
    }

    Ok(fields)
}

/// Parse a single field (works for both struct and message)
fn parse_field(line: &str, is_message: bool) -> Result<Option<BebopField>, AnalyzerError> {
    let line = line.trim();

    // Skip empty lines and comments
    if line.is_empty() || line.starts_with("//") {
        return Ok(None);
    }

    // Remove trailing semicolon
    let line = line.trim_end_matches(';').trim();

    let deprecated = line.contains("deprecated");
    let line = line.replace("deprecated", "").trim().to_string();

    // Message fields have format: number -> type name
    if is_message {
        let parts: Vec<&str> = line.split("->").collect();
        if parts.len() != 2 {
            return Err(AnalyzerError::ParseError(format!("Invalid message field format: {}", line)));
        }

        let number = parts[0].trim().parse::<i32>()
            .map_err(|e| AnalyzerError::ParseError(format!("Invalid field number: {}", e)))?;

        let type_and_name = parts[1].trim();
        parse_type_and_name(type_and_name, Some(number), deprecated)
    } else {
        // Struct fields have format: type name
        parse_type_and_name(line.as_str(), None, deprecated)
    }
}

/// Parse type and field name
fn parse_type_and_name(input: &str, number: Option<i32>, deprecated: bool) -> Result<Option<BebopField>, AnalyzerError> {
    // Check for array type: array[T]
    // SAFETY: constant regex pattern, compile-time verified
    let array_regex = Regex::new(r"array\[([^\]]+)\]\s+(\w+)").unwrap();
    if let Some(cap) = array_regex.captures(input) {
        let element_type = cap[1].to_string();
        let name = cap[2].to_string();

        return Ok(Some(BebopField {
            name,
            field_type: element_type,
            number,
            optional: false,
            deprecated,
            is_array: true,
            map_types: None,
        }));
    }

    // Check for map type: map[K, V]
    // SAFETY: constant regex pattern, compile-time verified
    let map_regex = Regex::new(r"map\[([^,]+),\s*([^\]]+)\]\s+(\w+)").unwrap();
    if let Some(cap) = map_regex.captures(input) {
        let key_type = cap[1].trim().to_string();
        let value_type = cap[2].trim().to_string();
        let name = cap[3].to_string();

        return Ok(Some(BebopField {
            name,
            field_type: "map".to_string(),
            number,
            optional: false,
            deprecated,
            is_array: false,
            map_types: Some((key_type, value_type)),
        }));
    }

    // Regular field: type name or type? name
    let parts: Vec<&str> = input.split_whitespace().collect();
    if parts.len() != 2 {
        return Err(AnalyzerError::ParseError(format!("Invalid field format: {}", input)));
    }

    let field_type = parts[0];
    let field_name = parts[1];

    // Check if optional (ends with ?)
    let (field_type, optional) = if field_type.ends_with('?') {
        (field_type.trim_end_matches('?'), true)
    } else {
        (field_type, false)
    };

    Ok(Some(BebopField {
        name: field_name.to_string(),
        field_type: field_type.to_string(),
        number,
        optional,
        deprecated,
        is_array: false,
        map_types: None,
    }))
}
