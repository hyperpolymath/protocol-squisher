// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Thrift IDL file parser using regex-based parsing

use crate::AnalyzerError;
use regex::Regex;
use std::path::Path;

/// Parsed thrift file representation
#[derive(Debug, Clone, Default)]
pub struct ParsedThrift {
    /// Top-level structs
    pub structs: Vec<ThriftStruct>,
    /// Top-level enums
    pub enums: Vec<ThriftEnum>,
    /// Top-level exceptions
    pub exceptions: Vec<ThriftException>,
    /// Type aliases (typedef)
    pub typedefs: Vec<ThriftTypedef>,
    /// Constants
    pub constants: Vec<ThriftConst>,
}

/// Parsed thrift struct
#[derive(Debug, Clone, Default)]
pub struct ThriftStruct {
    /// Struct name
    pub name: String,
    /// Fields
    pub fields: Vec<ThriftField>,
}

/// Parsed thrift exception (same structure as struct)
#[derive(Debug, Clone, Default)]
pub struct ThriftException {
    /// Exception name
    pub name: String,
    /// Fields
    pub fields: Vec<ThriftField>,
}

/// Parsed thrift field
#[derive(Debug, Clone)]
pub struct ThriftField {
    /// Field name
    pub name: String,
    /// Field type
    pub field_type: String,
    /// Field number
    pub number: i32,
    /// Field modifier (required/optional/default)
    pub modifier: FieldModifier,
    /// Default value if present
    pub default_value: Option<String>,
}

/// Field modifier
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldModifier {
    /// Required field
    Required,
    /// Optional field
    Optional,
    /// Default value (neither required nor optional)
    Default,
}

/// Parsed thrift enum
#[derive(Debug, Clone, Default)]
pub struct ThriftEnum {
    /// Enum name
    pub name: String,
    /// Enum values
    pub values: Vec<ThriftEnumValue>,
}

/// Parsed thrift enum value
#[derive(Debug, Clone)]
pub struct ThriftEnumValue {
    /// Value name
    pub name: String,
    /// Value number
    pub number: i32,
}

/// Parsed typedef
#[derive(Debug, Clone)]
pub struct ThriftTypedef {
    /// New type name
    pub name: String,
    /// Underlying type
    pub underlying_type: String,
}

/// Parsed constant
#[derive(Debug, Clone)]
pub struct ThriftConst {
    /// Constant name
    pub name: String,
    /// Constant type
    pub const_type: String,
    /// Constant value
    pub value: String,
}

/// Parser for thrift files
#[derive(Debug, Default)]
pub struct ThriftParser {}

impl ThriftParser {
    /// Create a new parser
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse a thrift file
    pub fn parse_file(&self, path: &Path) -> Result<ParsedThrift, AnalyzerError> {
        let content = std::fs::read_to_string(path)?;
        self.parse_str(&content)
    }

    /// Parse thrift content from a string
    pub fn parse_str(&self, content: &str) -> Result<ParsedThrift, AnalyzerError> {
        let mut parsed = ParsedThrift::default();

        // Remove comments
        let content = remove_comments(content);

        // Parse constants
        parsed.constants = parse_constants(&content)?;

        // Parse typedefs
        parsed.typedefs = parse_typedefs(&content)?;

        // Parse enums
        parsed.enums = parse_enums(&content)?;

        // Parse structs
        parsed.structs = parse_structs(&content)?;

        // Parse exceptions
        parsed.exceptions = parse_exceptions(&content)?;

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
        } else if !in_string && c == '#' {
            // Shell-style comment - skip to end of line
            while let Some(&nc) = chars.peek() {
                if nc == '\n' {
                    break;
                }
                chars.next();
            }
        } else {
            result.push(c);
        }
    }

    result
}

/// Parse all constants in the content
fn parse_constants(content: &str) -> Result<Vec<ThriftConst>, AnalyzerError> {
    let const_regex = Regex::new(r"const\s+(\w+)\s+(\w+)\s*=\s*([^;\n]+)").unwrap();
    let mut constants = Vec::new();

    for cap in const_regex.captures_iter(content) {
        let const_type = cap[1].to_string();
        let name = cap[2].to_string();
        let value = cap[3].trim().to_string();

        constants.push(ThriftConst {
            name,
            const_type,
            value,
        });
    }

    Ok(constants)
}

/// Parse all typedefs in the content
fn parse_typedefs(content: &str) -> Result<Vec<ThriftTypedef>, AnalyzerError> {
    let typedef_regex = Regex::new(r"typedef\s+([^\s]+)\s+(\w+)").unwrap();
    let mut typedefs = Vec::new();

    for cap in typedef_regex.captures_iter(content) {
        let underlying_type = cap[1].to_string();
        let name = cap[2].to_string();

        typedefs.push(ThriftTypedef {
            name,
            underlying_type,
        });
    }

    Ok(typedefs)
}

/// Parse all enums in the content
fn parse_enums(content: &str) -> Result<Vec<ThriftEnum>, AnalyzerError> {
    let enum_regex = Regex::new(r"enum\s+(\w+)\s*\{([^}]+)\}").unwrap();
    let mut enums = Vec::new();

    for cap in enum_regex.captures_iter(content) {
        let name = cap[1].to_string();
        let body = &cap[2];

        let values = parse_enum_values(body)?;

        enums.push(ThriftEnum { name, values });
    }

    Ok(enums)
}

/// Parse enum values from the enum body
fn parse_enum_values(body: &str) -> Result<Vec<ThriftEnumValue>, AnalyzerError> {
    let value_regex = Regex::new(r"(\w+)\s*=\s*(\d+)").unwrap();
    let mut values = Vec::new();

    for cap in value_regex.captures_iter(body) {
        let name = cap[1].to_string();
        let number = cap[2].parse::<i32>()
            .map_err(|e| AnalyzerError::ParseError(format!("Invalid enum value: {}", e)))?;

        values.push(ThriftEnumValue { name, number });
    }

    Ok(values)
}

/// Parse all structs in the content
fn parse_structs(content: &str) -> Result<Vec<ThriftStruct>, AnalyzerError> {
    let struct_regex = Regex::new(r"struct\s+(\w+)\s*\{([^}]+)\}").unwrap();
    let mut structs = Vec::new();

    for cap in struct_regex.captures_iter(content) {
        let name = cap[1].to_string();
        let body = &cap[2];

        let fields = parse_fields(body)?;

        structs.push(ThriftStruct { name, fields });
    }

    Ok(structs)
}

/// Parse all exceptions in the content
fn parse_exceptions(content: &str) -> Result<Vec<ThriftException>, AnalyzerError> {
    let exception_regex = Regex::new(r"exception\s+(\w+)\s*\{([^}]+)\}").unwrap();
    let mut exceptions = Vec::new();

    for cap in exception_regex.captures_iter(content) {
        let name = cap[1].to_string();
        let body = &cap[2];

        let fields = parse_fields(body)?;

        exceptions.push(ThriftException { name, fields });
    }

    Ok(exceptions)
}

/// Parse fields from the struct/exception body
fn parse_fields(body: &str) -> Result<Vec<ThriftField>, AnalyzerError> {
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
fn parse_field(line: &str) -> Result<Option<ThriftField>, AnalyzerError> {
    let line = line.trim();

    // Skip empty lines and comments
    if line.is_empty() || line.starts_with("//") {
        return Ok(None);
    }

    // Remove trailing comma or semicolon
    let line = line.trim_end_matches(',').trim_end_matches(';').trim();

    // Field format: number: [required|optional] type name [= default_value]
    // Examples:
    //   1: required string name
    //   2: optional i32 age
    //   3: i32 timeout = 30
    //   4: string host = "localhost"
    //   5: map<string, string> settings

    // Updated regex to handle generic types like map<K,V>, list<T>, set<T>
    let field_regex = Regex::new(
        r"^(\d+):\s*(required|optional)?\s*([^\s]+(?:<[^>]+>)?)\s+(\w+)(?:\s*=\s*(.+))?$"
    ).unwrap();

    if let Some(cap) = field_regex.captures(line) {
        let number = cap[1].parse::<i32>()
            .map_err(|e| AnalyzerError::ParseError(format!("Invalid field number: {}", e)))?;

        let modifier_str = cap.get(2).map(|m| m.as_str());
        let field_type = cap[3].to_string();
        let name = cap[4].to_string();
        let default_value = cap.get(5).map(|m| m.as_str().trim().to_string());

        let modifier = match (modifier_str, &default_value) {
            (Some("required"), _) => FieldModifier::Required,
            (Some("optional"), _) => FieldModifier::Optional,
            (None, Some(_)) => FieldModifier::Default,
            (None, None) => FieldModifier::Default, // Thrift default is "default"
            _ => FieldModifier::Default,
        };

        Ok(Some(ThriftField {
            name,
            field_type,
            number,
            modifier,
            default_value,
        }))
    } else {
        Err(AnalyzerError::ParseError(format!("Invalid field format: {}", line)))
    }
}
