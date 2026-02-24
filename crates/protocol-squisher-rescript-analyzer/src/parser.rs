// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! ReScript file parser using regex-based parsing

use crate::AnalyzerError;
use regex::Regex;
use std::path::Path;

/// Parsed ReScript file representation
#[derive(Debug, Clone, Default)]
pub struct ParsedReScript {
    /// Type aliases
    pub type_aliases: Vec<ReScriptTypeAlias>,
    /// Record types
    pub records: Vec<ReScriptRecord>,
    /// Variant types
    pub variants: Vec<ReScriptVariant>,
}

/// Type alias (e.g., `type userId = int`)
#[derive(Debug, Clone)]
pub struct ReScriptTypeAlias {
    pub name: String,
    pub target: String,
    pub type_params: Vec<String>,
}

/// Record type
#[derive(Debug, Clone)]
pub struct ReScriptRecord {
    pub name: String,
    pub fields: Vec<ReScriptField>,
    pub type_params: Vec<String>,
}

/// Record field
#[derive(Debug, Clone)]
pub struct ReScriptField {
    pub name: String,
    pub field_type: String,
    pub optional: bool,
    pub js_name: Option<String>, // From @as attribute
}

/// Variant type (enum/ADT)
#[derive(Debug, Clone)]
pub struct ReScriptVariant {
    pub name: String,
    pub constructors: Vec<ReScriptConstructor>,
    pub type_params: Vec<String>,
}

/// Variant constructor
#[derive(Debug, Clone)]
pub struct ReScriptConstructor {
    pub name: String,
    pub payload: Option<String>, // Type of payload if present
}

/// Parser for ReScript files
#[derive(Debug, Default)]
pub struct ReScriptParser {}

impl ReScriptParser {
    /// Create a new parser
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse a ReScript file
    pub fn parse_file(&self, path: &Path) -> Result<ParsedReScript, AnalyzerError> {
        let content = std::fs::read_to_string(path)?;
        self.parse_str(&content)
    }

    /// Parse ReScript content from a string
    pub fn parse_str(&self, content: &str) -> Result<ParsedReScript, AnalyzerError> {
        let mut parsed = ParsedReScript::default();

        // Remove comments
        let content = remove_comments(content);

        // Parse type aliases first
        parsed.type_aliases = parse_type_aliases(&content)?;

        // Parse record types
        parsed.records = parse_records(&content)?;

        // Parse variant types
        parsed.variants = parse_variants(&content)?;

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

/// Parse type aliases (e.g., `type userId = int`)
fn parse_type_aliases(content: &str) -> Result<Vec<ReScriptTypeAlias>, AnalyzerError> {
    // Match: type name<'a, 'b> = targetType
    // SAFETY: constant regex pattern, compile-time verified
    let alias_regex = Regex::new(r"type\s+(\w+)(?:<([^>]+)>)?\s*=\s*([^{}\n|]+)").unwrap();
    let mut aliases = Vec::new();

    for cap in alias_regex.captures_iter(content) {
        let name = cap[1].to_string();
        let type_params = cap.get(2)
            .map(|m| parse_type_params(m.as_str()))
            .unwrap_or_default();
        let target = cap[3].trim().to_string();

        // Skip if this is actually a record or variant (has { or |)
        if target.contains('{') || target.contains('|') {
            continue;
        }

        aliases.push(ReScriptTypeAlias {
            name,
            type_params,
            target,
        });
    }

    Ok(aliases)
}

/// Parse record types
fn parse_records(content: &str) -> Result<Vec<ReScriptRecord>, AnalyzerError> {
    // Match: type name<'a> = { field1: type1, field2: type2 }
    // SAFETY: constant regex pattern, compile-time verified
    let record_regex = Regex::new(r"type\s+(\w+)(?:<([^>]+)>)?\s*=\s*\{([^}]+)\}").unwrap();
    let mut records = Vec::new();

    for cap in record_regex.captures_iter(content) {
        let name = cap[1].to_string();
        let type_params = cap.get(2)
            .map(|m| parse_type_params(m.as_str()))
            .unwrap_or_default();
        let body = &cap[3];

        let fields = parse_record_fields(body)?;

        records.push(ReScriptRecord {
            name,
            type_params,
            fields,
        });
    }

    Ok(records)
}

/// Parse record fields from body
fn parse_record_fields(body: &str) -> Result<Vec<ReScriptField>, AnalyzerError> {
    let mut fields = Vec::new();

    // Split by comma, handling nested angle brackets
    let field_strs = split_by_comma(body);

    for field_str in field_strs {
        let field_str = field_str.trim();
        if field_str.is_empty() {
            continue;
        }

        // Check for @as attribute
        let js_name = extract_js_name(field_str);
        let field_str = remove_attributes(field_str);

        // Parse: fieldName: fieldType
        let parts: Vec<&str> = field_str.splitn(2, ':').collect();
        if parts.len() != 2 {
            continue; // Skip malformed fields
        }

        let name = parts[0].trim().to_string();
        let field_type = parts[1].trim().to_string();

        // Check if optional (field_type starts with option<)
        let optional = field_type.starts_with("option<");

        fields.push(ReScriptField {
            name,
            field_type,
            optional,
            js_name,
        });
    }

    Ok(fields)
}

/// Parse variant types
fn parse_variants(content: &str) -> Result<Vec<ReScriptVariant>, AnalyzerError> {
    // Match: type name<'a> = | Constructor1 | Constructor2(payload) | ...
    // Also handles: type name = Constructor1 | Constructor2
    // SAFETY: constant regex pattern, compile-time verified
    let variant_regex = Regex::new(r"type\s+(\w+)(?:<([^>]+)>)?\s*=\s*\|?\s*([^{}=]+)").unwrap();
    let mut variants = Vec::new();

    for cap in variant_regex.captures_iter(content) {
        let name = cap[1].to_string();
        let type_params = cap.get(2)
            .map(|m| parse_type_params(m.as_str()))
            .unwrap_or_default();
        let body = &cap[3];

        // Skip if this looks like a record or alias
        if body.contains('{') || (!body.contains('|') && !body.trim().chars().next().unwrap_or(' ').is_uppercase()) {
            continue;
        }

        let constructors = parse_variant_constructors(body)?;

        // Only add if we found actual constructors
        if !constructors.is_empty() {
            variants.push(ReScriptVariant {
                name,
                type_params,
                constructors,
            });
        }
    }

    Ok(variants)
}

/// Parse variant constructors
fn parse_variant_constructors(body: &str) -> Result<Vec<ReScriptConstructor>, AnalyzerError> {
    let mut constructors = Vec::new();

    // Split by | to get individual constructors
    let parts: Vec<&str> = body.split('|').collect();

    for part in parts {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }

        // Check if constructor has payload: Constructor(payload)
        if let Some(paren_pos) = part.find('(') {
            let name = part[..paren_pos].trim().to_string();
            let rest = &part[paren_pos + 1..];
            if let Some(close_pos) = rest.find(')') {
                let payload = rest[..close_pos].trim().to_string();
                constructors.push(ReScriptConstructor {
                    name,
                    payload: Some(payload),
                });
            }
        } else {
            // No payload
            constructors.push(ReScriptConstructor {
                name: part.to_string(),
                payload: None,
            });
        }
    }

    Ok(constructors)
}

/// Parse type parameters (e.g., "'a, 'b" -> ["'a", "'b"])
fn parse_type_params(params: &str) -> Vec<String> {
    params
        .split(',')
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect()
}

/// Extract @as("jsName") attribute
fn extract_js_name(field_str: &str) -> Option<String> {
    // SAFETY: constant regex pattern, compile-time verified
    let as_regex = Regex::new(r#"@as\("([^"]+)"\)"#).unwrap();
    as_regex.captures(field_str)
        .map(|cap| cap[1].to_string())
}

/// Remove attributes from field string
fn remove_attributes(field_str: &str) -> String {
    // SAFETY: constant regex pattern, compile-time verified
    let attr_regex = Regex::new(r"@\w+\([^)]*\)").unwrap();
    attr_regex.replace_all(field_str, "").to_string()
}

/// Split by comma, respecting nested angle brackets
fn split_by_comma(s: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth = 0;

    for c in s.chars() {
        match c {
            '<' | '(' => {
                depth += 1;
                current.push(c);
            }
            '>' | ')' => {
                depth -= 1;
                current.push(c);
            }
            ',' if depth == 0 => {
                parts.push(current.trim().to_string());
                current.clear();
            }
            _ => current.push(c),
        }
    }

    if !current.trim().is_empty() {
        parts.push(current.trim().to_string());
    }

    parts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_type_alias() {
        let content = "type userId = int";
        let aliases = parse_type_aliases(content).unwrap();
        assert_eq!(aliases.len(), 1);
        assert_eq!(aliases[0].name, "userId");
        assert_eq!(aliases[0].target, "int");
    }

    #[test]
    fn test_parse_simple_record() {
        let content = r#"
            type person = {
                name: string,
                age: int,
            }
        "#;
        let records = parse_records(content).unwrap();
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].name, "person");
        assert_eq!(records[0].fields.len(), 2);
    }

    #[test]
    fn test_parse_variant() {
        let content = r#"
            type status =
              | Active
              | Inactive
              | Pending
        "#;
        let variants = parse_variants(content).unwrap();
        assert_eq!(variants.len(), 1);
        assert_eq!(variants[0].name, "status");
        assert_eq!(variants[0].constructors.len(), 3);
    }

    #[test]
    fn test_parse_variant_with_payload() {
        let content = r#"
            type result<'a, 'e> =
              | Ok('a)
              | Error('e)
        "#;
        let variants = parse_variants(content).unwrap();
        assert_eq!(variants.len(), 1);
        assert_eq!(variants[0].name, "result");
        assert_eq!(variants[0].constructors.len(), 2);
        assert!(variants[0].constructors[0].payload.is_some());
    }

    #[test]
    fn test_parse_js_name_attribute() {
        let field_str = r#"@as("user_id") id: int"#;
        let js_name = extract_js_name(field_str);
        assert_eq!(js_name, Some("user_id".to_string()));
    }

    #[test]
    fn test_split_by_comma() {
        let s = "field1: int, field2: option<string>, field3: array<int>";
        let parts = split_by_comma(s);
        assert_eq!(parts.len(), 3);
        assert_eq!(parts[0], "field1: int");
        assert_eq!(parts[1], "field2: option<string>");
        assert_eq!(parts[2], "field3: array<int>");
    }

    #[test]
    fn test_parse_polymorphic_record() {
        let content = r#"
            type response<'data> = {
                status: int,
                data: 'data,
            }
        "#;
        let records = parse_records(content).unwrap();
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].type_params.len(), 1);
        assert_eq!(records[0].type_params[0], "'data");
    }

    #[test]
    fn test_remove_comments() {
        let content = r#"
            // This is a comment
            type user = {
                name: string, // Field comment
                /* Multi-line
                   comment */
                age: int,
            }
        "#;
        let cleaned = remove_comments(content);
        assert!(!cleaned.contains("This is a comment"));
        assert!(!cleaned.contains("Field comment"));
        assert!(!cleaned.contains("Multi-line"));
    }
}
