// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! TOML parser wrapper that converts TOML documents into an internal AST.
//!
//! Uses the `toml` crate for parsing, then maps the resulting `toml::Value`
//! tree into our own AST for consistent converter input.

use crate::AnalyzerError;
use std::path::Path;

/// A parsed TOML document containing a root table.
#[derive(Debug, Clone)]
pub struct ParsedToml {
    /// The root table entries.
    pub entries: Vec<TomlEntry>,
    /// The source document name.
    pub name: String,
}

/// A single key-value entry in a TOML table.
#[derive(Debug, Clone)]
pub struct TomlEntry {
    /// The key name.
    pub key: String,
    /// The value.
    pub value: TomlValue,
}

/// Internal AST for TOML values.
#[derive(Debug, Clone)]
pub enum TomlValue {
    /// A string value.
    String(String),
    /// An integer value.
    Integer(i64),
    /// A floating-point value.
    Float(f64),
    /// A boolean value.
    Boolean(bool),
    /// A date-time value (stored as string for simplicity).
    DateTime(String),
    /// A nested table (inline or standard).
    Table(Vec<TomlEntry>),
    /// An array of values.
    Array(Vec<TomlValue>),
}

/// The TOML parser.
#[derive(Debug, Default)]
pub struct TomlParser {}

impl TomlParser {
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse a TOML file from disk.
    pub fn parse_file(&self, path: &Path) -> Result<ParsedToml, AnalyzerError> {
        let content = std::fs::read_to_string(path).map_err(AnalyzerError::Io)?;
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("toml")
            .to_string();
        self.parse_str(&content, &name)
    }

    /// Parse a TOML string.
    pub fn parse_str(&self, content: &str, name: &str) -> Result<ParsedToml, AnalyzerError> {
        let table: toml::Value = content
            .parse()
            .map_err(|e: toml::de::Error| AnalyzerError::ParseError(e.to_string()))?;

        let entries = match table {
            toml::Value::Table(t) => convert_table(&t),
            _ => {
                return Err(AnalyzerError::ParseError(
                    "TOML root must be a table".to_string(),
                ))
            },
        };

        Ok(ParsedToml {
            entries,
            name: name.to_string(),
        })
    }
}

/// Convert a `toml::Table` into our internal entry list.
fn convert_table(table: &toml::map::Map<String, toml::Value>) -> Vec<TomlEntry> {
    table
        .iter()
        .map(|(key, value)| TomlEntry {
            key: key.clone(),
            value: convert_value(value),
        })
        .collect()
}

/// Convert a `toml::Value` into our internal AST.
fn convert_value(value: &toml::Value) -> TomlValue {
    match value {
        toml::Value::String(s) => TomlValue::String(s.clone()),
        toml::Value::Integer(i) => TomlValue::Integer(*i),
        toml::Value::Float(f) => TomlValue::Float(*f),
        toml::Value::Boolean(b) => TomlValue::Boolean(*b),
        toml::Value::Datetime(dt) => TomlValue::DateTime(dt.to_string()),
        toml::Value::Array(arr) => TomlValue::Array(arr.iter().map(convert_value).collect()),
        toml::Value::Table(t) => TomlValue::Table(convert_table(t)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_basic_toml() {
        let parser = TomlParser::new();
        let toml = r#"
            name = "test"
            version = "1.0.0"
            debug = true
            count = 42
        "#;
        let parsed = parser.parse_str(toml, "test").unwrap();
        assert_eq!(parsed.entries.len(), 4);
    }

    #[test]
    fn parse_nested_table() {
        let parser = TomlParser::new();
        let toml = r#"
            [server]
            host = "localhost"
            port = 8080
        "#;
        let parsed = parser.parse_str(toml, "test").unwrap();
        assert_eq!(parsed.entries.len(), 1);
        match &parsed.entries[0].value {
            TomlValue::Table(entries) => assert_eq!(entries.len(), 2),
            other => panic!("Expected Table, got {other:?}"),
        }
    }

    #[test]
    fn parse_array() {
        let parser = TomlParser::new();
        let toml = r#"
            tags = ["web", "api", "rust"]
        "#;
        let parsed = parser.parse_str(toml, "test").unwrap();
        match &parsed.entries[0].value {
            TomlValue::Array(arr) => assert_eq!(arr.len(), 3),
            other => panic!("Expected Array, got {other:?}"),
        }
    }
}
