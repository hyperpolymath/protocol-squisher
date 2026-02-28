// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Regex-based GraphQL SDL parser.
//!
//! Parses GraphQL Schema Definition Language into an internal AST
//! representing types, enums, unions, inputs, interfaces, and scalars.

use crate::AnalyzerError;
use regex::Regex;
use std::path::Path;

/// A parsed GraphQL schema containing all type definitions.
#[derive(Debug, Clone, Default)]
pub struct ParsedGraphql {
    pub objects: Vec<GraphqlObject>,
    pub enums: Vec<GraphqlEnum>,
    pub unions: Vec<GraphqlUnion>,
    pub inputs: Vec<GraphqlInput>,
    pub interfaces: Vec<GraphqlInterface>,
    pub scalars: Vec<GraphqlScalar>,
}

/// A GraphQL object type (e.g., `type User { ... }`).
#[derive(Debug, Clone)]
pub struct GraphqlObject {
    pub name: String,
    pub fields: Vec<GraphqlField>,
    pub implements: Vec<String>,
    pub directives: Vec<String>,
}

/// A GraphQL input type (e.g., `input CreateUserInput { ... }`).
#[derive(Debug, Clone)]
pub struct GraphqlInput {
    pub name: String,
    pub fields: Vec<GraphqlField>,
    pub directives: Vec<String>,
}

/// A GraphQL interface (e.g., `interface Node { ... }`).
#[derive(Debug, Clone)]
pub struct GraphqlInterface {
    pub name: String,
    pub fields: Vec<GraphqlField>,
    pub directives: Vec<String>,
}

/// A single field within an object, input, or interface.
#[derive(Debug, Clone)]
pub struct GraphqlField {
    pub name: String,
    pub field_type: GraphqlType,
    pub directives: Vec<String>,
}

/// A GraphQL type reference (may be nested with list/non-null modifiers).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GraphqlType {
    /// A named type reference (e.g., `String`, `User`).
    Named(String),
    /// A non-null type (e.g., `String!`).
    NonNull(Box<GraphqlType>),
    /// A list type (e.g., `[String]`).
    List(Box<GraphqlType>),
}

/// A GraphQL enum type.
#[derive(Debug, Clone)]
pub struct GraphqlEnum {
    pub name: String,
    pub values: Vec<GraphqlEnumValue>,
    pub directives: Vec<String>,
}

/// A single enum value.
#[derive(Debug, Clone)]
pub struct GraphqlEnumValue {
    pub name: String,
    pub directives: Vec<String>,
}

/// A GraphQL union type (e.g., `union SearchResult = User | Post`).
#[derive(Debug, Clone)]
pub struct GraphqlUnion {
    pub name: String,
    pub members: Vec<String>,
    pub directives: Vec<String>,
}

/// A custom scalar declaration (e.g., `scalar DateTime`).
#[derive(Debug, Clone)]
pub struct GraphqlScalar {
    pub name: String,
    pub directives: Vec<String>,
}

/// The GraphQL SDL parser.
#[derive(Debug, Default)]
pub struct GraphqlParser {}

impl GraphqlParser {
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse a GraphQL SDL file from disk.
    pub fn parse_file(&self, path: &Path) -> Result<ParsedGraphql, AnalyzerError> {
        let content = std::fs::read_to_string(path).map_err(AnalyzerError::Io)?;
        self.parse_str(&content)
    }

    /// Parse a GraphQL SDL string.
    pub fn parse_str(&self, content: &str) -> Result<ParsedGraphql, AnalyzerError> {
        let cleaned = remove_comments(content);
        let parsed = ParsedGraphql {
            enums: parse_enums(&cleaned),
            unions: parse_unions(&cleaned),
            scalars: parse_scalars(&cleaned),
            interfaces: parse_interfaces(&cleaned),
            objects: parse_objects(&cleaned),
            inputs: parse_inputs(&cleaned),
        };

        Ok(parsed)
    }
}

/// Remove single-line (#) and string-quoted comments from GraphQL SDL.
fn remove_comments(content: &str) -> String {
    content
        .lines()
        .map(|line| {
            if let Some(idx) = line.find('#') {
                &line[..idx]
            } else {
                line
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Parse enum definitions.
fn parse_enums(content: &str) -> Vec<GraphqlEnum> {
    let re = Regex::new(r"(?s)enum\s+(\w+)\s*(?:(@\w+(?:\([^)]*\))?)\s*)?\{([^}]+)\}").unwrap();
    re.captures_iter(content)
        .map(|cap| {
            let name = cap[1].to_string();
            let directives = extract_directives(cap.get(2).map(|m| m.as_str()).unwrap_or(""));
            let body = &cap[3];
            let values = body
                .lines()
                .filter_map(|line| {
                    let trimmed = line.trim();
                    if trimmed.is_empty() {
                        return None;
                    }
                    let parts: Vec<&str> = trimmed.split_whitespace().collect();
                    if parts.is_empty() {
                        return None;
                    }
                    let value_name = parts[0].to_string();
                    let dirs = parts[1..]
                        .iter()
                        .filter(|p| p.starts_with('@'))
                        .map(|p| p.to_string())
                        .collect();
                    Some(GraphqlEnumValue {
                        name: value_name,
                        directives: dirs,
                    })
                })
                .collect();
            GraphqlEnum {
                name,
                values,
                directives,
            }
        })
        .collect()
}

/// Parse union definitions.
fn parse_unions(content: &str) -> Vec<GraphqlUnion> {
    let re =
        Regex::new(r"union\s+(\w+)\s*(?:(@\w+(?:\([^)]*\))?)\s*)?=\s*([^\n]+)").unwrap();
    re.captures_iter(content)
        .map(|cap| {
            let name = cap[1].to_string();
            let directives = extract_directives(cap.get(2).map(|m| m.as_str()).unwrap_or(""));
            let members = cap[3]
                .split('|')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            GraphqlUnion {
                name,
                members,
                directives,
            }
        })
        .collect()
}

/// Parse scalar definitions.
fn parse_scalars(content: &str) -> Vec<GraphqlScalar> {
    let re = Regex::new(r"scalar\s+(\w+)\s*(?:(@\w+(?:\([^)]*\))?))?").unwrap();
    re.captures_iter(content)
        .map(|cap| {
            let name = cap[1].to_string();
            let directives = extract_directives(cap.get(2).map(|m| m.as_str()).unwrap_or(""));
            GraphqlScalar { name, directives }
        })
        .collect()
}

/// Parse interface definitions.
fn parse_interfaces(content: &str) -> Vec<GraphqlInterface> {
    let re = Regex::new(
        r"(?s)interface\s+(\w+)\s*(?:(@\w+(?:\([^)]*\))?)\s*)?\{([^}]+)\}",
    )
    .unwrap();
    re.captures_iter(content)
        .map(|cap| {
            let name = cap[1].to_string();
            let directives = extract_directives(cap.get(2).map(|m| m.as_str()).unwrap_or(""));
            let fields = parse_fields(&cap[3]);
            GraphqlInterface {
                name,
                fields,
                directives,
            }
        })
        .collect()
}

/// Parse object type definitions.
fn parse_objects(content: &str) -> Vec<GraphqlObject> {
    let re = Regex::new(
        r"(?s)type\s+(\w+)\s*(?:implements\s+([\w\s&]+))?\s*(?:(@\w+(?:\([^)]*\))?)\s*)?\{([^}]+)\}",
    )
    .unwrap();
    re.captures_iter(content)
        .map(|cap| {
            let name = cap[1].to_string();
            let implements = cap
                .get(2)
                .map(|m| {
                    m.as_str()
                        .split('&')
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty())
                        .collect()
                })
                .unwrap_or_default();
            let directives = extract_directives(cap.get(3).map(|m| m.as_str()).unwrap_or(""));
            let fields = parse_fields(&cap[4]);
            GraphqlObject {
                name,
                fields,
                implements,
                directives,
            }
        })
        .collect()
}

/// Parse input type definitions.
fn parse_inputs(content: &str) -> Vec<GraphqlInput> {
    let re = Regex::new(
        r"(?s)input\s+(\w+)\s*(?:(@\w+(?:\([^)]*\))?)\s*)?\{([^}]+)\}",
    )
    .unwrap();
    re.captures_iter(content)
        .map(|cap| {
            let name = cap[1].to_string();
            let directives = extract_directives(cap.get(2).map(|m| m.as_str()).unwrap_or(""));
            let fields = parse_fields(&cap[3]);
            GraphqlInput {
                name,
                fields,
                directives,
            }
        })
        .collect()
}

/// Parse field definitions from the body of a type/input/interface.
fn parse_fields(body: &str) -> Vec<GraphqlField> {
    body.lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            if trimmed.is_empty() {
                return None;
            }
            // Field format: name: Type @directive
            let colon_pos = trimmed.find(':')?;
            let name = trimmed[..colon_pos].trim().to_string();
            let rest = trimmed[colon_pos + 1..].trim();

            // Split off directives.
            let (type_str, directives) = if let Some(at_pos) = rest.find('@') {
                let t = rest[..at_pos].trim();
                let d = extract_directives(&rest[at_pos..]);
                (t.to_string(), d)
            } else {
                (rest.to_string(), vec![])
            };

            let field_type = parse_type(&type_str);

            Some(GraphqlField {
                name,
                field_type,
                directives,
            })
        })
        .collect()
}

/// Parse a GraphQL type string into a `GraphqlType`.
fn parse_type(s: &str) -> GraphqlType {
    let trimmed = s.trim();
    if let Some(inner) = trimmed.strip_suffix('!') {
        GraphqlType::NonNull(Box::new(parse_type(inner)))
    } else if trimmed.starts_with('[') && trimmed.ends_with(']') {
        GraphqlType::List(Box::new(parse_type(&trimmed[1..trimmed.len() - 1])))
    } else {
        GraphqlType::Named(trimmed.to_string())
    }
}

/// Extract directive names from a string fragment.
fn extract_directives(s: &str) -> Vec<String> {
    let re = Regex::new(r"@\w+").unwrap();
    re.find_iter(s).map(|m| m.as_str().to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_simple_type() {
        let t = parse_type("String");
        assert_eq!(t, GraphqlType::Named("String".to_string()));
    }

    #[test]
    fn parse_non_null_type() {
        let t = parse_type("String!");
        assert_eq!(
            t,
            GraphqlType::NonNull(Box::new(GraphqlType::Named("String".to_string())))
        );
    }

    #[test]
    fn parse_list_type() {
        let t = parse_type("[Int]");
        assert_eq!(
            t,
            GraphqlType::List(Box::new(GraphqlType::Named("Int".to_string())))
        );
    }

    #[test]
    fn parse_non_null_list() {
        let t = parse_type("[String!]!");
        assert_eq!(
            t,
            GraphqlType::NonNull(Box::new(GraphqlType::List(Box::new(
                GraphqlType::NonNull(Box::new(GraphqlType::Named("String".to_string())))
            ))))
        );
    }
}
