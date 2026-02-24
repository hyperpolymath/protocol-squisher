// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! ReScript schema analyzer for protocol-squisher
//!
//! Analyzes ReScript type definitions and converts them to protocol-squisher IR.
//! ReScript is the **primary application language** in the hyperpolymath ecosystem,
//! making this analyzer critical for ReScript ↔ everything else interoperability.
//!
//! # Features
//!
//! - **Full AST parsing**: Record types, variant types, option types, tuples
//! - **Module system**: Type definitions across module boundaries
//! - **JS interop**: `@as` attributes, `@deriving`, external declarations
//! - **Type inference**: Handles polymorphic types ('a, 'b)
//! - **Transport analysis**: Ephapax-powered compatibility checking
//!
//! # Quick Start
//!
//! ```rust,no_run
//! use protocol_squisher_rescript_analyzer::ReScriptAnalyzer;
//! use std::path::Path;
//!
//! let analyzer = ReScriptAnalyzer::new();
//!
//! // Analyze from file
//! let schema = analyzer.analyze_file(Path::new("Types.res")).unwrap();
//!
//! // Analyze from string
//! let rescript = r#"
//!     type user = {
//!       id: int,
//!       name: string,
//!       email: option<string>,
//!     }
//! "#;
//! let schema = analyzer.analyze_str(rescript, "user").unwrap();
//!
//! // Access types
//! for (name, type_def) in &schema.types {
//!     println!("Found type: {}", name);
//! }
//! ```
//!
//! # ReScript Type Mappings
//!
//! | ReScript | IR Type | Transport Compatible With |
//! |----------|---------|---------------------------|
//! | `int` | `I64` | `I64`, `I128` (widening) |
//! | `float` | `F64` | `F64` only |
//! | `string` | `String` | `String` only |
//! | `bool` | `Bool` | `Bool` only |
//! | `option<T>` | `Option<T>` | `Option<T>` with compatible T |
//! | `array<T>` | `Vec<T>` | `Vec<T>` with compatible T |
//! | `(T1, T2, ...)` | `Tuple<T1, T2, ...>` | Matching tuples |

mod converter;
mod ephapax_bridge;
mod parser;

pub use converter::ReScriptConverter;
pub use ephapax_bridge::{analyze_transport_compatibility, TransportAnalysis};
pub use parser::ReScriptParser;

use protocol_squisher_ir::IrSchema;
use std::path::Path;
use thiserror::Error;

/// Errors that can occur during ReScript analysis
#[derive(Debug, Error)]
pub enum AnalyzerError {
    /// Failed to parse ReScript file
    #[error("ReScript parse error: {0}")]
    ParseError(String),

    /// Invalid ReScript structure
    #[error("Invalid ReScript: {0}")]
    InvalidReScript(String),

    /// Unsupported ReScript feature
    #[error("Unsupported feature: {0}")]
    UnsupportedFeature(String),

    /// IO error
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Main analyzer for ReScript files
#[derive(Debug, Default)]
pub struct ReScriptAnalyzer {
    /// Parser for ReScript files
    parser: ReScriptParser,
    /// Converter from parsed ReScript to IR
    converter: ReScriptConverter,
}

impl ReScriptAnalyzer {
    /// Create a new ReScript analyzer
    pub fn new() -> Self {
        Self::default()
    }

    /// Analyze a ReScript file from a path
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_file(path)?;
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("schema");
        self.converter.convert(&parsed, name)
    }

    /// Analyze ReScript content from a string
    pub fn analyze_str(&self, content: &str, name: &str) -> Result<IrSchema, AnalyzerError> {
        let parsed = self.parser.parse_str(content)?;
        self.converter.convert(&parsed, name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_record() {
        let rescript = r#"
            type person = {
                name: string,
                age: int,
                active: bool,
            }
        "#;

        let analyzer = ReScriptAnalyzer::new();
        let result = analyzer.analyze_str(rescript, "person");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("person"));
    }

    #[test]
    fn test_variant_type() {
        let rescript = r#"
            type status =
              | Active
              | Inactive
              | Pending
        "#;

        let analyzer = ReScriptAnalyzer::new();
        let result = analyzer.analyze_str(rescript, "status");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert!(ir.types.contains_key("status"));
    }

    #[test]
    fn test_option_type() {
        let rescript = r#"
            type user = {
                id: int,
                name: string,
                email: option<string>,
            }
        "#;

        let analyzer = ReScriptAnalyzer::new();
        let result = analyzer.analyze_str(rescript, "user");
        assert!(result.is_ok());
    }

    #[test]
    fn test_array_type() {
        let rescript = r#"
            type post = {
                title: string,
                tags: array<string>,
            }
        "#;

        let analyzer = ReScriptAnalyzer::new();
        let result = analyzer.analyze_str(rescript, "post");
        assert!(result.is_ok());
    }

    #[test]
    fn test_tuple_type() {
        let rescript = r#"
            type coordinates = (float, float)

            type location = {
                name: string,
                coords: coordinates,
            }
        "#;

        let analyzer = ReScriptAnalyzer::new();
        let result = analyzer.analyze_str(rescript, "location");
        assert!(result.is_ok());
    }

    #[test]
    fn test_js_dict_type() {
        let rescript = r#"
            type config = {
                name: string,
                settings: Js.Dict.t<string>,
            }
        "#;

        let analyzer = ReScriptAnalyzer::new();
        let result = analyzer.analyze_str(rescript, "config");
        assert!(result.is_ok());
    }

    #[test]
    fn test_variant_with_payload() {
        let rescript = r#"
            type result<'a, 'e> =
              | Ok('a)
              | Error('e)
        "#;

        let analyzer = ReScriptAnalyzer::new();
        let result = analyzer.analyze_str(rescript, "result");
        assert!(result.is_ok());
    }

    #[test]
    fn test_multiple_types() {
        let rescript = r#"
            type userId = int

            type user = {
                id: userId,
                name: string,
                email: string,
            }

            type post = {
                id: int,
                authorId: userId,
                title: string,
                content: string,
            }
        "#;

        let analyzer = ReScriptAnalyzer::new();
        let result = analyzer.analyze_str(rescript, "schema");
        assert!(result.is_ok());

        let ir = result.unwrap();
        assert_eq!(ir.types.len(), 3);
        assert!(ir.types.contains_key("userId"));
        assert!(ir.types.contains_key("user"));
        assert!(ir.types.contains_key("post"));
    }

    #[test]
    fn test_nested_record() {
        let rescript = r#"
            type address = {
                street: string,
                city: string,
                zipCode: string,
            }

            type person = {
                name: string,
                address: address,
            }
        "#;

        let analyzer = ReScriptAnalyzer::new();
        let result = analyzer.analyze_str(rescript, "person");
        assert!(result.is_ok());
    }

    #[test]
    fn test_js_interop_attributes() {
        let rescript = r#"
            type user = {
                @as("user_id") id: int,
                @as("user_name") name: string,
            }
        "#;

        let analyzer = ReScriptAnalyzer::new();
        let result = analyzer.analyze_str(rescript, "user");
        assert!(result.is_ok());
    }

    #[test]
    fn test_polymorphic_type() {
        let rescript = r#"
            type response<'data> = {
                status: int,
                data: 'data,
            }
        "#;

        let analyzer = ReScriptAnalyzer::new();
        let result = analyzer.analyze_str(rescript, "response");
        assert!(result.is_ok());
    }
}
