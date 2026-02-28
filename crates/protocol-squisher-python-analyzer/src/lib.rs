// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! # Protocol Squisher Python Analyzer
//!
//! Analyzes Python source files with Pydantic models to extract type definitions
//! and convert them to the canonical IR.
//!
//! ## How It Works
//!
//! Unlike the Rust analyzer which parses source directly, the Python analyzer
//! uses a two-stage approach:
//!
//! 1. A Python introspection script is executed to extract type information
//!    from Pydantic models using Python's reflection capabilities
//! 2. The JSON output is parsed in Rust and converted to IR
//!
//! This approach handles Python's dynamic nature and Pydantic's runtime
//! type system more accurately than static analysis would.
//!
//! ## Supported Patterns
//!
//! - Pydantic v1 and v2 BaseModel classes
//! - Standard Python type annotations (List, Dict, Optional, Union, etc.)
//! - Pydantic field constraints (ge, le, min_length, max_length, pattern, etc.)
//! - Python Enum classes
//! - Nested models and references
//!
//! ## Usage
//!
//! ```rust,ignore
//! use protocol_squisher_python_analyzer::{PythonAnalyzer, PythonRunnerConfig};
//!
//! let analyzer = PythonAnalyzer::new();
//! let schema = analyzer.analyze_module("myapp.models")?;
//! ```

use protocol_squisher_ir::IrSchema;
use std::path::Path;

pub mod converter;
pub mod ephapax_bridge;
pub mod runner;
pub mod types;

pub use converter::convert_python_type;
pub use ephapax_bridge::*;
pub use runner::{PythonRunnerConfig, INTROSPECTION_SCRIPT};
pub use types::*;

/// Errors that can occur during Python analysis
#[derive(Debug, Clone)]
pub enum AnalyzerError {
    /// Python execution failed
    PythonError(String),
    /// Introspection script returned an error
    IntrospectionError(String),
    /// Unsupported Python type
    UnsupportedType(String),
    /// Failed to parse JSON output
    ParseError(String),
}

impl std::fmt::Display for AnalyzerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AnalyzerError::PythonError(msg) => write!(f, "Python error: {msg}"),
            AnalyzerError::IntrospectionError(msg) => write!(f, "Introspection error: {msg}"),
            AnalyzerError::UnsupportedType(msg) => write!(f, "Unsupported type: {msg}"),
            AnalyzerError::ParseError(msg) => write!(f, "Parse error: {msg}"),
        }
    }
}

impl std::error::Error for AnalyzerError {}

/// Python/Pydantic analyzer
pub struct PythonAnalyzer {
    /// Python runner configuration
    config: PythonRunnerConfig,
}

impl Default for PythonAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl PythonAnalyzer {
    /// Create a new analyzer with default configuration
    pub fn new() -> Self {
        Self {
            config: PythonRunnerConfig::default(),
        }
    }

    /// Create an analyzer with custom configuration
    pub fn with_config(config: PythonRunnerConfig) -> Self {
        Self { config }
    }

    /// Set the Python interpreter path
    pub fn python_path(mut self, path: impl Into<String>) -> Self {
        self.config.python_path = path.into();
        self
    }

    /// Add a directory to PYTHONPATH
    pub fn add_pythonpath(mut self, path: impl Into<String>) -> Self {
        self.config.pythonpath.push(path.into());
        self
    }

    /// Set the working directory
    pub fn working_dir(mut self, dir: impl Into<String>) -> Self {
        self.config.working_dir = Some(dir.into());
        self
    }

    /// Add an environment variable
    pub fn env(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.config.env.push((key.into(), value.into()));
        self
    }

    /// Check if Python and Pydantic are available
    pub fn check_available(&self) -> Result<bool, AnalyzerError> {
        runner::check_python_available(&self.config)
    }

    /// Analyze a Python module and extract Pydantic models
    pub fn analyze_module(&self, module_path: &str) -> Result<IrSchema, AnalyzerError> {
        self.analyze_module_filtered(module_path, &[])
    }

    /// Analyze specific models from a Python module
    pub fn analyze_module_filtered(
        &self,
        module_path: &str,
        model_names: &[String],
    ) -> Result<IrSchema, AnalyzerError> {
        let result = runner::run_introspection(module_path, model_names, &self.config)?;
        converter::convert_introspection(&result)
    }

    /// Analyze a Python source file by importing it as a module from its directory.
    ///
    /// The module name is derived from the file stem (e.g. `models.py` -> `models`).
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema, AnalyzerError> {
        let module_path = path.file_stem().and_then(|s| s.to_str()).ok_or_else(|| {
            AnalyzerError::ParseError(format!(
                "Could not derive Python module name from path: {}",
                path.display()
            ))
        })?;

        let parent = path.parent().unwrap_or_else(|| Path::new("."));
        let parent_str = parent.to_str().ok_or_else(|| {
            AnalyzerError::ParseError(format!(
                "Python file path contains non-UTF-8 directory: {}",
                path.display()
            ))
        })?;

        let mut config = self.config.clone();
        if config.working_dir.is_none() {
            config.working_dir = Some(parent_str.to_string());
        }
        if !config.pythonpath.iter().any(|p| p == parent_str) {
            config.pythonpath.push(parent_str.to_string());
        }

        let result = runner::run_introspection(module_path, &[], &config)?;
        converter::convert_introspection(&result)
    }

    /// Analyze from a JSON string (for testing or when Python output is cached)
    pub fn analyze_json(&self, json: &str) -> Result<IrSchema, AnalyzerError> {
        let result: IntrospectionResult =
            serde_json::from_str(json).map_err(|e| AnalyzerError::ParseError(e.to_string()))?;
        converter::convert_introspection(&result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{ContainerType, IrType, TypeDef};

    #[test]
    fn test_analyzer_creation() {
        let analyzer = PythonAnalyzer::new();
        assert_eq!(analyzer.config.python_path, "python3");
    }

    #[test]
    fn test_analyzer_builder() {
        let analyzer = PythonAnalyzer::new()
            .python_path("/usr/bin/python3.11")
            .add_pythonpath("/app/src")
            .working_dir("/app")
            .env("DJANGO_SETTINGS_MODULE", "myapp.settings");

        assert_eq!(analyzer.config.python_path, "/usr/bin/python3.11");
        assert_eq!(analyzer.config.pythonpath, vec!["/app/src"]);
        assert_eq!(analyzer.config.working_dir, Some("/app".to_string()));
    }

    #[test]
    fn test_analyze_json_simple() {
        let json = r#"{
            "module": "myapp.models",
            "pydantic_version": 2,
            "types": [
                {
                    "kind": "model",
                    "name": "User",
                    "module": "myapp.models",
                    "doc": "A user in the system",
                    "fields": [
                        {
                            "name": "id",
                            "type": {"kind": "primitive", "type": "int"},
                            "optional": false,
                            "constraints": {}
                        },
                        {
                            "name": "email",
                            "type": {"kind": "primitive", "type": "string"},
                            "optional": false,
                            "constraints": {"pattern": "^[\\w.-]+@[\\w.-]+$"}
                        },
                        {
                            "name": "name",
                            "type": {"kind": "optional", "inner": {"kind": "primitive", "type": "string"}},
                            "optional": true,
                            "default": null,
                            "constraints": {}
                        }
                    ],
                    "config": {}
                }
            ]
        }"#;

        let analyzer = PythonAnalyzer::new();
        let schema = analyzer.analyze_json(json).unwrap();

        assert_eq!(schema.name, "myapp.models");
        assert_eq!(schema.source_format, "pydantic");
        assert_eq!(schema.types.len(), 1);

        let Some(TypeDef::Struct(user)) = schema.types.get("User") else {
            unreachable!("User should convert to struct");
        };
        assert_eq!(user.fields.len(), 3);
        assert_eq!(user.fields[0].name, "id");
        assert!(!user.fields[0].optional);
        assert_eq!(user.fields[2].name, "name");
        assert!(user.fields[2].optional);
    }

    #[test]
    fn test_analyze_json_with_nested() {
        let json = r#"{
            "module": "myapp.models",
            "pydantic_version": 2,
            "types": [
                {
                    "kind": "model",
                    "name": "Address",
                    "module": "myapp.models",
                    "fields": [
                        {
                            "name": "street",
                            "type": {"kind": "primitive", "type": "string"},
                            "optional": false,
                            "constraints": {}
                        },
                        {
                            "name": "city",
                            "type": {"kind": "primitive", "type": "string"},
                            "optional": false,
                            "constraints": {}
                        }
                    ],
                    "config": {}
                },
                {
                    "kind": "model",
                    "name": "User",
                    "module": "myapp.models",
                    "fields": [
                        {
                            "name": "name",
                            "type": {"kind": "primitive", "type": "string"},
                            "optional": false,
                            "constraints": {}
                        },
                        {
                            "name": "address",
                            "type": {"kind": "reference", "name": "Address", "module": "myapp.models"},
                            "optional": false,
                            "constraints": {}
                        },
                        {
                            "name": "tags",
                            "type": {"kind": "list", "inner": {"kind": "primitive", "type": "string"}},
                            "optional": false,
                            "constraints": {}
                        }
                    ],
                    "config": {}
                }
            ]
        }"#;

        let analyzer = PythonAnalyzer::new();
        let schema = analyzer.analyze_json(json).unwrap();

        assert_eq!(schema.types.len(), 2);
        assert!(schema.types.contains_key("Address"));
        assert!(schema.types.contains_key("User"));

        let Some(TypeDef::Struct(user)) = schema.types.get("User") else {
            unreachable!("User should convert to struct");
        };
        // Check address field is a reference
        assert!(matches!(user.fields[1].ty, IrType::Reference(_)));
        // Check tags field is a list
        assert!(matches!(
            user.fields[2].ty,
            IrType::Container(ContainerType::Vec(_))
        ));
    }

    #[test]
    fn test_analyze_json_with_enum() {
        let json = r#"{
            "module": "myapp.models",
            "pydantic_version": 2,
            "types": [
                {
                    "kind": "enum",
                    "name": "Status",
                    "module": "myapp.models",
                    "doc": "Order status",
                    "variants": [
                        {"name": "PENDING", "value": "pending"},
                        {"name": "ACTIVE", "value": "active"},
                        {"name": "COMPLETED", "value": "completed"}
                    ]
                },
                {
                    "kind": "model",
                    "name": "Order",
                    "module": "myapp.models",
                    "fields": [
                        {
                            "name": "status",
                            "type": {"kind": "enum", "name": "Status", "module": "myapp.models", "variants": []},
                            "optional": false,
                            "constraints": {}
                        }
                    ],
                    "config": {}
                }
            ]
        }"#;

        let analyzer = PythonAnalyzer::new();
        let schema = analyzer.analyze_json(json).unwrap();

        assert_eq!(schema.types.len(), 2);

        let Some(TypeDef::Enum(status)) = schema.types.get("Status") else {
            unreachable!("Status should convert to enum");
        };
        assert_eq!(status.variants.len(), 3);
        assert_eq!(status.variants[0].name, "PENDING");
    }

    #[test]
    fn test_analyze_json_with_constraints() {
        let json = r#"{
            "module": "myapp.models",
            "pydantic_version": 2,
            "types": [
                {
                    "kind": "model",
                    "name": "Product",
                    "module": "myapp.models",
                    "fields": [
                        {
                            "name": "name",
                            "type": {"kind": "primitive", "type": "string"},
                            "optional": false,
                            "constraints": {"min_length": 1, "max_length": 100}
                        },
                        {
                            "name": "price",
                            "type": {"kind": "primitive", "type": "float"},
                            "optional": false,
                            "constraints": {"ge": 0.0}
                        },
                        {
                            "name": "quantity",
                            "type": {"kind": "primitive", "type": "int"},
                            "optional": false,
                            "constraints": {"ge": 0, "le": 10000}
                        }
                    ],
                    "config": {}
                }
            ]
        }"#;

        let analyzer = PythonAnalyzer::new();
        let schema = analyzer.analyze_json(json).unwrap();

        let Some(TypeDef::Struct(product)) = schema.types.get("Product") else {
            unreachable!("Product should convert to struct");
        };
        // Check name constraints
        assert_eq!(product.fields[0].constraints.len(), 2);
        // Check price constraints
        assert_eq!(product.fields[1].constraints.len(), 1);
        // Check quantity constraints
        assert_eq!(product.fields[2].constraints.len(), 2);
    }
}
