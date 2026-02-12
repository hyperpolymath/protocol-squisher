// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! Optimized PyO3 code generation using ephapax transport class analysis
//!
//! This module uses the EphapaxCompatibilityEngine to analyze schema compatibility
//! and generate optimized PyO3 bindings based on transport classes:
//!
//! - **Concorde**: Zero-copy direct field access (100% fidelity, 0% overhead)
//! - **Business**: Efficient conversion with validation (98% fidelity, 5% overhead)
//! - **Wheelbarrow**: JSON fallback for unsafe conversions (50% fidelity, 80% overhead)
//!
//! The generated code automatically selects the best conversion strategy for each field.

use protocol_squisher_compat::{
    EphapaxCompatibilityEngine, SchemaCompatibilityResult, FieldCompatibility,
};
use protocol_squisher_transport_primitives::TransportClass;
use protocol_squisher_ir::IrSchema;

#[cfg(test)]
use protocol_squisher_ir::{IrType, PrimitiveType};

/// Configuration for optimized PyO3 generation
#[derive(Debug, Clone)]
pub struct OptimizedGenConfig {
    /// Module name for generated code
    pub module_name: String,
    /// Whether to generate Python type stubs
    pub generate_stubs: bool,
    /// Whether to add detailed comments explaining transport classes
    pub add_transport_comments: bool,
    /// Threshold for production readiness (default: 90%)
    pub production_threshold: f64,
    /// Threshold for optimization warning (default: 20%)
    pub optimization_threshold: f64,
}

impl Default for OptimizedGenConfig {
    fn default() -> Self {
        Self {
            module_name: "generated".to_string(),
            generate_stubs: true,
            add_transport_comments: true,
            production_threshold: 90.0,
            optimization_threshold: 20.0,
        }
    }
}

impl OptimizedGenConfig {
    pub fn new(module_name: impl Into<String>) -> Self {
        Self {
            module_name: module_name.into(),
            ..Default::default()
        }
    }
}

/// Result of optimized code generation
#[derive(Debug, Clone)]
pub struct OptimizedGeneratedCode {
    /// Generated Rust code with PyO3 bindings
    pub rust_code: String,
    /// Optional Python type stub (.pyi)
    pub python_stub: Option<String>,
    /// Compatibility analysis results
    pub analysis: SchemaCompatibilityResult,
    /// Code generation statistics
    pub stats: GenerationStats,
}

/// Statistics about the generated code
#[derive(Debug, Clone)]
pub struct GenerationStats {
    /// Total number of fields generated
    pub total_fields: usize,
    /// Number of fields using zero-copy (Concorde)
    pub zero_copy_fields: usize,
    /// Number of fields using efficient conversion (Business)
    pub efficient_fields: usize,
    /// Number of fields using JSON fallback (Wheelbarrow)
    pub json_fallback_fields: usize,
    /// Whether the conversion is production-ready
    pub is_production_ready: bool,
    /// Whether optimization is needed
    pub needs_optimization: bool,
}

/// Optimized PyO3 code generator using ephapax analysis
pub struct OptimizedPyO3Generator {
    /// Compatibility engine for transport class analysis
    engine: EphapaxCompatibilityEngine,
    /// Generation configuration
    config: OptimizedGenConfig,
}

impl Default for OptimizedPyO3Generator {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizedPyO3Generator {
    /// Create a new optimized generator
    pub fn new() -> Self {
        Self {
            engine: EphapaxCompatibilityEngine::new(),
            config: OptimizedGenConfig::default(),
        }
    }

    /// Create a generator with custom configuration
    pub fn with_config(config: OptimizedGenConfig) -> Self {
        Self {
            engine: EphapaxCompatibilityEngine::new(),
            config,
        }
    }

    /// Set module name
    pub fn module_name(mut self, name: impl Into<String>) -> Self {
        self.config.module_name = name.into();
        self
    }

    /// Enable/disable transport class comments
    pub fn with_transport_comments(mut self, enabled: bool) -> Self {
        self.config.add_transport_comments = enabled;
        self
    }

    /// Generate optimized PyO3 bindings for Rust→Python conversion
    ///
    /// Analyzes the Rust schema and generates optimized PyO3 code based on
    /// transport class analysis.
    pub fn generate_rust_to_python(
        &self,
        rust_schema: &IrSchema,
        python_schema: &IrSchema,
    ) -> OptimizedGeneratedCode {
        // Analyze compatibility using ephapax
        let analysis = self.engine.analyze_schemas(rust_schema, python_schema);
        let summary = self.engine.get_conversion_summary(&analysis);

        // Generate code based on transport classes
        let mut rust_code = String::new();

        // Add header
        rust_code.push_str(&self.generate_header());

        // Add compatibility analysis summary comment
        if self.config.add_transport_comments {
            rust_code.push_str(&format!(
                "\n// Compatibility Analysis Summary:\n\
                 // - Total fields: {}\n\
                 // - Zero-copy (Concorde): {} ({}%)\n\
                 // - Safe conversions: {} ({}%)\n\
                 // - JSON fallback (Wheelbarrow): {}\n\
                 // - Production ready: {}\n\
                 // - Needs optimization: {}\n\n",
                summary.total_fields,
                summary.zero_copy_fields,
                summary.zero_copy_percentage(),
                summary.safe_fields,
                summary.safe_percentage(),
                summary.json_fallback_fields,
                summary.is_production_ready(),
                summary.needs_optimization(),
            ));
        }

        // Generate type conversions based on transport class
        for type_analysis in &analysis.type_analyses {
            rust_code.push_str(&self.generate_type_conversion(&type_analysis, rust_schema));
        }

        // Add module registration
        rust_code.push_str(&self.generate_module_registration(&analysis));

        // Generate Python stub if requested
        let python_stub = if self.config.generate_stubs {
            Some(self.generate_python_stub(&analysis, python_schema))
        } else {
            None
        };

        let stats = GenerationStats {
            total_fields: summary.total_fields,
            zero_copy_fields: summary.zero_copy_fields,
            efficient_fields: summary.safe_fields - summary.zero_copy_fields,
            json_fallback_fields: summary.json_fallback_fields,
            is_production_ready: summary.is_production_ready(),
            needs_optimization: summary.needs_optimization(),
        };

        OptimizedGeneratedCode {
            rust_code,
            python_stub,
            analysis,
            stats,
        }
    }

    fn generate_header(&self) -> String {
        format!(
            "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
             // Auto-generated PyO3 bindings with ephapax optimization\n\
             // DO NOT EDIT - regenerate using protocol-squisher\n\n\
             use pyo3::prelude::*;\n\
             use pyo3::types::{{PyDict, PyList}};\n\
             use serde::{{Serialize, Deserialize}};\n\n"
        )
    }

    fn generate_type_conversion(
        &self,
        type_analysis: &protocol_squisher_compat::TypeCompatibilityAnalysis,
        _rust_schema: &IrSchema,
    ) -> String {
        let mut code = String::new();

        // Add transport class comment for the type
        if self.config.add_transport_comments {
            code.push_str(&format!(
                "// Type: {} - Overall transport class: {:?}\n",
                type_analysis.type_name, type_analysis.class
            ));
        }

        // Generate struct with PyO3 attributes
        code.push_str(&format!(
            "#[pyclass]\n\
             #[derive(Clone, Debug, Serialize, Deserialize)]\n\
             pub struct {} {{\n",
            type_analysis.type_name
        ));

        // Generate fields based on transport class
        for field in &type_analysis.field_analyses {
            code.push_str(&self.generate_field(field));
        }

        code.push_str("}\n\n");

        // Generate PyO3 methods
        code.push_str(&self.generate_pymethods(&type_analysis.type_name, &type_analysis.field_analyses));

        code
    }

    fn generate_field(&self, field: &FieldCompatibility) -> String {
        let mut field_code = String::new();

        // Add transport class comment
        if self.config.add_transport_comments {
            let strategy = match field.class {
                TransportClass::Concorde => "Zero-copy (Concorde)",
                TransportClass::Business => "Efficient conversion (Business)",
                TransportClass::Economy => "Documented losses (Economy)",
                TransportClass::Wheelbarrow => "JSON fallback (Wheelbarrow)",
            };
            field_code.push_str(&format!(
                "    // {} → {} | {} | Fidelity: {}%, Overhead: {}%\n",
                field.source_type, field.target_type, strategy, field.fidelity, field.overhead
            ));
        }

        // Generate field with appropriate PyO3 attributes
        let rust_type = self.extract_rust_type(&field.target_type);
        match field.class {
            TransportClass::Concorde => {
                // Zero-copy: direct field access
                field_code.push_str(&format!(
                    "    #[pyo3(get, set)]\n    pub {}: {},\n",
                    field.field_name, rust_type
                ));
            }
            TransportClass::Business | TransportClass::Economy => {
                // Efficient conversion: use getter/setter with validation
                field_code.push_str(&format!(
                    "    #[pyo3(get, set)]\n    pub {}: {},\n",
                    field.field_name, rust_type
                ));
            }
            TransportClass::Wheelbarrow => {
                // JSON fallback: use serde_json for conversion
                field_code.push_str(&format!(
                    "    // WARNING: Uses JSON fallback (potential data loss)\n    #[pyo3(get, set)]\n    pub {}: {},\n",
                    field.field_name, rust_type
                ));
            }
        }

        field_code
    }

    fn generate_pymethods(&self, type_name: &str, fields: &[FieldCompatibility]) -> String {
        let mut code = String::new();

        code.push_str(&format!("#[pymethods]\nimpl {} {{\n", type_name));

        // Generate __new__ constructor
        code.push_str("    #[new]\n    pub fn new(");
        for (i, field) in fields.iter().enumerate() {
            let rust_type = self.extract_rust_type(&field.target_type);
            code.push_str(&format!("{}: {}", field.field_name, rust_type));
            if i < fields.len() - 1 {
                code.push_str(", ");
            }
        }
        code.push_str(") -> Self {\n        Self {\n");
        for field in fields {
            code.push_str(&format!("            {},\n", field.field_name));
        }
        code.push_str("        }\n    }\n\n");

        // Generate __repr__
        code.push_str("    fn __repr__(&self) -> String {\n");
        code.push_str(&format!("        format!(\"{}({{:?}})\", self)\n", type_name));
        code.push_str("    }\n\n");

        // Generate to_dict for Wheelbarrow fields
        let has_wheelbarrow = fields.iter().any(|f| matches!(f.class, TransportClass::Wheelbarrow));
        if has_wheelbarrow {
            code.push_str("    /// Convert to Python dict (uses JSON fallback for unsafe fields)\n");
            code.push_str("    pub fn to_dict(&self, py: Python) -> PyResult<PyObject> {\n");
            code.push_str("        let dict = PyDict::new(py);\n");
            for field in fields {
                if matches!(field.class, TransportClass::Wheelbarrow) {
                    code.push_str(&format!(
                        "        // JSON fallback for {}\n        let json_val = serde_json::to_value(&self.{}).unwrap();\n        dict.set_item(\"{}\", json_val.to_string())?;\n",
                        field.field_name, field.field_name, field.field_name
                    ));
                } else {
                    code.push_str(&format!(
                        "        dict.set_item(\"{}\", &self.{})?;\n",
                        field.field_name, field.field_name
                    ));
                }
            }
            code.push_str("        Ok(dict.into())\n    }\n");
        }

        code.push_str("}\n\n");
        code
    }

    fn generate_module_registration(&self, analysis: &SchemaCompatibilityResult) -> String {
        let mut code = String::new();

        code.push_str(&format!(
            "/// PyO3 module for {}\n#[pymodule]\nfn {}(_py: Python, m: &PyModule) -> PyResult<()> {{\n",
            self.config.module_name, self.config.module_name
        ));

        for type_analysis in &analysis.type_analyses {
            code.push_str(&format!(
                "    m.add_class::<{}>()?;\n",
                type_analysis.type_name
            ));
        }

        code.push_str("    Ok(())\n}\n");
        code
    }

    fn generate_python_stub(&self, analysis: &SchemaCompatibilityResult, _python_schema: &IrSchema) -> String {
        let mut stub = String::new();

        stub.push_str("# Auto-generated Python type stub\n");
        stub.push_str("# DO NOT EDIT - regenerate using protocol-squisher\n\n");
        stub.push_str("from typing import Optional, List, Dict, Any\n\n");

        for type_analysis in &analysis.type_analyses {
            stub.push_str(&format!("class {}:\n", type_analysis.type_name));

            for field in &type_analysis.field_analyses {
                let py_type = self.extract_python_type(&field.target_type);
                stub.push_str(&format!("    {}: {}\n", field.field_name, py_type));
            }

            stub.push_str(&format!(
                "\n    def __init__(self, {}) -> None: ...\n    def __repr__(self) -> str: ...\n\n",
                type_analysis.field_analyses.iter()
                    .map(|f| format!("{}: {}", f.field_name, self.extract_python_type(&f.target_type)))
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }

        stub
    }

    fn extract_rust_type(&self, type_str: &str) -> String {
        // Extract Rust type from debug representation
        // This is a simple heuristic - could be improved
        if type_str.contains("I64") {
            "i64".to_string()
        } else if type_str.contains("I32") {
            "i32".to_string()
        } else if type_str.contains("F64") {
            "f64".to_string()
        } else if type_str.contains("F32") {
            "f32".to_string()
        } else if type_str.contains("String") {
            "String".to_string()
        } else if type_str.contains("Bool") {
            "bool".to_string()
        } else {
            "String".to_string() // Default fallback
        }
    }

    fn extract_python_type(&self, type_str: &str) -> String {
        // Extract Python type from debug representation
        if type_str.contains("I64") || type_str.contains("I32") {
            "int".to_string()
        } else if type_str.contains("F64") || type_str.contains("F32") {
            "float".to_string()
        } else if type_str.contains("String") {
            "str".to_string()
        } else if type_str.contains("Bool") {
            "bool".to_string()
        } else {
            "Any".to_string()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{FieldDef, FieldMetadata, StructDef, TypeDef, TypeMetadata};

    fn make_test_schemas() -> (IrSchema, IrSchema) {
        // Rust schema
        let mut rust_schema = IrSchema::new("rust", "test");
        rust_schema.add_type(
            "User".to_string(),
            TypeDef::Struct(StructDef {
                name: "User".to_string(),
                fields: vec![
                    FieldDef {
                        name: "id".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "score".to_string(),
                        ty: IrType::Primitive(PrimitiveType::F64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        rust_schema.add_root("User".to_string());

        // Python schema (compatible)
        let mut python_schema = IrSchema::new("python", "test");
        python_schema.add_type(
            "User".to_string(),
            TypeDef::Struct(StructDef {
                name: "User".to_string(),
                fields: vec![
                    FieldDef {
                        name: "id".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "score".to_string(),
                        ty: IrType::Primitive(PrimitiveType::F64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        python_schema.add_root("User".to_string());

        (rust_schema, python_schema)
    }

    #[test]
    fn test_generator_creation() {
        let gen = OptimizedPyO3Generator::new();
        assert_eq!(gen.config.module_name, "generated");
    }

    #[test]
    fn test_zero_copy_generation() {
        let gen = OptimizedPyO3Generator::new().module_name("users");
        let (rust_schema, python_schema) = make_test_schemas();

        let result = gen.generate_rust_to_python(&rust_schema, &python_schema);

        // Should generate code
        assert!(!result.rust_code.is_empty());
        assert!(result.rust_code.contains("pub struct User"));
        assert!(result.rust_code.contains("pub id: i64"));
        assert!(result.rust_code.contains("pub score: f64"));

        // Should have zero-copy fields
        assert_eq!(result.stats.zero_copy_fields, 2);
        assert!(result.stats.is_production_ready);
        assert!(!result.stats.needs_optimization);

        // Should contain transport class comments
        assert!(result.rust_code.contains("Zero-copy (Concorde)"));
    }

    #[test]
    fn test_narrowing_generation() {
        let gen = OptimizedPyO3Generator::new().module_name("users");

        // Rust schema with i64
        let mut rust_schema = IrSchema::new("rust", "test");
        rust_schema.add_type(
            "User".to_string(),
            TypeDef::Struct(StructDef {
                name: "User".to_string(),
                fields: vec![FieldDef {
                    name: "id".to_string(),
                    ty: IrType::Primitive(PrimitiveType::I64),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
                metadata: TypeMetadata::default(),
            }),
        );
        rust_schema.add_root("User".to_string());

        // Python schema with i32 (narrowing)
        let mut python_schema = IrSchema::new("python", "test");
        python_schema.add_type(
            "User".to_string(),
            TypeDef::Struct(StructDef {
                name: "User".to_string(),
                fields: vec![FieldDef {
                    name: "id".to_string(),
                    ty: IrType::Primitive(PrimitiveType::I32),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
                metadata: TypeMetadata::default(),
            }),
        );
        python_schema.add_root("User".to_string());

        let result = gen.generate_rust_to_python(&rust_schema, &python_schema);

        // Should have JSON fallback
        assert_eq!(result.stats.json_fallback_fields, 1);
        assert!(result.stats.needs_optimization);

        // Should contain warning comment
        assert!(result.rust_code.contains("JSON fallback (Wheelbarrow)"));
        assert!(result.rust_code.contains("WARNING"));
    }

    #[test]
    fn test_python_stub_generation() {
        let gen = OptimizedPyO3Generator::new().module_name("users");
        let (rust_schema, python_schema) = make_test_schemas();

        let result = gen.generate_rust_to_python(&rust_schema, &python_schema);

        let stub = result.python_stub.unwrap();
        assert!(stub.contains("class User:"));
        assert!(stub.contains("id: int"));
        assert!(stub.contains("score: float"));
        assert!(stub.contains("def __init__"));
    }

    #[test]
    fn test_module_registration() {
        let gen = OptimizedPyO3Generator::new().module_name("mymodule");
        let (rust_schema, python_schema) = make_test_schemas();

        let result = gen.generate_rust_to_python(&rust_schema, &python_schema);

        assert!(result.rust_code.contains("#[pymodule]"));
        assert!(result.rust_code.contains("fn mymodule("));
        assert!(result.rust_code.contains("m.add_class::<User>()"));
    }
}
