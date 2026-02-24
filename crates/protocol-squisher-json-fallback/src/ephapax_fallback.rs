// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! Ephapax-aware JSON fallback for Wheelbarrow-class conversions
//!
//! This module uses the EphapaxCompatibilityEngine to identify which fields
//! require JSON fallback (Wheelbarrow class) and generates optimized conversion
//! code that only uses JSON serialization where necessary.
//!
//! ## Strategy
//!
//! - **Concorde/Business**: Use direct conversion (no JSON)
//! - **Wheelbarrow**: Use JSON serialization with data loss warnings
//!
//! ## Error Handling
//!
//! JSON fallback can fail in several ways:
//! - Serialization failure (should be rare with well-typed data)
//! - Deserialization failure (data doesn't match target schema)
//! - Data loss during narrowing (value out of range for target type)

use protocol_squisher_compat::{EphapaxCompatibilityEngine, SchemaCompatibilityResult};
use protocol_squisher_ir::IrSchema;
use protocol_squisher_transport_primitives::TransportClass;

/// Configuration for ephapax-aware JSON fallback
#[derive(Debug, Clone)]
pub struct EphapaxFallbackConfig {
    /// Module name for generated code
    pub module_name: String,
    /// Whether to add data loss warnings in generated code
    pub add_warnings: bool,
    /// Whether to validate data after deserialization
    pub validate: bool,
    /// Whether to pretty-print JSON (slower but debuggable)
    pub pretty_json: bool,
}

impl Default for EphapaxFallbackConfig {
    fn default() -> Self {
        Self {
            module_name: "fallback".to_string(),
            add_warnings: true,
            validate: true,
            pretty_json: false,
        }
    }
}

impl EphapaxFallbackConfig {
    pub fn new(module_name: impl Into<String>) -> Self {
        Self {
            module_name: module_name.into(),
            ..Default::default()
        }
    }
}

/// Result of ephapax-aware fallback generation
#[derive(Debug, Clone)]
pub struct EphapaxFallbackResult {
    /// Rust conversion code
    pub rust_code: String,
    /// Python conversion code
    pub python_code: String,
    /// Compatibility analysis
    pub analysis: SchemaCompatibilityResult,
    /// Statistics about fallback usage
    pub stats: FallbackStats,
}

/// Statistics about JSON fallback usage
#[derive(Debug, Clone)]
pub struct FallbackStats {
    /// Total number of fields
    pub total_fields: usize,
    /// Number of fields using direct conversion (Concorde/Business)
    pub direct_fields: usize,
    /// Number of fields using JSON fallback (Wheelbarrow)
    pub json_fallback_fields: usize,
    /// Percentage of fields using JSON fallback
    pub fallback_percentage: f64,
}

/// Ephapax-aware JSON fallback generator
pub struct EphapaxFallbackGenerator {
    /// Compatibility engine for transport class analysis
    engine: EphapaxCompatibilityEngine,
    /// Configuration
    config: EphapaxFallbackConfig,
}

impl Default for EphapaxFallbackGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl EphapaxFallbackGenerator {
    /// Create a new ephapax-aware fallback generator
    pub fn new() -> Self {
        Self {
            engine: EphapaxCompatibilityEngine::new(),
            config: EphapaxFallbackConfig::default(),
        }
    }

    /// Create a generator with custom configuration
    pub fn with_config(config: EphapaxFallbackConfig) -> Self {
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

    /// Enable/disable data loss warnings
    pub fn with_warnings(mut self, enabled: bool) -> Self {
        self.config.add_warnings = enabled;
        self
    }

    /// Generate optimized JSON fallback code
    ///
    /// Only fields with Wheelbarrow transport class will use JSON serialization.
    /// Concorde and Business fields use direct conversion.
    pub fn generate_fallback(
        &self,
        source_schema: &IrSchema,
        target_schema: &IrSchema,
    ) -> EphapaxFallbackResult {
        // Analyze compatibility using ephapax
        let analysis = self.engine.analyze_schemas(source_schema, target_schema);
        let summary = self.engine.get_conversion_summary(&analysis);

        // Generate Rust conversion code
        let rust_code = self.generate_rust_conversions(&analysis, source_schema, target_schema);

        // Generate Python conversion code
        let python_code = self.generate_python_conversions(&analysis, source_schema, target_schema);

        let stats = FallbackStats {
            total_fields: summary.total_fields,
            direct_fields: summary.safe_fields,
            json_fallback_fields: summary.json_fallback_fields,
            fallback_percentage: if summary.total_fields > 0 {
                (summary.json_fallback_fields as f64 / summary.total_fields as f64) * 100.0
            } else {
                0.0
            },
        };

        EphapaxFallbackResult {
            rust_code,
            python_code,
            analysis,
            stats,
        }
    }

    fn generate_rust_conversions(
        &self,
        analysis: &SchemaCompatibilityResult,
        source_schema: &IrSchema,
        target_schema: &IrSchema,
    ) -> String {
        let mut code = String::new();

        // Header
        code.push_str(
            "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
             // Auto-generated JSON fallback conversions\n\
             // DO NOT EDIT - regenerate using protocol-squisher\n\n\
             use serde::{Serialize, Deserialize};\n\
             use serde_json::{self, Value};\n\n",
        );

        // Add fallback statistics comment
        if self.config.add_warnings {
            code.push_str(&format!(
                "// Fallback Statistics:\n\
                 // - Total fields: {}\n\
                 // - Direct conversion: {}\n\
                 // - JSON fallback: {} ({}%)\n\n",
                analysis
                    .type_analyses
                    .iter()
                    .map(|t| t.field_analyses.len())
                    .sum::<usize>(),
                analysis
                    .type_analyses
                    .iter()
                    .flat_map(|t| &t.field_analyses)
                    .filter(|f| !matches!(f.class, TransportClass::Wheelbarrow))
                    .count(),
                analysis
                    .type_analyses
                    .iter()
                    .flat_map(|t| &t.field_analyses)
                    .filter(|f| matches!(f.class, TransportClass::Wheelbarrow))
                    .count(),
                if !analysis.type_analyses.is_empty() {
                    let total: usize = analysis
                        .type_analyses
                        .iter()
                        .map(|t| t.field_analyses.len())
                        .sum();
                    let json: usize = analysis
                        .type_analyses
                        .iter()
                        .flat_map(|t| &t.field_analyses)
                        .filter(|f| matches!(f.class, TransportClass::Wheelbarrow))
                        .count();
                    if total > 0 {
                        (json as f64 / total as f64) * 100.0
                    } else {
                        0.0
                    }
                } else {
                    0.0
                }
            ));
        }

        // Generate conversion trait
        code.push_str("/// Conversion with JSON fallback for Wheelbarrow-class fields\n");
        code.push_str(&format!(
            "pub trait {}Conversion {{\n    fn to_{}(&self) -> Result<{}, ConversionError>;\n}}\n\n",
            source_schema.name, target_schema.name, target_schema.name
        ));

        // Generate error type
        code.push_str(&self.generate_error_type());

        // Generate conversion implementations
        for type_analysis in &analysis.type_analyses {
            code.push_str(&self.generate_type_conversion_impl(type_analysis));
        }

        code
    }

    fn generate_error_type(&self) -> String {
        r#"/// Errors that can occur during JSON fallback conversion
#[derive(Debug, Clone)]
pub enum ConversionError {
    /// JSON serialization failed
    SerializationError(String),
    /// JSON deserialization failed
    DeserializationError(String),
    /// Data loss during narrowing conversion
    DataLoss { field: String, reason: String },
    /// Validation failed
    ValidationError(String),
}

impl std::fmt::Display for ConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConversionError::SerializationError(msg) => write!(f, "Serialization error: {}", msg),
            ConversionError::DeserializationError(msg) => write!(f, "Deserialization error: {}", msg),
            ConversionError::DataLoss { field, reason } => write!(f, "Data loss in field '{}': {}", field, reason),
            ConversionError::ValidationError(msg) => write!(f, "Validation error: {}", msg),
        }
    }
}

impl std::error::Error for ConversionError {}

"#.to_string()
    }

    fn generate_type_conversion_impl(
        &self,
        type_analysis: &protocol_squisher_compat::TypeCompatibilityAnalysis,
    ) -> String {
        let mut code = String::new();

        code.push_str(&format!(
            "// Type: {} - Transport class: {:?}\n",
            type_analysis.type_name, type_analysis.class
        ));

        code.push_str(&format!(
            "impl {}Conversion for {} {{\n    fn to_{}(&self) -> Result<{}, ConversionError> {{\n",
            type_analysis.type_name,
            type_analysis.type_name,
            type_analysis.type_name,
            type_analysis.type_name
        ));

        // Generate field conversions
        let has_json_fallback = type_analysis
            .field_analyses
            .iter()
            .any(|f| matches!(f.class, TransportClass::Wheelbarrow));

        if has_json_fallback {
            // Mixed conversion: some fields direct, some JSON
            code.push_str("        // Mixed conversion strategy\n");
            code.push_str(&format!("        Ok({} {{\n", type_analysis.type_name));

            for field in &type_analysis.field_analyses {
                match field.class {
                    TransportClass::Concorde | TransportClass::Business => {
                        // Direct field copy
                        code.push_str(&format!(
                            "            {}: self.{}, // Direct ({})\n",
                            field.field_name,
                            field.field_name,
                            if matches!(field.class, TransportClass::Concorde) {
                                "Concorde"
                            } else {
                                "Business"
                            }
                        ));
                    },
                    TransportClass::Wheelbarrow => {
                        // JSON fallback with warning
                        if self.config.add_warnings {
                            code.push_str(
                                "            // WARNING: JSON fallback (potential data loss)\n",
                            );
                        }
                        code.push_str(&format!(
                            "            {}: serde_json::from_value(\n                serde_json::to_value(&self.{}).map_err(|e| ConversionError::SerializationError(e.to_string()))?\n            ).map_err(|e| ConversionError::DeserializationError(e.to_string()))?,\n",
                            field.field_name, field.field_name
                        ));
                    },
                    TransportClass::Economy => {
                        // Conversion with possible data loss
                        code.push_str(&format!(
                            "            {}: self.{}, // Economy (documented losses)\n",
                            field.field_name, field.field_name
                        ));
                    },
                }
            }

            code.push_str("        })\n");
        } else {
            // All direct conversion (no JSON needed)
            code.push_str("        // All fields use direct conversion\n");
            code.push_str(&format!("        Ok({} {{\n", type_analysis.type_name));
            for field in &type_analysis.field_analyses {
                code.push_str(&format!(
                    "            {}: self.{},\n",
                    field.field_name, field.field_name
                ));
            }
            code.push_str("        })\n");
        }

        code.push_str("    }\n}\n\n");
        code
    }

    fn generate_python_conversions(
        &self,
        analysis: &SchemaCompatibilityResult,
        _source_schema: &IrSchema,
        _target_schema: &IrSchema,
    ) -> String {
        let mut code = String::new();

        // Header
        code.push_str("# SPDX-License-Identifier: PMPL-1.0-or-later\n");
        code.push_str("# Auto-generated JSON fallback conversions\n");
        code.push_str("# DO NOT EDIT - regenerate using protocol-squisher\n\n");
        code.push_str("import json\nfrom typing import Any, Dict\n\n");

        // Add statistics
        if self.config.add_warnings {
            let total: usize = analysis
                .type_analyses
                .iter()
                .map(|t| t.field_analyses.len())
                .sum();
            let json_count: usize = analysis
                .type_analyses
                .iter()
                .flat_map(|t| &t.field_analyses)
                .filter(|f| matches!(f.class, TransportClass::Wheelbarrow))
                .count();
            code.push_str(&format!(
                "# Fallback Statistics:\n\
                 # - Total fields: {}\n\
                 # - JSON fallback: {} ({}%)\n\n",
                total,
                json_count,
                if total > 0 {
                    (json_count as f64 / total as f64) * 100.0
                } else {
                    0.0
                }
            ));
        }

        // Generate conversion functions for each type
        for type_analysis in &analysis.type_analyses {
            code.push_str(&format!(
                "def convert_{}(source: Dict[str, Any]) -> Dict[str, Any]:\n    \"\"\"Convert {} using transport-class-optimized strategy\"\"\"\n    result = {{}}\n",
                type_analysis.type_name.to_lowercase(),
                type_analysis.type_name
            ));

            for field in &type_analysis.field_analyses {
                match field.class {
                    TransportClass::Concorde | TransportClass::Business => {
                        code.push_str(&format!(
                            "    result['{}'] = source['{}']  # Direct\n",
                            field.field_name, field.field_name
                        ));
                    },
                    TransportClass::Wheelbarrow => {
                        if self.config.add_warnings {
                            code.push_str("    # WARNING: JSON fallback (potential data loss)\n");
                        }
                        code.push_str(&format!(
                            "    result['{}'] = json.loads(json.dumps(source['{}']))\n",
                            field.field_name, field.field_name
                        ));
                    },
                    TransportClass::Economy => {
                        code.push_str(&format!(
                            "    result['{}'] = source['{}']  # Economy\n",
                            field.field_name, field.field_name
                        ));
                    },
                }
            }

            code.push_str("    return result\n\n");
        }

        code
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{
        FieldDef, FieldMetadata, IrType, PrimitiveType, StructDef, TypeDef, TypeMetadata,
    };

    fn make_test_schemas() -> (IrSchema, IrSchema) {
        // Source schema with i64
        let mut source = IrSchema::new("source", "test");
        source.add_type(
            "Data".to_string(),
            TypeDef::Struct(StructDef {
                name: "Data".to_string(),
                fields: vec![
                    FieldDef {
                        name: "id".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "count".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        source.add_root("Data".to_string());

        // Target schema with mixed types (i64 and i32)
        let mut target = IrSchema::new("target", "test");
        target.add_type(
            "Data".to_string(),
            TypeDef::Struct(StructDef {
                name: "Data".to_string(),
                fields: vec![
                    FieldDef {
                        name: "id".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "count".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I32), // Narrowing!
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        target.add_root("Data".to_string());

        (source, target)
    }

    #[test]
    fn test_generator_creation() {
        let gen = EphapaxFallbackGenerator::new();
        assert_eq!(gen.config.module_name, "fallback");
    }

    #[test]
    fn test_mixed_conversion() {
        let gen = EphapaxFallbackGenerator::new();
        let (source, target) = make_test_schemas();

        let result = gen.generate_fallback(&source, &target);

        // Should have generated code
        assert!(!result.rust_code.is_empty());
        assert!(!result.python_code.is_empty());

        // Statistics should show mixed conversion
        assert_eq!(result.stats.total_fields, 2);
        assert_eq!(result.stats.direct_fields, 1); // id field (Concorde)
        assert_eq!(result.stats.json_fallback_fields, 1); // count field (Wheelbarrow)
        assert_eq!(result.stats.fallback_percentage, 50.0);

        // Rust code should contain direct and JSON conversions
        assert!(result.rust_code.contains("Direct (Concorde)"));
        assert!(result.rust_code.contains("JSON fallback"));
        assert!(result.rust_code.contains("WARNING"));

        // Python code should contain conversions
        assert!(result.python_code.contains("convert_data"));
        assert!(result.python_code.contains("# Direct"));
        assert!(result.python_code.contains("json.loads(json.dumps"));
    }

    #[test]
    fn test_all_direct_conversion() {
        let gen = EphapaxFallbackGenerator::new();

        // Both schemas identical (all Concorde)
        let mut source = IrSchema::new("source", "test");
        source.add_type(
            "Data".to_string(),
            TypeDef::Struct(StructDef {
                name: "Data".to_string(),
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
        source.add_root("Data".to_string());

        let target = source.clone();

        let result = gen.generate_fallback(&source, &target);

        // Should have zero JSON fallback
        assert_eq!(result.stats.json_fallback_fields, 0);
        assert_eq!(result.stats.fallback_percentage, 0.0);
        assert!(result
            .rust_code
            .contains("All fields use direct conversion"));
    }

    #[test]
    fn test_error_type_generation() {
        let gen = EphapaxFallbackGenerator::new();
        let (source, target) = make_test_schemas();

        let result = gen.generate_fallback(&source, &target);

        // Should have error type
        assert!(result.rust_code.contains("enum ConversionError"));
        assert!(result.rust_code.contains("SerializationError"));
        assert!(result.rust_code.contains("DeserializationError"));
        assert!(result.rust_code.contains("DataLoss"));
    }

    #[test]
    fn test_warnings_toggle() {
        let gen = EphapaxFallbackGenerator::new().with_warnings(false);
        let (source, target) = make_test_schemas();

        let result = gen.generate_fallback(&source, &target);

        // Should not have WARNING comments
        assert!(!result.rust_code.contains("WARNING"));
    }
}
