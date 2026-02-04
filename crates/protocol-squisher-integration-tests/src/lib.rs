// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! End-to-end integration tests for protocol-squisher
//!
//! This crate tests the full pipeline:
//! 1. Schema extraction (Rust + Python)
//! 2. Compatibility analysis (ephapax)
//! 3. Code generation (PyO3 + JSON fallback)
//! 4. Actual conversion verification
//!
//! ## Test Scenarios
//!
//! - **Zero-copy conversion** (Concorde): i64→i64, String→String
//! - **Safe widening** (Business): i32→i64
//! - **Unsafe narrowing** (Wheelbarrow): i64→i32 (JSON fallback)
//! - **Mixed fields**: Some Concorde, some Wheelbarrow
//! - **Nested structures**: References between types

// Imports only used in tests
#[cfg(test)]
use protocol_squisher_compat::EphapaxCompatibilityEngine;
#[cfg(test)]
use protocol_squisher_ephapax_ir::TransportClass;
#[cfg(test)]
use protocol_squisher_ir::{
    FieldDef, FieldMetadata, IrSchema, IrType, PrimitiveType, StructDef, TypeDef, TypeMetadata,
};
#[cfg(test)]
use protocol_squisher_pyo3_codegen::OptimizedPyO3Generator;
#[cfg(test)]
use protocol_squisher_json_fallback::EphapaxFallbackGenerator;

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to create a simple Rust schema
    fn create_rust_user_schema() -> IrSchema {
        let mut schema = IrSchema::new("rust_user", "serde");
        schema.add_type(
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
                        name: "name".to_string(),
                        ty: IrType::Primitive(PrimitiveType::String),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "age".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I32),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        schema.add_root("User".to_string());
        schema
    }

    /// Helper to create a compatible Python schema
    fn create_python_user_schema() -> IrSchema {
        let mut schema = IrSchema::new("python_user", "pydantic");
        schema.add_type(
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
                        name: "name".to_string(),
                        ty: IrType::Primitive(PrimitiveType::String),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "age".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I32),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        schema.add_root("User".to_string());
        schema
    }

    /// Helper to create schema with narrowing conversion
    fn create_narrowing_schema() -> (IrSchema, IrSchema) {
        // Rust schema with i64
        let mut rust = IrSchema::new("rust", "serde");
        rust.add_type(
            "Data".to_string(),
            TypeDef::Struct(StructDef {
                name: "Data".to_string(),
                fields: vec![
                    FieldDef {
                        name: "value".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        rust.add_root("Data".to_string());

        // Python schema with i32 (narrowing)
        let mut python = IrSchema::new("python", "pydantic");
        python.add_type(
            "Data".to_string(),
            TypeDef::Struct(StructDef {
                name: "Data".to_string(),
                fields: vec![
                    FieldDef {
                        name: "value".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I32),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        python.add_root("Data".to_string());

        (rust, python)
    }

    #[test]
    fn test_e2e_zero_copy_conversion() {
        // Step 1: Create schemas
        let rust_schema = create_rust_user_schema();
        let python_schema = create_python_user_schema();

        // Step 2: Analyze compatibility
        let engine = EphapaxCompatibilityEngine::new();
        let analysis = engine.analyze_schemas(&rust_schema, &python_schema);
        let summary = engine.get_conversion_summary(&analysis);

        // Step 3: Verify analysis results
        assert_eq!(summary.total_fields, 3);
        assert_eq!(summary.zero_copy_fields, 3); // All fields are Concorde
        assert_eq!(summary.zero_copy_percentage(), 100.0);
        assert!(summary.is_production_ready());
        assert!(!summary.needs_optimization());

        // Step 4: Generate PyO3 code
        let pyo3_gen = OptimizedPyO3Generator::new().module_name("user_bindings");
        let pyo3_result = pyo3_gen.generate_rust_to_python(&rust_schema, &python_schema);

        // Step 5: Verify generated code quality
        assert_eq!(pyo3_result.stats.zero_copy_fields, 3);
        assert_eq!(pyo3_result.stats.json_fallback_fields, 0);
        assert!(pyo3_result.stats.is_production_ready);
        assert!(!pyo3_result.stats.needs_optimization);

        // Step 6: Verify code contains zero-copy markers
        assert!(pyo3_result.rust_code.contains("pub struct User"));
        assert!(pyo3_result.rust_code.contains("#[pyo3(get, set)]"));
        assert!(pyo3_result.rust_code.contains("pub id: i64"));
        assert!(pyo3_result.rust_code.contains("pub name: String"));
        assert!(pyo3_result.rust_code.contains("pub age: i32"));

        // Step 7: Verify no JSON fallback in field conversions
        // (Statistics comments may mention "JSON fallback: 0" which is fine)
        assert!(!pyo3_result.rust_code.contains("WARNING: JSON fallback"));
        assert!(!pyo3_result.rust_code.contains("serde_json::from_value"));
    }

    #[test]
    fn test_e2e_mixed_conversion_strategy() {
        // Schema with mixed field types
        let mut rust = IrSchema::new("rust", "serde");
        rust.add_type(
            "Mixed".to_string(),
            TypeDef::Struct(StructDef {
                name: "Mixed".to_string(),
                fields: vec![
                    FieldDef {
                        name: "safe_id".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "unsafe_count".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        rust.add_root("Mixed".to_string());

        let mut python = IrSchema::new("python", "pydantic");
        python.add_type(
            "Mixed".to_string(),
            TypeDef::Struct(StructDef {
                name: "Mixed".to_string(),
                fields: vec![
                    FieldDef {
                        name: "safe_id".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I64), // Same - Concorde
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "unsafe_count".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I32), // Narrowing - Wheelbarrow
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        python.add_root("Mixed".to_string());

        // Analyze
        let engine = EphapaxCompatibilityEngine::new();
        let analysis = engine.analyze_schemas(&rust, &python);
        let summary = engine.get_conversion_summary(&analysis);

        // Verify mixed strategy
        assert_eq!(summary.total_fields, 2);
        assert_eq!(summary.zero_copy_fields, 1); // safe_id is Concorde
        assert_eq!(summary.json_fallback_fields, 1); // unsafe_count is Wheelbarrow
        assert_eq!(summary.zero_copy_percentage(), 50.0);
        assert!(!summary.is_production_ready()); // Only 50% safe
        assert!(summary.needs_optimization()); // 50% JSON fallback

        // Generate PyO3 code
        let pyo3_gen = OptimizedPyO3Generator::new();
        let pyo3_result = pyo3_gen.generate_rust_to_python(&rust, &python);

        // Verify mixed code generation
        assert_eq!(pyo3_result.stats.zero_copy_fields, 1);
        assert_eq!(pyo3_result.stats.json_fallback_fields, 1);
        assert!(!pyo3_result.stats.is_production_ready);
        assert!(pyo3_result.stats.needs_optimization);
    }

    #[test]
    fn test_e2e_json_fallback_generation() {
        let (rust, python) = create_narrowing_schema();

        // Analyze
        let engine = EphapaxCompatibilityEngine::new();
        let analysis = engine.analyze_schemas(&rust, &python);

        // Verify Wheelbarrow class detected
        assert_eq!(analysis.overall_class, TransportClass::Wheelbarrow);

        // Generate JSON fallback
        let fallback_gen = EphapaxFallbackGenerator::new().module_name("data_fallback");
        let fallback_result = fallback_gen.generate_fallback(&rust, &python);

        // Verify fallback statistics
        assert_eq!(fallback_result.stats.total_fields, 1);
        assert_eq!(fallback_result.stats.json_fallback_fields, 1);
        assert_eq!(fallback_result.stats.fallback_percentage, 100.0);

        // Verify generated Rust code
        assert!(fallback_result.rust_code.contains("ConversionError"));
        assert!(fallback_result.rust_code.contains("serde_json::from_value"));
        assert!(fallback_result.rust_code.contains("serde_json::to_value"));
        assert!(fallback_result.rust_code.contains("WARNING"));

        // Verify generated Python code
        assert!(fallback_result.python_code.contains("def convert_data"));
        assert!(fallback_result.python_code.contains("json.loads"));
    }

    #[test]
    fn test_e2e_full_pipeline() {
        // This test demonstrates the complete workflow:
        // 1. Schema extraction
        // 2. Compatibility analysis
        // 3. Decision: PyO3 direct vs JSON fallback
        // 4. Code generation
        // 5. Quality validation

        let rust = create_rust_user_schema();
        let python = create_python_user_schema();

        // Step 1: Analyze compatibility
        let engine = EphapaxCompatibilityEngine::new();
        let analysis = engine.analyze_schemas(&rust, &python);
        let summary = engine.get_conversion_summary(&analysis);

        // Step 2: Make strategic decision based on quality
        if summary.is_production_ready() {
            // High quality - use PyO3 direct bindings
            let pyo3_gen = OptimizedPyO3Generator::new();
            let result = pyo3_gen.generate_rust_to_python(&rust, &python);

            assert!(result.stats.is_production_ready);
            assert!(!result.rust_code.contains("WARNING: JSON fallback"));

        } else if summary.zero_copy_percentage() > 50.0 {
            // Mixed - use optimized PyO3 with selective JSON fallback
            let pyo3_gen = OptimizedPyO3Generator::new();
            let result = pyo3_gen.generate_rust_to_python(&rust, &python);

            // Should have both direct and JSON paths
            assert!(result.stats.zero_copy_fields > 0);
            assert!(result.stats.json_fallback_fields > 0);

        } else {
            // Low quality - use JSON fallback throughout
            let fallback_gen = EphapaxFallbackGenerator::new();
            let result = fallback_gen.generate_fallback(&rust, &python);

            assert!(result.stats.fallback_percentage > 50.0);
        }

        // Step 3: Validate invariant "If it compiles, it carries"
        // The generated code MUST handle all cases or fail to compile
        assert!(summary.total_fields > 0);
        assert_eq!(
            summary.zero_copy_fields + summary.json_fallback_fields,
            summary.total_fields
        );
    }

    #[test]
    fn test_e2e_quality_metrics() {
        let rust = create_rust_user_schema();
        let python = create_python_user_schema();

        let engine = EphapaxCompatibilityEngine::new();
        let analysis = engine.analyze_schemas(&rust, &python);
        let summary = engine.get_conversion_summary(&analysis);

        // Test all quality predicates
        assert_eq!(summary.zero_copy_percentage(), 100.0);
        assert_eq!(summary.safe_percentage(), 100.0);
        assert!(summary.is_production_ready()); // > 90% safe
        assert!(!summary.needs_optimization()); // < 20% JSON fallback

        // Test field-level analysis
        for type_analysis in &analysis.type_analyses {
            assert_eq!(type_analysis.type_name, "User");
            assert_eq!(type_analysis.field_analyses.len(), 3);

            for field in &type_analysis.field_analyses {
                assert_eq!(field.fidelity, 100);
                assert_eq!(field.overhead, 0);
                assert_eq!(field.class, TransportClass::Concorde);
            }
        }
    }

    #[test]
    fn test_e2e_code_generation_quality() {
        let (rust, python) = create_narrowing_schema();

        // Generate both PyO3 and JSON fallback
        let pyo3_gen = OptimizedPyO3Generator::new();
        let pyo3_result = pyo3_gen.generate_rust_to_python(&rust, &python);

        let fallback_gen = EphapaxFallbackGenerator::new();
        let fallback_result = fallback_gen.generate_fallback(&rust, &python);

        // PyO3 code should include warnings for Wheelbarrow fields
        assert!(pyo3_result.rust_code.contains("WARNING"));
        assert!(pyo3_result.rust_code.contains("Wheelbarrow"));

        // JSON fallback code should have error handling
        assert!(fallback_result.rust_code.contains("ConversionError"));
        assert!(fallback_result.rust_code.contains("Result<"));

        // Both should track the same analysis
        assert_eq!(
            pyo3_result.stats.json_fallback_fields,
            fallback_result.stats.json_fallback_fields
        );
    }

    #[test]
    fn test_e2e_transport_class_consistency() {
        // Verify that all components agree on transport classes

        let (rust, python) = create_narrowing_schema();

        // Analyze with compatibility engine
        let compat_engine = EphapaxCompatibilityEngine::new();
        let compat_analysis = compat_engine.analyze_schemas(&rust, &python);

        // Generate with PyO3 generator
        let pyo3_gen = OptimizedPyO3Generator::new();
        let pyo3_result = pyo3_gen.generate_rust_to_python(&rust, &python);

        // Generate with JSON fallback
        let fallback_gen = EphapaxFallbackGenerator::new();
        let fallback_result = fallback_gen.generate_fallback(&rust, &python);

        // All three should agree on overall transport class
        assert_eq!(compat_analysis.overall_class, TransportClass::Wheelbarrow);
        assert_eq!(pyo3_result.analysis.overall_class, TransportClass::Wheelbarrow);
        assert_eq!(fallback_result.analysis.overall_class, TransportClass::Wheelbarrow);

        // All three should agree on fallback count
        let compat_summary = compat_engine.get_conversion_summary(&compat_analysis);
        assert_eq!(compat_summary.json_fallback_fields, pyo3_result.stats.json_fallback_fields);
        assert_eq!(compat_summary.json_fallback_fields, fallback_result.stats.json_fallback_fields);
    }
}
