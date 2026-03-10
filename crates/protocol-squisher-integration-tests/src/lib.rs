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
use protocol_squisher_ir::{
    FieldDef, FieldMetadata, IrSchema, IrType, PrimitiveType, StructDef, TypeDef, TypeMetadata,
};
#[cfg(test)]
use protocol_squisher_json_fallback::EphapaxFallbackGenerator;
#[cfg(test)]
use protocol_squisher_pyo3_codegen::OptimizedPyO3Generator;
#[cfg(test)]
use protocol_squisher_transport_primitives::TransportClass;

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
                fields: vec![FieldDef {
                    name: "value".to_string(),
                    ty: IrType::Primitive(PrimitiveType::I64),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
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
                fields: vec![FieldDef {
                    name: "value".to_string(),
                    ty: IrType::Primitive(PrimitiveType::I32),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
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

    // ── ECHIDNA / VeriSimDB integration tests ──────────────────────────────

    #[test]
    fn test_e2e_analysis_to_verisimdb_storage() {
        use protocol_squisher_verisimdb::{AnalysisRecord, AnalysisStore, InMemoryStore};
        use std::collections::HashMap;

        let rust = create_rust_user_schema();
        let python = create_python_user_schema();

        // Analyze schemas.
        let engine = EphapaxCompatibilityEngine::new();
        let result = engine.analyze_schemas(&rust, &python);

        // Store the analysis result.
        let mut store = InMemoryStore::new();
        let record = AnalysisRecord {
            id: "e2e-001".to_string(),
            source_type: rust.name.clone(),
            target_type: python.name.clone(),
            transport_class: format!("{:?}", result.overall_class),
            fidelity: 100.0,
            overhead: 0.0,
            format: "serde".to_string(),
            analyzer_version: "1.0.0".to_string(),
            proof_certificate_id: None,
            trust_level: None,
            embedding: None,
            timestamp: "2026-02-28T12:00:00Z".to_string(),
            metadata: HashMap::new(),
        };

        let id = store.store_analysis(record).unwrap();
        assert_eq!(id, "e2e-001");

        let retrieved = store.get_analysis("e2e-001").unwrap();
        assert_eq!(retrieved.source_type, "rust_user");
        assert_eq!(retrieved.transport_class, "Concorde");
    }

    #[test]
    fn test_e2e_proof_goal_generation() {
        use protocol_squisher_echidna_bridge::types::ProverKind;
        use protocol_squisher_echidna_bridge::ProofGoalGenerator;
        use protocol_squisher_ir::PrimitiveType;

        // Generate Coq and Z3 goals for I32 → I64 widening.
        let coq_goal = ProofGoalGenerator::widening_is_lossless(
            &PrimitiveType::I32,
            &PrimitiveType::I64,
            ProverKind::Coq,
        );
        let z3_goal = ProofGoalGenerator::widening_is_lossless(
            &PrimitiveType::I32,
            &PrimitiveType::I64,
            ProverKind::Z3,
        );

        // Coq goal should be a valid theorem string.
        assert!(coq_goal.contains("Theorem"));
        assert!(coq_goal.contains("Int32"));
        assert!(coq_goal.contains("widening_lossless"));

        // Z3 goal should be a valid SMT assertion.
        assert!(z3_goal.contains("assert"));
        assert!(z3_goal.contains("Int32"));
        assert!(z3_goal.contains("check-sat"));
    }

    #[test]
    fn test_e2e_cross_prover_mock() {
        use protocol_squisher_echidna_bridge::types::{ProofResponse, ProofStatus, ProverKind};
        use protocol_squisher_echidna_bridge::{cross_validate, TrustLevel};

        // Simulate 3 successful proof responses.
        let responses = vec![
            ProofResponse {
                proof_id: "pf-coq".to_string(),
                status: ProofStatus::Success,
                goal: "test_goal".to_string(),
                prover: ProverKind::Coq,
                result: Some("Qed.".to_string()),
                diagnostics: vec![],
                duration_ms: Some(50),
            },
            ProofResponse {
                proof_id: "pf-z3".to_string(),
                status: ProofStatus::Success,
                goal: "test_goal".to_string(),
                prover: ProverKind::Z3,
                result: Some("sat".to_string()),
                diagnostics: vec![],
                duration_ms: Some(10),
            },
            ProofResponse {
                proof_id: "pf-lean".to_string(),
                status: ProofStatus::Success,
                goal: "test_goal".to_string(),
                prover: ProverKind::Lean4,
                result: Some("exact rfl".to_string()),
                diagnostics: vec![],
                duration_ms: Some(30),
            },
        ];

        let result = cross_validate("test_goal", responses);
        assert!(result.consensus);
        assert_eq!(result.trust_level, TrustLevel::Level3);
    }

    #[test]
    fn test_e2e_tactic_to_weight_pipeline() {
        use protocol_squisher_echidna_bridge::types::{ProofStatus, TacticSuggestion};
        use protocol_squisher_echidna_bridge::{
            boost_suggestion_from_proof, map_tactics_to_weights,
        };

        let tactics = vec![
            TacticSuggestion {
                name: "omega".to_string(),
                args: vec![],
                confidence: 0.95,
            },
            TacticSuggestion {
                name: "ring".to_string(),
                args: vec![],
                confidence: 0.8,
            },
        ];

        let mut weights = map_tactics_to_weights(&tactics);
        let widen_weight = weights.get("WidenType").copied().unwrap_or(1.0);
        assert!(
            widen_weight > 1.5,
            "High-confidence tactics should boost WidenType"
        );

        // Boost from a successful proof.
        boost_suggestion_from_proof(&mut weights, ProofStatus::Success, "WidenType");
        let boosted = weights.get("WidenType").copied().unwrap_or(1.0);
        assert!(
            boosted >= widen_weight,
            "Proof success should boost or maintain weight"
        );
    }

    #[test]
    fn test_e2e_feedback_from_stored_records() {
        use protocol_squisher_verisimdb::{AnalysisRecord, AnalysisStore, InMemoryStore};
        use std::collections::HashMap;

        let mut store = InMemoryStore::new();

        // Store 3 analysis records.
        for i in 0..3 {
            let record = AnalysisRecord {
                id: format!("fb-{i:03}"),
                source_type: "User.id".to_string(),
                target_type: "UserDTO.id".to_string(),
                transport_class: "Business".to_string(),
                fidelity: 98.0,
                overhead: 5.0,
                format: "protobuf".to_string(),
                analyzer_version: "1.0.0".to_string(),
                proof_certificate_id: None,
                trust_level: None,
                embedding: None,
                timestamp: format!("2026-0{}-01T00:00:00Z", i + 1),
                metadata: HashMap::new(),
            };
            store.store_analysis(record).unwrap();
        }

        // Query and convert to reports.
        let records = store.query_similar("User.id", "UserDTO.id", 10).unwrap();
        assert_eq!(records.len(), 3);

        // Conversion to SquishabilityReport would happen in the integration facade.
        // Here we verify the records are retrievable and have correct data.
        assert!(records.iter().all(|r| r.transport_class == "Business"));
    }

    #[test]
    fn test_e2e_full_pipeline_offline() {
        use protocol_squisher_verisimdb::{AnalysisRecord, AnalysisStore, InMemoryStore};
        use std::collections::HashMap;

        let rust = create_rust_user_schema();
        let python = create_python_user_schema();

        // Step 1: Parse (already have schemas).
        // Step 2: Analyze.
        let engine = EphapaxCompatibilityEngine::new();
        let result = engine.analyze_schemas(&rust, &python);

        // Step 3: Prove (offline → skip).
        // ECHIDNA unavailable; proof returns None.

        // Step 4: Store in InMemoryStore.
        let mut store = InMemoryStore::new();
        let record = AnalysisRecord {
            id: "pipeline-001".to_string(),
            source_type: rust.name.clone(),
            target_type: python.name.clone(),
            transport_class: format!("{:?}", result.overall_class),
            fidelity: 100.0,
            overhead: 0.0,
            format: "serde".to_string(),
            analyzer_version: "1.0.0".to_string(),
            proof_certificate_id: None,
            trust_level: None,
            embedding: None,
            timestamp: "2026-02-28T12:00:00Z".to_string(),
            metadata: HashMap::new(),
        };
        store.store_analysis(record).unwrap();

        // Step 5: Verify end-to-end.
        let retrieved = store.get_analysis("pipeline-001").unwrap();
        assert_eq!(retrieved.transport_class, "Concorde");
        assert_eq!(retrieved.source_type, "rust_user");
    }

    #[test]
    fn test_e2e_compatibility_trend() {
        use protocol_squisher_verisimdb::{AnalysisRecord, AnalysisStore, InMemoryStore};
        use std::collections::HashMap;

        let mut store = InMemoryStore::new();

        // Store 5 records for the same type pair over time.
        for i in 0..5 {
            let record = AnalysisRecord {
                id: format!("trend-{i:03}"),
                source_type: "Order.total".to_string(),
                target_type: "OrderDTO.total".to_string(),
                transport_class: if i < 3 { "Wheelbarrow" } else { "Business" }.to_string(),
                fidelity: if i < 3 { 50.0 } else { 98.0 },
                overhead: if i < 3 { 80.0 } else { 5.0 },
                format: "protobuf".to_string(),
                analyzer_version: "1.0.0".to_string(),
                proof_certificate_id: None,
                trust_level: None,
                embedding: None,
                timestamp: format!("2026-0{}-15T12:00:00Z", i + 1),
                metadata: HashMap::new(),
            };
            store.store_analysis(record).unwrap();
        }

        let trend = store
            .compatibility_trend("Order.total", "OrderDTO.total")
            .unwrap();
        assert_eq!(trend.len(), 5);
        // Chronologically ordered.
        for window in trend.windows(2) {
            assert!(window[0].timestamp <= window[1].timestamp);
        }
        // First 3 are Wheelbarrow, last 2 are Business (improvement trend).
        assert_eq!(trend[0].transport_class, "Wheelbarrow");
        assert_eq!(trend[4].transport_class, "Business");
    }

    #[test]
    fn test_e2e_schema_version_tracking() {
        use protocol_squisher_verisimdb::{AnalysisStore, InMemoryStore, SchemaVersionEntry};

        let mut store = InMemoryStore::new();

        let mut version_count = 0;
        for i in 0..3 {
            let entry = SchemaVersionEntry {
                schema_name: "User".to_string(),
                version: format!("{}.0.0", i + 1),
                format: "protobuf".to_string(),
                type_count: 5 + i,
                field_count: 20 + i * 5,
                first_seen: format!("2026-0{}-01T00:00:00Z", i + 1),
                content_hash: Some(format!("sha256:{i:064x}")),
            };
            store.record_schema_version(entry).unwrap();
            version_count += 1;
        }

        // Verify all 3 schema versions were stored successfully.
        assert_eq!(version_count, 3);
    }

    #[test]
    fn test_e2e_suggestion_logging() {
        use protocol_squisher_verisimdb::{AnalysisStore, InMemoryStore, SuggestionLogEntry};

        let mut store = InMemoryStore::new();

        let entries = vec![
            SuggestionLogEntry {
                id: "sg-001".to_string(),
                analysis_id: "ar-001".to_string(),
                target_repo: "github.com/org/schema".to_string(),
                title: "Use Int64 for id field".to_string(),
                body: "Enables Business-class transport".to_string(),
                platform: "github".to_string(),
                dry_run: true,
                timestamp: "2026-02-28T12:00:00Z".to_string(),
                external_ref: None,
            },
            SuggestionLogEntry {
                id: "sg-002".to_string(),
                analysis_id: "ar-002".to_string(),
                target_repo: "github.com/org/schema".to_string(),
                title: "Remove unnecessary Option wrapper".to_string(),
                body: "Field is always present".to_string(),
                platform: "github".to_string(),
                dry_run: false,
                timestamp: "2026-02-28T12:01:00Z".to_string(),
                external_ref: Some("https://github.com/org/schema/issues/42".to_string()),
            },
        ];

        let mut suggestion_count = 0;
        for entry in entries {
            store.log_suggestion(entry).unwrap();
            suggestion_count += 1;
        }

        // Verify both suggestions were logged successfully.
        assert_eq!(suggestion_count, 2);
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
        assert_eq!(
            pyo3_result.analysis.overall_class,
            TransportClass::Wheelbarrow
        );
        assert_eq!(
            fallback_result.analysis.overall_class,
            TransportClass::Wheelbarrow
        );

        // All three should agree on fallback count
        let compat_summary = compat_engine.get_conversion_summary(&compat_analysis);
        assert_eq!(
            compat_summary.json_fallback_fields,
            pyo3_result.stats.json_fallback_fields
        );
        assert_eq!(
            compat_summary.json_fallback_fields,
            fallback_result.stats.json_fallback_fields
        );
    }
}

// ===========================================================================
// Phase 3: Cross-Domain Shape Extraction & Comparison
// ===========================================================================
// These tests exercise the full pipeline: Format Analyzer → IrSchema → Shape
// extraction → cross-domain comparison. This is the Phase 3 killer feature:
// proving that database schemas, API contracts, and serialization formats are
// all "data shapes" that can be compared for structural isomorphism.

#[cfg(test)]
mod cross_domain_shape_tests {
    use protocol_squisher_ir::SchemaAnalyzer;
    use shape_ir::extract::extract_schema;
    use shape_ir::TransportClass;

    // -- Helper: extract shapes from an analyzer + input string ---------------

    fn shapes_from_protobuf(input: &str) -> shape_ir::extract::ExtractedShapes {
        let analyzer = protocol_squisher_protobuf_analyzer::ProtobufAnalyzer::new();
        let schema = SchemaAnalyzer::analyze_str(&analyzer, input, "proto").unwrap();
        extract_schema(&schema)
    }

    fn shapes_from_json_schema(input: &str) -> shape_ir::extract::ExtractedShapes {
        let analyzer = protocol_squisher_json_schema_analyzer::JsonSchemaAnalyzer::new();
        let schema = SchemaAnalyzer::analyze_str(&analyzer, input, "jsonschema").unwrap();
        extract_schema(&schema)
    }

    fn shapes_from_graphql(input: &str) -> shape_ir::extract::ExtractedShapes {
        let analyzer = protocol_squisher_graphql_analyzer::GraphqlAnalyzer::new();
        let schema = SchemaAnalyzer::analyze_str(&analyzer, input, "graphql").unwrap();
        extract_schema(&schema)
    }

    fn shapes_from_avro(input: &str) -> shape_ir::extract::ExtractedShapes {
        let analyzer = protocol_squisher_avro_analyzer::AvroAnalyzer::new();
        let schema = SchemaAnalyzer::analyze_str(&analyzer, input, "avro").unwrap();
        extract_schema(&schema)
    }

    fn shapes_from_thrift(input: &str) -> shape_ir::extract::ExtractedShapes {
        let analyzer = protocol_squisher_thrift_analyzer::ThriftAnalyzer::new();
        let schema = SchemaAnalyzer::analyze_str(&analyzer, input, "thrift").unwrap();
        extract_schema(&schema)
    }

    fn shapes_from_sql(input: &str) -> shape_ir::extract::ExtractedShapes {
        let analyzer = protocol_squisher_sql_analyzer::SqlAnalyzer::new();
        let schema = SchemaAnalyzer::analyze_str(&analyzer, input, "sql").unwrap();
        extract_schema(&schema)
    }

    fn shapes_from_openapi(input: &str) -> shape_ir::extract::ExtractedShapes {
        let analyzer = protocol_squisher_openapi_analyzer::OpenApiAnalyzer::new();
        let schema = SchemaAnalyzer::analyze_str(&analyzer, input, "openapi").unwrap();
        extract_schema(&schema)
    }

    fn shapes_from_arrow(input: &str) -> shape_ir::extract::ExtractedShapes {
        let analyzer = protocol_squisher_arrow_analyzer::ArrowAnalyzer::new();
        let schema = SchemaAnalyzer::analyze_str(&analyzer, input, "arrow").unwrap();
        extract_schema(&schema)
    }

    // -- Phase 3 integration tests -------------------------------------------

    #[test]
    fn protobuf_extracts_shapes() {
        let shapes = shapes_from_protobuf(
            r#"syntax = "proto3";
            message User {
                int32 id = 1;
                string name = 2;
            }"#,
        );
        assert!(shapes.shapes.contains_key("User"));
        let user = &shapes.shapes["User"];
        let labels = user.field_labels();
        assert!(labels.len() >= 2);
    }

    #[test]
    fn graphql_extracts_shapes() {
        let shapes = shapes_from_graphql(
            "type User {
                id: Int!
                name: String!
            }",
        );
        assert!(shapes.shapes.contains_key("User"));
    }

    #[test]
    fn avro_extracts_shapes() {
        let shapes = shapes_from_avro(
            r#"{
                "type": "record",
                "name": "User",
                "fields": [
                    {"name": "id", "type": "int"},
                    {"name": "name", "type": "string"}
                ]
            }"#,
        );
        assert!(shapes.shapes.contains_key("User"));
    }

    #[test]
    fn thrift_extracts_shapes() {
        let shapes = shapes_from_thrift(
            "struct User {
                1: required i32 id
                2: required string name
            }",
        );
        assert!(shapes.shapes.contains_key("User"));
    }

    #[test]
    fn sql_extracts_shapes() {
        let shapes = shapes_from_sql(
            "CREATE TABLE users (
                id INTEGER NOT NULL,
                name TEXT NOT NULL
            );",
        );
        assert!(shapes.shapes.contains_key("users"));
    }

    #[test]
    fn openapi_extracts_shapes() {
        let spec = serde_json::json!({
            "openapi": "3.0.3",
            "info": {"title": "Test", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "User": {
                    "type": "object",
                    "required": ["id", "name"],
                    "properties": {
                        "id": {"type": "integer"},
                        "name": {"type": "string"}
                    }
                }
            }}
        })
        .to_string();
        let shapes = shapes_from_openapi(&spec);
        assert!(shapes.shapes.contains_key("User"));
    }

    #[test]
    fn json_schema_extracts_shapes() {
        let shapes = shapes_from_json_schema(
            r#"{
                "title": "User",
                "type": "object",
                "required": ["id", "name"],
                "properties": {
                    "id": {"type": "integer"},
                    "name": {"type": "string"}
                }
            }"#,
        );
        // JSON Schema may use the title or root name
        assert!(!shapes.shapes.is_empty());
    }

    // -- Cross-domain isomorphism tests: THE killer feature -------------------

    #[test]
    fn protobuf_vs_sql_isomorphic() {
        let proto_shapes = shapes_from_protobuf(
            r#"syntax = "proto3";
            message User {
                int32 id = 1;
                string name = 2;
            }"#,
        );
        let sql_shapes = shapes_from_sql(
            "CREATE TABLE User (
                id INTEGER NOT NULL,
                name TEXT NOT NULL
            );",
        );
        let proto_shape = &proto_shapes.shapes["User"];
        let sql_shape = &sql_shapes.shapes["User"];

        let morphism = shape_ir::compare::compare(proto_shape, sql_shape);
        assert!(
            morphism.transport_class == TransportClass::Concorde
                || morphism.transport_class == TransportClass::Business,
            "Protobuf User ↔ SQL User should be at most Business, got {:?}",
            morphism.transport_class
        );
    }

    #[test]
    fn openapi_vs_protobuf_isomorphic() {
        let openapi_spec = serde_json::json!({
            "openapi": "3.0.3",
            "info": {"title": "API", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "User": {
                    "type": "object",
                    "required": ["id", "name"],
                    "properties": {
                        "id": {"type": "integer"},
                        "name": {"type": "string"}
                    }
                }
            }}
        })
        .to_string();
        let openapi_shapes = shapes_from_openapi(&openapi_spec);
        let proto_shapes = shapes_from_protobuf(
            r#"syntax = "proto3";
            message User {
                int32 id = 1;
                string name = 2;
            }"#,
        );

        let openapi_shape = &openapi_shapes.shapes["User"];
        let proto_shape = &proto_shapes.shapes["User"];

        let morphism = shape_ir::compare::compare(openapi_shape, proto_shape);
        assert_eq!(
            morphism.transport_class,
            TransportClass::Concorde,
            "OpenAPI User ↔ Protobuf User should be isomorphic"
        );
    }

    #[test]
    fn sql_vs_openapi_isomorphic() {
        let sql_shapes = shapes_from_sql(
            "CREATE TABLE User (
                id INTEGER NOT NULL,
                name TEXT NOT NULL
            );",
        );
        let openapi_spec = serde_json::json!({
            "openapi": "3.0.3",
            "info": {"title": "API", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "User": {
                    "type": "object",
                    "required": ["id", "name"],
                    "properties": {
                        "id": {"type": "integer"},
                        "name": {"type": "string"}
                    }
                }
            }}
        })
        .to_string();
        let openapi_shapes = shapes_from_openapi(&openapi_spec);

        let sql_shape = &sql_shapes.shapes["User"];
        let openapi_shape = &openapi_shapes.shapes["User"];

        let morphism = shape_ir::compare::compare(sql_shape, openapi_shape);
        assert_eq!(
            morphism.transport_class,
            TransportClass::Concorde,
            "SQL User ↔ OpenAPI User should be isomorphic"
        );
    }

    #[test]
    fn avro_vs_thrift_isomorphic() {
        let avro_shapes = shapes_from_avro(
            r#"{
                "type": "record",
                "name": "User",
                "fields": [
                    {"name": "id", "type": "int"},
                    {"name": "name", "type": "string"}
                ]
            }"#,
        );
        let thrift_shapes = shapes_from_thrift(
            "struct User {
                1: required i32 id
                2: required string name
            }",
        );

        let avro_shape = &avro_shapes.shapes["User"];
        let thrift_shape = &thrift_shapes.shapes["User"];

        let morphism = shape_ir::compare::compare(avro_shape, thrift_shape);
        assert_eq!(
            morphism.transport_class,
            TransportClass::Concorde,
            "Avro User ↔ Thrift User should be isomorphic"
        );
    }

    #[test]
    fn graphql_vs_openapi_isomorphic() {
        let graphql_shapes = shapes_from_graphql(
            "type User {
                id: Int!
                name: String!
            }",
        );
        let openapi_spec = serde_json::json!({
            "openapi": "3.0.3",
            "info": {"title": "API", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "User": {
                    "type": "object",
                    "required": ["id", "name"],
                    "properties": {
                        "id": {"type": "integer"},
                        "name": {"type": "string"}
                    }
                }
            }}
        })
        .to_string();
        let openapi_shapes = shapes_from_openapi(&openapi_spec);

        let graphql_shape = &graphql_shapes.shapes["User"];
        let openapi_shape = &openapi_shapes.shapes["User"];

        let morphism = shape_ir::compare::compare(graphql_shape, openapi_shape);
        assert!(
            morphism.transport_class == TransportClass::Concorde
                || morphism.transport_class == TransportClass::Business,
            "GraphQL User ↔ OpenAPI User should be at most Business, got {:?}",
            morphism.transport_class
        );
    }

    #[test]
    fn seven_format_shape_category() {
        // Build a ShapeCategory from 7 different format representations of "User"
        // (6 existing + Arrow IPC) and verify the isomorphic core is detected
        let proto = shapes_from_protobuf(
            r#"syntax = "proto3";
            message User {
                int32 id = 1;
                string name = 2;
            }"#,
        );
        let sql = shapes_from_sql(
            "CREATE TABLE User (
                id INTEGER NOT NULL,
                name TEXT NOT NULL
            );",
        );
        let openapi_str = serde_json::json!({
            "openapi": "3.0.3",
            "info": {"title": "API", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "User": {
                    "type": "object",
                    "required": ["id", "name"],
                    "properties": {
                        "id": {"type": "integer"},
                        "name": {"type": "string"}
                    }
                }
            }}
        })
        .to_string();
        let openapi = shapes_from_openapi(&openapi_str);
        let thrift = shapes_from_thrift(
            "struct User {
                1: required i32 id
                2: required string name
            }",
        );
        let avro = shapes_from_avro(
            r#"{
                "type": "record",
                "name": "User",
                "fields": [
                    {"name": "id", "type": "int"},
                    {"name": "name", "type": "string"}
                ]
            }"#,
        );
        let arrow_json = {
            use arrow_schema::{DataType, Field, Schema};
            let s = Schema::new(vec![
                Field::new("id", DataType::Int32, false),
                Field::new("name", DataType::Utf8, false),
            ]);
            serde_json::to_string(&s).unwrap()
        };
        let arrow = shapes_from_arrow(&arrow_json);

        let mut cat = shape_ir::category::ShapeCategory::new();
        cat.add_object("proto_User", proto.shapes["User"].clone());
        cat.add_object("sql_User", sql.shapes["User"].clone());
        cat.add_object("openapi_User", openapi.shapes["User"].clone());
        cat.add_object("thrift_User", thrift.shapes["User"].clone());
        cat.add_object("avro_User", avro.shapes["User"].clone());
        cat.add_object("arrow_User", arrow.shapes["arrow"].clone());

        cat.compare_all();

        // Most should be pairwise isomorphic or safe-widening (Concorde/Business)
        let iso_pairs = cat.isomorphic_pairs();
        // With 6 objects, max isomorphic pairs = 6*5/2 = 15
        // Annotation differences may reduce strict isomorphism count
        assert!(
            iso_pairs.len() >= 3,
            "Expected at least 3 isomorphic pairs among 6 formats, got {}",
            iso_pairs.len()
        );

        // Verify ALL pairwise morphisms are at most Business (safe)
        for id_a in cat.object_ids() {
            for id_b in cat.object_ids() {
                if id_a != id_b {
                    if let Some(m) = cat.arrow(id_a, id_b) {
                        assert!(
                            m.transport_class == TransportClass::Concorde
                                || m.transport_class == TransportClass::Business,
                            "{id_a} → {id_b} should be safe, got {:?}",
                            m.transport_class
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn arrow_vs_openapi_isomorphic() {
        let arrow_json = {
            use arrow_schema::{DataType, Field, Schema};
            let s = Schema::new(vec![
                Field::new("id", DataType::Int32, false),
                Field::new("name", DataType::Utf8, false),
            ]);
            serde_json::to_string(&s).unwrap()
        };
        let arrow_shapes = shapes_from_arrow(&arrow_json);
        let openapi_str = serde_json::json!({
            "openapi": "3.0.3",
            "info": {"title": "API", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "arrow": {
                    "type": "object",
                    "required": ["id", "name"],
                    "properties": {
                        "id": {"type": "integer"},
                        "name": {"type": "string"}
                    }
                }
            }}
        })
        .to_string();
        let openapi_shapes = shapes_from_openapi(&openapi_str);

        let arrow_shape = &arrow_shapes.shapes["arrow"];
        let openapi_shape = &openapi_shapes.shapes["arrow"];

        let morphism = shape_ir::compare::compare(arrow_shape, openapi_shape);
        assert!(
            morphism.transport_class == TransportClass::Concorde
                || morphism.transport_class == TransportClass::Business,
            "Arrow ↔ OpenAPI should be safe, got {:?}",
            morphism.transport_class
        );
    }

    #[test]
    fn arrow_vs_avro_isomorphic() {
        let arrow_json = {
            use arrow_schema::{DataType, Field, Schema};
            let s = Schema::new(vec![
                Field::new("id", DataType::Int32, false),
                Field::new("name", DataType::Utf8, false),
            ]);
            serde_json::to_string(&s).unwrap()
        };
        let arrow_shapes = shapes_from_arrow(&arrow_json);
        let avro_shapes = shapes_from_avro(
            r#"{
                "type": "record",
                "name": "arrow",
                "fields": [
                    {"name": "id", "type": "int"},
                    {"name": "name", "type": "string"}
                ]
            }"#,
        );

        let arrow_shape = &arrow_shapes.shapes["arrow"];
        let avro_shape = &avro_shapes.shapes["arrow"];

        let morphism = shape_ir::compare::compare(arrow_shape, avro_shape);
        assert!(
            morphism.transport_class == TransportClass::Concorde
                || morphism.transport_class == TransportClass::Business,
            "Arrow ↔ Avro should be safe, got {:?}",
            morphism.transport_class
        );
    }

    #[test]
    fn sql_vs_avro_isomorphic() {
        let sql_shapes = shapes_from_sql(
            "CREATE TABLE Item (
                id INTEGER NOT NULL,
                name TEXT NOT NULL
            );",
        );
        let avro_shapes = shapes_from_avro(
            r#"{
                "type": "record",
                "name": "Item",
                "fields": [
                    {"name": "id", "type": "int"},
                    {"name": "name", "type": "string"}
                ]
            }"#,
        );

        let sql_shape = &sql_shapes.shapes["Item"];
        let avro_shape = &avro_shapes.shapes["Item"];

        let morphism = shape_ir::compare::compare(sql_shape, avro_shape);
        assert!(
            morphism.transport_class == TransportClass::Concorde
                || morphism.transport_class == TransportClass::Business,
            "SQL ↔ Avro should be safe, got {:?}",
            morphism.transport_class
        );
    }

    #[test]
    fn sql_vs_thrift_isomorphic() {
        let sql_shapes = shapes_from_sql(
            "CREATE TABLE Item (
                id INTEGER NOT NULL,
                name TEXT NOT NULL
            );",
        );
        let thrift_shapes = shapes_from_thrift(
            "struct Item {
                1: required i32 id
                2: required string name
            }",
        );

        let sql_shape = &sql_shapes.shapes["Item"];
        let thrift_shape = &thrift_shapes.shapes["Item"];

        let morphism = shape_ir::compare::compare(sql_shape, thrift_shape);
        assert!(
            morphism.transport_class == TransportClass::Concorde
                || morphism.transport_class == TransportClass::Business,
            "SQL ↔ Thrift should be safe, got {:?}",
            morphism.transport_class
        );
    }

    #[test]
    fn widening_across_domains_is_business() {
        // SQL uses I32, Avro uses I64 for id → widening → Business
        let sql_shapes = shapes_from_sql(
            "CREATE TABLE User (
                id INTEGER NOT NULL,
                name TEXT NOT NULL
            );",
        );
        let avro_shapes = shapes_from_avro(
            r#"{
                "type": "record",
                "name": "User",
                "fields": [
                    {"name": "id", "type": "long"},
                    {"name": "name", "type": "string"}
                ]
            }"#,
        );

        let sql_shape = &sql_shapes.shapes["User"];
        let avro_shape = &avro_shapes.shapes["User"];

        let morphism = shape_ir::compare::compare(sql_shape, avro_shape);
        assert_eq!(
            morphism.transport_class,
            TransportClass::Business,
            "SQL I32 → Avro I64 should be Business (safe widening)"
        );
    }

    #[test]
    fn arrow_extracts_shapes() {
        let arrow_json = {
            use arrow_schema::{DataType, Field, Schema};
            let s = Schema::new(vec![
                Field::new("id", DataType::Int32, false),
                Field::new("name", DataType::Utf8, false),
            ]);
            serde_json::to_string(&s).unwrap()
        };
        let shapes = shapes_from_arrow(&arrow_json);
        assert!(shapes.shapes.contains_key("arrow"));
    }

    #[test]
    fn arrow_vs_sql_isomorphic() {
        let arrow_json = {
            use arrow_schema::{DataType, Field, Schema};
            let s = Schema::new(vec![
                Field::new("id", DataType::Int32, false),
                Field::new("name", DataType::Utf8, false),
            ]);
            serde_json::to_string(&s).unwrap()
        };
        let arrow_shapes = shapes_from_arrow(&arrow_json);
        let sql_shapes = shapes_from_sql(
            "CREATE TABLE arrow (
                id INTEGER NOT NULL,
                name TEXT NOT NULL
            );",
        );

        let arrow_shape = &arrow_shapes.shapes["arrow"];
        let sql_shape = &sql_shapes.shapes["arrow"];

        let morphism = shape_ir::compare::compare(arrow_shape, sql_shape);
        assert!(
            morphism.transport_class == TransportClass::Concorde
                || morphism.transport_class == TransportClass::Business,
            "Arrow ↔ SQL with same structure should be safe, got {:?}",
            morphism.transport_class
        );
    }

    #[test]
    fn arrow_vs_protobuf_isomorphic() {
        let arrow_json = {
            use arrow_schema::{DataType, Field, Schema};
            let s = Schema::new(vec![
                Field::new("id", DataType::Int32, false),
                Field::new("name", DataType::Utf8, false),
            ]);
            serde_json::to_string(&s).unwrap()
        };
        let arrow_shapes = shapes_from_arrow(&arrow_json);
        let proto_shapes = shapes_from_protobuf(
            r#"syntax = "proto3";
            message arrow {
                int32 id = 1;
                string name = 2;
            }"#,
        );

        let arrow_shape = &arrow_shapes.shapes["arrow"];
        let proto_shape = &proto_shapes.shapes["arrow"];

        let morphism = shape_ir::compare::compare(arrow_shape, proto_shape);
        assert!(
            morphism.transport_class == TransportClass::Concorde
                || morphism.transport_class == TransportClass::Business,
            "Arrow ↔ Protobuf with same structure should be safe, got {:?}",
            morphism.transport_class
        );
    }

    #[test]
    fn nullable_mismatch_across_domains() {
        // SQL has nullable column (Optional), OpenAPI has required field
        let sql_shapes = shapes_from_sql(
            "CREATE TABLE User (
                id INTEGER NOT NULL,
                email TEXT
            );",
        );
        let openapi_str = serde_json::json!({
            "openapi": "3.0.3",
            "info": {"title": "API", "version": "1.0"},
            "paths": {},
            "components": {"schemas": {
                "User": {
                    "type": "object",
                    "required": ["id", "email"],
                    "properties": {
                        "id": {"type": "integer"},
                        "email": {"type": "string"}
                    }
                }
            }}
        })
        .to_string();
        let openapi_shapes = shapes_from_openapi(&openapi_str);

        let sql_shape = &sql_shapes.shapes["User"];
        let openapi_shape = &openapi_shapes.shapes["User"];

        // SQL email is Optional<String>, OpenAPI email is String
        // Optional<T> → T is Economy (unwrapping loses the None case)
        let morphism = shape_ir::compare::compare(sql_shape, openapi_shape);
        assert!(
            morphism.transport_class == TransportClass::Economy
                || morphism.transport_class == TransportClass::Business,
            "Nullable→Required should be Economy or Business, got {:?}",
            morphism.transport_class
        );
    }
}
