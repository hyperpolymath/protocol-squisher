// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! Compatibility engine powered by ephapax IR
//!
//! This module uses the ephapax IR's proven-correct transport class analysis
//! to determine the best conversion strategy between Rust and Python types.

use protocol_squisher_ephapax_ir::{IRContext, TransportClass as EphapaxTransportClass};
use protocol_squisher_ir::IrSchema;
use protocol_squisher_rust_analyzer::RustAnalyzer;
use protocol_squisher_python_analyzer::PythonAnalyzer;

/// Compatibility engine using ephapax for proven-correct analysis
pub struct EphapaxCompatibilityEngine {
    /// Ephapax IR context for transport class analysis
    ir_ctx: IRContext,
    /// Rust analyzer (reserved for future source-level analysis)
    #[allow(dead_code)]
    rust_analyzer: RustAnalyzer,
    /// Python analyzer (reserved for future source-level analysis)
    #[allow(dead_code)]
    python_analyzer: PythonAnalyzer,
}

impl Default for EphapaxCompatibilityEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl EphapaxCompatibilityEngine {
    /// Create a new ephapax-powered compatibility engine
    pub fn new() -> Self {
        Self {
            ir_ctx: IRContext::new(),
            rust_analyzer: RustAnalyzer::new(),
            python_analyzer: PythonAnalyzer::new(),
        }
    }

    /// Get the IR context for direct access to ephapax analysis
    pub fn ir_context(&self) -> &IRContext {
        &self.ir_ctx
    }

    /// Analyze compatibility between two IR schemas using ephapax
    ///
    /// This uses the ephapax IR to determine transport classes for all
    /// type pairs in the schemas.
    pub fn analyze_schemas(
        &self,
        source: &IrSchema,
        target: &IrSchema,
    ) -> SchemaCompatibilityResult {
        let mut type_analyses = Vec::new();
        let mut overall_class = EphapaxTransportClass::Concorde;

        // Compare all root types
        for source_name in &source.roots {
            if let Some(source_def) = source.types.get(source_name) {
                if let Some(target_def) = target.types.get(source_name) {
                    // Extract primitive types and analyze
                    if let Some(analysis) = self.analyze_type_def(source_def, target_def) {
                        // Track the worst transport class
                        if analysis.class as u8 > overall_class as u8 {
                            overall_class = analysis.class;
                        }
                        type_analyses.push(analysis);
                    }
                }
            }
        }

        SchemaCompatibilityResult {
            source_schema: source.name.clone(),
            target_schema: target.name.clone(),
            overall_class,
            type_analyses,
        }
    }

    /// Analyze a specific type definition pair
    fn analyze_type_def(
        &self,
        source: &protocol_squisher_ir::TypeDef,
        target: &protocol_squisher_ir::TypeDef,
    ) -> Option<TypeCompatibilityAnalysis> {
        use protocol_squisher_ir::TypeDef;

        match (source, target) {
            (TypeDef::Struct(s_struct), TypeDef::Struct(t_struct)) => {
                self.analyze_structs(s_struct, t_struct)
            }
            _ => None, // Other type combinations not yet supported
        }
    }

    /// Analyze struct compatibility
    fn analyze_structs(
        &self,
        source: &protocol_squisher_ir::StructDef,
        target: &protocol_squisher_ir::StructDef,
    ) -> Option<TypeCompatibilityAnalysis> {
        use protocol_squisher_rust_analyzer::to_ephapax_primitive;

        let mut field_analyses = Vec::new();
        let mut worst_class = EphapaxTransportClass::Concorde;

        for source_field in &source.fields {
            // Find matching field in target
            if let Some(target_field) = target.fields.iter().find(|f| f.name == source_field.name) {
                // Try to convert to ephapax primitives
                if let (Some(s_prim), Some(t_prim)) = (
                    to_ephapax_primitive(&source_field.ty),
                    to_ephapax_primitive(&target_field.ty),
                ) {
                    let class = self.ir_ctx.analyze_compatibility(s_prim, t_prim);
                    let fidelity = self.ir_ctx.get_fidelity(class);
                    let overhead = self.ir_ctx.get_overhead(class);

                    // Track worst class
                    if class as u8 > worst_class as u8 {
                        worst_class = class;
                    }

                    field_analyses.push(FieldCompatibility {
                        field_name: source_field.name.clone(),
                        source_type: format!("{:?}", source_field.ty),
                        target_type: format!("{:?}", target_field.ty),
                        class,
                        fidelity,
                        overhead,
                    });
                }
            }
        }

        Some(TypeCompatibilityAnalysis {
            type_name: source.name.clone(),
            class: worst_class,
            field_analyses,
        })
    }

    /// Get a summary of conversion quality
    pub fn get_conversion_summary(
        &self,
        result: &SchemaCompatibilityResult,
    ) -> ConversionSummary {
        let total_fields = result
            .type_analyses
            .iter()
            .map(|t| t.field_analyses.len())
            .sum();

        let zero_copy_fields = result
            .type_analyses
            .iter()
            .flat_map(|t| &t.field_analyses)
            .filter(|f| matches!(f.class, EphapaxTransportClass::Concorde))
            .count();

        let safe_fields = result
            .type_analyses
            .iter()
            .flat_map(|t| &t.field_analyses)
            .filter(|f| {
                matches!(
                    f.class,
                    EphapaxTransportClass::Concorde | EphapaxTransportClass::Business
                )
            })
            .count();

        let json_fallback_fields = result
            .type_analyses
            .iter()
            .flat_map(|t| &t.field_analyses)
            .filter(|f| matches!(f.class, EphapaxTransportClass::Wheelbarrow))
            .count();

        ConversionSummary {
            total_fields,
            zero_copy_fields,
            safe_fields,
            json_fallback_fields,
            overall_class: result.overall_class,
        }
    }
}

/// Result of schema-level compatibility analysis
#[derive(Debug, Clone)]
pub struct SchemaCompatibilityResult {
    pub source_schema: String,
    pub target_schema: String,
    pub overall_class: EphapaxTransportClass,
    pub type_analyses: Vec<TypeCompatibilityAnalysis>,
}

/// Result of type-level compatibility analysis
#[derive(Debug, Clone)]
pub struct TypeCompatibilityAnalysis {
    pub type_name: String,
    pub class: EphapaxTransportClass,
    pub field_analyses: Vec<FieldCompatibility>,
}

/// Field-level compatibility information
#[derive(Debug, Clone)]
pub struct FieldCompatibility {
    pub field_name: String,
    pub source_type: String,
    pub target_type: String,
    pub class: EphapaxTransportClass,
    pub fidelity: u8,
    pub overhead: u8,
}

/// Summary of conversion quality
#[derive(Debug, Clone)]
pub struct ConversionSummary {
    pub total_fields: usize,
    pub zero_copy_fields: usize,
    pub safe_fields: usize,
    pub json_fallback_fields: usize,
    pub overall_class: EphapaxTransportClass,
}

impl ConversionSummary {
    /// Get the percentage of fields that can use zero-copy
    pub fn zero_copy_percentage(&self) -> f64 {
        if self.total_fields == 0 {
            return 100.0;
        }
        (self.zero_copy_fields as f64 / self.total_fields as f64) * 100.0
    }

    /// Get the percentage of fields that are safe (no precision loss)
    pub fn safe_percentage(&self) -> f64 {
        if self.total_fields == 0 {
            return 100.0;
        }
        (self.safe_fields as f64 / self.total_fields as f64) * 100.0
    }

    /// Check if this conversion is production-ready (>90% safe)
    pub fn is_production_ready(&self) -> bool {
        self.safe_percentage() > 90.0
    }

    /// Check if this conversion needs optimization (>20% JSON fallback)
    pub fn needs_optimization(&self) -> bool {
        if self.total_fields == 0 {
            return false;
        }
        let fallback_pct =
            (self.json_fallback_fields as f64 / self.total_fields as f64) * 100.0;
        fallback_pct > 20.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{
        FieldDef, FieldMetadata, IrType, PrimitiveType, StructDef, TypeDef, TypeMetadata,
    };

    fn make_test_schema(name: &str, field_type: PrimitiveType) -> IrSchema {
        let mut schema = IrSchema::new(name, "test");
        schema.add_type(
            "User".to_string(),
            TypeDef::Struct(StructDef {
                name: "User".to_string(),
                fields: vec![FieldDef {
                    name: "id".to_string(),
                    ty: IrType::Primitive(field_type),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
                metadata: TypeMetadata::default(),
            }),
        );
        schema.add_root("User".to_string());
        schema
    }

    #[test]
    fn test_engine_creation() {
        let engine = EphapaxCompatibilityEngine::new();
        assert!(engine.ir_context().analyze_compatibility(
            protocol_squisher_ephapax_ir::PrimitiveType::I32,
            protocol_squisher_ephapax_ir::PrimitiveType::I32
        ) == EphapaxTransportClass::Concorde);
    }

    #[test]
    fn test_zero_copy_detection() {
        let engine = EphapaxCompatibilityEngine::new();
        let source = make_test_schema("rust", PrimitiveType::I64);
        let target = make_test_schema("python", PrimitiveType::I64);

        let result = engine.analyze_schemas(&source, &target);
        assert_eq!(result.overall_class, EphapaxTransportClass::Concorde);

        let summary = engine.get_conversion_summary(&result);
        assert_eq!(summary.zero_copy_fields, 1);
        assert_eq!(summary.zero_copy_percentage(), 100.0);
        assert!(summary.is_production_ready());
    }

    #[test]
    fn test_narrowing_detection() {
        let engine = EphapaxCompatibilityEngine::new();
        let source = make_test_schema("python", PrimitiveType::I64);
        let target = make_test_schema("rust", PrimitiveType::I32);

        let result = engine.analyze_schemas(&source, &target);
        assert_eq!(result.overall_class, EphapaxTransportClass::Wheelbarrow);

        let summary = engine.get_conversion_summary(&result);
        assert_eq!(summary.json_fallback_fields, 1);
        assert!(summary.needs_optimization());
    }

    #[test]
    fn test_conversion_summary() {
        let engine = EphapaxCompatibilityEngine::new();

        // Create schema with mixed field types
        let mut source = IrSchema::new("mixed", "test");
        source.add_type(
            "Mixed".to_string(),
            TypeDef::Struct(StructDef {
                name: "Mixed".to_string(),
                fields: vec![
                    FieldDef {
                        name: "safe".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "unsafe".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        source.add_root("Mixed".to_string());

        let mut target = IrSchema::new("mixed", "test");
        target.add_type(
            "Mixed".to_string(),
            TypeDef::Struct(StructDef {
                name: "Mixed".to_string(),
                fields: vec![
                    FieldDef {
                        name: "safe".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "unsafe".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I32),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        target.add_root("Mixed".to_string());

        let result = engine.analyze_schemas(&source, &target);
        let summary = engine.get_conversion_summary(&result);

        assert_eq!(summary.total_fields, 2);
        assert_eq!(summary.zero_copy_fields, 1);
        assert_eq!(summary.zero_copy_percentage(), 50.0);
    }
}
