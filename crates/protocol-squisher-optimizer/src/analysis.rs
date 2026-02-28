// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Schema analysis for optimization opportunities

use crate::{OptimizationLevel, OptimizationResult};
use protocol_squisher_ir::{IrSchema, TypeId};
use std::collections::HashMap;

/// Summary of optimization analysis
#[derive(Debug, Clone)]
pub struct OptimizationSummary {
    /// Total types analyzed
    pub total_types: usize,
    /// Types with zero-copy optimization
    pub zero_copy_count: usize,
    /// Types with direct cast optimization
    pub direct_cast_count: usize,
    /// Types with structural match optimization
    pub structural_match_count: usize,
    /// Types requiring fallback
    pub fallback_count: usize,
    /// Percentage of types optimized (not fallback)
    pub optimization_rate: f64,
}

impl OptimizationSummary {
    /// Create summary from optimization result
    pub fn from_result(result: &OptimizationResult) -> Self {
        let mut zero_copy = 0;
        let mut direct_cast = 0;
        let mut structural = 0;
        let mut fallback = 0;

        for path in result.type_paths.values() {
            match path.level {
                OptimizationLevel::ZeroCopy => zero_copy += 1,
                OptimizationLevel::DirectCast => direct_cast += 1,
                OptimizationLevel::StructuralMatch | OptimizationLevel::ContainerMatch => {
                    structural += 1
                },
                OptimizationLevel::Fallback => fallback += 1,
            }
        }

        let total = result.type_paths.len();
        let optimized = total - fallback;
        let rate = if total > 0 {
            (optimized as f64) / (total as f64) * 100.0
        } else {
            100.0
        };

        Self {
            total_types: total,
            zero_copy_count: zero_copy,
            direct_cast_count: direct_cast,
            structural_match_count: structural,
            fallback_count: fallback,
            optimization_rate: rate,
        }
    }
}

/// Detailed analysis report for a schema pair
#[derive(Debug, Clone)]
pub struct AnalysisReport {
    /// Source schema name
    pub source_name: String,
    /// Target schema name
    pub target_name: String,
    /// Optimization summary
    pub summary: OptimizationSummary,
    /// Per-type optimization details
    pub type_details: HashMap<TypeId, TypeOptimizationDetail>,
    /// Recommendations for improving optimization
    pub recommendations: Vec<String>,
}

/// Optimization details for a single type
#[derive(Debug, Clone)]
pub struct TypeOptimizationDetail {
    /// Type identifier
    pub type_id: TypeId,
    /// Achieved optimization level
    pub level: OptimizationLevel,
    /// Reason for the optimization level
    pub reason: String,
    /// Potential improvements
    pub improvements: Vec<String>,
}

/// Generate analysis report for two schemas
pub fn generate_report(source: &IrSchema, target: &IrSchema) -> AnalysisReport {
    let result = crate::analyze_optimization(source, target);
    let summary = OptimizationSummary::from_result(&result);

    let mut type_details = HashMap::new();
    let mut recommendations = Vec::new();

    for (type_id, path) in &result.type_paths {
        let reason = match path.level {
            OptimizationLevel::ZeroCopy => "Types are identical, no conversion needed".to_string(),
            OptimizationLevel::DirectCast => "Simple type cast available".to_string(),
            OptimizationLevel::StructuralMatch => "Field-by-field conversion possible".to_string(),
            OptimizationLevel::ContainerMatch => {
                "Container element conversion possible".to_string()
            },
            OptimizationLevel::Fallback => "Must use JSON serialization".to_string(),
        };

        let improvements = if path.level == OptimizationLevel::Fallback {
            vec![
                "Ensure field names match between schemas".to_string(),
                "Use compatible primitive types".to_string(),
                "Align enum variant names and payloads".to_string(),
            ]
        } else {
            vec![]
        };

        type_details.insert(
            type_id.clone(),
            TypeOptimizationDetail {
                type_id: type_id.clone(),
                level: path.level,
                reason,
                improvements,
            },
        );
    }

    // Generate recommendations
    if result.fallback_types.len() > result.optimized_types.len() {
        recommendations
            .push("Most types require fallback - consider aligning schema designs".to_string());
    }

    if summary.zero_copy_count == 0 && summary.total_types > 0 {
        recommendations.push(
            "No zero-copy types found - ensure some types have identical definitions".to_string(),
        );
    }

    AnalysisReport {
        source_name: source.name.clone(),
        target_name: target.name.clone(),
        summary,
        type_details,
        recommendations,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::*;

    fn create_matching_schemas() -> (IrSchema, IrSchema) {
        let mut source = IrSchema::new("source", "rust");
        let mut target = IrSchema::new("target", "rust");

        // Identical struct
        let point = TypeDef::Struct(StructDef {
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: IrType::Primitive(PrimitiveType::I32),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: IrType::Primitive(PrimitiveType::I32),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                },
            ],
            metadata: TypeMetadata::default(),
        });

        source.add_type("Point".to_string(), point.clone());
        target.add_type("Point".to_string(), point);

        (source, target)
    }

    #[test]
    fn test_summary_from_result() {
        let (source, target) = create_matching_schemas();
        let result = crate::analyze_optimization(&source, &target);
        let summary = OptimizationSummary::from_result(&result);

        assert_eq!(summary.total_types, 1);
        assert_eq!(summary.zero_copy_count, 1);
        assert_eq!(summary.fallback_count, 0);
        assert_eq!(summary.optimization_rate, 100.0);
    }

    #[test]
    fn test_generate_report() {
        let (source, target) = create_matching_schemas();
        let report = generate_report(&source, &target);

        assert_eq!(report.source_name, "source");
        assert_eq!(report.target_name, "target");
        assert_eq!(report.summary.total_types, 1);
        assert!(report.type_details.contains_key("Point"));
    }
}
