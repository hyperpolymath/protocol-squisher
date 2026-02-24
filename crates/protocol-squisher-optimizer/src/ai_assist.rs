// SPDX-License-Identifier: PMPL-1.0-or-later

use crate::{EmpiricalSynthesisHints, EphapaxOptimizationResult, EphapaxOptimizer};
use protocol_squisher_compat::EphapaxCompatibilityEngine;
use protocol_squisher_ir::IrSchema;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AiAssistedOptimizationSummary {
    pub potential_zero_copy_percentage: f64,
    pub production_ready: bool,
    pub empirical_hints_applied: bool,
    pub recommendation_confidence: f64,
    pub top_suggestions: Vec<String>,
}

pub fn ai_assisted_optimize(
    source: &IrSchema,
    target: &IrSchema,
    hints: Option<EmpiricalSynthesisHints>,
) -> AiAssistedOptimizationSummary {
    let engine = EphapaxCompatibilityEngine::new();
    let optimizer = match hints {
        Some(hints) => EphapaxOptimizer::new(engine).with_empirical_hints(hints),
        None => EphapaxOptimizer::new(engine),
    };

    let result = optimizer.analyze_and_suggest(source, target);
    summarize_result(&result)
}

fn summarize_result(result: &EphapaxOptimizationResult) -> AiAssistedOptimizationSummary {
    let top_suggestions = result
        .suggestions
        .iter()
        .take(5)
        .map(|s| format!("{} ({:.1}%): {}", s.target, s.impact, s.reason))
        .collect::<Vec<_>>();

    // A bounded confidence signal from achieved zero-copy + hint availability.
    let mut confidence = (result.potential_zero_copy_percentage / 100.0).clamp(0.0, 1.0);
    if result.empirical_hints_applied {
        confidence = (confidence + 0.1).clamp(0.0, 1.0);
    }

    AiAssistedOptimizationSummary {
        potential_zero_copy_percentage: result.potential_zero_copy_percentage,
        production_ready: result.would_be_production_ready,
        empirical_hints_applied: result.empirical_hints_applied,
        recommendation_confidence: confidence,
        top_suggestions,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{
        FieldDef, FieldMetadata, IrType, PrimitiveType, StructDef, TypeDef, TypeMetadata,
    };

    fn schema_with_field(name: &str, ty: PrimitiveType) -> IrSchema {
        let mut schema = IrSchema::new(name, "test");
        schema.add_type(
            "Record".to_string(),
            TypeDef::Struct(StructDef {
                name: "Record".to_string(),
                fields: vec![FieldDef {
                    name: "value".to_string(),
                    ty: IrType::Primitive(ty),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
                metadata: TypeMetadata::default(),
            }),
        );
        schema
    }

    #[test]
    fn ai_assist_returns_bounded_confidence() {
        let source = schema_with_field("src", PrimitiveType::I64);
        let target = schema_with_field("dst", PrimitiveType::I32);
        let summary = ai_assisted_optimize(&source, &target, None);

        assert!((0.0..=1.0).contains(&summary.recommendation_confidence));
        assert!(summary.potential_zero_copy_percentage >= 0.0);
    }

    #[test]
    fn ai_assist_reports_hint_usage() {
        let source = schema_with_field("src", PrimitiveType::I64);
        let target = schema_with_field("dst", PrimitiveType::I32);
        let hints = EmpiricalSynthesisHints::default();
        let summary = ai_assisted_optimize(&source, &target, Some(hints));
        assert!(summary.empirical_hints_applied);
    }
}
