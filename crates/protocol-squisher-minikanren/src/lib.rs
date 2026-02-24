// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! miniKanren-style adapter synthesis.
//!
//! This crate models adapter synthesis as a constrained search problem:
//! each field/path gets candidate transformation actions, and the solver picks
//! the best global assignment according to transport-class utility.

use protocol_squisher_compat::{
    compare_schemas, LossKind, SchemaComparison, TransportClass, TypeDefComparison,
};
use protocol_squisher_ir::IrSchema;
use serde::{Deserialize, Serialize};
use std::cmp::Ordering;

/// A synthesis action selected for some schema path.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SynthesisAction {
    ZeroCopy,
    StructuralMap,
    WidenType,
    RelaxOptional,
    Cut,
    Splice,
    Reify,
    JsonFallback,
}

/// A concrete synthesis step in the generated plan.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SynthesisStep {
    pub path: String,
    pub action: SynthesisAction,
    pub class: TransportClass,
    pub rationale: String,
}

/// Result of the synthesis search.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SynthesisPlan {
    pub source_schema: String,
    pub target_schema: String,
    pub satisfiable: bool,
    pub overall_class: TransportClass,
    pub requires_json_fallback: bool,
    pub steps: Vec<SynthesisStep>,
}

#[derive(Debug, Clone)]
struct Candidate {
    action: SynthesisAction,
    class: TransportClass,
    rationale: String,
    utility: i64,
}

#[derive(Debug, Clone)]
struct Goal {
    path: String,
    candidates: Vec<Candidate>,
}

/// Synthesize an adapter plan using a miniKanren-style constrained search.
pub fn synthesize_adapter(source: &IrSchema, target: &IrSchema) -> SynthesisPlan {
    let comparison = compare_schemas(source, target);
    let goals = build_goals(&comparison);
    let selected = solve_best_assignment(&goals);

    let steps: Vec<SynthesisStep> = selected
        .iter()
        .map(|(path, c)| SynthesisStep {
            path: path.clone(),
            action: c.action.clone(),
            class: c.class,
            rationale: c.rationale.clone(),
        })
        .collect();

    let overall_class = steps.iter().fold(TransportClass::Concorde, |acc, step| {
        acc.combine(step.class)
    });

    let requires_json_fallback = steps
        .iter()
        .any(|step| matches!(step.action, SynthesisAction::JsonFallback));

    SynthesisPlan {
        source_schema: source.name.clone(),
        target_schema: target.name.clone(),
        satisfiable: true,
        overall_class,
        requires_json_fallback,
        steps,
    }
}

fn build_goals(comparison: &SchemaComparison) -> Vec<Goal> {
    let mut goals = Vec::new();

    for type_cmp in comparison.type_comparisons.values() {
        build_type_goals(type_cmp, &mut goals);
    }

    // If no concrete field-level work is found, still emit a schema-level goal.
    if goals.is_empty() {
        goals.push(Goal {
            path: format!("{}::{}", comparison.source, comparison.target),
            candidates: vec![Candidate {
                action: SynthesisAction::JsonFallback,
                class: TransportClass::Wheelbarrow,
                rationale: "No explicit comparable fields; defaulting to safe JSON transport."
                    .to_string(),
                utility: utility(TransportClass::Wheelbarrow),
            }],
        });
    }

    goals
}

fn build_type_goals(type_cmp: &TypeDefComparison, goals: &mut Vec<Goal>) {
    for field in &type_cmp.field_comparisons {
        let mut candidates = vec![Candidate {
            action: SynthesisAction::JsonFallback,
            class: TransportClass::Wheelbarrow,
            rationale: "Guaranteed transport fallback through JSON bridge.".to_string(),
            utility: utility(TransportClass::Wheelbarrow),
        }];

        match field.class {
            TransportClass::Concorde => {
                candidates.push(Candidate {
                    action: SynthesisAction::ZeroCopy,
                    class: TransportClass::Concorde,
                    rationale: "Field is structurally identical and zero-copy compatible."
                        .to_string(),
                    utility: utility(TransportClass::Concorde),
                });
            },
            TransportClass::BusinessClass => {
                candidates.push(Candidate {
                    action: SynthesisAction::StructuralMap,
                    class: TransportClass::BusinessClass,
                    rationale: "Field can be losslessly mapped with minor transformation."
                        .to_string(),
                    utility: utility(TransportClass::BusinessClass),
                });
                candidates.push(Candidate {
                    action: SynthesisAction::Splice,
                    class: TransportClass::BusinessClass,
                    rationale:
                        "Splice transformation can reshape records without changing semantics."
                            .to_string(),
                    utility: utility(TransportClass::BusinessClass) + 1,
                });
            },
            TransportClass::Economy => {
                let has_precision_loss = field
                    .losses
                    .iter()
                    .any(|loss| matches!(loss.kind, LossKind::PrecisionLoss | LossKind::RangeLoss));

                if has_precision_loss {
                    candidates.push(Candidate {
                        action: SynthesisAction::WidenType,
                        class: TransportClass::BusinessClass,
                        rationale:
                            "Numeric narrowing detected; widening can lift this path to Business."
                                .to_string(),
                        utility: utility(TransportClass::BusinessClass),
                    });
                }

                candidates.push(Candidate {
                    action: SynthesisAction::StructuralMap,
                    class: TransportClass::Economy,
                    rationale: "Keep existing lossy mapping with explicit documentation."
                        .to_string(),
                    utility: utility(TransportClass::Economy),
                });
                candidates.push(Candidate {
                    action: SynthesisAction::Reify,
                    class: TransportClass::Economy,
                    rationale:
                        "Reify transformation can preserve intent via tagged representation."
                            .to_string(),
                    utility: utility(TransportClass::Economy) - 1,
                });
            },
            TransportClass::Wheelbarrow => {
                let has_missing_field = field
                    .losses
                    .iter()
                    .any(|loss| matches!(loss.kind, LossKind::FieldDropped));

                if has_missing_field {
                    candidates.push(Candidate {
                        action: SynthesisAction::RelaxOptional,
                        class: TransportClass::BusinessClass,
                        rationale:
                            "Missing-field pressure can be reduced by optional/nullable relaxation."
                                .to_string(),
                        utility: utility(TransportClass::BusinessClass),
                    });
                }
                candidates.push(Candidate {
                    action: SynthesisAction::Cut,
                    class: TransportClass::Economy,
                    rationale:
                        "Cut transformation explicitly trims incompatible payload fragments."
                            .to_string(),
                    utility: utility(TransportClass::Economy) - 5,
                });
            },
            TransportClass::Incompatible => {
                candidates.push(Candidate {
                    action: SynthesisAction::Reify,
                    class: TransportClass::Wheelbarrow,
                    rationale:
                        "Reify transformation preserves value meaning in encoded representation."
                            .to_string(),
                    utility: utility(TransportClass::Wheelbarrow) + 1,
                });
            },
        }

        goals.push(Goal {
            path: format!("{}.{}", type_cmp.name, field.name),
            candidates,
        });
    }
}

fn utility(class: TransportClass) -> i64 {
    match class {
        TransportClass::Concorde => 400,
        TransportClass::BusinessClass => 300,
        TransportClass::Economy => 200,
        TransportClass::Wheelbarrow => 100,
        TransportClass::Incompatible => 0,
    }
}

fn solve_best_assignment(goals: &[Goal]) -> Vec<(String, Candidate)> {
    let mut best: Option<(i64, Vec<(String, Candidate)>)> = None;
    let mut current = Vec::with_capacity(goals.len());
    dfs(goals, 0, 0, &mut current, &mut best);
    best.map(|(_, assignment)| assignment).unwrap_or_default()
}

fn dfs(
    goals: &[Goal],
    idx: usize,
    score: i64,
    current: &mut Vec<(String, Candidate)>,
    best: &mut Option<(i64, Vec<(String, Candidate)>)>,
) {
    if idx == goals.len() {
        match best {
            None => *best = Some((score, current.clone())),
            Some((best_score, _)) if score > *best_score => *best = Some((score, current.clone())),
            Some((best_score, best_assignment)) if score == *best_score => {
                if tie_breaker(current, best_assignment) == Ordering::Less {
                    *best = Some((score, current.clone()));
                }
            },
            _ => {},
        }
        return;
    }

    let goal = &goals[idx];
    for candidate in &goal.candidates {
        current.push((goal.path.clone(), candidate.clone()));
        dfs(goals, idx + 1, score + candidate.utility, current, best);
        current.pop();
    }
}

fn tie_breaker(a: &[(String, Candidate)], b: &[(String, Candidate)]) -> Ordering {
    // Prefer assignments with fewer JSON fallback steps.
    let a_fallbacks = a
        .iter()
        .filter(|(_, c)| matches!(c.action, SynthesisAction::JsonFallback))
        .count();
    let b_fallbacks = b
        .iter()
        .filter(|(_, c)| matches!(c.action, SynthesisAction::JsonFallback))
        .count();

    a_fallbacks.cmp(&b_fallbacks)
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{
        FieldDef, FieldMetadata, IrType, PrimitiveType, StructDef, TypeDef, TypeMetadata,
    };

    fn schema_with_field(name: &str, field_ty: PrimitiveType) -> IrSchema {
        let mut schema = IrSchema::new(name, "test");
        schema.add_type(
            "Record".to_string(),
            TypeDef::Struct(StructDef {
                name: "Record".to_string(),
                fields: vec![FieldDef {
                    name: "value".to_string(),
                    ty: IrType::Primitive(field_ty),
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
    fn identical_schemas_choose_zero_copy() {
        let source = schema_with_field("source", PrimitiveType::I64);
        let target = schema_with_field("target", PrimitiveType::I64);
        let plan = synthesize_adapter(&source, &target);

        assert!(plan.satisfiable);
        assert_eq!(plan.overall_class, TransportClass::Concorde);
        assert!(plan
            .steps
            .iter()
            .any(|s| matches!(s.action, SynthesisAction::ZeroCopy)));
    }

    #[test]
    fn narrowing_prefers_widen_type_candidate() {
        let source = schema_with_field("source", PrimitiveType::I64);
        let target = schema_with_field("target", PrimitiveType::I32);
        let plan = synthesize_adapter(&source, &target);

        assert!(plan.satisfiable);
        assert!(plan
            .steps
            .iter()
            .any(|s| matches!(s.action, SynthesisAction::WidenType)));
        assert!(!plan.requires_json_fallback);
    }

    #[test]
    fn incompatible_paths_select_reify_or_fallback() {
        let source = schema_with_field("source", PrimitiveType::String);
        let target = schema_with_field("target", PrimitiveType::Bool);
        let plan = synthesize_adapter(&source, &target);

        assert!(plan.satisfiable);
        assert!(
            plan.requires_json_fallback
                || plan
                    .steps
                    .iter()
                    .any(|s| matches!(s.action, SynthesisAction::Reify))
        );
        assert_eq!(plan.overall_class, TransportClass::Wheelbarrow);
    }
}
