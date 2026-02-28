// SPDX-License-Identifier: PMPL-1.0-or-later

use protocol_squisher_compat::{
    compare_schemas, LossKind, SchemaComparison, TransportClass, TypeDefComparison,
};
use protocol_squisher_ir::IrSchema;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum MigrationAction {
    Keep,
    StructuralMap,
    WidenType,
    NarrowWithGuard,
    AddOptional,
    DropField,
    JsonFallback,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MigrationStep {
    pub path: String,
    pub action: MigrationAction,
    pub class: TransportClass,
    pub breaking: bool,
    pub rationale: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MigrationPlan {
    pub source_schema: String,
    pub target_schema: String,
    pub overall_class: TransportClass,
    pub breaking_changes: usize,
    pub steps: Vec<MigrationStep>,
}

pub fn plan_migration(source: &IrSchema, target: &IrSchema) -> MigrationPlan {
    let comparison = compare_schemas(source, target);
    let steps = build_steps(&comparison);
    let overall_class = steps.iter().fold(TransportClass::Concorde, |acc, step| {
        acc.combine(step.class)
    });
    let breaking_changes = steps.iter().filter(|step| step.breaking).count();

    MigrationPlan {
        source_schema: source.name.clone(),
        target_schema: target.name.clone(),
        overall_class,
        breaking_changes,
        steps,
    }
}

fn build_steps(comparison: &SchemaComparison) -> Vec<MigrationStep> {
    let mut steps = Vec::new();
    for type_cmp in comparison.type_comparisons.values() {
        build_type_steps(type_cmp, &mut steps);
    }

    if steps.is_empty() {
        steps.push(MigrationStep {
            path: format!("{}::{}", comparison.source, comparison.target),
            action: MigrationAction::Keep,
            class: comparison.class,
            breaking: false,
            rationale: "No explicit field-level deltas detected.".to_string(),
        });
    }

    steps
}

fn build_type_steps(type_cmp: &TypeDefComparison, steps: &mut Vec<MigrationStep>) {
    for loss in &type_cmp.losses {
        if matches!(loss.kind, LossKind::FieldDropped) {
            steps.push(MigrationStep {
                path: loss.path.clone(),
                action: MigrationAction::DropField,
                class: loss.severity.to_transport_class(),
                breaking: true,
                rationale: loss.description.clone(),
            });
        }
    }

    for field in &type_cmp.field_comparisons {
        let path = format!("{}.{}", type_cmp.name, field.name);

        let has_drop = field
            .losses
            .iter()
            .any(|loss| matches!(loss.kind, LossKind::FieldDropped));
        let has_precision = field
            .losses
            .iter()
            .any(|loss| matches!(loss.kind, LossKind::PrecisionLoss | LossKind::RangeLoss));

        let (action, breaking, rationale) = if has_drop {
            (
                MigrationAction::DropField,
                true,
                "Field is not preserved in target schema and would be dropped.".to_string(),
            )
        } else if has_precision {
            match field.class {
                TransportClass::Concorde | TransportClass::BusinessClass => (
                    MigrationAction::WidenType,
                    false,
                    "Use widening cast to preserve value domain where possible.".to_string(),
                ),
                _ => (
                    MigrationAction::NarrowWithGuard,
                    true,
                    "Narrowing conversion requires explicit guard/default strategy.".to_string(),
                ),
            }
        } else {
            match field.class {
                TransportClass::Concorde => (
                    MigrationAction::Keep,
                    false,
                    "Field is structurally identical.".to_string(),
                ),
                TransportClass::BusinessClass => (
                    MigrationAction::StructuralMap,
                    false,
                    "Field maps losslessly with adapter glue.".to_string(),
                ),
                TransportClass::Economy => (
                    MigrationAction::AddOptional,
                    false,
                    "Field may need optional/default handling.".to_string(),
                ),
                TransportClass::Wheelbarrow | TransportClass::Incompatible => (
                    MigrationAction::JsonFallback,
                    true,
                    "Requires fallback transport path to preserve invariant.".to_string(),
                ),
            }
        };

        steps.push(MigrationStep {
            path,
            action,
            class: field.class,
            breaking,
            rationale,
        });
    }
}

/// Risk level for a planned migration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum MigrationRisk {
    /// No breaking changes, identical or widening-only.
    Safe,
    /// Non-breaking but requires attention (structural mapping).
    Warning,
    /// Contains breaking changes that will lose data.
    Breaking,
}

/// Pre-flight validation result for a migration plan.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MigrationValidation {
    /// The assessed risk level.
    pub risk: MigrationRisk,
    /// Specific issues found during validation.
    pub issues: Vec<String>,
    /// Whether the migration can proceed automatically.
    pub auto_migratable: bool,
}

/// A generated rollback plan that reverses a migration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RollbackPlan {
    /// Steps to reverse the forward migration, in order.
    pub steps: Vec<MigrationStep>,
    /// Whether all forward steps are fully reversible.
    pub fully_reversible: bool,
    /// Steps that cannot be reversed (e.g., DropField).
    pub irreversible_steps: Vec<String>,
}

/// Validate a migration plan before execution, assessing risk and
/// automatic migration feasibility.
pub fn validate_migration(plan: &MigrationPlan) -> MigrationValidation {
    let mut issues = Vec::new();

    for step in &plan.steps {
        if step.breaking {
            issues.push(format!(
                "Breaking change at {}: {:?}",
                step.path, step.action
            ));
        }
        if matches!(step.action, MigrationAction::JsonFallback) {
            issues.push(format!(
                "JSON fallback required at {} — performance impact",
                step.path
            ));
        }
    }

    let risk = if plan.breaking_changes > 0 {
        MigrationRisk::Breaking
    } else if plan.steps.iter().any(|s| {
        matches!(
            s.action,
            MigrationAction::NarrowWithGuard | MigrationAction::JsonFallback
        )
    }) {
        MigrationRisk::Warning
    } else {
        MigrationRisk::Safe
    };

    let auto_migratable = plan.breaking_changes == 0
        && !plan
            .steps
            .iter()
            .any(|s| matches!(s.action, MigrationAction::NarrowWithGuard));

    MigrationValidation {
        risk,
        issues,
        auto_migratable,
    }
}

/// Generate a rollback plan that attempts to reverse a forward migration.
pub fn rollback_plan(forward: &MigrationPlan) -> RollbackPlan {
    let mut steps = Vec::new();
    let mut irreversible = Vec::new();

    for step in forward.steps.iter().rev() {
        let (reverse_action, reversible) = match step.action {
            MigrationAction::Keep => (MigrationAction::Keep, true),
            MigrationAction::StructuralMap => (MigrationAction::StructuralMap, true),
            MigrationAction::WidenType => (MigrationAction::NarrowWithGuard, true),
            MigrationAction::NarrowWithGuard => (MigrationAction::WidenType, true),
            MigrationAction::AddOptional => (MigrationAction::DropField, true),
            MigrationAction::DropField => {
                irreversible.push(step.path.clone());
                (MigrationAction::AddOptional, false)
            },
            MigrationAction::JsonFallback => (MigrationAction::JsonFallback, true),
        };

        steps.push(MigrationStep {
            path: step.path.clone(),
            action: reverse_action,
            class: step.class,
            breaking: !reversible,
            rationale: format!("Rollback of {:?}", step.action),
        });
    }

    let fully_reversible = irreversible.is_empty();
    RollbackPlan {
        steps,
        fully_reversible,
        irreversible_steps: irreversible,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{
        FieldDef, FieldMetadata, IrType, PrimitiveType, StructDef, TypeDef, TypeMetadata,
    };

    fn schema_with_fields(name: &str, fields: Vec<(&str, PrimitiveType)>) -> IrSchema {
        let mut schema = IrSchema::new(name, "test");
        schema.add_type(
            "Record".to_string(),
            TypeDef::Struct(StructDef {
                name: "Record".to_string(),
                fields: fields
                    .into_iter()
                    .map(|(field_name, ty)| FieldDef {
                        name: field_name.to_string(),
                        ty: IrType::Primitive(ty),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    })
                    .collect(),
                metadata: TypeMetadata::default(),
            }),
        );
        schema
    }

    #[test]
    fn identical_schema_has_non_breaking_plan() {
        let source = schema_with_fields("source", vec![("id", PrimitiveType::I64)]);
        let target = schema_with_fields("target", vec![("id", PrimitiveType::I64)]);

        let plan = plan_migration(&source, &target);
        assert_eq!(plan.breaking_changes, 0);
        assert!(plan
            .steps
            .iter()
            .any(|step| matches!(step.action, MigrationAction::Keep)));
    }

    #[test]
    fn dropped_field_is_marked_breaking() {
        let source = schema_with_fields(
            "source",
            vec![("id", PrimitiveType::I64), ("legacy", PrimitiveType::I64)],
        );
        let target = schema_with_fields("target", vec![("id", PrimitiveType::I64)]);

        let plan = plan_migration(&source, &target);
        assert!(plan.breaking_changes >= 1);
        assert!(plan
            .steps
            .iter()
            .any(|step| step.breaking && matches!(step.action, MigrationAction::DropField)));
    }

    #[test]
    fn validate_safe_migration() {
        let source = schema_with_fields("source", vec![("id", PrimitiveType::I64)]);
        let target = schema_with_fields("target", vec![("id", PrimitiveType::I64)]);
        let plan = plan_migration(&source, &target);
        let validation = validate_migration(&plan);
        assert_eq!(validation.risk, MigrationRisk::Safe);
        assert!(validation.auto_migratable);
        assert!(validation.issues.is_empty());
    }

    #[test]
    fn validate_breaking_migration() {
        let source = schema_with_fields(
            "source",
            vec![("id", PrimitiveType::I64), ("legacy", PrimitiveType::I32)],
        );
        let target = schema_with_fields("target", vec![("id", PrimitiveType::I64)]);
        let plan = plan_migration(&source, &target);
        let validation = validate_migration(&plan);
        assert_eq!(validation.risk, MigrationRisk::Breaking);
        assert!(!validation.auto_migratable);
        assert!(!validation.issues.is_empty());
    }

    #[test]
    fn rollback_reverses_forward_steps() {
        let plan = MigrationPlan {
            source_schema: "A".to_string(),
            target_schema: "B".to_string(),
            overall_class: TransportClass::BusinessClass,
            breaking_changes: 0,
            steps: vec![MigrationStep {
                path: "Record.id".to_string(),
                action: MigrationAction::WidenType,
                class: TransportClass::BusinessClass,
                breaking: false,
                rationale: "I32 -> I64".to_string(),
            }],
        };

        let rollback = rollback_plan(&plan);
        assert!(rollback.fully_reversible);
        assert!(rollback.irreversible_steps.is_empty());
        assert_eq!(rollback.steps.len(), 1);
        assert_eq!(rollback.steps[0].action, MigrationAction::NarrowWithGuard);
    }

    #[test]
    fn rollback_flags_irreversible_drops() {
        let plan = MigrationPlan {
            source_schema: "A".to_string(),
            target_schema: "B".to_string(),
            overall_class: TransportClass::Wheelbarrow,
            breaking_changes: 1,
            steps: vec![MigrationStep {
                path: "Record.legacy".to_string(),
                action: MigrationAction::DropField,
                class: TransportClass::Wheelbarrow,
                breaking: true,
                rationale: "Dropped field".to_string(),
            }],
        };

        let rollback = rollback_plan(&plan);
        assert!(!rollback.fully_reversible);
        assert_eq!(rollback.irreversible_steps.len(), 1);
        assert_eq!(rollback.irreversible_steps[0], "Record.legacy");
    }
}
