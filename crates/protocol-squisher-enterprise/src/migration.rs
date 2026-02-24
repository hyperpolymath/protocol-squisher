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
}
