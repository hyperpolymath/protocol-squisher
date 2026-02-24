// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Distributed protocol squishing primitives.

use protocol_squisher_compat::{compare_schemas, TransportClass};
use protocol_squisher_ir::IrSchema;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DistributedSquishTask {
    pub id: String,
    pub source: IrSchema,
    pub target: IrSchema,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DistributedSquishResult {
    pub id: String,
    pub source_schema: String,
    pub target_schema: String,
    pub class: TransportClass,
    pub loss_count: usize,
}

pub fn run_distributed(
    tasks: &[DistributedSquishTask],
    workers: Option<usize>,
) -> Result<Vec<DistributedSquishResult>, String> {
    if tasks.is_empty() {
        return Ok(vec![]);
    }

    let compute = || {
        tasks
            .par_iter()
            .map(|task| {
                let comparison = compare_schemas(&task.source, &task.target);
                DistributedSquishResult {
                    id: task.id.clone(),
                    source_schema: comparison.source,
                    target_schema: comparison.target,
                    class: comparison.class,
                    loss_count: comparison.all_losses.len(),
                }
            })
            .collect::<Vec<_>>()
    };

    let mut results = if let Some(workers) = workers {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(workers.max(1))
            .build()
            .map_err(|err| format!("Failed to build rayon thread pool: {err}"))?;
        pool.install(compute)
    } else {
        compute()
    };

    results.sort_by(|a, b| a.id.cmp(&b.id));
    Ok(results)
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{
        FieldDef, FieldMetadata, IrType, PrimitiveType, StructDef, TypeDef, TypeMetadata,
    };

    fn schema_with_field(name: &str, field: PrimitiveType) -> IrSchema {
        let mut schema = IrSchema::new(name, "test");
        schema.add_type(
            "Record".to_string(),
            TypeDef::Struct(StructDef {
                name: "Record".to_string(),
                fields: vec![FieldDef {
                    name: "value".to_string(),
                    ty: IrType::Primitive(field),
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
    fn distributed_run_returns_sorted_results() {
        let task_a = DistributedSquishTask {
            id: "b-task".to_string(),
            source: schema_with_field("source-b", PrimitiveType::I64),
            target: schema_with_field("target-b", PrimitiveType::I64),
        };
        let task_b = DistributedSquishTask {
            id: "a-task".to_string(),
            source: schema_with_field("source-a", PrimitiveType::I64),
            target: schema_with_field("target-a", PrimitiveType::I32),
        };

        let results = run_distributed(&[task_a, task_b], Some(2)).expect("distributed run");
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].id, "a-task");
        assert_eq!(results[1].id, "b-task");
    }
}
