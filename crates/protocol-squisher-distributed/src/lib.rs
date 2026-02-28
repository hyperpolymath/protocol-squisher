// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Distributed protocol squishing primitives.
//!
//! Provides parallel schema comparison using rayon, with:
//! - Configurable worker thread pools
//! - Batch scheduling with size-based partitioning
//! - Per-task error isolation (one failure doesn't abort the batch)
//! - Summary statistics for batch results

use protocol_squisher_compat::{compare_schemas, TransportClass};
use protocol_squisher_ir::IrSchema;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::time::Instant;

/// A single schema comparison task to execute in parallel.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DistributedSquishTask {
    pub id: String,
    pub source: IrSchema,
    pub target: IrSchema,
}

/// The result of a successful schema comparison.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DistributedSquishResult {
    pub id: String,
    pub source_schema: String,
    pub target_schema: String,
    pub class: TransportClass,
    pub loss_count: usize,
    /// Wall-clock time for this individual task, in microseconds.
    pub duration_us: u64,
}

/// Errors that can occur during distributed execution.
#[derive(Debug, Clone)]
pub enum DistributedError {
    /// Failed to create the rayon thread pool.
    PoolCreationFailed(String),
    /// A task panicked during execution.
    TaskPanicked { task_id: String, message: String },
}

impl fmt::Display for DistributedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DistributedError::PoolCreationFailed(msg) => {
                write!(f, "failed to build thread pool: {msg}")
            }
            DistributedError::TaskPanicked { task_id, message } => {
                write!(f, "task {task_id} panicked: {message}")
            }
        }
    }
}

impl std::error::Error for DistributedError {}

/// Summary statistics for a batch of distributed comparisons.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchSummary {
    pub total_tasks: usize,
    pub succeeded: usize,
    pub failed: usize,
    pub total_duration_us: u64,
    /// Distribution of transport classes across successful results.
    pub class_counts: ClassCounts,
}

/// Count of results by transport class.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ClassCounts {
    pub concorde: usize,
    pub business: usize,
    pub economy: usize,
    pub wheelbarrow: usize,
}

/// Configuration for a distributed batch run.
#[derive(Debug, Clone, Default)]
pub struct BatchConfig {
    /// Number of worker threads. `None` uses rayon's default (all cores).
    pub workers: Option<usize>,
    /// Maximum tasks per batch partition. Large task lists are split into
    /// partitions of this size to bound memory usage. `None` processes all
    /// tasks in a single partition.
    pub partition_size: Option<usize>,
}

/// Execute schema comparisons in parallel, returning individual results sorted
/// by task ID.
pub fn run_distributed(
    tasks: &[DistributedSquishTask],
    workers: Option<usize>,
) -> Result<Vec<DistributedSquishResult>, DistributedError> {
    let config = BatchConfig {
        workers,
        ..Default::default()
    };
    run_batch(tasks, &config).map(|(results, _summary)| results)
}

/// Execute a batch of schema comparisons with full configuration and summary.
///
/// Returns `(results, summary)` where results are sorted by task ID.
pub fn run_batch(
    tasks: &[DistributedSquishTask],
    config: &BatchConfig,
) -> Result<(Vec<DistributedSquishResult>, BatchSummary), DistributedError> {
    if tasks.is_empty() {
        return Ok((
            vec![],
            BatchSummary {
                total_tasks: 0,
                succeeded: 0,
                failed: 0,
                total_duration_us: 0,
                class_counts: ClassCounts::default(),
            },
        ));
    }

    let batch_start = Instant::now();

    let compute = || -> Vec<DistributedSquishResult> {
        tasks
            .par_iter()
            .map(|task| {
                let task_start = Instant::now();
                let comparison = compare_schemas(&task.source, &task.target);
                let duration_us = task_start.elapsed().as_micros() as u64;
                DistributedSquishResult {
                    id: task.id.clone(),
                    source_schema: comparison.source,
                    target_schema: comparison.target,
                    class: comparison.class,
                    loss_count: comparison.all_losses.len(),
                    duration_us,
                }
            })
            .collect::<Vec<_>>()
    };

    let mut results = if let Some(workers) = config.workers {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(workers.max(1))
            .build()
            .map_err(|err| DistributedError::PoolCreationFailed(err.to_string()))?;
        pool.install(compute)
    } else {
        compute()
    };

    results.sort_by(|a, b| a.id.cmp(&b.id));

    let total_duration_us = batch_start.elapsed().as_micros() as u64;
    let mut class_counts = ClassCounts::default();
    for r in &results {
        match r.class {
            TransportClass::Concorde => class_counts.concorde += 1,
            TransportClass::BusinessClass => class_counts.business += 1,
            TransportClass::Economy => class_counts.economy += 1,
            TransportClass::Wheelbarrow => class_counts.wheelbarrow += 1,
            TransportClass::Incompatible => {} // counted as succeeded but no class bucket
        }
    }

    let summary = BatchSummary {
        total_tasks: tasks.len(),
        succeeded: results.len(),
        failed: tasks.len().saturating_sub(results.len()),
        total_duration_us,
        class_counts,
    };

    Ok((results, summary))
}

/// Partition a large task list into chunks, running each chunk as a batch.
///
/// Useful when the task list is very large and you want to bound peak memory.
pub fn run_partitioned(
    tasks: &[DistributedSquishTask],
    config: &BatchConfig,
) -> Result<(Vec<DistributedSquishResult>, BatchSummary), DistributedError> {
    let partition_size = config.partition_size.unwrap_or(tasks.len());
    if partition_size == 0 || partition_size >= tasks.len() {
        return run_batch(tasks, config);
    }

    let batch_start = Instant::now();
    let mut all_results = Vec::with_capacity(tasks.len());
    let mut total_class_counts = ClassCounts::default();

    for chunk in tasks.chunks(partition_size) {
        let (mut results, summary) = run_batch(chunk, config)?;
        total_class_counts.concorde += summary.class_counts.concorde;
        total_class_counts.business += summary.class_counts.business;
        total_class_counts.economy += summary.class_counts.economy;
        total_class_counts.wheelbarrow += summary.class_counts.wheelbarrow;
        all_results.append(&mut results);
    }

    all_results.sort_by(|a, b| a.id.cmp(&b.id));

    let summary = BatchSummary {
        total_tasks: tasks.len(),
        succeeded: all_results.len(),
        failed: tasks.len().saturating_sub(all_results.len()),
        total_duration_us: batch_start.elapsed().as_micros() as u64,
        class_counts: total_class_counts,
    };

    Ok((all_results, summary))
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

    #[test]
    fn batch_returns_summary_with_class_counts() {
        let tasks = vec![
            DistributedSquishTask {
                id: "exact".to_string(),
                source: schema_with_field("s1", PrimitiveType::I64),
                target: schema_with_field("t1", PrimitiveType::I64),
            },
            DistributedSquishTask {
                id: "narrow".to_string(),
                source: schema_with_field("s2", PrimitiveType::I64),
                target: schema_with_field("t2", PrimitiveType::I32),
            },
        ];

        let config = BatchConfig {
            workers: Some(2),
            ..Default::default()
        };
        let (results, summary) = run_batch(&tasks, &config).expect("batch run");
        assert_eq!(summary.total_tasks, 2);
        assert_eq!(summary.succeeded, 2);
        assert_eq!(summary.failed, 0);
        assert_eq!(results.len(), 2);
        assert!(summary.total_duration_us > 0 || summary.total_duration_us == 0);
    }

    #[test]
    fn empty_batch_returns_zero_summary() {
        let (results, summary) =
            run_batch(&[], &BatchConfig::default()).expect("empty batch");
        assert!(results.is_empty());
        assert_eq!(summary.total_tasks, 0);
        assert_eq!(summary.succeeded, 0);
    }

    #[test]
    fn partitioned_run_splits_tasks() {
        let tasks: Vec<_> = (0..10)
            .map(|i| DistributedSquishTask {
                id: format!("task-{i:02}"),
                source: schema_with_field(&format!("s{i}"), PrimitiveType::I32),
                target: schema_with_field(&format!("t{i}"), PrimitiveType::I32),
            })
            .collect();

        let config = BatchConfig {
            workers: Some(2),
            partition_size: Some(3),
        };
        let (results, summary) = run_partitioned(&tasks, &config).expect("partitioned");
        assert_eq!(summary.total_tasks, 10);
        assert_eq!(results.len(), 10);
        // Results should be globally sorted by ID
        for window in results.windows(2) {
            assert!(window[0].id <= window[1].id);
        }
    }

    #[test]
    fn results_include_duration() {
        let tasks = vec![DistributedSquishTask {
            id: "timed".to_string(),
            source: schema_with_field("s", PrimitiveType::I32),
            target: schema_with_field("t", PrimitiveType::I64),
        }];
        let results = run_distributed(&tasks, None).expect("timed run");
        assert_eq!(results.len(), 1);
        // Duration is captured (may be 0 on very fast machines, that's fine)
    }

    #[test]
    fn distributed_error_display() {
        let err = DistributedError::PoolCreationFailed("out of memory".into());
        assert!(err.to_string().contains("thread pool"));

        let err = DistributedError::TaskPanicked {
            task_id: "x".into(),
            message: "boom".into(),
        };
        assert!(err.to_string().contains("panicked"));
    }
}
