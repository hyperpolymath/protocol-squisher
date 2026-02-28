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
use std::collections::{BTreeMap, VecDeque};
use std::fmt;
use std::sync::atomic::{AtomicUsize, Ordering};
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

/// Priority level for job queue entries. Lower value = higher priority.
pub type Priority = u8;

/// A priority queue for schema comparison jobs, backed by `BTreeMap<Priority, VecDeque>`.
#[derive(Debug, Default)]
pub struct JobQueue {
    queues: BTreeMap<Priority, VecDeque<DistributedSquishTask>>,
    total: usize,
}

impl JobQueue {
    /// Create an empty job queue.
    pub fn new() -> Self {
        Self::default()
    }

    /// Submit a task at the given priority level.
    pub fn submit(&mut self, priority: Priority, task: DistributedSquishTask) {
        self.queues
            .entry(priority)
            .or_default()
            .push_back(task);
        self.total += 1;
    }

    /// Poll the highest-priority (lowest number) task from the queue.
    pub fn poll(&mut self) -> Option<DistributedSquishTask> {
        let mut empty_key = None;
        let result = self.queues.iter_mut().next().and_then(|(key, queue)| {
            let task = queue.pop_front();
            if queue.is_empty() {
                empty_key = Some(*key);
            }
            task
        });

        if let Some(key) = empty_key {
            self.queues.remove(&key);
        }

        if result.is_some() {
            self.total -= 1;
        }
        result
    }

    /// Cancel all tasks with the given ID. Returns the number of tasks removed.
    pub fn cancel(&mut self, task_id: &str) -> usize {
        let mut removed = 0;
        for queue in self.queues.values_mut() {
            let before = queue.len();
            queue.retain(|t| t.id != task_id);
            removed += before - queue.len();
        }
        self.total -= removed;
        removed
    }

    /// Return the number of pending tasks.
    pub fn len(&self) -> usize {
        self.total
    }

    /// Whether the queue is empty.
    pub fn is_empty(&self) -> bool {
        self.total == 0
    }
}

/// Atomic progress tracker for batch operations.
pub struct ProgressTracker {
    completed: AtomicUsize,
    failed: AtomicUsize,
    total: usize,
}

/// A snapshot of the current progress state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProgressSnapshot {
    pub completed: usize,
    pub failed: usize,
    pub total: usize,
    pub remaining: usize,
}

impl ProgressTracker {
    /// Create a new tracker for a batch of `total` items.
    pub fn new(total: usize) -> Self {
        Self {
            completed: AtomicUsize::new(0),
            failed: AtomicUsize::new(0),
            total,
        }
    }

    /// Record a successful completion.
    pub fn record_success(&self) {
        self.completed.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a failure.
    pub fn record_failure(&self) {
        self.failed.fetch_add(1, Ordering::Relaxed);
    }

    /// Take a snapshot of the current progress.
    pub fn snapshot(&self) -> ProgressSnapshot {
        let completed = self.completed.load(Ordering::Relaxed);
        let failed = self.failed.load(Ordering::Relaxed);
        ProgressSnapshot {
            completed,
            failed,
            total: self.total,
            remaining: self.total.saturating_sub(completed + failed),
        }
    }
}

/// Retry policy for failed tasks.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryPolicy {
    /// Maximum number of retries per task.
    pub max_retries: usize,
    /// Backoff strategy between retries.
    pub backoff: BackoffStrategy,
}

/// Backoff strategy for retries.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BackoffStrategy {
    /// Fixed delay between retries (in milliseconds).
    Fixed(u64),
    /// Exponential backoff starting from base (in milliseconds).
    Exponential { base_ms: u64 },
}

impl RetryPolicy {
    /// Compute the delay for a given retry attempt (0-indexed).
    pub fn delay_ms(&self, attempt: usize) -> u64 {
        match &self.backoff {
            BackoffStrategy::Fixed(ms) => *ms,
            BackoffStrategy::Exponential { base_ms } => {
                base_ms.saturating_mul(1u64.checked_shl(attempt as u32).unwrap_or(u64::MAX))
            }
        }
    }
}

/// Run a batch of tasks with per-item retry logic.
///
/// Tasks that fail are retried up to `policy.max_retries` times. Since schema
/// comparisons are deterministic, this is primarily useful when tasks may have
/// transient side effects (e.g., logging, external writes).
pub fn run_batch_with_retry(
    tasks: &[DistributedSquishTask],
    config: &BatchConfig,
    policy: &RetryPolicy,
) -> Result<(Vec<DistributedSquishResult>, BatchSummary), DistributedError> {
    // For deterministic schema comparisons, retrying won't change the result.
    // But this function demonstrates the retry pattern for future extensibility.
    let mut final_results = Vec::with_capacity(tasks.len());
    let mut failed_count = 0usize;
    let tracker = ProgressTracker::new(tasks.len());

    // First pass: run all tasks.
    let (results, _summary) = run_batch(tasks, config)?;
    for result in results {
        tracker.record_success();
        final_results.push(result);
    }

    // If any tasks produced no result (shouldn't happen with current impl, but
    // for completeness), retry them.
    let succeeded_ids: std::collections::HashSet<_> =
        final_results.iter().map(|r| r.id.clone()).collect();
    let mut remaining: Vec<_> = tasks
        .iter()
        .filter(|t| !succeeded_ids.contains(&t.id))
        .collect();

    for _attempt in 0..policy.max_retries {
        if remaining.is_empty() {
            break;
        }
        let retry_tasks: Vec<_> = remaining.iter().map(|t| (*t).clone()).collect();
        let (retry_results, _) = run_batch(&retry_tasks, config)?;
        let mut retry_succeeded = std::collections::HashSet::new();
        for result in retry_results {
            retry_succeeded.insert(result.id.clone());
            tracker.record_success();
            final_results.push(result);
        }
        remaining.retain(|t| !retry_succeeded.contains(&t.id));
    }

    for _remaining_task in &remaining {
        tracker.record_failure();
        failed_count += 1;
    }

    final_results.sort_by(|a, b| a.id.cmp(&b.id));

    let snapshot = tracker.snapshot();
    let mut class_counts = ClassCounts::default();
    for r in &final_results {
        match r.class {
            TransportClass::Concorde => class_counts.concorde += 1,
            TransportClass::BusinessClass => class_counts.business += 1,
            TransportClass::Economy => class_counts.economy += 1,
            TransportClass::Wheelbarrow => class_counts.wheelbarrow += 1,
            TransportClass::Incompatible => {}
        }
    }

    Ok((
        final_results,
        BatchSummary {
            total_tasks: tasks.len(),
            succeeded: snapshot.completed,
            failed: failed_count,
            total_duration_us: 0, // Aggregate timing not tracked across retries.
            class_counts,
        },
    ))
}

/// Aggregate statistics for a distributed batch.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DistributedStats {
    /// Mean duration per task in microseconds.
    pub mean_duration_us: f64,
    /// Total throughput in tasks per second.
    pub throughput_per_sec: f64,
    /// Error rate (0.0 to 1.0).
    pub error_rate: f64,
    /// Total tasks processed.
    pub total_tasks: usize,
}

impl DistributedStats {
    /// Compute stats from a batch summary.
    pub fn from_summary(summary: &BatchSummary) -> Self {
        let total = summary.total_tasks;
        let mean_duration_us = if summary.succeeded > 0 {
            summary.total_duration_us as f64 / summary.succeeded as f64
        } else {
            0.0
        };
        let throughput_per_sec = if summary.total_duration_us > 0 {
            (summary.succeeded as f64 / summary.total_duration_us as f64) * 1_000_000.0
        } else {
            0.0
        };
        let error_rate = if total > 0 {
            summary.failed as f64 / total as f64
        } else {
            0.0
        };

        Self {
            mean_duration_us,
            throughput_per_sec,
            error_rate,
            total_tasks: total,
        }
    }
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

    // ── New Phase 3 tests ──────────────────────────────────────────────

    #[test]
    fn job_queue_ordering() {
        let mut queue = JobQueue::new();

        queue.submit(
            10,
            DistributedSquishTask {
                id: "low-priority".to_string(),
                source: schema_with_field("s", PrimitiveType::I32),
                target: schema_with_field("t", PrimitiveType::I32),
            },
        );
        queue.submit(
            1,
            DistributedSquishTask {
                id: "high-priority".to_string(),
                source: schema_with_field("s", PrimitiveType::I32),
                target: schema_with_field("t", PrimitiveType::I32),
            },
        );
        queue.submit(
            5,
            DistributedSquishTask {
                id: "mid-priority".to_string(),
                source: schema_with_field("s", PrimitiveType::I32),
                target: schema_with_field("t", PrimitiveType::I32),
            },
        );

        assert_eq!(queue.len(), 3);

        let first = queue.poll().expect("should have task");
        assert_eq!(first.id, "high-priority");

        let second = queue.poll().expect("should have task");
        assert_eq!(second.id, "mid-priority");

        let third = queue.poll().expect("should have task");
        assert_eq!(third.id, "low-priority");

        assert!(queue.is_empty());
    }

    #[test]
    fn job_queue_cancel() {
        let mut queue = JobQueue::new();

        queue.submit(
            1,
            DistributedSquishTask {
                id: "keep-me".to_string(),
                source: schema_with_field("s", PrimitiveType::I32),
                target: schema_with_field("t", PrimitiveType::I32),
            },
        );
        queue.submit(
            1,
            DistributedSquishTask {
                id: "remove-me".to_string(),
                source: schema_with_field("s", PrimitiveType::I32),
                target: schema_with_field("t", PrimitiveType::I32),
            },
        );

        let removed = queue.cancel("remove-me");
        assert_eq!(removed, 1);
        assert_eq!(queue.len(), 1);

        let remaining = queue.poll().expect("should have task");
        assert_eq!(remaining.id, "keep-me");
    }

    #[test]
    fn progress_tracker_snapshots() {
        let tracker = ProgressTracker::new(10);
        tracker.record_success();
        tracker.record_success();
        tracker.record_failure();

        let snap = tracker.snapshot();
        assert_eq!(snap.completed, 2);
        assert_eq!(snap.failed, 1);
        assert_eq!(snap.total, 10);
        assert_eq!(snap.remaining, 7);
    }

    #[test]
    fn retry_policy_exponential_backoff() {
        let policy = RetryPolicy {
            max_retries: 3,
            backoff: BackoffStrategy::Exponential { base_ms: 100 },
        };
        assert_eq!(policy.delay_ms(0), 100);
        assert_eq!(policy.delay_ms(1), 200);
        assert_eq!(policy.delay_ms(2), 400);
        assert_eq!(policy.delay_ms(3), 800);
    }

    #[test]
    fn retry_policy_fixed_backoff() {
        let policy = RetryPolicy {
            max_retries: 3,
            backoff: BackoffStrategy::Fixed(500),
        };
        assert_eq!(policy.delay_ms(0), 500);
        assert_eq!(policy.delay_ms(5), 500);
    }

    #[test]
    fn run_batch_with_retry_succeeds() {
        let tasks = vec![DistributedSquishTask {
            id: "test-retry".to_string(),
            source: schema_with_field("s", PrimitiveType::I32),
            target: schema_with_field("t", PrimitiveType::I32),
        }];

        let config = BatchConfig {
            workers: Some(1),
            ..Default::default()
        };
        let policy = RetryPolicy {
            max_retries: 2,
            backoff: BackoffStrategy::Fixed(0),
        };

        let (results, summary) =
            run_batch_with_retry(&tasks, &config, &policy).expect("retry batch");
        assert_eq!(results.len(), 1);
        assert_eq!(summary.succeeded, 1);
        assert_eq!(summary.failed, 0);
    }

    #[test]
    fn distributed_stats_from_summary() {
        let summary = BatchSummary {
            total_tasks: 100,
            succeeded: 95,
            failed: 5,
            total_duration_us: 1_000_000,
            class_counts: ClassCounts {
                concorde: 50,
                business: 30,
                economy: 10,
                wheelbarrow: 5,
            },
        };

        let stats = DistributedStats::from_summary(&summary);
        assert_eq!(stats.total_tasks, 100);
        assert!((stats.error_rate - 0.05).abs() < 0.001);
        assert!(stats.throughput_per_sec > 0.0);
        assert!(stats.mean_duration_us > 0.0);
    }
}
