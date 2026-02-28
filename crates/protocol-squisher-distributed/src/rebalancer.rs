// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Partition rebalancer for distributed schema comparison workloads.
//!
//! Provides a pure-computation rebalancing algorithm that identifies overloaded
//! and underloaded workers and generates a set of `TaskMove` instructions to
//! equalize the load. The caller is responsible for applying the moves.
//!
//! ## Algorithm
//!
//! 1. Compute the mean pending task count across all workers.
//! 2. Identify workers exceeding `mean * threshold_ratio` as overloaded.
//! 3. Identify workers below `mean / threshold_ratio` as underloaded.
//! 4. Generate moves from overloaded → underloaded until balanced.

use serde::{Deserialize, Serialize};

/// Snapshot of a single worker's current load.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct WorkerLoad {
    /// Unique identifier for the worker.
    pub worker_id: String,
    /// Number of tasks currently pending on this worker.
    pub pending_tasks: usize,
    /// Number of tasks completed by this worker (for context/stats).
    pub completed_tasks: usize,
    /// Average task duration in microseconds (for weighted rebalancing).
    pub avg_duration_us: u64,
}

/// A single task migration instruction.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TaskMove {
    /// ID of the task to move (opaque; assigned by the overloaded worker's queue).
    pub task_id: String,
    /// Worker to move the task from.
    pub from_worker: String,
    /// Worker to move the task to.
    pub to_worker: String,
}

/// The result of a rebalancing computation.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RebalanceDecision {
    /// Set of task moves to apply (empty if already balanced).
    pub moves: Vec<TaskMove>,
}

/// Computes rebalancing decisions for a set of worker loads.
///
/// The `threshold_ratio` controls how far a worker's load must deviate from
/// the mean before it is considered overloaded or underloaded. A ratio of 2.0
/// means a worker must have 2x the mean load to be considered overloaded.
pub struct PartitionRebalancer {
    /// How far from the mean a worker must be to trigger rebalancing.
    pub threshold_ratio: f64,
}

impl PartitionRebalancer {
    /// Create a rebalancer with the given threshold ratio.
    pub fn new(threshold_ratio: f64) -> Self {
        Self { threshold_ratio }
    }

    /// Compute rebalancing moves for the given worker loads.
    ///
    /// This is a pure computation: it returns a set of `TaskMove` instructions
    /// without modifying any state. The caller applies the moves.
    pub fn compute_rebalance(&self, workers: &[WorkerLoad]) -> RebalanceDecision {
        if workers.len() <= 1 {
            return RebalanceDecision { moves: vec![] };
        }

        let total_tasks: usize = workers.iter().map(|w| w.pending_tasks).sum();
        if total_tasks == 0 {
            return RebalanceDecision { moves: vec![] };
        }

        let mean = total_tasks as f64 / workers.len() as f64;
        let overload_threshold = (mean * self.threshold_ratio).ceil() as usize;
        let underload_threshold = (mean / self.threshold_ratio).floor() as usize;

        // Collect overloaded and underloaded workers.
        let mut overloaded: Vec<(usize, usize)> = workers
            .iter()
            .enumerate()
            .filter(|(_, w)| w.pending_tasks > overload_threshold)
            .map(|(i, w)| (i, w.pending_tasks - (mean.ceil() as usize)))
            .collect();

        let mut underloaded: Vec<(usize, usize)> = workers
            .iter()
            .enumerate()
            .filter(|(_, w)| w.pending_tasks <= underload_threshold)
            .map(|(i, w)| (i, (mean.floor() as usize).saturating_sub(w.pending_tasks)))
            .collect();

        let mut moves = Vec::new();
        let mut move_counter = 0usize;

        for (over_idx, excess) in &mut overloaded {
            for (under_idx, capacity) in &mut underloaded {
                if *excess == 0 || *capacity == 0 {
                    continue;
                }

                let to_move = (*excess).min(*capacity);
                for _ in 0..to_move {
                    moves.push(TaskMove {
                        task_id: format!("rebalance-{move_counter}"),
                        from_worker: workers[*over_idx].worker_id.clone(),
                        to_worker: workers[*under_idx].worker_id.clone(),
                    });
                    move_counter += 1;
                }

                *excess -= to_move;
                *capacity -= to_move;
            }
        }

        RebalanceDecision { moves }
    }
}

impl Default for PartitionRebalancer {
    fn default() -> Self {
        Self::new(2.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn worker(id: &str, pending: usize) -> WorkerLoad {
        WorkerLoad {
            worker_id: id.to_string(),
            pending_tasks: pending,
            completed_tasks: 0,
            avg_duration_us: 100,
        }
    }

    #[test]
    fn balanced_no_moves() {
        let rebalancer = PartitionRebalancer::default();
        let workers = vec![worker("w1", 10), worker("w2", 10), worker("w3", 10)];
        let decision = rebalancer.compute_rebalance(&workers);
        assert!(decision.moves.is_empty());
    }

    #[test]
    fn imbalanced_produces_moves() {
        let rebalancer = PartitionRebalancer::new(1.5);
        let workers = vec![worker("w1", 30), worker("w2", 2), worker("w3", 1)];
        let decision = rebalancer.compute_rebalance(&workers);
        assert!(
            !decision.moves.is_empty(),
            "Imbalanced workers should produce moves"
        );
        // All moves should be from w1 to w2 or w3.
        for m in &decision.moves {
            assert_eq!(m.from_worker, "w1");
            assert!(m.to_worker == "w2" || m.to_worker == "w3");
        }
    }

    #[test]
    fn single_worker_no_moves() {
        let rebalancer = PartitionRebalancer::default();
        let workers = vec![worker("w1", 100)];
        let decision = rebalancer.compute_rebalance(&workers);
        assert!(decision.moves.is_empty());
    }

    #[test]
    fn empty_workers_no_moves() {
        let rebalancer = PartitionRebalancer::default();
        let decision = rebalancer.compute_rebalance(&[]);
        assert!(decision.moves.is_empty());
    }

    #[test]
    fn threshold_respected() {
        // With a high threshold (10x), moderate imbalance should not trigger moves.
        let rebalancer = PartitionRebalancer::new(10.0);
        let workers = vec![worker("w1", 15), worker("w2", 5)];
        let decision = rebalancer.compute_rebalance(&workers);
        assert!(
            decision.moves.is_empty(),
            "High threshold should tolerate moderate imbalance"
        );
    }
}
