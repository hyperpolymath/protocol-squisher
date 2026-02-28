// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Checkpoint-based recovery for long-running batch analysis jobs.
//!
//! When a distributed batch job is interrupted (crash, timeout, user cancel),
//! `AnalysisCheckpoint` preserves the progress so the job can resume from
//! where it left off rather than restarting from scratch.

use serde::{Deserialize, Serialize};
use std::path::Path;

/// A checkpoint snapshot of a batch analysis job's progress.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AnalysisCheckpoint {
    /// Unique identifier for this job.
    pub job_id: String,
    /// Total number of type pairs to analyze.
    pub total_pairs: usize,
    /// Number of pairs completed so far.
    pub completed_pairs: usize,
    /// Accumulated results (task ID → transport class string).
    pub results: Vec<CheckpointResult>,
    /// ISO 8601 timestamp of when this checkpoint was created.
    pub checkpoint_time: String,
}

/// A single result entry in a checkpoint.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CheckpointResult {
    /// Task identifier.
    pub task_id: String,
    /// Transport class result (as string).
    pub transport_class: String,
    /// Number of losses detected.
    pub loss_count: usize,
}

impl AnalysisCheckpoint {
    /// Create a new empty checkpoint for a job.
    pub fn new(job_id: impl Into<String>, total_pairs: usize) -> Self {
        Self {
            job_id: job_id.into(),
            total_pairs,
            completed_pairs: 0,
            results: Vec::new(),
            checkpoint_time: String::new(),
        }
    }

    /// Record a completed result.
    pub fn record(&mut self, result: CheckpointResult) {
        self.completed_pairs += 1;
        self.results.push(result);
    }

    /// Completion percentage (0.0–100.0).
    pub fn progress_percent(&self) -> f64 {
        if self.total_pairs == 0 {
            return 100.0;
        }
        (self.completed_pairs as f64 / self.total_pairs as f64) * 100.0
    }
}

/// Save a checkpoint to a JSON file.
pub fn save_checkpoint(checkpoint: &AnalysisCheckpoint, path: &Path) -> Result<(), String> {
    let json = serde_json::to_string_pretty(checkpoint)
        .map_err(|e| format!("failed to serialize checkpoint: {e}"))?;
    std::fs::write(path, json)
        .map_err(|e| format!("failed to write checkpoint to {}: {e}", path.display()))?;
    Ok(())
}

/// Load a checkpoint from a JSON file.
pub fn load_checkpoint(path: &Path) -> Result<AnalysisCheckpoint, String> {
    let json = std::fs::read_to_string(path)
        .map_err(|e| format!("failed to read checkpoint from {}: {e}", path.display()))?;
    serde_json::from_str(&json)
        .map_err(|e| format!("failed to parse checkpoint from {}: {e}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::env::temp_dir;

    #[test]
    fn checkpoint_round_trip() {
        let mut checkpoint = AnalysisCheckpoint::new("job-001", 10);
        checkpoint.record(CheckpointResult {
            task_id: "t1".to_string(),
            transport_class: "Concorde".to_string(),
            loss_count: 0,
        });
        checkpoint.record(CheckpointResult {
            task_id: "t2".to_string(),
            transport_class: "Economy".to_string(),
            loss_count: 3,
        });
        checkpoint.checkpoint_time = "2026-02-28T12:00:00Z".to_string();

        let path = temp_dir().join(format!(
            "protocol-squisher-checkpoint-test-{}.json",
            std::process::id()
        ));

        save_checkpoint(&checkpoint, &path).expect("save checkpoint");
        let loaded = load_checkpoint(&path).expect("load checkpoint");

        assert_eq!(checkpoint, loaded);
        assert_eq!(loaded.completed_pairs, 2);
        assert_eq!(loaded.total_pairs, 10);
        assert!((loaded.progress_percent() - 20.0).abs() < 0.01);

        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn empty_checkpoint_progress() {
        let cp = AnalysisCheckpoint::new("empty", 0);
        assert!((cp.progress_percent() - 100.0).abs() < f64::EPSILON);
    }
}
