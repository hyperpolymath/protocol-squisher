// SPDX-License-Identifier: PMPL-1.0-or-later

use crate::unix_timestamp_utc;
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::fs::{self, OpenOptions};
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AuditEvent {
    pub timestamp_utc: String,
    pub actor: String,
    pub action: String,
    pub outcome: String,
    pub details: Value,
}

#[derive(Debug, Clone)]
pub struct AuditLogger {
    path: PathBuf,
}

impl AuditLogger {
    pub fn new(path: impl Into<PathBuf>) -> Self {
        Self { path: path.into() }
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn record(
        &self,
        actor: impl Into<String>,
        action: impl Into<String>,
        outcome: impl Into<String>,
        details: Value,
    ) -> Result<()> {
        let event = AuditEvent {
            timestamp_utc: unix_timestamp_utc(),
            actor: actor.into(),
            action: action.into(),
            outcome: outcome.into(),
            details,
        };
        self.append(&event)
    }

    pub fn append(&self, event: &AuditEvent) -> Result<()> {
        if let Some(parent) = self.path.parent() {
            fs::create_dir_all(parent)
                .with_context(|| format!("Failed to create audit dir {}", parent.display()))?;
        }

        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.path)
            .with_context(|| format!("Failed to open audit log {}", self.path.display()))?;
        let line = serde_json::to_string(event).context("Failed to serialize audit event")?;
        file.write_all(line.as_bytes())
            .context("Failed to write audit event")?;
        file.write_all(b"\n").context("Failed to finalize line")?;
        Ok(())
    }

    pub fn read_all(&self) -> Result<Vec<AuditEvent>> {
        if !self.path.exists() {
            return Ok(vec![]);
        }

        let file = fs::File::open(&self.path)
            .with_context(|| format!("Failed to open audit log {}", self.path.display()))?;
        let reader = BufReader::new(file);

        let mut events = Vec::new();
        for line in reader.lines() {
            let line = line?;
            if line.trim().is_empty() {
                continue;
            }
            let event = serde_json::from_str::<AuditEvent>(&line)
                .with_context(|| "Failed to parse audit event line")?;
            events.push(event);
        }
        Ok(events)
    }
}

/// Time range and type filters for querying audit entries.
#[derive(Debug, Clone, Default)]
pub struct AuditQuery {
    /// Only return events at or after this UTC timestamp.
    pub from_timestamp: Option<String>,
    /// Only return events at or before this UTC timestamp.
    pub to_timestamp: Option<String>,
    /// Only return events matching this action.
    pub action_filter: Option<String>,
    /// Only return events by this actor.
    pub actor_filter: Option<String>,
}

/// Summary statistics for a set of audit events.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuditStats {
    /// Total number of events.
    pub total_events: usize,
    /// Number of events with outcome "success".
    pub success_count: usize,
    /// Number of events with outcome "failure".
    pub failure_count: usize,
    /// Distinct actors seen.
    pub distinct_actors: usize,
    /// Distinct actions seen.
    pub distinct_actions: usize,
}

impl AuditLogger {
    /// Query audit events with optional time range and type filters.
    pub fn query_entries(&self, query: &AuditQuery) -> Result<Vec<AuditEvent>> {
        let all = self.read_all()?;
        let filtered = all
            .into_iter()
            .filter(|event| {
                if let Some(from) = &query.from_timestamp {
                    if event.timestamp_utc < *from {
                        return false;
                    }
                }
                if let Some(to) = &query.to_timestamp {
                    if event.timestamp_utc > *to {
                        return false;
                    }
                }
                if let Some(action) = &query.action_filter {
                    if !event.action.contains(action.as_str()) {
                        return false;
                    }
                }
                if let Some(actor) = &query.actor_filter {
                    if event.actor != *actor {
                        return false;
                    }
                }
                true
            })
            .collect();
        Ok(filtered)
    }

    /// Compute summary statistics over all events in the log.
    pub fn stats(&self) -> Result<AuditStats> {
        let events = self.read_all()?;
        let mut actors = std::collections::HashSet::new();
        let mut actions = std::collections::HashSet::new();
        let mut success_count = 0usize;
        let mut failure_count = 0usize;

        for event in &events {
            actors.insert(event.actor.clone());
            actions.insert(event.action.clone());
            if event.outcome == "success" {
                success_count += 1;
            } else if event.outcome == "failure" {
                failure_count += 1;
            }
        }

        Ok(AuditStats {
            total_events: events.len(),
            success_count,
            failure_count,
            distinct_actors: actors.len(),
            distinct_actions: actions.len(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn temp_log_path() -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos();
        std::env::temp_dir().join(format!("protocol-squisher-audit-{nanos}.jsonl"))
    }

    #[test]
    fn audit_log_round_trip() {
        let path = temp_log_path();
        let logger = AuditLogger::new(&path);
        logger
            .record(
                "ci",
                "schema_registry.publish",
                "success",
                serde_json::json!({"name":"orders","version":"1.0.0"}),
            )
            .expect("record audit event");

        let events = logger.read_all().expect("read audit events");
        assert_eq!(events.len(), 1);
        assert_eq!(events[0].actor, "ci");
        assert_eq!(events[0].action, "schema_registry.publish");

        fs::remove_file(path).ok();
    }

    #[test]
    fn query_filters_by_action() {
        let path = temp_log_path();
        let logger = AuditLogger::new(&path);
        logger
            .record("ci", "schema.publish", "success", serde_json::json!({}))
            .expect("record");
        logger
            .record("ci", "governance.evaluate", "success", serde_json::json!({}))
            .expect("record");

        let query = AuditQuery {
            action_filter: Some("schema".to_string()),
            ..Default::default()
        };
        let results = logger.query_entries(&query).expect("query");
        assert_eq!(results.len(), 1);
        assert!(results[0].action.contains("schema"));

        fs::remove_file(path).ok();
    }

    #[test]
    fn query_filters_by_actor() {
        let path = temp_log_path();
        let logger = AuditLogger::new(&path);
        logger
            .record("alice", "publish", "success", serde_json::json!({}))
            .expect("record");
        logger
            .record("bob", "publish", "failure", serde_json::json!({}))
            .expect("record");

        let query = AuditQuery {
            actor_filter: Some("bob".to_string()),
            ..Default::default()
        };
        let results = logger.query_entries(&query).expect("query");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].actor, "bob");

        fs::remove_file(path).ok();
    }

    #[test]
    fn stats_counts_outcomes() {
        let path = temp_log_path();
        let logger = AuditLogger::new(&path);
        logger
            .record("ci", "action-a", "success", serde_json::json!({}))
            .expect("record");
        logger
            .record("ci", "action-b", "failure", serde_json::json!({}))
            .expect("record");
        logger
            .record("admin", "action-a", "success", serde_json::json!({}))
            .expect("record");

        let stats = logger.stats().expect("stats");
        assert_eq!(stats.total_events, 3);
        assert_eq!(stats.success_count, 2);
        assert_eq!(stats.failure_count, 1);
        assert_eq!(stats.distinct_actors, 2);
        assert_eq!(stats.distinct_actions, 2);

        fs::remove_file(path).ok();
    }
}
