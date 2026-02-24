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
}
