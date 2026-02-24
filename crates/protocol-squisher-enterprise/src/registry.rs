// SPDX-License-Identifier: PMPL-1.0-or-later

use crate::unix_timestamp_utc;
use anyhow::{Context, Result};
use protocol_squisher_ir::IrSchema;
use semver::Version;
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegistryEntry {
    pub name: String,
    pub version: String,
    pub format: String,
    pub published_at_utc: String,
    pub schema: IrSchema,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RegistryIndexRecord {
    pub name: String,
    pub version: String,
    pub format: String,
    pub published_at_utc: String,
}

#[derive(Debug, Clone)]
pub struct SchemaRegistry {
    root: PathBuf,
}

impl SchemaRegistry {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn publish(
        &self,
        name: &str,
        version: &str,
        format: &str,
        schema: IrSchema,
    ) -> Result<RegistryEntry> {
        let entry = RegistryEntry {
            name: name.to_string(),
            version: version.to_string(),
            format: format.to_string(),
            published_at_utc: unix_timestamp_utc(),
            schema,
        };

        let path = self.entry_path(name, version);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .with_context(|| format!("Failed to create registry dir {}", parent.display()))?;
        }

        let payload =
            serde_json::to_string_pretty(&entry).context("Failed to serialize registry entry")?;
        fs::write(&path, payload)
            .with_context(|| format!("Failed to write registry entry {}", path.display()))?;

        Ok(entry)
    }

    pub fn fetch(&self, name: &str, version: &str) -> Result<RegistryEntry> {
        let path = self.entry_path(name, version);
        let raw = fs::read_to_string(&path)
            .with_context(|| format!("Failed to read registry entry {}", path.display()))?;
        let entry = serde_json::from_str::<RegistryEntry>(&raw)
            .with_context(|| format!("Failed to parse registry entry {}", path.display()))?;
        Ok(entry)
    }

    pub fn latest(&self, name: &str) -> Result<Option<RegistryEntry>> {
        let mut versions = self.list(Some(name))?;
        versions.sort_by(|a, b| compare_versions(&a.version, &b.version));
        let Some(last) = versions.last() else {
            return Ok(None);
        };
        self.fetch(&last.name, &last.version).map(Some)
    }

    pub fn list(&self, name: Option<&str>) -> Result<Vec<RegistryIndexRecord>> {
        if !self.root.exists() {
            return Ok(vec![]);
        }

        let mut records = Vec::new();
        if let Some(filter_name) = name {
            let dir = self.root.join(sanitize_component(filter_name));
            collect_records(&dir, &mut records)?;
        } else {
            for entry in fs::read_dir(&self.root)
                .with_context(|| format!("Failed to read registry root {}", self.root.display()))?
            {
                let entry = entry?;
                if entry.path().is_dir() {
                    collect_records(&entry.path(), &mut records)?;
                }
            }
        }

        records.sort_by(|a, b| {
            a.name
                .cmp(&b.name)
                .then_with(|| compare_versions(&a.version, &b.version))
        });
        Ok(records)
    }

    fn entry_path(&self, name: &str, version: &str) -> PathBuf {
        self.root
            .join(sanitize_component(name))
            .join(format!("{}.json", sanitize_component(version)))
    }
}

fn collect_records(dir: &Path, out: &mut Vec<RegistryIndexRecord>) -> Result<()> {
    if !dir.exists() {
        return Ok(());
    }

    for entry in fs::read_dir(dir).with_context(|| format!("Failed to read {}", dir.display()))? {
        let entry = entry?;
        let path = entry.path();
        if path.extension().and_then(|ext| ext.to_str()) != Some("json") {
            continue;
        }

        let raw = fs::read_to_string(&path)
            .with_context(|| format!("Failed to read registry file {}", path.display()))?;
        let parsed = serde_json::from_str::<RegistryEntry>(&raw)
            .with_context(|| format!("Failed to parse registry file {}", path.display()))?;

        out.push(RegistryIndexRecord {
            name: parsed.name,
            version: parsed.version,
            format: parsed.format,
            published_at_utc: parsed.published_at_utc,
        });
    }

    Ok(())
}

fn compare_versions(a: &str, b: &str) -> std::cmp::Ordering {
    match (Version::parse(a), Version::parse(b)) {
        (Ok(va), Ok(vb)) => va.cmp(&vb),
        _ => a.cmp(b),
    }
}

fn sanitize_component(input: &str) -> String {
    input
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '-' || c == '_' || c == '.' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn temp_registry_dir() -> PathBuf {
        let nanos = match SystemTime::now().duration_since(UNIX_EPOCH) {
            Ok(duration) => duration.as_nanos(),
            Err(_) => 0,
        };
        std::env::temp_dir().join(format!("protocol-squisher-registry-test-{nanos}"))
    }

    fn sample_schema(name: &str) -> IrSchema {
        IrSchema::new(name, "test")
    }

    #[test]
    fn publish_and_fetch_round_trip() -> Result<()> {
        let root = temp_registry_dir();
        let registry = SchemaRegistry::new(&root);

        registry
            .publish("billing.events", "1.2.0", "json-schema", sample_schema("Billing"))?;
        let fetched = registry.fetch("billing.events", "1.2.0")?;
        assert_eq!(fetched.name, "billing.events");
        assert_eq!(fetched.version, "1.2.0");
        assert_eq!(fetched.schema.name, "Billing");

        fs::remove_dir_all(root).ok();
        Ok(())
    }

    #[test]
    fn latest_prefers_newer_semver() -> Result<()> {
        let root = temp_registry_dir();
        let registry = SchemaRegistry::new(&root);

        registry
            .publish("billing.events", "1.9.0", "json-schema", sample_schema("A"))?;
        registry
            .publish("billing.events", "1.10.0", "json-schema", sample_schema("B"))?;

        let latest = registry
            .latest("billing.events")?
            .ok_or_else(|| anyhow::anyhow!("expected latest entry"))?;
        assert_eq!(latest.version, "1.10.0");
        assert_eq!(latest.schema.name, "B");

        fs::remove_dir_all(root).ok();
        Ok(())
    }
}
