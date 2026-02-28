// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! `AnalysisStore` trait and implementations for persisting analysis results.
//!
//! Two implementations are provided:
//! - `VeriSimDBStore`: Production backend using VeriSimDB's HTTP API.
//! - `InMemoryStore`: In-process fallback for testing and offline use.

use crate::error::VeriSimError;
use crate::models::{AnalysisRecord, SchemaVersionEntry, SuggestionLogEntry};
use std::collections::HashMap;

/// Trait for persisting and querying protocol-squisher analysis results.
///
/// Implementations must support CRUD operations on analysis records,
/// suggestion logging, schema version tracking, and compatibility trend
/// queries. The trait is object-safe for dynamic dispatch.
pub trait AnalysisStore {
    /// Store a new analysis record. Returns the record ID.
    fn store_analysis(&mut self, record: AnalysisRecord) -> Result<String, VeriSimError>;

    /// Retrieve an analysis record by ID.
    fn get_analysis(&self, id: &str) -> Result<AnalysisRecord, VeriSimError>;

    /// Find analysis records similar to the given type pair (by name matching).
    fn query_similar(
        &self,
        source_type: &str,
        target_type: &str,
        limit: usize,
    ) -> Result<Vec<AnalysisRecord>, VeriSimError>;

    /// Query analysis history for a specific type pair, ordered chronologically.
    fn query_history(
        &self,
        source_type: &str,
        target_type: &str,
    ) -> Result<Vec<AnalysisRecord>, VeriSimError>;

    /// Query records produced by a specific analyzer version.
    fn query_by_provenance(
        &self,
        analyzer_version: &str,
    ) -> Result<Vec<AnalysisRecord>, VeriSimError>;

    /// Log a suggestion that was generated (or submitted) upstream.
    fn log_suggestion(&mut self, entry: SuggestionLogEntry) -> Result<(), VeriSimError>;

    /// Record a schema version observation.
    fn record_schema_version(&mut self, entry: SchemaVersionEntry) -> Result<(), VeriSimError>;

    /// Query the compatibility trend for a type pair over time.
    ///
    /// Returns records ordered by timestamp, useful for detecting regressions
    /// or improvements in transport class assignments across schema versions.
    fn compatibility_trend(
        &self,
        source_type: &str,
        target_type: &str,
    ) -> Result<Vec<AnalysisRecord>, VeriSimError>;

    /// Check whether the underlying storage is available.
    fn is_available(&self) -> bool;
}

/// In-memory implementation of `AnalysisStore` for testing and offline fallback.
///
/// All data is stored in `HashMap`s and lost when the store is dropped.
/// This implementation always reports itself as available.
#[derive(Debug, Default)]
pub struct InMemoryStore {
    analyses: HashMap<String, AnalysisRecord>,
    suggestions: Vec<SuggestionLogEntry>,
    schema_versions: Vec<SchemaVersionEntry>,
}

impl InMemoryStore {
    /// Create an empty in-memory store.
    pub fn new() -> Self {
        Self::default()
    }
}

impl AnalysisStore for InMemoryStore {
    fn store_analysis(&mut self, record: AnalysisRecord) -> Result<String, VeriSimError> {
        let id = record.id.clone();
        self.analyses.insert(id.clone(), record);
        Ok(id)
    }

    fn get_analysis(&self, id: &str) -> Result<AnalysisRecord, VeriSimError> {
        self.analyses
            .get(id)
            .cloned()
            .ok_or_else(|| VeriSimError::NotFound(id.to_string()))
    }

    fn query_similar(
        &self,
        source_type: &str,
        target_type: &str,
        limit: usize,
    ) -> Result<Vec<AnalysisRecord>, VeriSimError> {
        let results: Vec<AnalysisRecord> = self
            .analyses
            .values()
            .filter(|r| r.source_type == source_type || r.target_type == target_type)
            .take(limit)
            .cloned()
            .collect();
        Ok(results)
    }

    fn query_history(
        &self,
        source_type: &str,
        target_type: &str,
    ) -> Result<Vec<AnalysisRecord>, VeriSimError> {
        let mut results: Vec<AnalysisRecord> = self
            .analyses
            .values()
            .filter(|r| r.source_type == source_type && r.target_type == target_type)
            .cloned()
            .collect();
        results.sort_by(|a, b| a.timestamp.cmp(&b.timestamp));
        Ok(results)
    }

    fn query_by_provenance(
        &self,
        analyzer_version: &str,
    ) -> Result<Vec<AnalysisRecord>, VeriSimError> {
        let results: Vec<AnalysisRecord> = self
            .analyses
            .values()
            .filter(|r| r.analyzer_version == analyzer_version)
            .cloned()
            .collect();
        Ok(results)
    }

    fn log_suggestion(&mut self, entry: SuggestionLogEntry) -> Result<(), VeriSimError> {
        self.suggestions.push(entry);
        Ok(())
    }

    fn record_schema_version(&mut self, entry: SchemaVersionEntry) -> Result<(), VeriSimError> {
        self.schema_versions.push(entry);
        Ok(())
    }

    fn compatibility_trend(
        &self,
        source_type: &str,
        target_type: &str,
    ) -> Result<Vec<AnalysisRecord>, VeriSimError> {
        // Same as query_history for in-memory store.
        self.query_history(source_type, target_type)
    }

    fn is_available(&self) -> bool {
        true
    }
}

/// VeriSimDB HTTP backend for `AnalysisStore`.
///
/// Uses `VeriSimDBClient` to persist records. Falls back to returning
/// `VeriSimError::Unavailable` when the server is unreachable.
pub struct VeriSimDBStore {
    client: crate::client::VeriSimDBClient,
}

impl VeriSimDBStore {
    /// Create a store connected to a VeriSimDB instance.
    pub fn new(base_url: impl Into<String>) -> Self {
        Self {
            client: crate::client::VeriSimDBClient::new(base_url),
        }
    }
}

impl AnalysisStore for VeriSimDBStore {
    fn store_analysis(&mut self, record: AnalysisRecord) -> Result<String, VeriSimError> {
        let id = record.id.clone();
        let value = serde_json::to_value(&record)
            .map_err(|e| VeriSimError::SerializationError(e.to_string()))?;
        self.client.create_entity("analyses", &value)?;
        Ok(id)
    }

    fn get_analysis(&self, id: &str) -> Result<AnalysisRecord, VeriSimError> {
        let value = self.client.get_entity("analyses", id)?;
        serde_json::from_value(value).map_err(|e| VeriSimError::SerializationError(e.to_string()))
    }

    fn query_similar(
        &self,
        source_type: &str,
        target_type: &str,
        limit: usize,
    ) -> Result<Vec<AnalysisRecord>, VeriSimError> {
        let vql = format!(
            "SELECT * FROM analyses \
             WHERE source_type = '{source_type}' \
             OR target_type = '{target_type}' \
             LIMIT {limit}"
        );
        let result = self.client.vql_query(&vql)?;
        serde_json::from_value(result).map_err(|e| VeriSimError::SerializationError(e.to_string()))
    }

    fn query_history(
        &self,
        source_type: &str,
        target_type: &str,
    ) -> Result<Vec<AnalysisRecord>, VeriSimError> {
        let vql = crate::queries::build_temporal_query(
            source_type,
            target_type,
            "1970-01-01",
            "2099-12-31",
        );
        let result = self.client.vql_query(&vql)?;
        serde_json::from_value(result).map_err(|e| VeriSimError::SerializationError(e.to_string()))
    }

    fn query_by_provenance(
        &self,
        analyzer_version: &str,
    ) -> Result<Vec<AnalysisRecord>, VeriSimError> {
        let vql = crate::queries::build_provenance_query(analyzer_version, None);
        let result = self.client.vql_query(&vql)?;
        serde_json::from_value(result).map_err(|e| VeriSimError::SerializationError(e.to_string()))
    }

    fn log_suggestion(&mut self, entry: SuggestionLogEntry) -> Result<(), VeriSimError> {
        let value = serde_json::to_value(&entry)
            .map_err(|e| VeriSimError::SerializationError(e.to_string()))?;
        self.client.create_entity("suggestions", &value)?;
        Ok(())
    }

    fn record_schema_version(&mut self, entry: SchemaVersionEntry) -> Result<(), VeriSimError> {
        let value = serde_json::to_value(&entry)
            .map_err(|e| VeriSimError::SerializationError(e.to_string()))?;
        self.client.create_entity("schema_versions", &value)?;
        Ok(())
    }

    fn compatibility_trend(
        &self,
        source_type: &str,
        target_type: &str,
    ) -> Result<Vec<AnalysisRecord>, VeriSimError> {
        self.query_history(source_type, target_type)
    }

    fn is_available(&self) -> bool {
        self.client.health().unwrap_or(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn sample_record(id: &str, source: &str, target: &str, ts: &str) -> AnalysisRecord {
        AnalysisRecord {
            id: id.to_string(),
            source_type: source.to_string(),
            target_type: target.to_string(),
            transport_class: "Business".to_string(),
            fidelity: 98.0,
            overhead: 5.0,
            format: "protobuf".to_string(),
            analyzer_version: "1.0.0".to_string(),
            proof_certificate_id: None,
            trust_level: None,
            embedding: None,
            timestamp: ts.to_string(),
            metadata: HashMap::new(),
        }
    }

    #[test]
    fn in_memory_store_retrieve() {
        let mut store = InMemoryStore::new();
        let record = sample_record("r1", "User.id", "UserDTO.id", "2026-01-01T00:00:00Z");

        let id = store.store_analysis(record.clone()).unwrap();
        assert_eq!(id, "r1");

        let retrieved = store.get_analysis("r1").unwrap();
        assert_eq!(retrieved.source_type, "User.id");
    }

    #[test]
    fn in_memory_query_history() {
        let mut store = InMemoryStore::new();
        store
            .store_analysis(sample_record("r1", "A", "B", "2026-01-01"))
            .unwrap();
        store
            .store_analysis(sample_record("r2", "A", "B", "2026-02-01"))
            .unwrap();
        store
            .store_analysis(sample_record("r3", "A", "B", "2026-03-01"))
            .unwrap();

        let history = store.query_history("A", "B").unwrap();
        assert_eq!(history.len(), 3);
        assert!(history[0].timestamp <= history[1].timestamp);
        assert!(history[1].timestamp <= history[2].timestamp);
    }

    #[test]
    fn in_memory_query_provenance() {
        let mut store = InMemoryStore::new();
        let mut r1 = sample_record("r1", "A", "B", "2026-01-01");
        r1.analyzer_version = "1.0.0".to_string();
        let mut r2 = sample_record("r2", "C", "D", "2026-01-02");
        r2.analyzer_version = "2.0.0".to_string();

        store.store_analysis(r1).unwrap();
        store.store_analysis(r2).unwrap();

        let v1 = store.query_by_provenance("1.0.0").unwrap();
        assert_eq!(v1.len(), 1);
        assert_eq!(v1[0].id, "r1");
    }

    #[test]
    fn in_memory_log_suggestion() {
        let mut store = InMemoryStore::new();
        let entry = SuggestionLogEntry {
            id: "s1".to_string(),
            analysis_id: "r1".to_string(),
            target_repo: "github.com/test".to_string(),
            title: "Test".to_string(),
            body: "Body".to_string(),
            platform: "github".to_string(),
            dry_run: true,
            timestamp: "2026-01-01".to_string(),
            external_ref: None,
        };

        store.log_suggestion(entry).unwrap();
        assert_eq!(store.suggestions.len(), 1);
    }

    #[test]
    fn in_memory_schema_version() {
        let mut store = InMemoryStore::new();
        let entry = SchemaVersionEntry {
            schema_name: "User".to_string(),
            version: "1.0.0".to_string(),
            format: "protobuf".to_string(),
            type_count: 5,
            field_count: 20,
            first_seen: "2026-01-01".to_string(),
            content_hash: None,
        };

        store.record_schema_version(entry).unwrap();
        assert_eq!(store.schema_versions.len(), 1);
    }

    #[test]
    fn in_memory_trend() {
        let mut store = InMemoryStore::new();
        for i in 0..5 {
            store
                .store_analysis(sample_record(
                    &format!("r{i}"),
                    "X",
                    "Y",
                    &format!("2026-0{}-01", i + 1),
                ))
                .unwrap();
        }

        let trend = store.compatibility_trend("X", "Y").unwrap();
        assert_eq!(trend.len(), 5);
        // Should be chronologically ordered.
        for window in trend.windows(2) {
            assert!(window[0].timestamp <= window[1].timestamp);
        }
    }

    #[test]
    fn in_memory_not_found() {
        let store = InMemoryStore::new();
        let result = store.get_analysis("nonexistent");
        assert!(result.is_err());
    }

    #[test]
    fn store_fallback_unavailable() {
        // VeriSimDBStore pointing to unreachable URL reports unavailable.
        let store = VeriSimDBStore::new("http://127.0.0.1:1");
        assert!(!store.is_available());
    }
}
