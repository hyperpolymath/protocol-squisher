// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Data models for analysis records, suggestion logs, and schema versions.
//!
//! These structures represent the entities persisted in VeriSimDB. Each
//! `AnalysisRecord` captures a complete snapshot of a compatibility analysis,
//! including provenance (which analyzer version produced it), proof certificate
//! references, trust levels, and optional vector embeddings for similarity search.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// A complete record of a compatibility analysis, suitable for persistence.
///
/// This is the primary entity stored in VeriSimDB. It captures the full
/// context of an analysis: input types, output transport class, fidelity
/// metrics, provenance, and optional cross-references to ECHIDNA proof
/// certificates.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AnalysisRecord {
    /// Unique identifier for this record (UUID or hash).
    pub id: String,
    /// Source type name (e.g., "User.id").
    pub source_type: String,
    /// Target type name (e.g., "UserDTO.id").
    pub target_type: String,
    /// Assigned transport class (as string: "Concorde", "Business", etc.).
    pub transport_class: String,
    /// Fidelity percentage (0.0–100.0).
    pub fidelity: f64,
    /// Estimated overhead percentage (0.0–100.0).
    pub overhead: f64,
    /// Source format (e.g., "protobuf", "avro", "rust-serde").
    pub format: String,
    /// Version of the analyzer that produced this result.
    pub analyzer_version: String,
    /// Reference to an ECHIDNA proof certificate ID (if proven).
    pub proof_certificate_id: Option<String>,
    /// Trust level from cross-prover validation (1–5).
    pub trust_level: Option<u8>,
    /// Optional vector embedding for similarity search.
    pub embedding: Option<Vec<f64>>,
    /// ISO 8601 timestamp of when this analysis was performed.
    pub timestamp: String,
    /// Free-form key-value metadata.
    pub metadata: HashMap<String, String>,
}

/// A log entry recording a suggestion sent to a schema owner.
///
/// Tracks which suggestions have been generated, whether they were submitted
/// upstream, and their current status. Used for deduplication and audit trails.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SuggestionLogEntry {
    /// Unique identifier for this suggestion.
    pub id: String,
    /// The analysis record ID that triggered this suggestion.
    pub analysis_id: String,
    /// Target repository (e.g., "github.com/org/repo").
    pub target_repo: String,
    /// Suggestion title (for issue/PR).
    pub title: String,
    /// Suggestion body (markdown).
    pub body: String,
    /// Platform the suggestion was submitted to (e.g., "github", "gitlab").
    pub platform: String,
    /// Whether this was a dry run (not actually submitted).
    pub dry_run: bool,
    /// ISO 8601 timestamp.
    pub timestamp: String,
    /// External reference (e.g., issue URL) if actually submitted.
    pub external_ref: Option<String>,
}

/// A record of a schema version observed during analysis.
///
/// Tracks the evolution of schemas over time, enabling trend analysis
/// and compatibility regression detection.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SchemaVersionEntry {
    /// Schema name.
    pub schema_name: String,
    /// Schema version (semver).
    pub version: String,
    /// Source format.
    pub format: String,
    /// Number of types in this schema version.
    pub type_count: usize,
    /// Number of fields across all types.
    pub field_count: usize,
    /// ISO 8601 timestamp of when this version was first observed.
    pub first_seen: String,
    /// Optional hash of the schema content for deduplication.
    pub content_hash: Option<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn analysis_record_serialization() {
        let record = AnalysisRecord {
            id: "ar-001".to_string(),
            source_type: "User.id".to_string(),
            target_type: "UserDTO.id".to_string(),
            transport_class: "Business".to_string(),
            fidelity: 98.0,
            overhead: 5.0,
            format: "protobuf".to_string(),
            analyzer_version: "1.0.0".to_string(),
            proof_certificate_id: Some("pf-xyz".to_string()),
            trust_level: Some(3),
            embedding: None,
            timestamp: "2026-02-28T12:00:00Z".to_string(),
            metadata: HashMap::new(),
        };

        let json = serde_json::to_string(&record).unwrap();
        let parsed: AnalysisRecord = serde_json::from_str(&json).unwrap();
        assert_eq!(record, parsed);
    }

    #[test]
    fn suggestion_log_serialization() {
        let entry = SuggestionLogEntry {
            id: "sg-001".to_string(),
            analysis_id: "ar-001".to_string(),
            target_repo: "github.com/org/schema".to_string(),
            title: "Consider using Int64".to_string(),
            body: "Enables Business-class transport".to_string(),
            platform: "github".to_string(),
            dry_run: true,
            timestamp: "2026-02-28T12:00:00Z".to_string(),
            external_ref: None,
        };

        let json = serde_json::to_string(&entry).unwrap();
        let parsed: SuggestionLogEntry = serde_json::from_str(&json).unwrap();
        assert_eq!(entry, parsed);
    }
}
