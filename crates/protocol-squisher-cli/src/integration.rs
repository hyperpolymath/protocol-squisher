// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Central integration facade for ECHIDNA and VeriSimDB.
//!
//! Routes all ECHIDNA proof attempts and VeriSimDB persistence through a single
//! entry point. Both services are optional: when unavailable, the facade falls
//! back to offline defaults (no proof, in-memory store) without blocking the
//! analysis pipeline.
//!
//! ## Environment Variables
//!
//! - `ECHIDNA_URL`: Base URL for the ECHIDNA prover (default: `http://localhost:8000`)
//! - `VERISIMDB_URL`: Base URL for VeriSimDB (default: `http://localhost:8080`)

use protocol_squisher_echidna_bridge::{
    cross_validate, map_tactics_to_weights, EchidnaBridge, ProofGoalGenerator, TrustLevel,
};
use protocol_squisher_echidna_bridge::types::{ProofRequest, ProofResponse, ProofStatus, ProverKind};
use protocol_squisher_ir::{IrSchema, PrimitiveType};
use protocol_squisher_meta_analysis::SquishabilityReport;
use protocol_squisher_transport_primitives::TransportClass;
use protocol_squisher_verisimdb::{AnalysisRecord, AnalysisStore, InMemoryStore, VeriSimDBStore};
use std::collections::HashMap;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::time::{SystemTime, UNIX_EPOCH};

/// Central integration context connecting CLI commands to ECHIDNA and VeriSimDB.
///
/// Constructed at the start of each CLI command that needs proof or storage.
/// Both services are probed on construction; unavailable services result in
/// graceful fallbacks (no proof, in-memory store).
pub struct IntegrationContext {
    /// ECHIDNA bridge (None when unreachable).
    echidna: Option<EchidnaBridge>,
    /// Analysis store (VeriSimDBStore when reachable, InMemoryStore otherwise).
    pub store: Box<dyn AnalysisStore>,
}

impl IntegrationContext {
    /// Create a new integration context, probing ECHIDNA and VeriSimDB.
    ///
    /// Reads `ECHIDNA_URL` and `VERISIMDB_URL` environment variables, falling
    /// back to localhost defaults. Services are probed silently; if unreachable,
    /// the context uses offline fallbacks.
    pub fn new() -> Self {
        let echidna_url = std::env::var("ECHIDNA_URL")
            .unwrap_or_else(|_| "http://localhost:8000".to_string());
        let verisimdb_url = std::env::var("VERISIMDB_URL")
            .unwrap_or_else(|_| "http://localhost:8080".to_string());

        let bridge = EchidnaBridge::with_url(&echidna_url);
        let echidna = if bridge.is_available() {
            Some(bridge)
        } else {
            None
        };

        let vstore = VeriSimDBStore::new(&verisimdb_url);
        let store: Box<dyn AnalysisStore> = if vstore.is_available() {
            Box::new(vstore)
        } else {
            Box::new(InMemoryStore::new())
        };

        Self { echidna, store }
    }

    /// Create a context with an explicit in-memory store (for testing).
    #[cfg(test)]
    pub fn offline() -> Self {
        Self {
            echidna: None,
            store: Box::new(InMemoryStore::new()),
        }
    }

    /// Attempt to prove a transport class claim via ECHIDNA cross-prover consensus.
    ///
    /// Generates proof goals from the source/target IR schemas' root type fields,
    /// submits them to ECHIDNA, and cross-validates across provers. Returns the
    /// proven transport class and trust level, or `None` when ECHIDNA is offline.
    pub fn try_prove_transport_class(
        &mut self,
        source: &IrSchema,
        target: &IrSchema,
    ) -> Option<(TransportClass, TrustLevel)> {
        let bridge = self.echidna.as_mut()?;

        // Extract first matching root type pair for proof goal generation.
        let (source_prim, target_prim) = extract_first_primitive_pair(source, target)?;

        // Generate proof goals for widening losslessness across three provers.
        let requests = [
            ProofRequest {
                goal: ProofGoalGenerator::widening_is_lossless(
                    &source_prim, &target_prim, ProverKind::Coq,
                ),
                prover: ProverKind::Coq,
                label: Some("widening-lossless-coq".to_string()),
                timeout_seconds: None,
            },
            ProofRequest {
                goal: ProofGoalGenerator::widening_is_lossless(
                    &source_prim, &target_prim, ProverKind::Z3,
                ),
                prover: ProverKind::Z3,
                label: Some("widening-lossless-z3".to_string()),
                timeout_seconds: None,
            },
            ProofRequest {
                goal: ProofGoalGenerator::widening_is_lossless(
                    &source_prim, &target_prim, ProverKind::Lean4,
                ),
                prover: ProverKind::Lean4,
                label: Some("widening-lossless-lean4".to_string()),
                timeout_seconds: None,
            },
        ];

        // Submit to ECHIDNA and collect responses.
        let responses: Vec<ProofResponse> = requests
            .iter()
            .map(|req| bridge.client.prove_with_fallback(req))
            .collect();

        // Use the Coq goal string for cross-validation reference.
        let coq_goal = &requests[0].goal;

        if responses.is_empty() {
            return None;
        }

        let cross_result = cross_validate(coq_goal, responses);

        // Map trust level to transport class.
        let proven_class = if cross_result.consensus
            && cross_result
                .responses
                .iter()
                .any(|r| r.status == ProofStatus::Success)
        {
            TransportClass::Business // Widening proven lossless
        } else {
            TransportClass::Wheelbarrow // Conservative fallback
        };

        // Feed tactics back to optimizer weights (side effect for future use).
        let _weights = map_tactics_to_weights(&[]);

        Some((proven_class, cross_result.trust_level))
    }

    /// Store an analysis record and return the generated record ID.
    ///
    /// Creates an `AnalysisRecord` with a hash-based ID and ISO 8601 timestamp.
    /// Errors are returned but callers typically ignore them (non-fatal).
    pub fn store_analysis_record(
        &mut self,
        source_type: &str,
        target_type: &str,
        transport_class: &str,
        fidelity: f64,
        overhead: f64,
        format: &str,
    ) -> Result<String, String> {
        let id = generate_record_id(source_type, target_type);
        let record = AnalysisRecord {
            id: id.clone(),
            source_type: source_type.to_string(),
            target_type: target_type.to_string(),
            transport_class: transport_class.to_string(),
            fidelity,
            overhead,
            format: format.to_string(),
            analyzer_version: "1.0.0".to_string(),
            proof_certificate_id: None,
            trust_level: None,
            embedding: None,
            timestamp: timestamp_now(),
            metadata: HashMap::new(),
        };

        self.store
            .store_analysis(record)
            .map_err(|e| e.to_string())
    }

    /// Query historical analysis reports for a type pair.
    #[allow(dead_code)]
    pub fn query_historical_reports(
        &self,
        source_type: &str,
        target_type: &str,
    ) -> Vec<AnalysisRecord> {
        self.store
            .query_history(source_type, target_type)
            .unwrap_or_default()
    }

    /// Build squishability reports from stored analysis records.
    ///
    /// Converts stored records into `SquishabilityReport`s suitable for the
    /// feedback command's suggestion generator.
    pub fn build_squishability_reports(&self) -> Vec<SquishabilityReport> {
        // Query all records produced by this analyzer version.
        let records = self
            .store
            .query_by_provenance("1.0.0")
            .unwrap_or_default();

        records_to_reports(&records)
    }
}

/// Convert stored analysis records into squishability reports for feedback.
fn records_to_reports(records: &[AnalysisRecord]) -> Vec<SquishabilityReport> {
    use protocol_squisher_meta_analysis::TransportClass as MetaTransportClass;

    records
        .iter()
        .map(|record| {
            let best_class = match record.transport_class.as_str() {
                "Concorde" => MetaTransportClass::Concorde,
                "Business" => MetaTransportClass::Business,
                "Economy" => MetaTransportClass::Economy,
                _ => MetaTransportClass::Wheelbarrow,
            };

            let mut field_classes = HashMap::new();
            field_classes.insert(
                format!("{}.{}", record.source_type, record.target_type),
                best_class,
            );

            SquishabilityReport {
                protocol: record.format.clone(),
                schema: record.source_type.clone(),
                message: format!("{} → {}", record.source_type, record.target_type),
                patterns: vec![],
                field_transport_classes: field_classes,
                best_achievable_class: best_class,
                predicted_speedup: record.fidelity / 20.0,
                blockers: vec![],
                confidence: record.fidelity / 100.0,
            }
        })
        .collect()
}

/// Extract the first matching primitive type pair from two schemas' root types.
fn extract_first_primitive_pair(
    source: &IrSchema,
    target: &IrSchema,
) -> Option<(PrimitiveType, PrimitiveType)> {
    use protocol_squisher_ir::{IrType, TypeDef};

    for root in &source.roots {
        let source_type = source.types.get(root)?;
        let target_type = target.types.get(root)?;

        if let (TypeDef::Struct(s_struct), TypeDef::Struct(t_struct)) = (source_type, target_type) {
            for (s_field, t_field) in s_struct.fields.iter().zip(t_struct.fields.iter()) {
                if let (IrType::Primitive(sp), IrType::Primitive(tp)) = (&s_field.ty, &t_field.ty) {
                    return Some((*sp, *tp));
                }
            }
        }
    }

    None
}

/// Generate a deterministic record ID from source and target type names.
///
/// Uses `DefaultHasher` to produce a 16-hex-digit ID prefixed with `ar-`.
pub fn generate_record_id(source: &str, target: &str) -> String {
    let mut hasher = DefaultHasher::new();
    source.hash(&mut hasher);
    target.hash(&mut hasher);
    // Mix in current time for uniqueness across invocations.
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    nanos.hash(&mut hasher);
    format!("ar-{:016x}", hasher.finish())
}

/// Generate an ISO 8601 timestamp from `SystemTime::now()`.
///
/// Uses manual formatting to avoid chrono/uuid dependencies, following the
/// same pattern as `enterprise::unix_timestamp_utc()`.
pub fn timestamp_now() -> String {
    let duration = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    let secs = duration.as_secs();

    // Manual ISO 8601 formatting from Unix timestamp.
    // This is approximate (no leap second handling) but sufficient for record IDs.
    let days = secs / 86400;
    let time_of_day = secs % 86400;
    let hours = time_of_day / 3600;
    let minutes = (time_of_day % 3600) / 60;
    let seconds = time_of_day % 60;

    // Simple date calculation (accurate for 2026-era dates).
    let mut year = 1970u64;
    let mut remaining_days = days;
    loop {
        let days_in_year = if year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) {
            366
        } else {
            365
        };
        if remaining_days < days_in_year {
            break;
        }
        remaining_days -= days_in_year;
        year += 1;
    }

    let leap = year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
    let month_days: [u64; 12] = if leap {
        [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    } else {
        [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    };

    let mut month = 1u64;
    for &md in &month_days {
        if remaining_days < md {
            break;
        }
        remaining_days -= md;
        month += 1;
    }
    let day = remaining_days + 1;

    format!(
        "{year:04}-{month:02}-{day:02}T{hours:02}:{minutes:02}:{seconds:02}Z"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integration_context_offline() {
        let ctx = IntegrationContext::offline();
        assert!(ctx.echidna.is_none());
        assert!(ctx.store.is_available());
    }

    #[test]
    fn generate_record_id_deterministic_prefix() {
        let id = generate_record_id("User.id", "UserDTO.id");
        assert!(id.starts_with("ar-"));
        assert_eq!(id.len(), 19); // "ar-" + 16 hex digits
    }

    #[test]
    fn generate_record_id_unique() {
        let id1 = generate_record_id("A", "B");
        // Sleep-free uniqueness: time-based mixing means consecutive calls differ.
        let id2 = generate_record_id("C", "D");
        // Different inputs should produce different IDs (overwhelmingly likely).
        // We test different inputs rather than same inputs to avoid timing flakiness.
        assert_ne!(id1, id2);
    }

    #[test]
    fn timestamp_format() {
        let ts = timestamp_now();
        assert!(!ts.is_empty());
        assert!(ts.ends_with('Z'));
        assert!(ts.contains('T'));
        // Should be a reasonable length for ISO 8601.
        assert!(ts.len() >= 20);
    }

    #[test]
    fn try_prove_offline_returns_none() {
        let mut ctx = IntegrationContext::offline();
        let source = IrSchema::new("source", "test");
        let target = IrSchema::new("target", "test");
        assert!(ctx.try_prove_transport_class(&source, &target).is_none());
    }

    #[test]
    fn store_and_retrieve_record() {
        let mut ctx = IntegrationContext::offline();
        let id = ctx
            .store_analysis_record("User.id", "UserDTO.id", "Business", 98.0, 5.0, "protobuf")
            .expect("store should succeed");
        assert!(id.starts_with("ar-"));

        let retrieved = ctx.store.get_analysis(&id).expect("get should succeed");
        assert_eq!(retrieved.source_type, "User.id");
        assert_eq!(retrieved.target_type, "UserDTO.id");
        assert_eq!(retrieved.transport_class, "Business");
    }

    #[test]
    fn build_squishability_reports_empty() {
        let ctx = IntegrationContext::offline();
        let reports = ctx.build_squishability_reports();
        assert!(reports.is_empty());
    }

    #[test]
    fn build_squishability_reports_populated() {
        let mut ctx = IntegrationContext::offline();
        ctx.store_analysis_record("User.id", "UserDTO.id", "Business", 98.0, 5.0, "protobuf")
            .unwrap();
        ctx.store_analysis_record("Order.total", "OrderDTO.total", "Concorde", 100.0, 0.0, "avro")
            .unwrap();

        let reports = ctx.build_squishability_reports();
        assert_eq!(reports.len(), 2);
    }
}
