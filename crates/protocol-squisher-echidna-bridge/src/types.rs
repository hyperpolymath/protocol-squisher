// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Mirror types for the ECHIDNA neurosymbolic theorem prover API.
//!
//! These types model the request/response structures used by ECHIDNA's REST
//! interface. Each proof goal targets a specific prover backend (one of 30
//! supported engines) and tracks status through a well-defined lifecycle:
//! `Pending → InProgress → Success | Failed | Timeout`.

use serde::{Deserialize, Serialize};

/// Supported prover backends in ECHIDNA (30 engines).
///
/// Each variant represents a distinct theorem proving or verification engine.
/// The bridge generates prover-specific goal syntax via `ProofGoalGenerator`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProverKind {
    Agda,
    Coq,
    Isabelle,
    Lean4,
    Z3,
    Cvc5,
    Vampire,
    EProver,
    Dafny,
    Fstar,
    Idris2,
    TwelfLf,
    Acl2,
    Hol4,
    HolLight,
    Isabelle2024,
    Mizar,
    Pvs,
    Maude,
    NuXmv,
    Spin,
    Alloy,
    Tlc,
    Apalache,
    Cbmc,
    Klee,
    SymbiYosys,
    Rosette,
    Redex,
    MiniKanren,
}

/// Lifecycle status of a proof submitted to ECHIDNA.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProofStatus {
    /// Proof goal has been accepted but not yet assigned to a prover.
    Pending,
    /// A prover backend is actively working on the goal.
    InProgress,
    /// The goal was successfully proven.
    Success,
    /// The prover determined the goal is unprovable or found a counterexample.
    Failed,
    /// The prover exceeded its time budget without a conclusion.
    Timeout,
}

/// Request body for submitting a proof goal to ECHIDNA.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ProofRequest {
    /// The formal goal string in the target prover's syntax.
    pub goal: String,
    /// Which prover backend to use.
    pub prover: ProverKind,
    /// Optional human-readable label for tracking.
    pub label: Option<String>,
    /// Timeout in seconds (ECHIDNA default if `None`).
    pub timeout_seconds: Option<u64>,
}

/// Response from ECHIDNA after submitting or querying a proof.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ProofResponse {
    /// Server-assigned proof identifier.
    pub proof_id: String,
    /// Current lifecycle status.
    pub status: ProofStatus,
    /// The original goal string.
    pub goal: String,
    /// Which prover handled this goal.
    pub prover: ProverKind,
    /// Human-readable proof term or counterexample (when available).
    pub result: Option<String>,
    /// Diagnostic messages from the prover.
    pub diagnostics: Vec<String>,
    /// Wall-clock duration in milliseconds (populated after completion).
    pub duration_ms: Option<u64>,
}

/// A tactic suggestion returned by ECHIDNA's tactic advisor.
///
/// Tactics are hints about which proof strategy would likely succeed for a
/// given goal shape. The `confidence` score (0.0–1.0) reflects the advisor's
/// belief that applying this tactic will close the goal.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TacticSuggestion {
    /// Tactic name (e.g., "ring", "omega", "simp", "auto").
    pub name: String,
    /// Arguments to pass to the tactic (prover-specific).
    pub args: Vec<String>,
    /// Confidence that this tactic will succeed (0.0–1.0).
    pub confidence: f64,
}

/// Trust level assigned to a proof result based on cross-prover consensus.
///
/// Higher levels indicate stronger confidence:
/// - Level1: Single prover, no cross-validation.
/// - Level5: Unanimous agreement across 5+ independent provers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum TrustLevel {
    /// Single prover, no cross-validation.
    Level1 = 1,
    /// Two provers agree.
    Level2 = 2,
    /// Three or more provers agree (majority consensus).
    Level3 = 3,
    /// Four provers agree with no dissent.
    Level4 = 4,
    /// Five or more provers unanimously agree.
    Level5 = 5,
}

/// Result of cross-prover validation (submitting the same goal to N provers).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CrossProverResult {
    /// The goal that was cross-validated.
    pub goal: String,
    /// Individual proof responses from each prover.
    pub responses: Vec<ProofResponse>,
    /// Whether all provers that completed agree on the result.
    pub consensus: bool,
    /// Computed trust level based on the number of agreeing provers.
    pub trust_level: TrustLevel,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prover_kind_all_variants() {
        // Verify all 30 variants serialize to distinct strings.
        let all_provers = [
            ProverKind::Agda,
            ProverKind::Coq,
            ProverKind::Isabelle,
            ProverKind::Lean4,
            ProverKind::Z3,
            ProverKind::Cvc5,
            ProverKind::Vampire,
            ProverKind::EProver,
            ProverKind::Dafny,
            ProverKind::Fstar,
            ProverKind::Idris2,
            ProverKind::TwelfLf,
            ProverKind::Acl2,
            ProverKind::Hol4,
            ProverKind::HolLight,
            ProverKind::Isabelle2024,
            ProverKind::Mizar,
            ProverKind::Pvs,
            ProverKind::Maude,
            ProverKind::NuXmv,
            ProverKind::Spin,
            ProverKind::Alloy,
            ProverKind::Tlc,
            ProverKind::Apalache,
            ProverKind::Cbmc,
            ProverKind::Klee,
            ProverKind::SymbiYosys,
            ProverKind::Rosette,
            ProverKind::Redex,
            ProverKind::MiniKanren,
        ];
        assert_eq!(all_provers.len(), 30);

        let mut serialized: Vec<String> = all_provers
            .iter()
            .map(|p| serde_json::to_string(p).unwrap())
            .collect();
        serialized.sort();
        serialized.dedup();
        assert_eq!(serialized.len(), 30, "All 30 provers must serialize to unique strings");
    }

    #[test]
    fn proof_request_serialization() {
        let request = ProofRequest {
            goal: "forall (n : nat), n + 0 = n".to_string(),
            prover: ProverKind::Coq,
            label: Some("nat_add_zero".to_string()),
            timeout_seconds: Some(30),
        };

        let json = serde_json::to_string(&request).unwrap();
        let parsed: ProofRequest = serde_json::from_str(&json).unwrap();
        assert_eq!(request, parsed);
    }

    #[test]
    fn proof_response_deserialization() {
        let json = r#"{
            "proof_id": "pf-001",
            "status": "success",
            "goal": "1 + 1 = 2",
            "prover": "z3",
            "result": "sat",
            "diagnostics": ["Solved in 0.01s"],
            "duration_ms": 10
        }"#;

        let response: ProofResponse = serde_json::from_str(json).unwrap();
        assert_eq!(response.proof_id, "pf-001");
        assert_eq!(response.status, ProofStatus::Success);
        assert_eq!(response.prover, ProverKind::Z3);
        assert_eq!(response.duration_ms, Some(10));
    }

    #[test]
    fn trust_level_ordering() {
        assert!(TrustLevel::Level1 < TrustLevel::Level2);
        assert!(TrustLevel::Level2 < TrustLevel::Level3);
        assert!(TrustLevel::Level3 < TrustLevel::Level4);
        assert!(TrustLevel::Level4 < TrustLevel::Level5);
    }

    #[test]
    fn proof_status_lifecycle() {
        // Verify the three terminal states are distinct from the two active states.
        let active = [ProofStatus::Pending, ProofStatus::InProgress];
        let terminal = [ProofStatus::Success, ProofStatus::Failed, ProofStatus::Timeout];

        for a in &active {
            for t in &terminal {
                assert_ne!(a, t);
            }
        }
    }
}
