// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Cross-prover validation: submit the same goal to N provers and aggregate.
//!
//! Cross-validation increases confidence in a proof result by checking it
//! against multiple independent backends. The `compute_trust_level()` function
//! maps the number of agreeing provers to a `TrustLevel` (1–5).

use crate::types::{CrossProverResult, ProofResponse, ProofStatus, TrustLevel};

/// Aggregate proof responses from multiple provers into a cross-validation result.
///
/// `responses` should contain the results from submitting the same goal to
/// different ECHIDNA prover backends. Only completed proofs (Success/Failed)
/// are considered; Pending/InProgress/Timeout responses are excluded from
/// consensus computation.
pub fn cross_validate(goal: &str, responses: Vec<ProofResponse>) -> CrossProverResult {
    let completed: Vec<&ProofResponse> = responses
        .iter()
        .filter(|r| r.status == ProofStatus::Success || r.status == ProofStatus::Failed)
        .collect();

    let success_count = completed
        .iter()
        .filter(|r| r.status == ProofStatus::Success)
        .count();
    let fail_count = completed
        .iter()
        .filter(|r| r.status == ProofStatus::Failed)
        .count();

    // Consensus requires all completed provers to agree.
    let consensus = !completed.is_empty()
        && (success_count == completed.len() || fail_count == completed.len());

    let agreeing_count = success_count.max(fail_count);
    let trust_level = compute_trust_level(agreeing_count, completed.len());

    CrossProverResult {
        goal: goal.to_string(),
        responses,
        consensus,
        trust_level,
    }
}

/// Compute a trust level from the number of agreeing provers.
///
/// The trust level reflects both the count of agreeing provers and whether
/// there was unanimous agreement:
///
/// | Agreeing | Total | Consensus? | Trust |
/// |----------|-------|------------|-------|
/// | 0        | any   | N/A        | 1     |
/// | 1        | 1     | Yes        | 1     |
/// | 2        | 2     | Yes        | 2     |
/// | 2        | 3     | No         | 2     |
/// | 3        | 3     | Yes        | 3     |
/// | 3        | 4     | No         | 3     |
/// | 4        | 4     | Yes        | 4     |
/// | 5+       | 5+    | Yes        | 5     |
pub fn compute_trust_level(agreeing: usize, total: usize) -> TrustLevel {
    if total == 0 || agreeing == 0 {
        return TrustLevel::Level1;
    }

    match agreeing {
        1 => TrustLevel::Level1,
        2 => TrustLevel::Level2,
        3 => TrustLevel::Level3,
        4 => TrustLevel::Level4,
        _ => TrustLevel::Level5,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::ProverKind;

    fn make_response(prover: ProverKind, status: ProofStatus) -> ProofResponse {
        ProofResponse {
            proof_id: format!("pf-{prover:?}"),
            status,
            goal: "test_goal".to_string(),
            prover,
            result: None,
            diagnostics: vec![],
            duration_ms: Some(10),
        }
    }

    #[test]
    fn cross_prover_all_succeed() {
        let responses = vec![
            make_response(ProverKind::Coq, ProofStatus::Success),
            make_response(ProverKind::Lean4, ProofStatus::Success),
            make_response(ProverKind::Z3, ProofStatus::Success),
        ];

        let result = cross_validate("test_goal", responses);
        assert!(result.consensus);
        assert_eq!(result.trust_level, TrustLevel::Level3);
    }

    #[test]
    fn cross_prover_partial() {
        let responses = vec![
            make_response(ProverKind::Coq, ProofStatus::Success),
            make_response(ProverKind::Lean4, ProofStatus::Success),
            make_response(ProverKind::Z3, ProofStatus::Failed),
        ];

        let result = cross_validate("test_goal", responses);
        assert!(!result.consensus);
        // 2 out of 3 agree on Success → TrustLevel::Level2.
        assert_eq!(result.trust_level, TrustLevel::Level2);
    }

    #[test]
    fn cross_prover_with_pending() {
        // Pending responses should be excluded from consensus.
        let responses = vec![
            make_response(ProverKind::Coq, ProofStatus::Success),
            make_response(ProverKind::Lean4, ProofStatus::Pending),
        ];

        let result = cross_validate("test_goal", responses);
        // Only 1 completed → trust level 1.
        assert!(result.consensus); // 1/1 agree
        assert_eq!(result.trust_level, TrustLevel::Level1);
    }
}
