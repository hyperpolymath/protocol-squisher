// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Maps ECHIDNA tactic suggestions to optimizer empirical hint weights.
//!
//! When ECHIDNA returns tactic suggestions with confidence scores, these can
//! be translated into `EmpiricalSynthesisHints.suggestion_weights` to bias
//! the optimizer's ranking of `OptimizationSuggestion` entries. Proven
//! widenings get a boost; failed proofs leave weights unchanged.

use crate::types::{ProofStatus, TacticSuggestion};
use std::collections::HashMap;

/// Map a set of tactic suggestions to optimizer suggestion weights.
///
/// Each tactic's confidence (0.0–1.0) is mapped to a weight multiplier
/// in the range [0.5, 2.0]. Higher tactic confidence → higher weight.
///
/// The returned map uses the same keys as `EmpiricalSynthesisHints.suggestion_weights`
/// (e.g., `"WidenType"`, `"MakeOptional"`, `"ChangeContainer"`).
pub fn map_tactics_to_weights(tactics: &[TacticSuggestion]) -> HashMap<String, f64> {
    let mut weights = HashMap::new();

    for tactic in tactics {
        // Map tactic names to optimizer suggestion kinds.
        let suggestion_key = tactic_to_suggestion_key(&tactic.name);
        // Convert confidence [0.0, 1.0] to weight [0.5, 2.0].
        let weight = 0.5 + (tactic.confidence * 1.5);
        let clamped = weight.clamp(0.5, 2.0);

        // Keep the highest weight if multiple tactics map to the same key.
        let current = weights.entry(suggestion_key).or_insert(clamped);
        if clamped > *current {
            *current = clamped;
        }
    }

    weights
}

/// Boost a specific suggestion weight when ECHIDNA proves a widening is lossless.
///
/// When a proof succeeds for a widening conversion, the `WidenType` weight
/// is boosted by 50% (clamped to 2.0). Failed proofs leave the weight unchanged.
pub fn boost_suggestion_from_proof(
    weights: &mut HashMap<String, f64>,
    proof_status: ProofStatus,
    suggestion_key: &str,
) {
    if proof_status == ProofStatus::Success {
        let weight = weights.entry(suggestion_key.to_string()).or_insert(1.0);
        *weight = (*weight * 1.5).min(2.0);
    }
    // Failed/Timeout/Pending/InProgress: no change.
}

/// Map ECHIDNA tactic names to optimizer `SuggestionKind` weight keys.
///
/// Tactics like "ring", "omega", "norm_num" typically prove numeric
/// properties → map to `WidenType`. Tactics like "simp", "auto" are
/// general-purpose → map to the default `WidenType` as well.
fn tactic_to_suggestion_key(tactic_name: &str) -> String {
    match tactic_name {
        "ring" | "omega" | "norm_num" | "linarith" | "decide" => "WidenType".to_string(),
        "cases" | "induction" | "destruct" => "ChangeContainer".to_string(),
        "simp" | "auto" | "trivial" | "tauto" => "WidenType".to_string(),
        "unfold" | "rewrite" | "subst" => "RenameField".to_string(),
        "exact" | "apply" | "refine" => "AddField".to_string(),
        _ => "WidenType".to_string(), // safe default
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tactic_mapper_boosts_proven() {
        let mut weights = HashMap::new();
        weights.insert("WidenType".to_string(), 1.0);

        boost_suggestion_from_proof(&mut weights, ProofStatus::Success, "WidenType");

        let weight = weights.get("WidenType").copied().unwrap();
        assert!(
            weight > 1.0,
            "Proven widening should boost weight; got {weight}"
        );
        assert!((weight - 1.5).abs() < f64::EPSILON);
    }

    #[test]
    fn tactic_mapper_no_boost_on_failure() {
        let mut weights = HashMap::new();
        weights.insert("WidenType".to_string(), 1.0);

        boost_suggestion_from_proof(&mut weights, ProofStatus::Failed, "WidenType");

        let weight = weights.get("WidenType").copied().unwrap();
        assert!(
            (weight - 1.0).abs() < f64::EPSILON,
            "Failed proof should not change weight; got {weight}"
        );
    }

    #[test]
    fn map_tactics_high_confidence() {
        let tactics = vec![TacticSuggestion {
            name: "omega".to_string(),
            args: vec![],
            confidence: 0.95,
        }];

        let weights = map_tactics_to_weights(&tactics);
        let widen_weight = weights.get("WidenType").copied().unwrap_or(1.0);
        // confidence 0.95 → weight = 0.5 + 0.95*1.5 = 1.925
        assert!(widen_weight > 1.5, "High confidence tactic should boost weight");
    }

    #[test]
    fn map_tactics_low_confidence() {
        let tactics = vec![TacticSuggestion {
            name: "auto".to_string(),
            args: vec![],
            confidence: 0.1,
        }];

        let weights = map_tactics_to_weights(&tactics);
        let widen_weight = weights.get("WidenType").copied().unwrap_or(1.0);
        // confidence 0.1 → weight = 0.5 + 0.1*1.5 = 0.65
        assert!(widen_weight < 1.0, "Low confidence should produce sub-1.0 weight");
    }
}
