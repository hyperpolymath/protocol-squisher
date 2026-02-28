// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # ECHIDNA Bridge for Protocol Squisher
//!
//! Connects protocol-squisher's analysis pipeline to the ECHIDNA neurosymbolic
//! theorem prover (30 backends, REST/gRPC/GraphQL). This crate handles:
//!
//! - **Proof goal generation** from IR type pairs and transport class claims
//! - **REST client** for submitting proofs and querying results
//! - **Cross-prover validation** for consensus-based trust levels
//! - **Tactic-to-weight mapping** for feeding proof insights back to the optimizer
//! - **Offline fallback** via an in-memory proof cache
//!
//! ## Data Flow
//!
//! ```text
//! IR type pair  →  ProofGoalGenerator  →  EchidnaClient.submit_proof()
//!                                              ↓
//!                                         ProofResponse
//!                                              ↓
//!                                     cross_validate() (N provers)
//!                                              ↓
//!                                      TrustLevel (1–5)
//!                                              ↓
//!                                  map_tactics_to_weights()
//!                                              ↓
//!                                  EmpiricalSynthesisHints
//! ```
//!
//! ## Offline Mode
//!
//! When ECHIDNA is unavailable, `EchidnaClient::prove_with_fallback()` returns
//! cached results or a safe default (trust level 1). The bridge never blocks
//! the analysis pipeline on prover availability.

pub mod cache;
pub mod client;
pub mod cross_prover;
pub mod goal_generator;
pub mod tactic_mapper;
pub mod types;

pub use cache::ProofCache;
pub use client::{EchidnaClient, EchidnaError};
pub use cross_prover::{compute_trust_level, cross_validate};
pub use goal_generator::ProofGoalGenerator;
pub use tactic_mapper::{boost_suggestion_from_proof, map_tactics_to_weights};
pub use types::{
    CrossProverResult, ProofRequest, ProofResponse, ProofStatus, ProverKind, TacticSuggestion,
    TrustLevel,
};

/// Facade providing a high-level API for ECHIDNA integration.
///
/// Combines the client, goal generator, cross-prover, and tactic mapper
/// into a single entry point for the analysis pipeline.
pub struct EchidnaBridge {
    /// The underlying REST client.
    pub client: EchidnaClient,
}

impl EchidnaBridge {
    /// Create a bridge connected to the default ECHIDNA URL.
    pub fn new() -> Self {
        Self {
            client: EchidnaClient::default_url(),
        }
    }

    /// Create a bridge connected to a custom ECHIDNA URL.
    pub fn with_url(url: impl Into<String>) -> Self {
        Self {
            client: EchidnaClient::new(url),
        }
    }

    /// Check whether ECHIDNA is reachable.
    pub fn is_available(&self) -> bool {
        self.client.health_check()
    }
}

impl Default for EchidnaBridge {
    fn default() -> Self {
        Self::new()
    }
}
