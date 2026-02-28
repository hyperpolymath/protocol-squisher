// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! HTTP REST client for ECHIDNA's neurosymbolic theorem prover API.
//!
//! `EchidnaClient` wraps a blocking `reqwest::blocking::Client` and provides
//! typed methods for proof submission, tactic queries, and prover health
//! checks. When ECHIDNA is unreachable, `prove_with_fallback()` returns
//! cached results or safe defaults (trust level 1).

use crate::cache::ProofCache;
use crate::types::{ProofRequest, ProofResponse, ProofStatus, ProverKind, TacticSuggestion};
use thiserror::Error;

/// Errors from ECHIDNA client operations.
#[derive(Debug, Error)]
pub enum EchidnaError {
    #[error("HTTP request failed: {0}")]
    Http(String),
    #[error("ECHIDNA API error: {status} — {message}")]
    Api { status: u16, message: String },
    #[error("ECHIDNA service unavailable at {url}")]
    Unavailable { url: String },
    #[error("Serialization error: {0}")]
    Serialization(String),
}

/// REST client for the ECHIDNA neurosymbolic theorem prover.
///
/// Communicates with ECHIDNA's HTTP API (default port 8000). All methods are
/// blocking; an async variant can be added behind a feature flag in future.
pub struct EchidnaClient {
    /// Base URL for the ECHIDNA API (e.g., `http://localhost:8000`).
    base_url: String,
    /// Proof result cache for offline fallback.
    cache: ProofCache,
}

impl EchidnaClient {
    /// Create a new client pointing at `base_url`.
    ///
    /// # Example
    /// ```ignore
    /// let client = EchidnaClient::new("http://localhost:8000");
    /// ```
    pub fn new(base_url: impl Into<String>) -> Self {
        Self {
            base_url: base_url.into(),
            cache: ProofCache::new(),
        }
    }

    /// Create a client with the default ECHIDNA URL (`http://localhost:8000`).
    pub fn default_url() -> Self {
        Self::new("http://localhost:8000")
    }

    /// Return the base URL this client connects to.
    pub fn base_url(&self) -> &str {
        &self.base_url
    }

    /// Access the internal proof cache (e.g., for pre-populating).
    pub fn cache(&self) -> &ProofCache {
        &self.cache
    }

    /// Mutable access to the internal proof cache.
    pub fn cache_mut(&mut self) -> &mut ProofCache {
        &mut self.cache
    }

    /// Submit a proof goal to ECHIDNA.
    ///
    /// Returns the initial `ProofResponse` (usually with status `Pending`).
    /// The proof runs asynchronously on the server; poll with `get_proof()`.
    pub fn submit_proof(&self, request: &ProofRequest) -> Result<ProofResponse, EchidnaError> {
        let url = format!("{}/api/v1/proofs", self.base_url);
        let body = serde_json::to_string(request)
            .map_err(|e| EchidnaError::Serialization(e.to_string()))?;

        let response = reqwest::blocking::Client::new()
            .post(&url)
            .header("Content-Type", "application/json")
            .body(body)
            .send()
            .map_err(|_| EchidnaError::Unavailable { url: url.clone() })?;

        if !response.status().is_success() {
            return Err(EchidnaError::Api {
                status: response.status().as_u16(),
                message: response.text().unwrap_or_default(),
            });
        }

        let proof_response: ProofResponse = response
            .json()
            .map_err(|e| EchidnaError::Serialization(e.to_string()))?;

        Ok(proof_response)
    }

    /// Query the status of an existing proof by ID.
    pub fn get_proof(&self, proof_id: &str) -> Result<ProofResponse, EchidnaError> {
        let url = format!("{}/api/v1/proofs/{}", self.base_url, proof_id);

        let response = reqwest::blocking::Client::new()
            .get(&url)
            .send()
            .map_err(|_| EchidnaError::Unavailable { url: url.clone() })?;

        if !response.status().is_success() {
            return Err(EchidnaError::Api {
                status: response.status().as_u16(),
                message: response.text().unwrap_or_default(),
            });
        }

        response
            .json()
            .map_err(|e| EchidnaError::Serialization(e.to_string()))
    }

    /// Request tactic suggestions for a proof goal.
    pub fn suggest_tactics(
        &self,
        goal: &str,
        prover: ProverKind,
    ) -> Result<Vec<TacticSuggestion>, EchidnaError> {
        let url = format!("{}/api/v1/tactics/suggest", self.base_url);
        let body = serde_json::json!({
            "goal": goal,
            "prover": prover,
        });

        let response = reqwest::blocking::Client::new()
            .post(&url)
            .json(&body)
            .send()
            .map_err(|_| EchidnaError::Unavailable { url: url.clone() })?;

        if !response.status().is_success() {
            return Err(EchidnaError::Api {
                status: response.status().as_u16(),
                message: response.text().unwrap_or_default(),
            });
        }

        response
            .json()
            .map_err(|e| EchidnaError::Serialization(e.to_string()))
    }

    /// Apply a specific tactic to a proof goal.
    pub fn apply_tactic(
        &self,
        proof_id: &str,
        tactic: &TacticSuggestion,
    ) -> Result<ProofResponse, EchidnaError> {
        let url = format!("{}/api/v1/proofs/{}/tactics", self.base_url, proof_id);

        let response = reqwest::blocking::Client::new()
            .post(&url)
            .json(tactic)
            .send()
            .map_err(|_| EchidnaError::Unavailable { url: url.clone() })?;

        if !response.status().is_success() {
            return Err(EchidnaError::Api {
                status: response.status().as_u16(),
                message: response.text().unwrap_or_default(),
            });
        }

        response
            .json()
            .map_err(|e| EchidnaError::Serialization(e.to_string()))
    }

    /// Cancel a running proof by ID.
    pub fn cancel_proof(&self, proof_id: &str) -> Result<(), EchidnaError> {
        let url = format!("{}/api/v1/proofs/{}", self.base_url, proof_id);

        let response = reqwest::blocking::Client::new()
            .delete(&url)
            .send()
            .map_err(|_| EchidnaError::Unavailable { url: url.clone() })?;

        if !response.status().is_success() {
            return Err(EchidnaError::Api {
                status: response.status().as_u16(),
                message: response.text().unwrap_or_default(),
            });
        }

        Ok(())
    }

    /// List available prover backends on the connected ECHIDNA instance.
    pub fn list_provers(&self) -> Result<Vec<ProverKind>, EchidnaError> {
        let url = format!("{}/api/v1/provers", self.base_url);

        let response = reqwest::blocking::Client::new()
            .get(&url)
            .send()
            .map_err(|_| EchidnaError::Unavailable { url: url.clone() })?;

        if !response.status().is_success() {
            return Err(EchidnaError::Api {
                status: response.status().as_u16(),
                message: response.text().unwrap_or_default(),
            });
        }

        response
            .json()
            .map_err(|e| EchidnaError::Serialization(e.to_string()))
    }

    /// Check whether the ECHIDNA service is reachable and healthy.
    pub fn health_check(&self) -> bool {
        let url = format!("{}/api/v1/health", self.base_url);
        reqwest::blocking::Client::new()
            .get(&url)
            .timeout(std::time::Duration::from_secs(3))
            .send()
            .map(|r| r.status().is_success())
            .unwrap_or(false)
    }

    /// Submit a proof with offline fallback.
    ///
    /// If ECHIDNA is reachable, submits the proof and caches the result.
    /// If ECHIDNA is unreachable, returns a cached result for the same goal
    /// (if available), or a safe default response with `TrustLevel::Level1`.
    pub fn prove_with_fallback(&mut self, request: &ProofRequest) -> ProofResponse {
        // Try the live service first.
        match self.submit_proof(request) {
            Ok(response) => {
                // Cache successful completions.
                if response.status == ProofStatus::Success || response.status == ProofStatus::Failed
                {
                    self.cache.store(&request.goal, &response);
                }
                response
            },
            Err(_) => {
                // Offline: try cache.
                if let Some(cached) = self.cache.get(&request.goal) {
                    return cached;
                }
                // No cache hit: return safe default.
                ProofResponse {
                    proof_id: "offline-fallback".to_string(),
                    status: ProofStatus::Timeout,
                    goal: request.goal.clone(),
                    prover: request.prover,
                    result: None,
                    diagnostics: vec!["ECHIDNA unavailable; returning safe default".to_string()],
                    duration_ms: None,
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn client_creation() {
        let client = EchidnaClient::default_url();
        assert_eq!(client.base_url(), "http://localhost:8000");
    }

    #[test]
    fn unavailable_uses_cache() {
        let mut client = EchidnaClient::new("http://127.0.0.1:1"); // unreachable

        // Pre-populate cache.
        let goal = "test_goal";
        let cached_response = ProofResponse {
            proof_id: "cached-001".to_string(),
            status: ProofStatus::Success,
            goal: goal.to_string(),
            prover: ProverKind::Z3,
            result: Some("proved".to_string()),
            diagnostics: vec![],
            duration_ms: Some(5),
        };
        client.cache_mut().store(goal, &cached_response);

        let request = ProofRequest {
            goal: goal.to_string(),
            prover: ProverKind::Z3,
            label: None,
            timeout_seconds: None,
        };

        let response = client.prove_with_fallback(&request);
        assert_eq!(response.proof_id, "cached-001");
        assert_eq!(response.status, ProofStatus::Success);
    }
}
