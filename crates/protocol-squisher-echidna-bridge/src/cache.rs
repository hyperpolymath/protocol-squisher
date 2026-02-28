// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! In-memory proof result cache with optional TTL expiry.
//!
//! `ProofCache` stores `ProofResponse` values keyed by goal string hash.
//! When ECHIDNA is unavailable, cached results allow the bridge to return
//! previously computed proof outcomes instead of failing outright.

use crate::types::ProofResponse;
use std::collections::HashMap;
use std::time::{Duration, Instant};

/// Default time-to-live for cached proof results (1 hour).
const DEFAULT_TTL: Duration = Duration::from_secs(3600);

/// A cached proof result with an expiration timestamp.
#[derive(Debug, Clone)]
pub struct CachedProofResult {
    /// The cached proof response.
    pub response: ProofResponse,
    /// When this entry was stored.
    stored_at: Instant,
    /// How long this entry is valid.
    ttl: Duration,
}

impl CachedProofResult {
    /// Whether this cache entry has expired.
    pub fn is_expired(&self) -> bool {
        self.stored_at.elapsed() > self.ttl
    }
}

/// In-memory cache for ECHIDNA proof results.
///
/// Proof responses are indexed by goal string. Expired entries are not returned
/// by `get()` but are lazily purged (not removed until the next `store()` or
/// explicit `purge_expired()` call).
pub struct ProofCache {
    entries: HashMap<String, CachedProofResult>,
    ttl: Duration,
}

impl ProofCache {
    /// Create a new cache with the default TTL (1 hour).
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
            ttl: DEFAULT_TTL,
        }
    }

    /// Create a cache with a custom TTL.
    pub fn with_ttl(ttl: Duration) -> Self {
        Self {
            entries: HashMap::new(),
            ttl,
        }
    }

    /// Store a proof response in the cache, keyed by goal string.
    pub fn store(&mut self, goal: &str, response: &ProofResponse) {
        self.entries.insert(
            goal.to_string(),
            CachedProofResult {
                response: response.clone(),
                stored_at: Instant::now(),
                ttl: self.ttl,
            },
        );
    }

    /// Retrieve a cached proof response for a goal, if present and not expired.
    pub fn get(&self, goal: &str) -> Option<ProofResponse> {
        self.entries.get(goal).and_then(|entry| {
            if entry.is_expired() {
                None
            } else {
                Some(entry.response.clone())
            }
        })
    }

    /// Return the number of entries in the cache (including expired ones).
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the cache has no entries.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Remove all expired entries from the cache.
    pub fn purge_expired(&mut self) {
        self.entries.retain(|_, entry| !entry.is_expired());
    }

    /// Clear all entries from the cache.
    pub fn clear(&mut self) {
        self.entries.clear();
    }
}

impl Default for ProofCache {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{ProofStatus, ProverKind};

    fn sample_response(goal: &str) -> ProofResponse {
        ProofResponse {
            proof_id: "pf-test".to_string(),
            status: ProofStatus::Success,
            goal: goal.to_string(),
            prover: ProverKind::Z3,
            result: Some("proved".to_string()),
            diagnostics: vec![],
            duration_ms: Some(5),
        }
    }

    #[test]
    fn cache_store_retrieve() {
        let mut cache = ProofCache::new();
        let response = sample_response("goal_a");

        cache.store("goal_a", &response);
        let retrieved = cache.get("goal_a");

        assert!(retrieved.is_some());
        assert_eq!(retrieved.unwrap().proof_id, "pf-test");
    }

    #[test]
    fn cache_miss() {
        let cache = ProofCache::new();
        assert!(cache.get("nonexistent").is_none());
    }

    #[test]
    fn cache_expiry() {
        // Use a zero-duration TTL so entries expire immediately.
        let mut cache = ProofCache::with_ttl(Duration::from_secs(0));
        let response = sample_response("goal_b");

        cache.store("goal_b", &response);
        // Entry should be expired by the time we retrieve it.
        // (Instant resolution means this might occasionally pass on very fast
        // machines; using Duration::ZERO makes it reliably expire.)
        std::thread::sleep(Duration::from_millis(1));
        assert!(cache.get("goal_b").is_none());
    }

    #[test]
    fn cache_purge() {
        let mut cache = ProofCache::with_ttl(Duration::from_secs(0));
        cache.store("a", &sample_response("a"));
        cache.store("b", &sample_response("b"));
        assert_eq!(cache.len(), 2);

        std::thread::sleep(Duration::from_millis(1));
        cache.purge_expired();
        assert_eq!(cache.len(), 0);
    }
}
