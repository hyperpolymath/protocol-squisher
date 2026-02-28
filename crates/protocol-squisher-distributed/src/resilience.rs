// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Circuit breaker pattern for resilient external service calls.
//!
//! The `CircuitBreaker` tracks consecutive failures and opens the circuit
//! when a threshold is reached, preventing cascading failures. After a
//! cooldown period (or manual reset), the circuit enters half-open state
//! where a single success closes it again.

use serde::{Deserialize, Serialize};

/// Circuit breaker states.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CircuitState {
    /// Normal operation. Requests pass through.
    Closed,
    /// Circuit is tripped. All requests are immediately rejected.
    Open,
    /// Trial state: the next request is allowed through as a probe.
    HalfOpen,
}

/// A circuit breaker for protecting against cascading failures.
///
/// When the number of consecutive failures reaches `failure_threshold`, the
/// circuit opens and all subsequent calls are rejected without executing.
/// After the circuit is manually reset (or via `try_half_open()`), a single
/// probe request is allowed. If it succeeds, the circuit closes; if it fails,
/// the circuit re-opens.
#[derive(Debug, Clone)]
pub struct CircuitBreaker {
    state: CircuitState,
    consecutive_failures: usize,
    failure_threshold: usize,
    success_threshold: usize,
    consecutive_successes: usize,
}

impl CircuitBreaker {
    /// Create a new circuit breaker.
    ///
    /// - `failure_threshold`: number of consecutive failures before opening.
    /// - `success_threshold`: number of consecutive successes in half-open
    ///   state before fully closing.
    pub fn new(failure_threshold: usize, success_threshold: usize) -> Self {
        Self {
            state: CircuitState::Closed,
            consecutive_failures: 0,
            failure_threshold,
            success_threshold,
            consecutive_successes: 0,
        }
    }

    /// Return the current circuit state.
    pub fn state(&self) -> CircuitState {
        self.state
    }

    /// Whether the circuit allows requests through.
    pub fn is_closed(&self) -> bool {
        self.state == CircuitState::Closed
    }

    /// Record a successful call.
    pub fn record_success(&mut self) {
        self.consecutive_failures = 0;

        match self.state {
            CircuitState::HalfOpen => {
                self.consecutive_successes += 1;
                if self.consecutive_successes >= self.success_threshold {
                    self.state = CircuitState::Closed;
                    self.consecutive_successes = 0;
                }
            }
            CircuitState::Open => {
                // Shouldn't happen, but recover gracefully.
                self.state = CircuitState::HalfOpen;
                self.consecutive_successes = 1;
            }
            CircuitState::Closed => {
                // Normal operation.
            }
        }
    }

    /// Record a failed call.
    pub fn record_failure(&mut self) {
        self.consecutive_successes = 0;
        self.consecutive_failures += 1;

        if self.consecutive_failures >= self.failure_threshold {
            self.state = CircuitState::Open;
        }
    }

    /// Transition from Open to HalfOpen (allows a probe request).
    pub fn try_half_open(&mut self) {
        if self.state == CircuitState::Open {
            self.state = CircuitState::HalfOpen;
            self.consecutive_successes = 0;
        }
    }

    /// Fully reset the circuit to Closed state.
    pub fn reset(&mut self) {
        self.state = CircuitState::Closed;
        self.consecutive_failures = 0;
        self.consecutive_successes = 0;
    }
}

/// Retry an operation with exponential backoff.
///
/// This is a synchronous helper that calls `operation` up to `max_retries`
/// times. On failure, it waits `base_delay_ms * 2^attempt` milliseconds
/// before retrying.
///
/// Returns the first successful result, or the last error if all retries fail.
pub fn retry_with_backoff<T, E>(
    mut operation: impl FnMut() -> Result<T, E>,
    max_retries: usize,
    base_delay_ms: u64,
) -> Result<T, E> {
    let mut last_error = None;

    for attempt in 0..=max_retries {
        match operation() {
            Ok(value) => return Ok(value),
            Err(e) => {
                last_error = Some(e);
                if attempt < max_retries {
                    let delay = base_delay_ms.saturating_mul(1u64 << attempt);
                    std::thread::sleep(std::time::Duration::from_millis(delay));
                }
            }
        }
    }

    Err(last_error.expect("at least one attempt must have been made"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn circuit_breaker_opens_after_threshold() {
        let mut cb = CircuitBreaker::new(3, 1);
        assert!(cb.is_closed());

        cb.record_failure();
        cb.record_failure();
        assert!(cb.is_closed()); // Not yet at threshold.

        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Open); // Threshold reached.
    }

    #[test]
    fn circuit_breaker_recovers_via_half_open() {
        let mut cb = CircuitBreaker::new(2, 1);

        // Trip the circuit.
        cb.record_failure();
        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Open);

        // Transition to half-open.
        cb.try_half_open();
        assert_eq!(cb.state(), CircuitState::HalfOpen);

        // Successful probe closes the circuit.
        cb.record_success();
        assert_eq!(cb.state(), CircuitState::Closed);
    }

    #[test]
    fn retry_succeeds_on_third_attempt() {
        let mut attempt = 0;
        let result: Result<i32, &str> = retry_with_backoff(
            || {
                attempt += 1;
                if attempt < 3 {
                    Err("not yet")
                } else {
                    Ok(42)
                }
            },
            5,
            1, // 1ms base delay for fast tests
        );

        assert_eq!(result.unwrap(), 42);
        assert_eq!(attempt, 3);
    }
}
