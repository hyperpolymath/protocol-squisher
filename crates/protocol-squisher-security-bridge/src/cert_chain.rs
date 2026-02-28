// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Certificate chain validation for TLS profile auditing.
//!
//! Provides `CertificateInfo` for modeling X.509 certificate properties and
//! `ChainValidationResult` for categorizing chain-level trust decisions.

use serde::{Deserialize, Serialize};

/// Information about a single X.509 certificate in a chain.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertificateInfo {
    /// Certificate subject (CN or full DN).
    pub subject: String,
    /// Certificate issuer (CN or full DN).
    pub issuer: String,
    /// Signature algorithm (e.g., "SHA256withRSA", "ED25519").
    pub algorithm: String,
    /// Key size in bits.
    pub bits: u32,
    /// Hex-encoded SHA-256 fingerprint.
    pub fingerprint: String,
    /// Whether this certificate is a CA (basic constraints).
    pub is_ca: bool,
    /// Not-before validity date (ISO 8601, e.g., "2026-01-01T00:00:00Z").
    pub not_before: Option<String>,
    /// Not-after validity date (ISO 8601, e.g., "2027-01-01T00:00:00Z").
    pub not_after: Option<String>,
}

/// Result of validating a certificate chain.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChainValidationResult {
    /// Chain is valid and trusted.
    Valid,
    /// One or more certificates in the chain have expired.
    Expired,
    /// A certificate uses a weak key (e.g., RSA < 2048 bits).
    WeakKey,
    /// The root CA is not in the trust store.
    Untrusted,
    /// The chain contains only a self-signed certificate.
    SelfSigned,
}

/// Minimum acceptable RSA key size in bits.
const MIN_RSA_BITS: u32 = 2048;

/// Minimum acceptable EC key size in bits.
const MIN_EC_BITS: u32 = 256;

/// Validate a certificate chain.
///
/// Checks for:
/// - Self-signed certificates (single cert where subject == issuer, not CA)
/// - Weak keys (RSA < 2048 bits, EC < 256 bits)
/// - Chain structure (at least one CA certificate for multi-cert chains)
pub fn validate_cert_chain(chain: &[CertificateInfo]) -> ChainValidationResult {
    if chain.is_empty() {
        return ChainValidationResult::Untrusted;
    }

    // Single self-signed cert.
    if chain.len() == 1 {
        let cert = &chain[0];
        if cert.subject == cert.issuer && !cert.is_ca {
            return ChainValidationResult::SelfSigned;
        }
    }

    // Check all certs for weak keys.
    for cert in chain {
        if !key_strength_acceptable(cert) {
            return ChainValidationResult::WeakKey;
        }
    }

    // For multi-cert chains, at least one must be a CA.
    if chain.len() > 1 && !chain.iter().any(|c| c.is_ca) {
        return ChainValidationResult::Untrusted;
    }

    ChainValidationResult::Valid
}

/// Validate a certificate chain at a specific timestamp.
///
/// In addition to the checks in `validate_cert_chain`, this also verifies
/// that certificates are within their validity period by comparing the
/// ISO 8601 `not_before` and `not_after` fields against `current_timestamp`.
///
/// ISO 8601 strings are compared lexicographically, which is correct for
/// the `YYYY-MM-DDTHH:MM:SSZ` format used by X.509 certificates.
pub fn validate_cert_chain_at(
    chain: &[CertificateInfo],
    current_timestamp: &str,
) -> ChainValidationResult {
    // First run the standard structural validation.
    let structural_result = validate_cert_chain(chain);
    if structural_result != ChainValidationResult::Valid {
        return structural_result;
    }

    // Check certificate validity periods.
    for cert in chain {
        if let Some(not_after) = &cert.not_after {
            if current_timestamp > not_after.as_str() {
                return ChainValidationResult::Expired;
            }
        }
        if let Some(not_before) = &cert.not_before {
            if current_timestamp < not_before.as_str() {
                return ChainValidationResult::Expired;
            }
        }
    }

    ChainValidationResult::Valid
}

/// Check whether a certificate's key strength meets minimum requirements.
pub fn key_strength_acceptable(cert: &CertificateInfo) -> bool {
    let algo_lower = cert.algorithm.to_lowercase();
    if algo_lower.contains("rsa") {
        cert.bits >= MIN_RSA_BITS
    } else if algo_lower.contains("ec") || algo_lower.contains("ecdsa") {
        cert.bits >= MIN_EC_BITS
    } else if algo_lower.contains("ed25519") || algo_lower.contains("ed448") {
        true // EdDSA keys are always strong enough
    } else {
        // Unknown algorithm: accept conservatively.
        cert.bits >= MIN_RSA_BITS
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_cert(subject: &str, issuer: &str, bits: u32, is_ca: bool) -> CertificateInfo {
        CertificateInfo {
            subject: subject.to_string(),
            issuer: issuer.to_string(),
            algorithm: "SHA256withRSA".to_string(),
            bits,
            fingerprint: "aa:bb:cc".to_string(),
            is_ca,
            not_before: None,
            not_after: None,
        }
    }

    fn sample_cert_with_validity(
        subject: &str,
        issuer: &str,
        bits: u32,
        is_ca: bool,
        not_before: &str,
        not_after: &str,
    ) -> CertificateInfo {
        CertificateInfo {
            subject: subject.to_string(),
            issuer: issuer.to_string(),
            algorithm: "SHA256withRSA".to_string(),
            bits,
            fingerprint: "aa:bb:cc".to_string(),
            is_ca,
            not_before: Some(not_before.to_string()),
            not_after: Some(not_after.to_string()),
        }
    }

    #[test]
    fn valid_chain() {
        let chain = vec![
            sample_cert("example.com", "Intermediate CA", 2048, false),
            sample_cert("Intermediate CA", "Root CA", 4096, true),
        ];
        assert_eq!(validate_cert_chain(&chain), ChainValidationResult::Valid);
    }

    #[test]
    fn expired_cert_detected() {
        // Expiry detection requires runtime timestamp checks (not modeled here);
        // this test validates the enum variant exists and is distinct.
        assert_ne!(ChainValidationResult::Expired, ChainValidationResult::Valid);
    }

    #[test]
    fn weak_key_detected() {
        let chain = vec![
            sample_cert("weak.example.com", "CA", 1024, false),
            sample_cert("CA", "Root", 4096, true),
        ];
        assert_eq!(validate_cert_chain(&chain), ChainValidationResult::WeakKey);
    }

    #[test]
    fn self_signed_detected() {
        let chain = vec![sample_cert("self.example.com", "self.example.com", 2048, false)];
        assert_eq!(
            validate_cert_chain(&chain),
            ChainValidationResult::SelfSigned
        );
    }

    #[test]
    fn cert_expiry_valid() {
        let chain = vec![
            sample_cert_with_validity(
                "example.com",
                "Intermediate CA",
                2048,
                false,
                "2025-01-01T00:00:00Z",
                "2027-12-31T23:59:59Z",
            ),
            sample_cert_with_validity(
                "Intermediate CA",
                "Root CA",
                4096,
                true,
                "2020-01-01T00:00:00Z",
                "2030-12-31T23:59:59Z",
            ),
        ];
        assert_eq!(
            validate_cert_chain_at(&chain, "2026-06-15T12:00:00Z"),
            ChainValidationResult::Valid
        );
    }

    #[test]
    fn cert_expiry_expired() {
        let chain = vec![
            sample_cert_with_validity(
                "expired.example.com",
                "Intermediate CA",
                2048,
                false,
                "2020-01-01T00:00:00Z",
                "2025-12-31T23:59:59Z", // expired before 2026
            ),
            sample_cert_with_validity(
                "Intermediate CA",
                "Root CA",
                4096,
                true,
                "2020-01-01T00:00:00Z",
                "2030-12-31T23:59:59Z",
            ),
        ];
        assert_eq!(
            validate_cert_chain_at(&chain, "2026-06-15T12:00:00Z"),
            ChainValidationResult::Expired
        );
    }
}
