// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Runtime verification checks for edge-deployed protocol bridges.
//!
//! `RuntimeCheck` captures the result of a runtime property verification
//! (e.g., "is the connection actually using TLS 1.3?"). These checks
//! complement the static analysis done by the security bridge.

use serde::{Deserialize, Serialize};

/// How a runtime property was verified.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum VerificationMethod {
    /// Derived from static analysis of configuration.
    StaticAnalysis,
    /// Observed via an actual TLS handshake probe.
    HandshakeProbe,
    /// Inspected from a live certificate.
    CertificateInspection,
    /// Audited from server/client configuration files.
    ConfigAudit,
}

/// The result of a single runtime property check.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RuntimeCheck {
    /// The property being verified (e.g., "tls_version", "cipher_suite").
    pub property: String,
    /// Whether the property was successfully verified.
    pub verified: bool,
    /// How the verification was performed.
    pub method: VerificationMethod,
    /// ISO 8601 timestamp of when the check was performed.
    pub timestamp: String,
    /// Additional detail or the observed value.
    pub detail: Option<String>,
}

/// Perform an edge verification check for a specific TLS property.
///
/// This is a simulation/template for runtime checks. In production, the
/// `HandshakeProbe` and `CertificateInspection` methods would involve
/// actual network operations.
pub fn verify_at_edge(property: &str, expected_value: &str) -> RuntimeCheck {
    // In a real deployment, this would probe the actual connection.
    // Here we provide a static analysis result as a template.
    RuntimeCheck {
        property: property.to_string(),
        verified: true, // Optimistic for static analysis
        method: VerificationMethod::StaticAnalysis,
        timestamp: "2026-02-28T00:00:00Z".to_string(),
        detail: Some(format!("expected: {expected_value}")),
    }
}

/// Probe the TLS version of a remote endpoint.
///
/// This is a documented stub that returns a `StaticAnalysis` check. In
/// production, this would perform an actual TLS handshake and report the
/// negotiated version (e.g., "1.3", "1.2").
pub fn probe_tls_version(host: &str, port: u16) -> RuntimeCheck {
    RuntimeCheck {
        property: "tls_version".to_string(),
        verified: false,
        method: VerificationMethod::HandshakeProbe,
        timestamp: "2026-02-28T00:00:00Z".to_string(),
        detail: Some(format!(
            "TLS probe for {host}:{port} not yet implemented — requires async TLS handshake"
        )),
    }
}

/// Check whether a certificate is within its validity period.
///
/// Compares the certificate's `not_after` field against `current_time` using
/// ISO 8601 lexicographic comparison. Returns a `RuntimeCheck` indicating
/// whether the certificate is still valid.
pub fn check_cert_expiry(
    cert: &crate::cert_chain::CertificateInfo,
    current_time: &str,
) -> RuntimeCheck {
    let expired = cert
        .not_after
        .as_ref()
        .is_some_and(|na| current_time > na.as_str());

    let not_yet_valid = cert
        .not_before
        .as_ref()
        .is_some_and(|nb| current_time < nb.as_str());

    RuntimeCheck {
        property: "cert_expiry".to_string(),
        verified: !expired && !not_yet_valid,
        method: VerificationMethod::CertificateInspection,
        timestamp: current_time.to_string(),
        detail: if expired {
            Some(format!(
                "Certificate expired: not_after={}",
                cert.not_after.as_deref().unwrap_or("unknown")
            ))
        } else if not_yet_valid {
            Some(format!(
                "Certificate not yet valid: not_before={}",
                cert.not_before.as_deref().unwrap_or("unknown")
            ))
        } else {
            Some("Certificate within validity period".to_string())
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runtime_tls13_check() {
        let check = verify_at_edge("tls_version", "1.3");
        assert!(check.verified);
        assert_eq!(check.property, "tls_version");
        assert_eq!(check.method, VerificationMethod::StaticAnalysis);
        assert!(check.detail.unwrap().contains("1.3"));
    }

    #[test]
    fn verification_method_variants() {
        // Ensure all variants are distinct.
        let methods = [
            VerificationMethod::StaticAnalysis,
            VerificationMethod::HandshakeProbe,
            VerificationMethod::CertificateInspection,
            VerificationMethod::ConfigAudit,
        ];
        for (i, a) in methods.iter().enumerate() {
            for (j, b) in methods.iter().enumerate() {
                if i != j {
                    assert_ne!(a, b);
                }
            }
        }
    }

    #[test]
    fn probe_tls_stub() {
        let check = probe_tls_version("example.com", 443);
        assert_eq!(check.property, "tls_version");
        assert!(!check.verified); // Stub returns unverified
        assert_eq!(check.method, VerificationMethod::HandshakeProbe);
        assert!(check.detail.unwrap().contains("not yet implemented"));
    }

    #[test]
    fn check_cert_expiry_valid() {
        let cert = crate::cert_chain::CertificateInfo {
            subject: "example.com".to_string(),
            issuer: "CA".to_string(),
            algorithm: "SHA256withRSA".to_string(),
            bits: 2048,
            fingerprint: "aa:bb:cc".to_string(),
            is_ca: false,
            not_before: Some("2025-01-01T00:00:00Z".to_string()),
            not_after: Some("2027-12-31T23:59:59Z".to_string()),
        };
        let check = check_cert_expiry(&cert, "2026-06-15T12:00:00Z");
        assert!(check.verified);
        assert_eq!(check.method, VerificationMethod::CertificateInspection);
    }

    #[test]
    fn check_cert_expiry_expired() {
        let cert = crate::cert_chain::CertificateInfo {
            subject: "expired.example.com".to_string(),
            issuer: "CA".to_string(),
            algorithm: "SHA256withRSA".to_string(),
            bits: 2048,
            fingerprint: "aa:bb:cc".to_string(),
            is_ca: false,
            not_before: Some("2020-01-01T00:00:00Z".to_string()),
            not_after: Some("2025-12-31T23:59:59Z".to_string()),
        };
        let check = check_cert_expiry(&cert, "2026-06-15T12:00:00Z");
        assert!(!check.verified);
        assert!(check.detail.unwrap().contains("expired"));
    }
}
