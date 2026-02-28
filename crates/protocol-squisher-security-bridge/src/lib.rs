// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Security protocol bridging between TLS profiles and Noise patterns.
//!
//! The bridge enforces conservative safety rules:
//! - reject unsafe/legacy TLS versions
//! - reject weak key-exchange and unauthenticated combinations
//! - verify requested security properties before accepting a translation

use serde::{Deserialize, Serialize};
use std::fmt;

/// Supported TLS protocol versions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TlsVersion {
    Tls10,
    Tls11,
    Tls12,
    Tls13,
}

/// Key exchange mechanisms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum KeyExchange {
    RsaKeyExchange,
    Dhe,
    Ecdhe,
    PskOnly,
}

/// Noise framework handshake patterns.
///
/// Each pattern implies a different trust model:
/// - `NN`: No authentication on either side (anonymous).
/// - `XX`: Both parties transmit their static keys during handshake.
/// - `IK`: Initiator knows responder's static key ahead of time.
/// - `NK`: Initiator knows responder's key; responder doesn't authenticate initiator.
/// - `KK`: Both parties know each other's static keys before the handshake.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum NoisePattern {
    NN,
    XX,
    IK,
    NK,
    KK,
}

/// Security properties that a bridge translation can provide.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SecurityProperty {
    ForwardSecrecy,
    MutualAuthentication,
    IdentityHiding,
    ReplayResistance,
    ZeroRoundTrip,
    PostQuantumResistance,
}

/// Protocol families that the security bridge can translate between.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProtocolFamily {
    Tls,
    Noise,
    WireGuard,
}

/// Errors from the security bridge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BridgeError {
    /// The source protocol configuration is unsafe and cannot be bridged.
    UnsafeConfiguration(String),
    /// The requested translation is not supported between these families.
    UnsupportedTranslation {
        from: ProtocolFamily,
        to: ProtocolFamily,
    },
    /// Required security properties cannot be satisfied by the target.
    MissingProperties(Vec<SecurityProperty>),
}

impl fmt::Display for BridgeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BridgeError::UnsafeConfiguration(reason) => write!(f, "unsafe configuration: {reason}"),
            BridgeError::UnsupportedTranslation { from, to } => {
                write!(f, "unsupported translation: {from:?} -> {to:?}")
            }
            BridgeError::MissingProperties(props) => {
                write!(f, "missing required properties: {props:?}")
            }
        }
    }
}

impl std::error::Error for BridgeError {}

/// Minimum security requirements for accepting a translation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityRequirements {
    /// Properties that the target MUST provide.
    pub required_properties: Vec<SecurityProperty>,
    /// Minimum TLS version to accept as input (defaults to TLS 1.2).
    pub min_tls_version: Option<TlsVersion>,
    /// Whether to reject configurations without forward secrecy.
    pub require_forward_secrecy: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TlsProfile {
    pub version: TlsVersion,
    pub key_exchange: KeyExchange,
    pub mutual_authentication: bool,
    pub cert_validation: bool,
    pub session_resumption: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SecurityBridge {
    pub noise_pattern: NoisePattern,
    pub properties: Vec<SecurityProperty>,
    pub notes: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum BridgeDecision {
    Accept(SecurityBridge),
    Reject { reason: String },
}

pub fn translate_tls_to_noise(profile: &TlsProfile) -> BridgeDecision {
    if matches!(profile.version, TlsVersion::Tls10 | TlsVersion::Tls11) {
        return BridgeDecision::Reject {
            reason: "Legacy TLS versions (1.0/1.1) are rejected.".to_string(),
        };
    }

    if !profile.cert_validation {
        return BridgeDecision::Reject {
            reason: "Certificate validation disabled; unsafe translation rejected.".to_string(),
        };
    }

    if matches!(
        profile.key_exchange,
        KeyExchange::RsaKeyExchange | KeyExchange::PskOnly
    ) {
        return BridgeDecision::Reject {
            reason: "Non-forward-secret key exchange is rejected.".to_string(),
        };
    }

    let pattern = if profile.mutual_authentication {
        NoisePattern::IK
    } else {
        NoisePattern::XX
    };

    let mut properties = vec![
        SecurityProperty::ForwardSecrecy,
        SecurityProperty::ReplayResistance,
    ];
    let mut notes = vec!["Translated from TLS profile using conservative policy.".to_string()];

    if profile.mutual_authentication {
        properties.push(SecurityProperty::MutualAuthentication);
    } else {
        properties.push(SecurityProperty::IdentityHiding);
    }

    if profile.session_resumption {
        notes.push(
            "Session resumption enabled; evaluate replay windows at deployment edge.".to_string(),
        );
    }

    BridgeDecision::Accept(SecurityBridge {
        noise_pattern: pattern,
        properties,
        notes,
    })
}

/// Verify that a TLS→Noise translation satisfies a set of required security
/// properties. Returns `Reject` if any property is missing.
pub fn verify_security_properties(
    profile: &TlsProfile,
    required: &[SecurityProperty],
) -> BridgeDecision {
    match translate_tls_to_noise(profile) {
        BridgeDecision::Reject { reason } => BridgeDecision::Reject { reason },
        BridgeDecision::Accept(bridge) => {
            let missing: Vec<_> = required
                .iter()
                .filter(|p| !bridge.properties.contains(p))
                .copied()
                .collect();

            if missing.is_empty() {
                BridgeDecision::Accept(bridge)
            } else {
                BridgeDecision::Reject {
                    reason: format!("Required properties not satisfied: {:?}", missing),
                }
            }
        },
    }
}

/// WireGuard uses Noise_IKpsk2 under the hood. This function determines the
/// minimum Noise pattern that could serve as a bridge from a TLS profile to a
/// WireGuard-compatible tunnel.
///
/// WireGuard requires:
/// - Static keys pre-shared (maps to IK or KK)
/// - Forward secrecy via ephemeral DH
/// - PSK layer for post-quantum hedging
pub fn translate_tls_to_wireguard(profile: &TlsProfile) -> BridgeDecision {
    // WireGuard mandates forward secrecy, so reject anything without it
    if matches!(
        profile.key_exchange,
        KeyExchange::RsaKeyExchange | KeyExchange::PskOnly
    ) {
        return BridgeDecision::Reject {
            reason: "WireGuard requires forward-secret key exchange (ECDHE or DHE).".to_string(),
        };
    }

    if matches!(profile.version, TlsVersion::Tls10 | TlsVersion::Tls11) {
        return BridgeDecision::Reject {
            reason: "Legacy TLS versions cannot map to WireGuard's Noise_IKpsk2.".to_string(),
        };
    }

    if !profile.cert_validation {
        return BridgeDecision::Reject {
            reason: "WireGuard requires authenticated peers; cert validation must be enabled."
                .to_string(),
        };
    }

    // WireGuard always uses IK (initiator knows responder's static key)
    let properties = vec![
        SecurityProperty::ForwardSecrecy,
        SecurityProperty::MutualAuthentication,
        SecurityProperty::ReplayResistance,
    ];

    let mut notes =
        vec!["WireGuard tunnel uses Noise_IKpsk2; PSK must be provisioned separately.".to_string()];

    if !profile.mutual_authentication {
        notes.push(
            "Source TLS profile lacks mutual auth; WireGuard enforces it via static keys."
                .to_string(),
        );
    }

    BridgeDecision::Accept(SecurityBridge {
        noise_pattern: NoisePattern::IK,
        properties,
        notes,
    })
}

/// Determine the minimum TLS requirements needed to match a given Noise pattern.
///
/// This is the reverse direction: given a Noise handshake we want to run, what
/// TLS profile constraints would provide equivalent security?
pub fn noise_to_tls_requirements(pattern: NoisePattern) -> SecurityRequirements {
    match pattern {
        NoisePattern::NN => SecurityRequirements {
            required_properties: vec![],
            min_tls_version: Some(TlsVersion::Tls12),
            require_forward_secrecy: false,
        },
        NoisePattern::NK => SecurityRequirements {
            required_properties: vec![SecurityProperty::ForwardSecrecy],
            min_tls_version: Some(TlsVersion::Tls12),
            require_forward_secrecy: true,
        },
        NoisePattern::XX => SecurityRequirements {
            required_properties: vec![
                SecurityProperty::ForwardSecrecy,
                SecurityProperty::IdentityHiding,
            ],
            min_tls_version: Some(TlsVersion::Tls13),
            require_forward_secrecy: true,
        },
        NoisePattern::IK | NoisePattern::KK => SecurityRequirements {
            required_properties: vec![
                SecurityProperty::ForwardSecrecy,
                SecurityProperty::MutualAuthentication,
                SecurityProperty::ReplayResistance,
            ],
            min_tls_version: Some(TlsVersion::Tls13),
            require_forward_secrecy: true,
        },
    }
}

/// List the security properties guaranteed by a given Noise pattern.
pub fn noise_pattern_properties(pattern: NoisePattern) -> Vec<SecurityProperty> {
    let mut props = vec![SecurityProperty::ReplayResistance];
    match pattern {
        NoisePattern::NN => {}
        NoisePattern::NK => {
            props.push(SecurityProperty::ForwardSecrecy);
        }
        NoisePattern::XX => {
            props.push(SecurityProperty::ForwardSecrecy);
            props.push(SecurityProperty::IdentityHiding);
        }
        NoisePattern::IK => {
            props.push(SecurityProperty::ForwardSecrecy);
            props.push(SecurityProperty::MutualAuthentication);
        }
        NoisePattern::KK => {
            props.push(SecurityProperty::ForwardSecrecy);
            props.push(SecurityProperty::MutualAuthentication);
        }
    }
    props
}

#[cfg(test)]
mod tests {
    use super::*;

    fn secure_tls13_profile() -> TlsProfile {
        TlsProfile {
            version: TlsVersion::Tls13,
            key_exchange: KeyExchange::Ecdhe,
            mutual_authentication: true,
            cert_validation: true,
            session_resumption: false,
        }
    }

    #[test]
    fn tls13_mutual_auth_maps_to_ik() {
        let profile = secure_tls13_profile();
        let decision = translate_tls_to_noise(&profile);

        match decision {
            BridgeDecision::Accept(bridge) => {
                assert_eq!(bridge.noise_pattern, NoisePattern::IK);
                assert!(bridge
                    .properties
                    .contains(&SecurityProperty::ForwardSecrecy));
                assert!(bridge
                    .properties
                    .contains(&SecurityProperty::MutualAuthentication));
            },
            BridgeDecision::Reject { reason } => {
                panic!("expected accept, got reject: {reason}");
            },
        }
    }

    #[test]
    fn legacy_tls_is_rejected() {
        let mut profile = secure_tls13_profile();
        profile.version = TlsVersion::Tls10;

        let decision = translate_tls_to_noise(&profile);
        assert!(matches!(decision, BridgeDecision::Reject { .. }));
    }

    #[test]
    fn weak_key_exchange_is_rejected() {
        let mut profile = secure_tls13_profile();
        profile.key_exchange = KeyExchange::RsaKeyExchange;

        let decision = translate_tls_to_noise(&profile);
        assert!(matches!(decision, BridgeDecision::Reject { .. }));
    }

    #[test]
    fn property_verification_rejects_missing_requirements() {
        let mut profile = secure_tls13_profile();
        profile.mutual_authentication = false;

        let decision =
            verify_security_properties(&profile, &[SecurityProperty::MutualAuthentication]);
        assert!(matches!(decision, BridgeDecision::Reject { .. }));
    }

    #[test]
    fn tls13_ecdhe_maps_to_wireguard() {
        let profile = secure_tls13_profile();
        let decision = translate_tls_to_wireguard(&profile);
        match decision {
            BridgeDecision::Accept(bridge) => {
                assert_eq!(bridge.noise_pattern, NoisePattern::IK);
                assert!(bridge
                    .properties
                    .contains(&SecurityProperty::MutualAuthentication));
            }
            BridgeDecision::Reject { reason } => {
                panic!("expected accept for WireGuard, got reject: {reason}");
            }
        }
    }

    #[test]
    fn rsa_rejected_for_wireguard() {
        let mut profile = secure_tls13_profile();
        profile.key_exchange = KeyExchange::RsaKeyExchange;
        let decision = translate_tls_to_wireguard(&profile);
        assert!(matches!(decision, BridgeDecision::Reject { .. }));
    }

    #[test]
    fn noise_ik_requires_tls13_and_mutual_auth() {
        let reqs = noise_to_tls_requirements(NoisePattern::IK);
        assert_eq!(reqs.min_tls_version, Some(TlsVersion::Tls13));
        assert!(reqs.require_forward_secrecy);
        assert!(reqs
            .required_properties
            .contains(&SecurityProperty::MutualAuthentication));
    }

    #[test]
    fn noise_nn_has_minimal_requirements() {
        let reqs = noise_to_tls_requirements(NoisePattern::NN);
        assert!(!reqs.require_forward_secrecy);
        assert!(reqs.required_properties.is_empty());
    }

    #[test]
    fn noise_pattern_properties_are_consistent() {
        let ik_props = noise_pattern_properties(NoisePattern::IK);
        assert!(ik_props.contains(&SecurityProperty::ForwardSecrecy));
        assert!(ik_props.contains(&SecurityProperty::MutualAuthentication));

        let nn_props = noise_pattern_properties(NoisePattern::NN);
        assert!(!nn_props.contains(&SecurityProperty::ForwardSecrecy));
    }

    #[test]
    fn bridge_error_display() {
        let err = BridgeError::UnsafeConfiguration("test".into());
        assert!(err.to_string().contains("unsafe configuration"));

        let err = BridgeError::UnsupportedTranslation {
            from: ProtocolFamily::Tls,
            to: ProtocolFamily::WireGuard,
        };
        assert!(err.to_string().contains("unsupported translation"));
    }
}
