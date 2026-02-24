// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Security protocol bridging between TLS profiles and Noise patterns.
//!
//! The bridge enforces conservative safety rules:
//! - reject unsafe/legacy TLS versions
//! - reject weak key-exchange and unauthenticated combinations
//! - verify requested security properties before accepting a translation

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TlsVersion {
    Tls10,
    Tls11,
    Tls12,
    Tls13,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum KeyExchange {
    RsaKeyExchange,
    Dhe,
    Ecdhe,
    PskOnly,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum NoisePattern {
    NN,
    XX,
    IK,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SecurityProperty {
    ForwardSecrecy,
    MutualAuthentication,
    IdentityHiding,
    ReplayResistance,
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
}
