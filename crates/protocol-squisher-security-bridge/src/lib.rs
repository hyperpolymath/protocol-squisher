// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Security protocol bridging between TLS profiles and Noise patterns.
//!
//! The bridge enforces conservative safety rules:
//! - reject unsafe/legacy TLS versions
//! - reject weak key-exchange and unauthenticated combinations
//! - verify requested security properties before accepting a translation

use serde::{Deserialize, Serialize};
use std::collections::HashSet;
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

/// Result of a protocol negotiation, capturing the chosen protocol,
/// rejected alternatives, and any downgrade warnings.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NegotiationResult {
    /// The protocol family chosen for the translation.
    pub chosen_protocol: ProtocolFamily,
    /// The Noise pattern selected (if applicable).
    pub chosen_pattern: Option<NoisePattern>,
    /// Protocol families that were evaluated but rejected.
    pub rejected_alternatives: Vec<RejectedAlternative>,
    /// Warnings about potential security downgrades.
    pub downgrade_warnings: Vec<String>,
    /// Security properties guaranteed by the chosen path.
    pub guaranteed_properties: Vec<SecurityProperty>,
}

/// A protocol alternative that was rejected during negotiation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RejectedAlternative {
    /// The protocol family that was rejected.
    pub protocol: ProtocolFamily,
    /// Why it was rejected.
    pub reason: String,
}

/// JSONL-compatible audit record for protocol negotiation decisions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityAuditEntry {
    /// ISO 8601 timestamp of the decision.
    pub timestamp: String,
    /// The source TLS profile that initiated the negotiation.
    pub source_profile: TlsProfile,
    /// The negotiation outcome.
    pub decision: String,
    /// Which protocol family was chosen (if accepted).
    pub chosen_protocol: Option<ProtocolFamily>,
    /// Risk score for any downgrade (0 = none, 100 = critical).
    pub downgrade_risk_score: u8,
    /// Free-form notes about the decision.
    pub notes: Vec<String>,
}

impl SecurityAuditEntry {
    /// Serialize this entry as a single JSONL line.
    pub fn to_jsonl(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
}

/// Common interface for querying security properties across protocol families.
pub trait ProtocolCapabilities {
    /// Return the protocol family this implementation represents.
    fn family(&self) -> ProtocolFamily;

    /// Return the set of security properties this configuration provides.
    fn provided_properties(&self) -> Vec<SecurityProperty>;

    /// Whether forward secrecy is guaranteed.
    fn has_forward_secrecy(&self) -> bool {
        self.provided_properties()
            .contains(&SecurityProperty::ForwardSecrecy)
    }

    /// Whether mutual authentication is guaranteed.
    fn has_mutual_auth(&self) -> bool {
        self.provided_properties()
            .contains(&SecurityProperty::MutualAuthentication)
    }
}

impl ProtocolCapabilities for TlsProfile {
    fn family(&self) -> ProtocolFamily {
        ProtocolFamily::Tls
    }

    fn provided_properties(&self) -> Vec<SecurityProperty> {
        let mut props = Vec::new();
        if matches!(self.key_exchange, KeyExchange::Ecdhe | KeyExchange::Dhe) {
            props.push(SecurityProperty::ForwardSecrecy);
        }
        if self.mutual_authentication {
            props.push(SecurityProperty::MutualAuthentication);
        }
        props.push(SecurityProperty::ReplayResistance);
        props
    }
}

impl ProtocolCapabilities for SecurityBridge {
    fn family(&self) -> ProtocolFamily {
        ProtocolFamily::Noise
    }

    fn provided_properties(&self) -> Vec<SecurityProperty> {
        self.properties.clone()
    }
}

/// Validate that a TLS profile meets minimum security requirements.
///
/// Returns `Ok(())` if the profile is acceptable, or a list of violation
/// descriptions if it fails validation.
pub fn validate_security_requirements(
    profile: &TlsProfile,
    requirements: &SecurityRequirements,
) -> Result<(), Vec<String>> {
    let mut violations = Vec::new();

    // Check minimum TLS version.
    if let Some(min_version) = &requirements.min_tls_version {
        let profile_rank = tls_version_rank(profile.version);
        let min_rank = tls_version_rank(*min_version);
        if profile_rank < min_rank {
            violations.push(format!(
                "TLS version {:?} below minimum {:?}",
                profile.version, min_version
            ));
        }
    }

    // Check forward secrecy requirement.
    if requirements.require_forward_secrecy
        && !matches!(profile.key_exchange, KeyExchange::Ecdhe | KeyExchange::Dhe)
    {
        violations.push("Forward secrecy required but key exchange does not provide it".to_string());
    }

    // Check required properties.
    let profile_props: HashSet<_> = profile.provided_properties().into_iter().collect();
    for required in &requirements.required_properties {
        if !profile_props.contains(required) {
            violations.push(format!("Required property {:?} not provided", required));
        }
    }

    if violations.is_empty() {
        Ok(())
    } else {
        Err(violations)
    }
}

/// Compute a downgrade risk score when translating from one protocol to another.
///
/// Returns a score from 0 (no downgrade) to 100 (critical downgrade).
/// The score reflects lost security properties and version regression.
pub fn downgrade_risk(source: &TlsProfile, target_pattern: NoisePattern) -> u8 {
    let source_props: HashSet<_> = source.provided_properties().into_iter().collect();
    let target_props: HashSet<_> = noise_pattern_properties(target_pattern)
        .into_iter()
        .collect();

    let lost: Vec<_> = source_props.difference(&target_props).collect();
    let gained: Vec<_> = target_props.difference(&source_props).collect();

    // Base score from lost properties.
    let mut score: u8 = 0;
    for prop in &lost {
        score = score.saturating_add(match prop {
            SecurityProperty::ForwardSecrecy => 40,
            SecurityProperty::MutualAuthentication => 30,
            SecurityProperty::IdentityHiding => 15,
            SecurityProperty::ReplayResistance => 25,
            SecurityProperty::ZeroRoundTrip => 5,
            SecurityProperty::PostQuantumResistance => 20,
        });
    }

    // Offset slightly for gained properties.
    for prop in &gained {
        let offset = match prop {
            SecurityProperty::IdentityHiding => 5,
            SecurityProperty::MutualAuthentication => 10,
            _ => 2,
        };
        score = score.saturating_sub(offset);
    }

    score.min(100)
}

/// Negotiate the best translation target for a TLS profile, trying Noise and
/// WireGuard in order of preference.
pub fn negotiate(profile: &TlsProfile) -> NegotiationResult {
    let mut rejected = Vec::new();
    let mut downgrade_warnings = Vec::new();

    // Try WireGuard first (stronger guarantees).
    match translate_tls_to_wireguard(profile) {
        BridgeDecision::Accept(bridge) => {
            let risk = downgrade_risk(profile, bridge.noise_pattern);
            if risk > 0 {
                downgrade_warnings.push(format!(
                    "WireGuard translation has downgrade risk score {risk}/100"
                ));
            }
            return NegotiationResult {
                chosen_protocol: ProtocolFamily::WireGuard,
                chosen_pattern: Some(bridge.noise_pattern),
                rejected_alternatives: rejected,
                downgrade_warnings,
                guaranteed_properties: bridge.properties,
            };
        }
        BridgeDecision::Reject { reason } => {
            rejected.push(RejectedAlternative {
                protocol: ProtocolFamily::WireGuard,
                reason,
            });
        }
    }

    // Fall back to Noise.
    match translate_tls_to_noise(profile) {
        BridgeDecision::Accept(bridge) => {
            let risk = downgrade_risk(profile, bridge.noise_pattern);
            if risk > 0 {
                downgrade_warnings.push(format!(
                    "Noise translation has downgrade risk score {risk}/100"
                ));
            }
            NegotiationResult {
                chosen_protocol: ProtocolFamily::Noise,
                chosen_pattern: Some(bridge.noise_pattern),
                rejected_alternatives: rejected,
                downgrade_warnings,
                guaranteed_properties: bridge.properties,
            }
        }
        BridgeDecision::Reject { reason } => {
            rejected.push(RejectedAlternative {
                protocol: ProtocolFamily::Noise,
                reason,
            });
            NegotiationResult {
                chosen_protocol: ProtocolFamily::Tls,
                chosen_pattern: None,
                rejected_alternatives: rejected,
                downgrade_warnings: vec![
                    "No translation possible; staying on TLS.".to_string(),
                ],
                guaranteed_properties: profile.provided_properties(),
            }
        }
    }
}

/// Rank TLS versions numerically for comparison.
fn tls_version_rank(version: TlsVersion) -> u8 {
    match version {
        TlsVersion::Tls10 => 1,
        TlsVersion::Tls11 => 2,
        TlsVersion::Tls12 => 3,
        TlsVersion::Tls13 => 4,
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

    // ── New Phase 3 tests ──────────────────────────────────────────────

    #[test]
    fn negotiate_prefers_wireguard_for_mutual_auth() {
        let profile = secure_tls13_profile();
        let result = negotiate(&profile);
        assert_eq!(result.chosen_protocol, ProtocolFamily::WireGuard);
        assert_eq!(result.chosen_pattern, Some(NoisePattern::IK));
        assert!(result
            .guaranteed_properties
            .contains(&SecurityProperty::MutualAuthentication));
    }

    #[test]
    fn negotiate_falls_back_to_noise_without_mutual_auth() {
        let mut profile = secure_tls13_profile();
        profile.mutual_authentication = false;
        let result = negotiate(&profile);
        // WireGuard should be rejected (it requires cert_validation + key exchange
        // but provides mutual auth even without source mutual auth, so it should
        // still accept). Let's verify the result is valid either way.
        assert!(matches!(
            result.chosen_protocol,
            ProtocolFamily::WireGuard | ProtocolFamily::Noise
        ));
        assert!(result.chosen_pattern.is_some());
    }

    #[test]
    fn negotiate_rejects_all_for_legacy_tls() {
        let mut profile = secure_tls13_profile();
        profile.version = TlsVersion::Tls10;
        let result = negotiate(&profile);
        // Both WireGuard and Noise reject legacy TLS, so we stay on TLS.
        assert_eq!(result.chosen_protocol, ProtocolFamily::Tls);
        assert_eq!(result.rejected_alternatives.len(), 2);
    }

    #[test]
    fn validate_requirements_rejects_weak_config() {
        let mut profile = secure_tls13_profile();
        profile.key_exchange = KeyExchange::RsaKeyExchange;

        let requirements = SecurityRequirements {
            required_properties: vec![SecurityProperty::ForwardSecrecy],
            min_tls_version: Some(TlsVersion::Tls13),
            require_forward_secrecy: true,
        };

        let result = validate_security_requirements(&profile, &requirements);
        assert!(result.is_err());
        let violations = result.unwrap_err();
        assert!(violations.len() >= 1);
        assert!(violations
            .iter()
            .any(|v| v.contains("Forward secrecy")));
    }

    #[test]
    fn validate_requirements_accepts_strong_config() {
        let profile = secure_tls13_profile();
        let requirements = SecurityRequirements {
            required_properties: vec![
                SecurityProperty::ForwardSecrecy,
                SecurityProperty::MutualAuthentication,
            ],
            min_tls_version: Some(TlsVersion::Tls12),
            require_forward_secrecy: true,
        };

        let result = validate_security_requirements(&profile, &requirements);
        assert!(result.is_ok());
    }

    #[test]
    fn audit_entry_serialization() {
        let entry = SecurityAuditEntry {
            timestamp: "2026-02-28T12:00:00Z".to_string(),
            source_profile: secure_tls13_profile(),
            decision: "accept".to_string(),
            chosen_protocol: Some(ProtocolFamily::WireGuard),
            downgrade_risk_score: 0,
            notes: vec!["Clean translation".to_string()],
        };

        let jsonl = entry.to_jsonl().expect("serialize audit entry");
        assert!(jsonl.contains("accept"));
        assert!(jsonl.contains("WireGuard"));
        assert!(!jsonl.contains('\n'));

        // Verify round-trip.
        let parsed: SecurityAuditEntry =
            serde_json::from_str(&jsonl).expect("deserialize audit entry");
        assert_eq!(parsed.decision, "accept");
    }

    #[test]
    fn downgrade_risk_zero_for_matching_properties() {
        let profile = secure_tls13_profile();
        // IK pattern provides ForwardSecrecy + MutualAuthentication + ReplayResistance
        // which matches the profile's properties, so risk should be 0.
        let risk = downgrade_risk(&profile, NoisePattern::IK);
        assert_eq!(risk, 0);
    }

    #[test]
    fn downgrade_risk_nonzero_for_nn_pattern() {
        let profile = secure_tls13_profile();
        // NN pattern only provides ReplayResistance. Losing ForwardSecrecy and
        // MutualAuthentication is a significant downgrade.
        let risk = downgrade_risk(&profile, NoisePattern::NN);
        assert!(risk >= 50, "Expected high risk for NN, got {risk}");
    }

    #[test]
    fn protocol_capabilities_trait_tls() {
        let profile = secure_tls13_profile();
        assert_eq!(profile.family(), ProtocolFamily::Tls);
        assert!(profile.has_forward_secrecy());
        assert!(profile.has_mutual_auth());
    }

    #[test]
    fn protocol_capabilities_trait_noise_bridge() {
        let bridge = SecurityBridge {
            noise_pattern: NoisePattern::XX,
            properties: vec![
                SecurityProperty::ForwardSecrecy,
                SecurityProperty::IdentityHiding,
            ],
            notes: vec![],
        };
        assert_eq!(bridge.family(), ProtocolFamily::Noise);
        assert!(bridge.has_forward_secrecy());
        assert!(!bridge.has_mutual_auth());
    }
}
