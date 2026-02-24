// SPDX-License-Identifier: PMPL-1.0-or-later

use crate::migration::{MigrationAction, MigrationPlan};
use protocol_squisher_compat::TransportClass;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GovernancePolicy {
    pub max_breaking_changes: usize,
    pub minimum_transport_class: TransportClass,
    pub require_audit_log: bool,
    pub allowed_formats: Vec<String>,
    pub banned_actions: Vec<MigrationAction>,
}

impl Default for GovernancePolicy {
    fn default() -> Self {
        Self {
            max_breaking_changes: 0,
            minimum_transport_class: TransportClass::Economy,
            require_audit_log: true,
            allowed_formats: vec![],
            banned_actions: vec![MigrationAction::DropField],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GovernanceDecision {
    pub allowed: bool,
    pub reasons: Vec<String>,
}

pub fn evaluate_policy(
    policy: &GovernancePolicy,
    plan: &MigrationPlan,
    source_format: &str,
    target_format: &str,
    audit_log_present: bool,
) -> GovernanceDecision {
    let mut reasons = Vec::new();

    if !policy.allowed_formats.is_empty() {
        let src_allowed = policy
            .allowed_formats
            .iter()
            .any(|f| f.eq_ignore_ascii_case(source_format));
        let dst_allowed = policy
            .allowed_formats
            .iter()
            .any(|f| f.eq_ignore_ascii_case(target_format));
        if !src_allowed || !dst_allowed {
            reasons.push(format!(
                "Formats not allowed by policy: source={source_format}, target={target_format}"
            ));
        }
    }

    if plan.breaking_changes > policy.max_breaking_changes {
        reasons.push(format!(
            "Breaking changes {} exceed policy max {}",
            plan.breaking_changes, policy.max_breaking_changes
        ));
    }

    if plan.overall_class > policy.minimum_transport_class {
        reasons.push(format!(
            "Overall class {:?} below minimum {:?}",
            plan.overall_class, policy.minimum_transport_class
        ));
    }

    if policy.require_audit_log && !audit_log_present {
        reasons.push("Audit log missing while policy requires audit trail".to_string());
    }

    for step in &plan.steps {
        if policy.banned_actions.contains(&step.action) {
            reasons.push(format!(
                "Banned action {:?} found at {}",
                step.action, step.path
            ));
        }
    }

    GovernanceDecision {
        allowed: reasons.is_empty(),
        reasons,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::migration::{MigrationAction, MigrationStep};

    fn sample_plan() -> MigrationPlan {
        MigrationPlan {
            source_schema: "S".to_string(),
            target_schema: "T".to_string(),
            overall_class: TransportClass::Wheelbarrow,
            breaking_changes: 1,
            steps: vec![MigrationStep {
                path: "Record.legacy".to_string(),
                action: MigrationAction::DropField,
                class: TransportClass::Wheelbarrow,
                breaking: true,
                rationale: "Dropped".to_string(),
            }],
        }
    }

    #[test]
    fn policy_rejects_breaking_and_banned_actions() {
        let plan = sample_plan();
        let policy = GovernancePolicy::default();
        let decision = evaluate_policy(&policy, &plan, "rust", "python", true);
        assert!(!decision.allowed);
        assert!(!decision.reasons.is_empty());
    }

    #[test]
    fn permissive_policy_allows_clean_plan() {
        let mut plan = sample_plan();
        plan.breaking_changes = 0;
        plan.overall_class = TransportClass::BusinessClass;
        plan.steps.clear();

        let policy = GovernancePolicy {
            max_breaking_changes: 2,
            minimum_transport_class: TransportClass::Wheelbarrow,
            require_audit_log: false,
            allowed_formats: vec!["rust".to_string(), "python".to_string()],
            banned_actions: vec![],
        };

        let decision = evaluate_policy(&policy, &plan, "rust", "python", false);
        assert!(decision.allowed);
    }
}
