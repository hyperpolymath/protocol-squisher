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

/// Severity level for policy violations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ViolationSeverity {
    /// Informational — policy preference not met.
    Info,
    /// Warning — may be acceptable with justification.
    Warning,
    /// Error — must be resolved before proceeding.
    Error,
    /// Critical — blocks all further processing.
    Critical,
}

/// A structured policy violation with severity and path.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolicyViolation {
    /// The severity of the violation.
    pub severity: ViolationSeverity,
    /// Which step or aspect triggered the violation.
    pub path: String,
    /// Human-readable description.
    pub description: String,
}

/// Aggregated report from evaluating multiple schemas against policy.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolicyReport {
    /// Total number of schemas evaluated.
    pub schemas_evaluated: usize,
    /// How many passed policy.
    pub passed: usize,
    /// How many failed policy.
    pub failed: usize,
    /// All violations across all schemas.
    pub violations: Vec<PolicyViolation>,
}

/// Evaluate a governance policy and return structured violations instead of
/// simple boolean + strings.
pub fn evaluate_policy_violations(
    policy: &GovernancePolicy,
    plan: &MigrationPlan,
    source_format: &str,
    target_format: &str,
    audit_log_present: bool,
) -> Vec<PolicyViolation> {
    let mut violations = Vec::new();

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
            violations.push(PolicyViolation {
                severity: ViolationSeverity::Error,
                path: format!("{source_format} -> {target_format}"),
                description: format!(
                    "Formats not allowed by policy: source={source_format}, target={target_format}"
                ),
            });
        }
    }

    if plan.breaking_changes > policy.max_breaking_changes {
        violations.push(PolicyViolation {
            severity: ViolationSeverity::Critical,
            path: "migration".to_string(),
            description: format!(
                "Breaking changes {} exceed policy max {}",
                plan.breaking_changes, policy.max_breaking_changes
            ),
        });
    }

    if plan.overall_class > policy.minimum_transport_class {
        violations.push(PolicyViolation {
            severity: ViolationSeverity::Warning,
            path: "transport_class".to_string(),
            description: format!(
                "Overall class {:?} below minimum {:?}",
                plan.overall_class, policy.minimum_transport_class
            ),
        });
    }

    if policy.require_audit_log && !audit_log_present {
        violations.push(PolicyViolation {
            severity: ViolationSeverity::Error,
            path: "audit".to_string(),
            description: "Audit log missing while policy requires audit trail".to_string(),
        });
    }

    for step in &plan.steps {
        if policy.banned_actions.contains(&step.action) {
            violations.push(PolicyViolation {
                severity: ViolationSeverity::Critical,
                path: step.path.clone(),
                description: format!("Banned action {:?} found", step.action),
            });
        }
    }

    violations
}

/// Evaluate a batch of migration plans against the same policy.
pub fn evaluate_batch(
    policy: &GovernancePolicy,
    plans: &[(MigrationPlan, &str, &str, bool)],
) -> PolicyReport {
    let mut all_violations = Vec::new();
    let mut passed = 0usize;
    let mut failed = 0usize;

    for (plan, src_fmt, tgt_fmt, has_audit) in plans {
        let violations = evaluate_policy_violations(policy, plan, src_fmt, tgt_fmt, *has_audit);
        if violations.is_empty() {
            passed += 1;
        } else {
            failed += 1;
            all_violations.extend(violations);
        }
    }

    PolicyReport {
        schemas_evaluated: plans.len(),
        passed,
        failed,
        violations: all_violations,
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

    #[test]
    fn violations_have_correct_severity() {
        let plan = sample_plan();
        let policy = GovernancePolicy::default();
        let violations =
            evaluate_policy_violations(&policy, &plan, "rust", "python", true);
        assert!(!violations.is_empty());
        // Breaking changes should produce Critical violation.
        assert!(violations
            .iter()
            .any(|v| v.severity == ViolationSeverity::Critical));
    }

    #[test]
    fn batch_evaluation_aggregates_results() {
        let mut passing_plan = sample_plan();
        passing_plan.breaking_changes = 0;
        passing_plan.overall_class = TransportClass::BusinessClass;
        passing_plan.steps.clear();

        let failing_plan = sample_plan();

        let permissive_policy = GovernancePolicy {
            max_breaking_changes: 2,
            minimum_transport_class: TransportClass::Wheelbarrow,
            require_audit_log: false,
            allowed_formats: vec![],
            banned_actions: vec![],
        };

        let plans = vec![
            (passing_plan, "rust", "python", false),
            (failing_plan, "rust", "python", false),
        ];

        let report = evaluate_batch(&permissive_policy, &plans);
        assert_eq!(report.schemas_evaluated, 2);
        // With permissive policy, both should pass (no breaking limit exceeded,
        // no banned actions with empty ban list, no format restrictions).
        assert_eq!(report.passed, 2);
    }
}
