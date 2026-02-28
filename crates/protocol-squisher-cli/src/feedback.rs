// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Feedback-o-tron bridge: upstream suggestion generation and submission.
//!
//! Analyzes `SquishabilityReport` results from the meta-analysis crate to
//! generate actionable suggestions for schema owners. Suggestions can be
//! submitted upstream via the `feedback-a-tron` CLI tool (invoked as a
//! subprocess) or printed as a dry-run report.
//!
//! **Dry-run is the default.** Real submission requires the `--submit` flag.

use protocol_squisher_meta_analysis::{Pattern, SquishabilityReport};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::process::Command;

/// An upstream optimization suggestion generated from analysis patterns.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct UpstreamSuggestion {
    /// Target repository (e.g., "github.com/org/schema-repo").
    pub repo: String,
    /// Suggestion title (for issue/PR).
    pub title: String,
    /// Suggestion body (markdown).
    pub body: String,
    /// Platform to submit to (e.g., "github", "gitlab").
    pub platform: String,
    /// Confidence in this suggestion (0.0–1.0).
    pub confidence: f64,
    /// Which meta-analysis pattern triggered this suggestion.
    pub source_pattern: String,
    /// Expected improvement description.
    pub expected_improvement: String,
}

/// Configuration for the feedback bridge.
#[derive(Debug, Clone)]
pub struct FeedbackConfig {
    /// Path to the `feedback-a-tron` binary.
    pub binary_path: PathBuf,
    /// Minimum confidence threshold for generating suggestions (0.0–1.0).
    pub confidence_threshold: f64,
    /// Whether to actually submit (false = dry-run).
    pub dry_run: bool,
    /// Target platform for submissions.
    pub platform: String,
}

impl Default for FeedbackConfig {
    fn default() -> Self {
        Self {
            binary_path: PathBuf::from("feedback-a-tron"),
            confidence_threshold: 0.8,
            dry_run: true,
            platform: "github".to_string(),
        }
    }
}

/// Check whether the `feedback-a-tron` binary is available on the system.
pub fn is_feedback_available(config: &FeedbackConfig) -> bool {
    Command::new(&config.binary_path)
        .arg("--version")
        .output()
        .is_ok()
}

/// Generate upstream suggestions from a set of squishability reports.
///
/// Only patterns with confidence above `config.confidence_threshold` are
/// included. Each matching pattern is translated into a human-readable
/// suggestion with an actionable title and markdown body.
pub fn generate_suggestions(
    reports: &[SquishabilityReport],
    config: &FeedbackConfig,
    repo: &str,
) -> Vec<UpstreamSuggestion> {
    let mut suggestions = Vec::new();

    for report in reports {
        if report.confidence < config.confidence_threshold {
            continue;
        }

        for pattern in &report.patterns {
            if let Some(suggestion) = pattern_to_suggestion(pattern, report, config, repo) {
                suggestions.push(suggestion);
            }
        }
    }

    suggestions
}

/// Map a single meta-analysis pattern to an upstream suggestion.
///
/// Returns `None` for patterns that don't have a meaningful upstream action
/// (e.g., `ZeroCopyCandidate` is already optimal, `DeprecatedField` is
/// informational).
fn pattern_to_suggestion(
    pattern: &Pattern,
    report: &SquishabilityReport,
    config: &FeedbackConfig,
    repo: &str,
) -> Option<UpstreamSuggestion> {
    match pattern {
        Pattern::SafeWidening {
            field,
            from_type,
            to_type,
            expected_class,
        } => {
            let title = format!("Consider using {to_type} for field `{field}`");
            let body = format_suggestion_body(
                &title,
                &format!(
                    "Field `{field}` is currently `{from_type}`. Widening to `{to_type}` \
                     enables {expected_class:?}-class transport with downstream consumers \
                     (protocol: {}).",
                    report.protocol
                ),
                report,
            );
            Some(UpstreamSuggestion {
                repo: repo.to_string(),
                title,
                body,
                platform: config.platform.clone(),
                confidence: report.confidence,
                source_pattern: "SafeWidening".to_string(),
                expected_improvement: format!(
                    "Enables {expected_class:?}-class transport for field `{field}`"
                ),
            })
        },

        Pattern::UnnecessaryOption {
            field,
            reason,
            blocker_to,
        } => {
            let title = format!(
                "Field `{field}` is always present — removing Option enables zero-copy transport"
            );
            let body = format_suggestion_body(
                &title,
                &format!(
                    "Field `{field}` appears to always be present ({reason}). \
                     Removing the Option wrapper would enable {blocker_to:?}-class transport \
                     (protocol: {}).",
                    report.protocol
                ),
                report,
            );
            Some(UpstreamSuggestion {
                repo: repo.to_string(),
                title,
                body,
                platform: config.platform.clone(),
                confidence: report.confidence,
                source_pattern: "UnnecessaryOption".to_string(),
                expected_improvement: format!(
                    "Enables {blocker_to:?}-class transport for field `{field}`"
                ),
            })
        },

        Pattern::StringThatCouldBeEnum {
            field,
            possible_values,
            blocker_to,
        } => {
            let values_display = if possible_values.len() <= 5 {
                possible_values.join(", ")
            } else {
                format!("{} values", possible_values.len())
            };
            let title = format!(
                "Field `{field}` has {values_display} — using an enum enables {blocker_to:?}-class transport"
            );
            let body = format_suggestion_body(
                &title,
                &format!(
                    "Field `{field}` has a fixed set of values ({values_display}). \
                     Converting to an enum would enable {blocker_to:?}-class transport \
                     (protocol: {}).",
                    report.protocol
                ),
                report,
            );
            Some(UpstreamSuggestion {
                repo: repo.to_string(),
                title,
                body,
                platform: config.platform.clone(),
                confidence: report.confidence,
                source_pattern: "StringThatCouldBeEnum".to_string(),
                expected_improvement: format!(
                    "Enables {blocker_to:?}-class transport for field `{field}`"
                ),
            })
        },

        Pattern::OverprecisionFloat {
            field,
            current_bits,
            needed_bits,
            ..
        } => {
            let savings = current_bits - needed_bits;
            let title = format!(
                "Field `{field}` only needs {needed_bits}-bit precision — saves {savings} bits per record"
            );
            let body = format_suggestion_body(
                &title,
                &format!(
                    "Field `{field}` uses {current_bits}-bit float but only needs \
                     {needed_bits}-bit precision. Reducing saves {savings} bits per record \
                     (protocol: {}).",
                    report.protocol
                ),
                report,
            );
            Some(UpstreamSuggestion {
                repo: repo.to_string(),
                title,
                body,
                platform: config.platform.clone(),
                confidence: report.confidence,
                source_pattern: "OverprecisionFloat".to_string(),
                expected_improvement: format!(
                    "Saves {savings} bits per record for field `{field}`"
                ),
            })
        },

        // Patterns without actionable upstream suggestions.
        Pattern::ZeroCopyCandidate { .. }
        | Pattern::DeprecatedField { .. }
        | Pattern::RepeatedCopyable { .. }
        | Pattern::UnnecessaryNesting { .. } => None,
    }
}

/// Format a suggestion body in markdown with protocol-squisher branding.
pub fn format_suggestion_body(
    title: &str,
    description: &str,
    report: &SquishabilityReport,
) -> String {
    format!(
        "## {title}\n\n\
         {description}\n\n\
         ### Analysis Details\n\n\
         - **Protocol**: {protocol}\n\
         - **Schema**: {schema}\n\
         - **Message**: {message}\n\
         - **Best achievable class**: {best_class:?}\n\
         - **Predicted speedup**: {speedup:.1}x\n\
         - **Confidence**: {confidence:.0}%\n\n\
         ---\n\
         *Generated by [protocol-squisher](https://github.com/hyperpolymath/protocol-squisher) \
         meta-analysis*",
        protocol = report.protocol,
        schema = report.schema,
        message = report.message,
        best_class = report.best_achievable_class,
        speedup = report.predicted_speedup,
        confidence = report.confidence * 100.0,
    )
}

/// Submit a single suggestion via the `feedback-a-tron` CLI.
///
/// In dry-run mode, returns `Ok(())` without invoking the binary.
pub fn submit_suggestion(
    suggestion: &UpstreamSuggestion,
    config: &FeedbackConfig,
) -> Result<(), String> {
    if config.dry_run {
        return Ok(());
    }

    let output = Command::new(&config.binary_path)
        .arg("submit")
        .arg("--repo")
        .arg(&suggestion.repo)
        .arg("--platform")
        .arg(&suggestion.platform)
        .arg("--title")
        .arg(&suggestion.title)
        .arg("--body")
        .arg(&suggestion.body)
        .output()
        .map_err(|e| format!("failed to invoke feedback-a-tron: {e}"))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("feedback-a-tron failed: {stderr}"));
    }

    Ok(())
}

/// Submit a batch of suggestions. Stops on first error.
pub fn submit_batch(
    suggestions: &[UpstreamSuggestion],
    config: &FeedbackConfig,
) -> Result<usize, String> {
    let mut submitted = 0;
    for suggestion in suggestions {
        submit_suggestion(suggestion, config)?;
        submitted += 1;
    }
    Ok(submitted)
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_meta_analysis::TransportClass;
    use std::collections::HashMap;

    fn sample_report(patterns: Vec<Pattern>, confidence: f64) -> SquishabilityReport {
        SquishabilityReport {
            protocol: "Protobuf".to_string(),
            schema: "test.proto".to_string(),
            message: "TestMessage".to_string(),
            patterns,
            field_transport_classes: HashMap::new(),
            best_achievable_class: TransportClass::Business,
            predicted_speedup: 5.0,
            blockers: vec![],
            confidence,
        }
    }

    #[test]
    fn filters_by_threshold() {
        let config = FeedbackConfig {
            confidence_threshold: 0.8,
            ..Default::default()
        };

        let reports = vec![sample_report(
            vec![Pattern::SafeWidening {
                field: "id".to_string(),
                from_type: "Int32".to_string(),
                to_type: "Int64".to_string(),
                expected_class: TransportClass::Business,
            }],
            0.5, // below threshold
        )];

        let suggestions = generate_suggestions(&reports, &config, "org/repo");
        assert!(
            suggestions.is_empty(),
            "Low-confidence reports should be filtered out"
        );
    }

    #[test]
    fn safe_widening_produces_suggestion() {
        let config = FeedbackConfig::default();
        let reports = vec![sample_report(
            vec![Pattern::SafeWidening {
                field: "id".to_string(),
                from_type: "Int32".to_string(),
                to_type: "Int64".to_string(),
                expected_class: TransportClass::Business,
            }],
            0.95,
        )];

        let suggestions = generate_suggestions(&reports, &config, "org/repo");
        assert_eq!(suggestions.len(), 1);
        assert!(suggestions[0].title.contains("Int64"));
        assert_eq!(suggestions[0].source_pattern, "SafeWidening");
    }

    #[test]
    fn unnecessary_option_produces_suggestion() {
        let config = FeedbackConfig::default();
        let reports = vec![sample_report(
            vec![Pattern::UnnecessaryOption {
                field: "name".to_string(),
                reason: "never null in 10k samples".to_string(),
                blocker_to: TransportClass::Concorde,
            }],
            0.9,
        )];

        let suggestions = generate_suggestions(&reports, &config, "org/repo");
        assert_eq!(suggestions.len(), 1);
        assert!(suggestions[0].title.contains("Option"));
    }

    #[test]
    fn format_body_markdown() {
        let report = sample_report(vec![], 0.95);
        let body = format_suggestion_body("Test Title", "Test description.", &report);
        assert!(body.contains("## Test Title"));
        assert!(body.contains("protocol-squisher"));
        assert!(body.contains("Protobuf"));
    }

    #[test]
    fn suggestion_serialization() {
        let suggestion = UpstreamSuggestion {
            repo: "org/repo".to_string(),
            title: "Test".to_string(),
            body: "Body".to_string(),
            platform: "github".to_string(),
            confidence: 0.95,
            source_pattern: "SafeWidening".to_string(),
            expected_improvement: "Better transport".to_string(),
        };

        let json = serde_json::to_string(&suggestion).unwrap();
        let parsed: UpstreamSuggestion = serde_json::from_str(&json).unwrap();
        assert_eq!(suggestion, parsed);
    }

    #[test]
    fn config_defaults() {
        let config = FeedbackConfig::default();
        assert!(config.dry_run);
        assert!((config.confidence_threshold - 0.8).abs() < f64::EPSILON);
        assert_eq!(config.platform, "github");
    }

    #[test]
    fn missing_binary_detected() {
        let config = FeedbackConfig {
            binary_path: PathBuf::from("/nonexistent/feedback-a-tron"),
            ..Default::default()
        };
        assert!(!is_feedback_available(&config));
    }

    #[test]
    fn empty_reports_no_suggestions() {
        let config = FeedbackConfig::default();
        let suggestions = generate_suggestions(&[], &config, "org/repo");
        assert!(suggestions.is_empty());
    }

    #[test]
    fn batch_all_dry_run() {
        let config = FeedbackConfig::default(); // dry_run = true
        let suggestions = vec![UpstreamSuggestion {
            repo: "org/repo".to_string(),
            title: "Test".to_string(),
            body: "Body".to_string(),
            platform: "github".to_string(),
            confidence: 0.95,
            source_pattern: "SafeWidening".to_string(),
            expected_improvement: "Better".to_string(),
        }];

        let result = submit_batch(&suggestions, &config);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 1);
    }

    #[test]
    fn high_confidence_only() {
        let config = FeedbackConfig {
            confidence_threshold: 0.9,
            ..Default::default()
        };

        let reports = vec![
            sample_report(
                vec![Pattern::SafeWidening {
                    field: "a".to_string(),
                    from_type: "I32".to_string(),
                    to_type: "I64".to_string(),
                    expected_class: TransportClass::Business,
                }],
                0.85, // below 0.9 threshold
            ),
            sample_report(
                vec![Pattern::SafeWidening {
                    field: "b".to_string(),
                    from_type: "I32".to_string(),
                    to_type: "I64".to_string(),
                    expected_class: TransportClass::Business,
                }],
                0.95, // above threshold
            ),
        ];

        let suggestions = generate_suggestions(&reports, &config, "org/repo");
        assert_eq!(suggestions.len(), 1);
        assert!(suggestions[0].title.contains("b"));
    }
}
