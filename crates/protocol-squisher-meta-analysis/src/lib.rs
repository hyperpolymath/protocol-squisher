// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2025 Jonathan D.A. Jewell

//! Meta-analysis framework for discovering squishing patterns across protocols.
//!
//! This crate provides tools to:
//! - Analyze multiple protocol schemas
//! - Discover common optimization patterns
//! - Compare transport class opportunities across protocols
//! - Generate hypothesis-driven insights

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Transport class from ephapax IR
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TransportClass {
    /// 100% fidelity, 0% overhead (zero-copy, pointer passing)
    Concorde,
    /// 98% fidelity, 5% overhead (safe widening, i32→i64)
    Business,
    /// 80% fidelity, 25% overhead (allocation, cloning)
    Economy,
    /// 50% fidelity, 80% overhead (JSON serialization fallback)
    Wheelbarrow,
}

/// Optimization patterns discovered in schemas
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Pattern {
    /// Safe numeric widening opportunity (i32→i64, f32→f64)
    SafeWidening {
        field: String,
        from_type: String,
        to_type: String,
        expected_class: TransportClass,
    },

    /// Unnecessary optional field (could be required or have default)
    UnnecessaryOption {
        field: String,
        reason: String,
        blocker_to: TransportClass,
    },

    /// Float with more precision than needed
    OverprecisionFloat {
        field: String,
        current_bits: u8,
        needed_bits: u8,
        savings_ns: f64,
    },

    /// String that's actually an enum
    StringThatCouldBeEnum {
        field: String,
        possible_values: Vec<String>,
        blocker_to: TransportClass,
    },

    /// Repeated copyable data (Vec<PrimitiveType>)
    RepeatedCopyable {
        field: String,
        item_type: String,
        count_estimate: usize,
        can_use_class: TransportClass,
    },

    /// Nested message that could be flattened
    UnnecessaryNesting {
        field: String,
        depth: usize,
        blocker_to: TransportClass,
    },

    /// Backwards compatibility bloat
    DeprecatedField {
        field: String,
        reason: String,
        cost_ns: f64,
    },

    /// Zero-copy opportunity (already optimal)
    ZeroCopyCandidate {
        field: String,
        protocol_native: bool,
    },
}

/// Blocker preventing use of better transport class
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Blocker {
    /// Type mismatch requires conversion
    TypeMismatch {
        source: String,
        target: String,
        prevents: TransportClass,
    },

    /// Optional field prevents zero-copy
    OptionalField {
        field: String,
        prevents: TransportClass,
    },

    /// Schema evolution requirement
    BackwardsCompatibility {
        requirement: String,
        prevents: TransportClass,
    },

    /// Dynamic typing (no schema)
    NoSchema {
        prevents: TransportClass,
    },

    /// Custom encoding/compression
    CustomEncoding {
        encoding: String,
        prevents: TransportClass,
    },
}

/// Squishability analysis for a single schema
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SquishabilityReport {
    /// Protocol name (Protobuf, Avro, Thrift, etc.)
    pub protocol: String,

    /// Schema name or file
    pub schema: String,

    /// Message/struct name being analyzed
    pub message: String,

    /// Patterns discovered in this schema
    pub patterns: Vec<Pattern>,

    /// Which transport class can we use for each field?
    pub field_transport_classes: HashMap<String, TransportClass>,

    /// Overall best transport class achievable
    pub best_achievable_class: TransportClass,

    /// Theoretical speedup vs JSON baseline
    pub predicted_speedup: f64,

    /// What's preventing better transport classes?
    pub blockers: Vec<Blocker>,

    /// Confidence in this analysis (0.0-1.0)
    pub confidence: f64,
}

impl SquishabilityReport {
    /// Count patterns of a specific type
    pub fn count_pattern(&self, pattern_type: &str) -> usize {
        self.patterns
            .iter()
            .filter(|p| {
                matches!(
                    (pattern_type, p),
                    ("safe_widening", Pattern::SafeWidening { .. })
                        | ("unnecessary_option", Pattern::UnnecessaryOption { .. })
                        | ("overprecision_float", Pattern::OverprecisionFloat { .. })
                        | ("string_enum", Pattern::StringThatCouldBeEnum { .. })
                        | ("repeated_copyable", Pattern::RepeatedCopyable { .. })
                        | ("unnecessary_nesting", Pattern::UnnecessaryNesting { .. })
                        | ("deprecated", Pattern::DeprecatedField { .. })
                        | ("zero_copy", Pattern::ZeroCopyCandidate { .. })
                )
            })
            .count()
    }

    /// Get distribution of transport classes across fields
    pub fn class_distribution(&self) -> HashMap<TransportClass, usize> {
        let mut dist = HashMap::new();
        for class in self.field_transport_classes.values() {
            *dist.entry(*class).or_insert(0) += 1;
        }
        dist
    }

    /// Calculate "squishability score" (0.0-1.0, higher = more squishable)
    pub fn squishability_score(&self) -> f64 {
        let dist = self.class_distribution();
        let total_fields = self.field_transport_classes.len() as f64;

        if total_fields == 0.0 {
            return 0.0;
        }

        // Weight by transport class quality
        let concorde = *dist.get(&TransportClass::Concorde).unwrap_or(&0) as f64;
        let business = *dist.get(&TransportClass::Business).unwrap_or(&0) as f64;
        let economy = *dist.get(&TransportClass::Economy).unwrap_or(&0) as f64;
        let wheelbarrow = *dist.get(&TransportClass::Wheelbarrow).unwrap_or(&0) as f64;

        // Score: 1.0 for Concorde, 0.8 for Business, 0.4 for Economy, 0.1 for Wheelbarrow
        (concorde * 1.0 + business * 0.8 + economy * 0.4 + wheelbarrow * 0.1) / total_fields
    }
}

/// Cross-protocol comparison analysis
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComparativeAnalysis {
    /// Reports for each protocol
    pub reports: Vec<SquishabilityReport>,

    /// Common patterns across protocols
    pub common_patterns: Vec<String>,

    /// Protocol-specific patterns
    pub unique_patterns: HashMap<String, Vec<String>>,

    /// Ranking by squishability score
    pub ranking: Vec<(String, f64)>,
}

impl ComparativeAnalysis {
    /// Create from multiple reports
    pub fn from_reports(reports: Vec<SquishabilityReport>) -> Self {
        // Collect unique protocols
        let protocols: Vec<String> = reports
            .iter()
            .map(|r| r.protocol.clone())
            .collect::<std::collections::HashSet<_>>()
            .into_iter()
            .collect();
        let protocol_count = protocols.len();

        // Count pattern types per protocol
        let pattern_types = [
            "safe_widening",
            "unnecessary_option",
            "overprecision_float",
            "string_enum",
            "repeated_copyable",
            "unnecessary_nesting",
            "deprecated",
            "zero_copy",
        ];

        let mut pattern_by_protocol: HashMap<String, HashMap<String, usize>> = HashMap::new();
        for report in &reports {
            let proto_entry = pattern_by_protocol
                .entry(report.protocol.clone())
                .or_default();
            for pt in &pattern_types {
                let count = report.count_pattern(pt);
                if count > 0 {
                    *proto_entry.entry(pt.to_string()).or_insert(0) += count;
                }
            }
        }

        // A pattern type is "common" if it appears in >50% of protocols
        let mut pattern_presence: HashMap<String, usize> = HashMap::new();
        for proto_patterns in pattern_by_protocol.values() {
            for pt in proto_patterns.keys() {
                *pattern_presence.entry(pt.clone()).or_insert(0) += 1;
            }
        }

        let threshold = (protocol_count as f64 * 0.5).ceil() as usize;
        let common_patterns: Vec<String> = pattern_presence
            .iter()
            .filter(|(_, count)| **count >= threshold)
            .map(|(name, _)| name.clone())
            .collect();

        // Unique patterns: appear in only one protocol
        let mut unique_patterns: HashMap<String, Vec<String>> = HashMap::new();
        for (proto, proto_patterns) in &pattern_by_protocol {
            for pt in proto_patterns.keys() {
                if pattern_presence.get(pt).copied().unwrap_or(0) == 1 {
                    unique_patterns
                        .entry(proto.clone())
                        .or_default()
                        .push(pt.clone());
                }
            }
        }

        // Rank by squishability score
        let mut ranking: Vec<(String, f64)> = reports
            .iter()
            .map(|r| (r.protocol.clone(), r.squishability_score()))
            .collect();
        ranking.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());

        Self {
            reports,
            common_patterns,
            unique_patterns,
            ranking,
        }
    }

    /// Generate hypothesis test results
    pub fn test_hypothesis(&self, hypothesis: &str) -> HypothesisResult {
        match hypothesis {
            "evolution_creates_opportunities" => {
                // Check if schema-evolution protocols (Avro, Thrift) score higher
                let evolution_protocols = ["Avro", "Thrift"];
                let evolution_scores: Vec<f64> = self
                    .reports
                    .iter()
                    .filter(|r| evolution_protocols.contains(&r.protocol.as_str()))
                    .map(|r| r.squishability_score())
                    .collect();

                let other_scores: Vec<f64> = self
                    .reports
                    .iter()
                    .filter(|r| !evolution_protocols.contains(&r.protocol.as_str()))
                    .map(|r| r.squishability_score())
                    .collect();

                if evolution_scores.is_empty() || other_scores.is_empty() {
                    return HypothesisResult {
                        hypothesis: hypothesis.to_string(),
                        supported: false,
                        confidence: 0.0,
                        evidence: "Not enough protocols analyzed yet".to_string(),
                    };
                }

                let evolution_avg = evolution_scores.iter().sum::<f64>() / evolution_scores.len() as f64;
                let other_avg = other_scores.iter().sum::<f64>() / other_scores.len() as f64;

                HypothesisResult {
                    hypothesis: hypothesis.to_string(),
                    supported: evolution_avg > other_avg,
                    confidence: (evolution_avg - other_avg).abs(),
                    evidence: format!(
                        "Evolution protocols avg: {:.3}, Others avg: {:.3}",
                        evolution_avg, other_avg
                    ),
                }
            }
            "zero_copy_unsquishable" => {
                // Check if zero-copy protocols (Cap'n Proto, FlatBuffers) have low scores
                let zero_copy_protocols = ["Cap'n Proto", "FlatBuffers"];
                let zero_copy_scores: Vec<f64> = self
                    .reports
                    .iter()
                    .filter(|r| zero_copy_protocols.contains(&r.protocol.as_str()))
                    .map(|r| r.squishability_score())
                    .collect();

                if zero_copy_scores.is_empty() {
                    return HypothesisResult {
                        hypothesis: hypothesis.to_string(),
                        supported: false,
                        confidence: 0.0,
                        evidence: "No zero-copy protocols analyzed yet".to_string(),
                    };
                }

                let zero_copy_avg = zero_copy_scores.iter().sum::<f64>() / zero_copy_scores.len() as f64;

                HypothesisResult {
                    hypothesis: hypothesis.to_string(),
                    supported: zero_copy_avg < 0.3, // Low squishability = already optimized
                    confidence: 1.0 - zero_copy_avg,
                    evidence: format!("Zero-copy protocols avg score: {:.3}", zero_copy_avg),
                }
            }
            _ => HypothesisResult {
                hypothesis: hypothesis.to_string(),
                supported: false,
                confidence: 0.0,
                evidence: "Unknown hypothesis".to_string(),
            },
        }
    }
}

/// Result of testing a hypothesis
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HypothesisResult {
    pub hypothesis: String,
    pub supported: bool,
    pub confidence: f64,
    pub evidence: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_squishability_score() {
        let mut report = SquishabilityReport {
            protocol: "Test".to_string(),
            schema: "test.proto".to_string(),
            message: "TestMessage".to_string(),
            patterns: vec![],
            field_transport_classes: HashMap::new(),
            best_achievable_class: TransportClass::Concorde,
            predicted_speedup: 10.0,
            blockers: vec![],
            confidence: 1.0,
        };

        // All Concorde = score 1.0
        report.field_transport_classes.insert("field1".to_string(), TransportClass::Concorde);
        report.field_transport_classes.insert("field2".to_string(), TransportClass::Concorde);
        assert!((report.squishability_score() - 1.0).abs() < 0.01);

        // Mix of classes
        report.field_transport_classes.insert("field3".to_string(), TransportClass::Wheelbarrow);
        let score = report.squishability_score();
        assert!(score > 0.5 && score < 1.0);
    }
}
