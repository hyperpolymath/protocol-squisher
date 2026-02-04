// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2025 Jonathan D.A. Jewell

//! Apache Thrift IDL analyzer for protocol-squisher.
//!
//! **Hypothesis Test: "Evolution = Gold" (Part 2)**
//!
//! Thrift is designed with backward compatibility and evolution in mind:
//! - Explicit `required`, `optional`, and default field modifiers
//! - Multiple protocol formats (Binary, Compact, JSON)
//! - Field IDs allow reordering and evolution
//!
//! **Prediction:** Thrift should show HIGH squishability scores because:
//! 1. `optional` fields create Optional bloat (Business → Economy)
//! 2. Default values suggest fields could be required (Wheelbarrow → Business)
//! 3. Multiple protocols mean conservative type choices (i32 instead of i16)
//!
//! **Comparison with Avro:**
//! - Avro uses union types for optionals → Thrift uses `optional` keyword
//! - Avro has single encoding → Thrift has multiple protocols
//! - Which approach creates more squishing opportunities?

use lazy_static::lazy_static;
use protocol_squisher_meta_analysis::{
    Blocker, Pattern, SquishabilityReport, TransportClass,
};
use regex::Regex;
use std::collections::HashMap;

lazy_static! {
    // Match struct definitions: struct MyStruct { ... }
    static ref STRUCT_RE: Regex = Regex::new(r"struct\s+(\w+)\s*\{([^}]+)\}").unwrap();

    // Match field definitions: 1: required i32 id
    static ref FIELD_RE: Regex = Regex::new(
        r"(\d+):\s*(required|optional)?\s*(\w+(?:<[^>]+>)?)\s+(\w+)\s*(=\s*[^,\n]+)?"
    ).unwrap();
}

/// Analyze a Thrift IDL file and generate squishability reports
pub fn analyze_schema(thrift_idl: &str, schema_name: &str) -> Result<Vec<SquishabilityReport>, String> {
    let mut reports = Vec::new();

    // Find all struct definitions
    for struct_cap in STRUCT_RE.captures_iter(thrift_idl) {
        let struct_name = struct_cap.get(1).unwrap().as_str();
        let struct_body = struct_cap.get(2).unwrap().as_str();

        let report = analyze_struct(struct_name, struct_body, schema_name)?;
        reports.push(report);
    }

    if reports.is_empty() {
        return Err("No struct definitions found in Thrift IDL".to_string());
    }

    Ok(reports)
}

/// Analyze a single Thrift struct
fn analyze_struct(
    struct_name: &str,
    struct_body: &str,
    schema_name: &str,
) -> Result<SquishabilityReport, String> {
    let mut patterns = Vec::new();
    let mut field_transport_classes = HashMap::new();
    let mut blockers = Vec::new();

    // Parse each field
    for field_cap in FIELD_RE.captures_iter(struct_body) {
        let _field_id = field_cap.get(1).unwrap().as_str();
        let requiredness = field_cap.get(2).map(|m| m.as_str());
        let field_type = field_cap.get(3).unwrap().as_str();
        let field_name = field_cap.get(4).unwrap().as_str();
        let has_default = field_cap.get(5).is_some();

        let (transport_class, field_patterns, field_blockers) =
            analyze_field(field_name, field_type, requiredness, has_default);

        field_transport_classes.insert(field_name.to_string(), transport_class);
        patterns.extend(field_patterns);
        blockers.extend(field_blockers);
    }

    // Determine best achievable class
    let best_class = field_transport_classes
        .values()
        .min_by_key(|&&c| class_rank(c))
        .copied()
        .unwrap_or(TransportClass::Wheelbarrow);

    // Calculate predicted speedup
    let speedup = calculate_speedup(&field_transport_classes);

    Ok(SquishabilityReport {
        protocol: "Thrift".to_string(),
        schema: schema_name.to_string(),
        message: struct_name.to_string(),
        patterns,
        field_transport_classes,
        best_achievable_class: best_class,
        predicted_speedup: speedup,
        blockers,
        confidence: 0.80, // Slightly lower than Avro (regex-based parsing)
    })
}

/// Analyze a single Thrift field
fn analyze_field(
    field_name: &str,
    field_type: &str,
    requiredness: Option<&str>,
    has_default: bool,
) -> (
    TransportClass,
    Vec<Pattern>,
    Vec<Blocker>,
) {
    let mut patterns = Vec::new();
    let mut blockers = Vec::new();

    // Check if field is optional
    let is_optional = matches!(requiredness, Some("optional"));
    let is_required = matches!(requiredness, Some("required"));

    let transport_class = match field_type {
        // Primitive types
        "bool" => TransportClass::Concorde,
        "byte" | "i8" => TransportClass::Concorde,
        "i16" => TransportClass::Concorde,
        "i32" => {
            // Detect safe widening opportunity
            patterns.push(Pattern::SafeWidening {
                field: field_name.to_string(),
                from_type: "i32".to_string(),
                to_type: "i64".to_string(),
                expected_class: TransportClass::Business,
            });
            TransportClass::Concorde
        }
        "i64" => TransportClass::Concorde,
        "double" => TransportClass::Concorde,
        "string" => TransportClass::Economy, // String allocation
        "binary" => TransportClass::Economy, // Vec<u8> allocation

        // Container types
        t if t.starts_with("list<") => {
            if is_primitive_container(t) {
                patterns.push(Pattern::RepeatedCopyable {
                    field: field_name.to_string(),
                    item_type: t.to_string(),
                    count_estimate: 0,
                    can_use_class: TransportClass::Economy,
                });
            }
            TransportClass::Economy
        }
        t if t.starts_with("set<") => TransportClass::Economy,
        t if t.starts_with("map<") => TransportClass::Economy,

        // Custom types (struct references)
        _ => {
            patterns.push(Pattern::UnnecessaryNesting {
                field: field_name.to_string(),
                depth: 1,
                blocker_to: TransportClass::Concorde,
            });
            TransportClass::Economy
        }
    };

    // Handle optional fields (key pattern for evolution hypothesis!)
    if is_optional {
        patterns.push(Pattern::UnnecessaryOption {
            field: field_name.to_string(),
            reason: "Thrift optional field for backwards compatibility".to_string(),
            blocker_to: TransportClass::Concorde,
        });

        blockers.push(Blocker::OptionalField {
            field: field_name.to_string(),
            prevents: TransportClass::Concorde,
        });

        // Optional fields always use Business class (best case for Option<T>)
        // This is better than Economy/Wheelbarrow, worse than Concorde
        return (TransportClass::Business, patterns, blockers);
    }

    // Handle default values (also indicates evolution concern)
    if has_default && !is_required {
        patterns.push(Pattern::DeprecatedField {
            field: field_name.to_string(),
            reason: "Has default value, suggests evolution compatibility".to_string(),
            cost_ns: 5.0, // Estimate
        });

        blockers.push(Blocker::BackwardsCompatibility {
            requirement: format!("Field {} has default value", field_name),
            prevents: TransportClass::Concorde,
        });
    }

    (transport_class, patterns, blockers)
}

/// Check if a container type contains primitives
fn is_primitive_container(container_type: &str) -> bool {
    container_type.contains("<i") || container_type.contains("<bool") || container_type.contains("<double")
}

/// Rank transport classes (lower = better)
fn class_rank(class: TransportClass) -> u8 {
    match class {
        TransportClass::Concorde => 0,
        TransportClass::Business => 1,
        TransportClass::Economy => 2,
        TransportClass::Wheelbarrow => 3,
    }
}

/// Calculate predicted speedup based on transport class distribution
fn calculate_speedup(classes: &HashMap<String, TransportClass>) -> f64 {
    let total = classes.len() as f64;
    if total == 0.0 {
        return 1.0;
    }

    let mut speedup = 0.0;
    for class in classes.values() {
        speedup += match class {
            TransportClass::Concorde => 100.0,
            TransportClass::Business => 50.0,
            TransportClass::Economy => 10.0,
            TransportClass::Wheelbarrow => 1.0,
        };
    }

    speedup / total
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_struct() {
        let thrift = r#"
        struct User {
            1: required i64 id
            2: required string name
        }
        "#;

        let reports = analyze_schema(thrift, "user.thrift").unwrap();
        assert_eq!(reports.len(), 1);

        let report = &reports[0];
        assert_eq!(report.protocol, "Thrift");
        assert_eq!(report.message, "User");
        assert_eq!(report.field_transport_classes.len(), 2);

        // id: i64 → Concorde
        assert_eq!(
            report.field_transport_classes.get("id"),
            Some(&TransportClass::Concorde)
        );

        // name: string → Economy
        assert_eq!(
            report.field_transport_classes.get("name"),
            Some(&TransportClass::Economy)
        );
    }

    #[test]
    fn test_optional_field() {
        let thrift = r#"
        struct User {
            1: required i64 id
            2: optional string email
        }
        "#;

        let reports = analyze_schema(thrift, "user.thrift").unwrap();
        let report = &reports[0];

        // email: optional string → Business (optional blocker)
        assert_eq!(
            report.field_transport_classes.get("email"),
            Some(&TransportClass::Business)
        );

        // Should detect unnecessary option pattern
        let has_optional_pattern = report.patterns.iter().any(|p| {
            matches!(p, Pattern::UnnecessaryOption { field, .. } if field == "email")
        });
        assert!(has_optional_pattern, "Should detect optional pattern");

        // Should have OptionalField blocker
        let has_optional_blocker = report.blockers.iter().any(|b| {
            matches!(b, Blocker::OptionalField { field, prevents }
                if field == "email" && *prevents == TransportClass::Concorde)
        });
        assert!(has_optional_blocker, "Should have optional blocker");
    }

    #[test]
    fn test_default_value() {
        let thrift = r#"
        struct Config {
            1: i32 timeout = 30
            2: string host = "localhost"
        }
        "#;

        let reports = analyze_schema(thrift, "config.thrift").unwrap();
        let report = &reports[0];

        // Should detect deprecated fields (fields with defaults)
        let deprecated_count = report.patterns.iter().filter(|p| {
            matches!(p, Pattern::DeprecatedField { .. })
        }).count();

        assert!(deprecated_count >= 2, "Should detect fields with defaults");
    }

    #[test]
    fn test_list_field() {
        let thrift = r#"
        struct UserList {
            1: list<i64> user_ids
        }
        "#;

        let reports = analyze_schema(thrift, "user_list.thrift").unwrap();
        let report = &reports[0];

        // user_ids: list<i64> → Economy
        assert_eq!(
            report.field_transport_classes.get("user_ids"),
            Some(&TransportClass::Economy)
        );

        // Should detect repeated copyable pattern
        let has_repeated_pattern = report.patterns.iter().any(|p| {
            matches!(p, Pattern::RepeatedCopyable { field, .. } if field == "user_ids")
        });
        assert!(has_repeated_pattern, "Should detect repeated copyable pattern");
    }

    #[test]
    fn test_squishability_score() {
        let thrift = r#"
        struct MixedTypes {
            1: required i64 id
            2: required i32 count
            3: optional string description
            4: list<string> tags
        }
        "#;

        let reports = analyze_schema(thrift, "mixed.thrift").unwrap();
        let report = &reports[0];

        // Calculate squishability score
        let score = report.squishability_score();

        // Expect moderate score (mix of Concorde, Business, Economy)
        // id: Concorde (1.0), count: Concorde (1.0), description: Business (0.8), tags: Economy (0.4)
        // Score = (1.0 + 1.0 + 0.8 + 0.4) / 4 = 0.8
        assert!((score - 0.8).abs() < 0.01, "Score was: {}", score);
    }
}
