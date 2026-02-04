// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2025 Jonathan D.A. Jewell

//! Apache Avro schema analyzer for protocol-squisher.
//!
//! **Hypothesis Test: "Evolution = Gold"**
//!
//! Avro is designed with schema evolution as a first-class concern. It has:
//! - Default values for fields (backwards/forwards compatibility)
//! - Union types (especially `null` unions for optional fields)
//! - Name resolution with aliases
//!
//! **Prediction:** Avro should show HIGH squishability scores because:
//! 1. Union types create Optional bloat (Business → Economy)
//! 2. Default values suggest fields could be required (Wheelbarrow → Business)
//! 3. Schema evolution means old/new versions coexist (compatibility tax)
//!
//! If this hypothesis is true, Avro will rank high in squishability vs protocols
//! that don't prioritize evolution (MessagePack, Cap'n Proto).

use apache_avro::Schema;
use protocol_squisher_meta_analysis::{
    Blocker, Pattern, SquishabilityReport, TransportClass,
};
use std::collections::HashMap;

/// Analyze an Avro schema and generate squishability report
pub fn analyze_schema(schema_json: &str, schema_name: &str) -> Result<SquishabilityReport, String> {
    let schema = Schema::parse_str(schema_json)
        .map_err(|e| format!("Failed to parse Avro schema: {}", e))?;

    match &schema {
        Schema::Record(record) => analyze_record(record, schema_name),
        _ => Err(format!("Expected record schema, got {:?}", schema)),
    }
}

/// Analyze an Avro record
fn analyze_record(
    record: &apache_avro::schema::RecordSchema,
    schema_name: &str,
) -> Result<SquishabilityReport, String> {
    let mut patterns = Vec::new();
    let mut field_transport_classes = HashMap::new();
    let mut blockers = Vec::new();

    for field in &record.fields {
        let field_name = field.name.clone();
        let (transport_class, field_patterns, field_blockers) =
            analyze_field(&field_name, &field.schema);

        field_transport_classes.insert(field_name.clone(), transport_class);
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
        protocol: "Avro".to_string(),
        schema: schema_name.to_string(),
        message: record.name.name.clone(),
        patterns,
        field_transport_classes,
        best_achievable_class: best_class,
        predicted_speedup: speedup,
        blockers,
        confidence: 0.85, // High confidence for static schema analysis
    })
}

/// Analyze a single field's schema
fn analyze_field(
    field_name: &str,
    schema: &Schema,
) -> (
    TransportClass,
    Vec<Pattern>,
    Vec<Blocker>,
) {
    let mut patterns = Vec::new();
    let mut blockers = Vec::new();

    let transport_class = match schema {
        // Primitive types → Concorde or Business depending on size
        Schema::Boolean => TransportClass::Concorde,
        Schema::Int => TransportClass::Concorde, // i32
        Schema::Long => TransportClass::Concorde, // i64
        Schema::Float => TransportClass::Concorde, // f32
        Schema::Double => TransportClass::Concorde, // f64
        Schema::Bytes => TransportClass::Economy, // Vec<u8>
        Schema::String => TransportClass::Economy, // String allocation

        // Union types → Detect optionals
        Schema::Union(union_schema) => {
            if is_optional_union(union_schema) {
                // Union<null, T> pattern → Optional field
                patterns.push(Pattern::UnnecessaryOption {
                    field: field_name.to_string(),
                    reason: "Avro union with null for backwards compatibility".to_string(),
                    blocker_to: TransportClass::Concorde,
                });

                blockers.push(Blocker::OptionalField {
                    field: field_name.to_string(),
                    prevents: TransportClass::Concorde,
                });

                TransportClass::Business // Optional prevents Concorde
            } else {
                // Complex union → Need runtime type checking
                TransportClass::Economy
            }
        }

        // Array → Economy (allocation)
        Schema::Array(items_schema) => {
            let item_class = analyze_field("", items_schema.as_ref()).0;

            if matches!(item_class, TransportClass::Concorde) {
                patterns.push(Pattern::RepeatedCopyable {
                    field: field_name.to_string(),
                    item_type: format!("{:?}", items_schema),
                    count_estimate: 0, // Unknown from schema
                    can_use_class: TransportClass::Economy,
                });
            }

            TransportClass::Economy
        }

        // Map → Economy (HashMap allocation)
        Schema::Map(_) => TransportClass::Economy,

        // Nested record → Check nesting depth
        Schema::Record(nested) => {
            patterns.push(Pattern::UnnecessaryNesting {
                field: field_name.to_string(),
                depth: 1, // TODO: Calculate actual depth
                blocker_to: TransportClass::Concorde,
            });

            TransportClass::Economy
        }

        // Enum → Concorde (small numeric value)
        Schema::Enum(_) => TransportClass::Concorde,

        // Fixed bytes → Concorde if small, Economy if large
        Schema::Fixed(fixed) => {
            if fixed.size <= 16 {
                TransportClass::Concorde
            } else {
                TransportClass::Economy
            }
        }

        // Ref (named type reference) → Follow the reference
        Schema::Ref { name } => {
            // TODO: Resolve named type
            // For now, assume Economy
            TransportClass::Economy
        }

        // Decimal → Business (needs conversion)
        Schema::Decimal { .. } => TransportClass::Business,

        // UUID, Date, etc. → Business (string/numeric representation)
        Schema::Uuid | Schema::Date | Schema::TimeMillis | Schema::TimeMicros
        | Schema::TimestampMillis | Schema::TimestampMicros | Schema::Duration => {
            TransportClass::Business
        }

        _ => TransportClass::Wheelbarrow, // Unknown or complex
    };

    // Detect safe widening opportunities
    if matches!(schema, Schema::Int) {
        patterns.push(Pattern::SafeWidening {
            field: field_name.to_string(),
            from_type: "i32".to_string(),
            to_type: "i64".to_string(),
            expected_class: TransportClass::Business,
        });
    }

    (transport_class, patterns, blockers)
}

/// Check if a union represents an optional field (union of null + one other type)
fn is_optional_union(union_schema: &apache_avro::schema::UnionSchema) -> bool {
    if union_schema.variants().len() != 2 {
        return false;
    }

    union_schema
        .variants()
        .iter()
        .any(|s| matches!(s, Schema::Null))
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
            TransportClass::Concorde => 100.0,   // 100x vs JSON
            TransportClass::Business => 50.0,    // 50x vs JSON
            TransportClass::Economy => 10.0,     // 10x vs JSON
            TransportClass::Wheelbarrow => 1.0,  // 1x vs JSON (baseline)
        };
    }

    speedup / total
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_record() {
        let schema = r#"
        {
            "type": "record",
            "name": "User",
            "fields": [
                {"name": "id", "type": "long"},
                {"name": "name", "type": "string"}
            ]
        }
        "#;

        let report = analyze_schema(schema, "user.avsc").unwrap();

        assert_eq!(report.protocol, "Avro");
        assert_eq!(report.message, "User");
        assert_eq!(report.field_transport_classes.len(), 2);

        // id: long → Concorde
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
        let schema = r#"
        {
            "type": "record",
            "name": "User",
            "fields": [
                {"name": "id", "type": "long"},
                {"name": "email", "type": ["null", "string"]}
            ]
        }
        "#;

        let report = analyze_schema(schema, "user.avsc").unwrap();

        // email: union<null, string> → Business (optional blocker)
        assert_eq!(
            report.field_transport_classes.get("email"),
            Some(&TransportClass::Business)
        );

        // Should detect unnecessary option pattern
        let has_optional_pattern = report.patterns.iter().any(|p| {
            matches!(p, Pattern::UnnecessaryOption { field, .. } if field == "email")
        });
        assert!(has_optional_pattern);

        // Should have OptionalField blocker
        let has_optional_blocker = report.blockers.iter().any(|b| {
            matches!(b, Blocker::OptionalField { field, prevents }
                if field == "email" && *prevents == TransportClass::Concorde)
        });
        assert!(has_optional_blocker);
    }

    #[test]
    fn test_array_field() {
        let schema = r#"
        {
            "type": "record",
            "name": "UserList",
            "fields": [
                {"name": "users", "type": {"type": "array", "items": "long"}}
            ]
        }
        "#;

        let report = analyze_schema(schema, "user_list.avsc").unwrap();

        // users: array<long> → Economy
        assert_eq!(
            report.field_transport_classes.get("users"),
            Some(&TransportClass::Economy)
        );

        // Should detect repeated copyable pattern
        let has_repeated_pattern = report.patterns.iter().any(|p| {
            matches!(p, Pattern::RepeatedCopyable { field, .. } if field == "users")
        });
        assert!(has_repeated_pattern);
    }

    #[test]
    fn test_squishability_score() {
        let schema = r#"
        {
            "type": "record",
            "name": "MixedTypes",
            "fields": [
                {"name": "id", "type": "long"},
                {"name": "count", "type": "int"},
                {"name": "optional_field", "type": ["null", "string"]},
                {"name": "tags", "type": {"type": "array", "items": "string"}}
            ]
        }
        "#;

        let report = analyze_schema(schema, "mixed.avsc").unwrap();

        // Calculate squishability score
        let score = report.squishability_score();

        // Expect moderate score (mix of Concorde, Business, Economy)
        // id: Concorde (1.0), count: Concorde (1.0), optional: Business (0.8), tags: Economy (0.4)
        // Score = (1.0 + 1.0 + 0.8 + 0.4) / 4 = 0.8
        assert!((score - 0.8).abs() < 0.01, "Score was: {}", score);
    }
}
