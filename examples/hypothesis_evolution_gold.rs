// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <jonathan.jewell@open.ac.uk>

//! **Hypothesis Test: "Evolution = Gold"**
//!
//! Tests whether protocols designed for schema evolution (Avro, Thrift)
//! have more squishing opportunities than protocols without this focus.
//!
//! **Hypothesis:** Avro + Thrift will have higher squishability scores than Protobuf
//! **Reason:** Evolution-focused protocols use optional fields and defaults for
//! backwards compatibility, creating patterns we can optimize.

use protocol_squisher_avro_analyzer::AvroAnalyzer;
use protocol_squisher_meta_analysis::{
    Blocker, ComparativeAnalysis, Pattern, SquishabilityReport, TransportClass,
};
use protocol_squisher_thrift_analyzer::ThriftAnalyzer;
use std::collections::HashMap;

fn main() {
    let sep = "=".repeat(80);
    println!("{}", sep);
    println!("HYPOTHESIS TEST: Evolution-Focused Protocols = More Squishing Opportunities");
    println!("{}", sep);
    println!();

    let mut all_reports = Vec::new();

    // 1. Avro Analysis (Evolution-focused)
    println!("Analyzing Avro schemas...");
    let avro_reports = run_avro_analysis();
    println!("   {} Avro schemas analyzed", avro_reports.len());
    all_reports.extend(avro_reports);
    println!();

    // 2. Thrift Analysis (Evolution-focused)
    println!("Analyzing Thrift schemas...");
    let thrift_reports = run_thrift_analysis();
    println!("   {} Thrift schemas analyzed", thrift_reports.len());
    all_reports.extend(thrift_reports);
    println!();

    // 3. Protobuf Analysis (Baseline)
    println!("Analyzing Protobuf schemas (baseline)...");
    let protobuf_reports = run_protobuf_analysis();
    println!("   {} Protobuf schemas analyzed", protobuf_reports.len());
    all_reports.extend(protobuf_reports);
    println!();

    // Run comparative analysis
    let analysis = ComparativeAnalysis::from_reports(all_reports);

    display_results(&analysis);
    test_hypothesis(&analysis);
}

/// Build a SquishabilityReport from an analyzed IrSchema
fn schema_to_report(
    protocol: &str,
    schema_name: &str,
    ir: &protocol_squisher_ir::IrSchema,
) -> Vec<SquishabilityReport> {
    use protocol_squisher_ir::{IrType, PrimitiveType, TypeDef};

    let mut reports = Vec::new();

    for (type_name, type_def) in &ir.types {
        let mut field_transport_classes = HashMap::new();
        let mut patterns = Vec::new();
        let mut blockers = Vec::new();

        if let TypeDef::Struct(s) = type_def {
            for field in &s.fields {
                // Classify each field
                let class = match &field.ty {
                    IrType::Primitive(PrimitiveType::I64 | PrimitiveType::I32) => {
                        TransportClass::Concorde
                    }
                    IrType::Primitive(PrimitiveType::F64) => TransportClass::Business,
                    IrType::Primitive(PrimitiveType::String) => TransportClass::Economy,
                    IrType::Primitive(PrimitiveType::Bool) => TransportClass::Concorde,
                    IrType::Container(_) => TransportClass::Economy,
                    _ => TransportClass::Wheelbarrow,
                };

                // Optional fields create optimization opportunities
                if field.optional {
                    patterns.push(Pattern::UnnecessaryOption {
                        field: field.name.clone(),
                        reason: format!("{} optional field in {}", protocol, type_name),
                        blocker_to: TransportClass::Concorde,
                    });
                    blockers.push(Blocker::OptionalField {
                        field: field.name.clone(),
                        prevents: TransportClass::Concorde,
                    });
                }

                field_transport_classes.insert(field.name.clone(), class);
            }
        }

        let report = SquishabilityReport {
            protocol: protocol.to_string(),
            schema: schema_name.to_string(),
            message: type_name.clone(),
            patterns,
            field_transport_classes,
            best_achievable_class: TransportClass::Business,
            predicted_speedup: 10.0,
            blockers,
            confidence: 0.85,
        };
        reports.push(report);
    }

    reports
}

fn run_avro_analysis() -> Vec<SquishabilityReport> {
    let analyzer = AvroAnalyzer::new();
    let mut reports = Vec::new();

    let user_schema = r#"
    {
        "type": "record",
        "name": "User",
        "fields": [
            {"name": "id", "type": "long"},
            {"name": "name", "type": "string"},
            {"name": "email", "type": ["null", "string"]},
            {"name": "age", "type": ["null", "int"]}
        ]
    }
    "#;

    if let Ok(ir) = analyzer.analyze_str(user_schema, "user") {
        reports.extend(schema_to_report("Avro", "user.avsc", &ir));
    }

    let product_schema = r#"
    {
        "type": "record",
        "name": "Product",
        "fields": [
            {"name": "id", "type": "long"},
            {"name": "name", "type": "string"},
            {"name": "price", "type": "double"},
            {"name": "description", "type": ["null", "string"]},
            {"name": "category", "type": ["null", "string"]},
            {"name": "tags", "type": {"type": "array", "items": "string"}}
        ]
    }
    "#;

    if let Ok(ir) = analyzer.analyze_str(product_schema, "product") {
        reports.extend(schema_to_report("Avro", "product.avsc", &ir));
    }

    reports
}

fn run_thrift_analysis() -> Vec<SquishabilityReport> {
    let analyzer = ThriftAnalyzer::new();
    let mut reports = Vec::new();

    let user_thrift = r#"
    struct User {
        1: required i64 id
        2: required string name
        3: optional string email
        4: optional i32 age
    }
    "#;

    if let Ok(ir) = analyzer.analyze_str(user_thrift, "user") {
        reports.extend(schema_to_report("Thrift", "user.thrift", &ir));
    }

    let config_thrift = r#"
    struct ServerConfig {
        1: i32 port = 8080
        2: string host = "localhost"
        3: i32 timeout = 30
        4: optional string log_level
        5: bool debug = false
    }
    "#;

    if let Ok(ir) = analyzer.analyze_str(config_thrift, "config") {
        reports.extend(schema_to_report("Thrift", "config.thrift", &ir));
    }

    reports
}

fn run_protobuf_analysis() -> Vec<SquishabilityReport> {
    let mut reports = Vec::new();

    // Manual Protobuf report for baseline comparison
    let mut user_classes = HashMap::new();
    user_classes.insert("id".to_string(), TransportClass::Concorde);
    user_classes.insert("name".to_string(), TransportClass::Economy);
    user_classes.insert("email".to_string(), TransportClass::Business);

    reports.push(SquishabilityReport {
        protocol: "Protobuf".to_string(),
        schema: "user.proto".to_string(),
        message: "User".to_string(),
        patterns: vec![
            Pattern::SafeWidening {
                field: "id".to_string(),
                from_type: "i32".to_string(),
                to_type: "i64".to_string(),
                expected_class: TransportClass::Business,
            },
            Pattern::UnnecessaryOption {
                field: "email".to_string(),
                reason: "Proto3 optional field".to_string(),
                blocker_to: TransportClass::Concorde,
            },
        ],
        field_transport_classes: user_classes,
        best_achievable_class: TransportClass::Business,
        predicted_speedup: 50.0,
        blockers: vec![Blocker::OptionalField {
            field: "email".to_string(),
            prevents: TransportClass::Concorde,
        }],
        confidence: 0.90,
    });

    reports
}

fn display_results(analysis: &ComparativeAnalysis) {
    let sep = "=".repeat(80);
    println!("{}", sep);
    println!("RESULTS: Squishability Ranking");
    println!("{}", sep);
    println!();

    for (idx, (protocol, score)) in analysis.ranking.iter().enumerate() {
        let bar_length = (score * 50.0) as usize;
        let bar = "#".repeat(bar_length);

        println!("{}. {} - Score: {:.3}", idx + 1, protocol, score);
        println!("   {}", bar);
        println!();
    }

    println!("{}", sep);
    println!("DETAILED STATISTICS");
    println!("{}", sep);
    println!();

    for report in &analysis.reports {
        println!("{} - {}", report.protocol, report.message);
        println!("   Squishability Score: {:.3}", report.squishability_score());
        println!("   Best Class: {:?}", report.best_achievable_class);
        println!("   Predicted Speedup: {:.1}x", report.predicted_speedup);

        let safe_widening = report.count_pattern("safe_widening");
        let unnecessary_options = report.count_pattern("unnecessary_option");
        let deprecated = report.count_pattern("deprecated");

        if safe_widening > 0 || unnecessary_options > 0 || deprecated > 0 {
            println!("   Patterns:");
            if safe_widening > 0 {
                println!("      - Safe widening: {}", safe_widening);
            }
            if unnecessary_options > 0 {
                println!("      - Unnecessary options: {}", unnecessary_options);
            }
            if deprecated > 0 {
                println!("      - Deprecated fields: {}", deprecated);
            }
        }
        println!();
    }
}

fn test_hypothesis(analysis: &ComparativeAnalysis) {
    let sep = "=".repeat(80);
    println!("{}", sep);
    println!("HYPOTHESIS TEST RESULTS");
    println!("{}", sep);
    println!();

    let result = analysis.test_hypothesis("evolution_creates_opportunities");

    println!("Hypothesis: {}", result.hypothesis);
    println!(
        "Status: {}",
        if result.supported {
            "SUPPORTED"
        } else {
            "NOT SUPPORTED"
        }
    );
    println!("Confidence: {:.3}", result.confidence);
    println!("Evidence: {}", result.evidence);
    println!();

    if result.supported {
        println!("CONCLUSION: Evolution-focused protocols (Avro, Thrift) DO show higher");
        println!("   squishability scores than baseline protocols!");
    } else {
        println!("CONCLUSION: Evolution-focused protocols did NOT show significantly");
        println!("   higher squishability scores. Hypothesis needs refinement.");
    }
}
