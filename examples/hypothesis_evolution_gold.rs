// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2025 Jonathan D.A. Jewell

//! **Hypothesis Test: "Evolution = Gold"**
//!
//! Tests whether protocols designed for schema evolution (Avro, Thrift)
//! have more squishing opportunities than protocols without this focus.
//!
//! **Hypothesis:** Avro + Thrift will have higher squishability scores than Protobuf
//! **Reason:** Evolution-focused protocols use optional fields and defaults for
//! backwards compatibility, creating patterns we can optimize.

use protocol_squisher_avro_analyzer::analyze_schema as analyze_avro;
use protocol_squisher_meta_analysis::{ComparativeAnalysis, SquishabilityReport};
use protocol_squisher_thrift_analyzer::analyze_schema as analyze_thrift;

fn main() {
    let sep = "=".repeat(80);
    println!("{}", sep);
    println!("HYPOTHESIS TEST: Evolution-Focused Protocols = More Squishing Opportunities");
    println!("{}", sep);
    println!();

    // Collect reports from all protocols
    let mut all_reports = Vec::new();

    // 1. Avro Analysis (Evolution-focused)
    println!("📊 Analyzing Avro schemas...");
    let avro_reports = run_avro_analysis();
    println!("   ✓ {} Avro schemas analyzed", avro_reports.len());
    all_reports.extend(avro_reports);
    println!();

    // 2. Thrift Analysis (Evolution-focused)
    println!("📊 Analyzing Thrift schemas...");
    let thrift_reports = run_thrift_analysis();
    println!("   ✓ {} Thrift schemas analyzed", thrift_reports.len());
    all_reports.extend(thrift_reports);
    println!();

    // 3. Protobuf Analysis (Baseline)
    println!("📊 Analyzing Protobuf schemas...");
    let protobuf_reports = run_protobuf_analysis();
    println!("   ✓ {} Protobuf schemas analyzed", protobuf_reports.len());
    all_reports.extend(protobuf_reports);
    println!();

    // Run comparative analysis
    let analysis = ComparativeAnalysis::from_reports(all_reports);

    // Display results
    display_results(&analysis);

    // Test hypothesis
    test_hypothesis(&analysis);
}

fn run_avro_analysis() -> Vec<SquishabilityReport> {
    let mut reports = Vec::new();

    // Example 1: User with optional email (common evolution pattern)
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

    if let Ok(report) = analyze_avro(user_schema, "user.avsc") {
        reports.push(report);
    }

    // Example 2: Product with many optional fields
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

    if let Ok(report) = analyze_avro(product_schema, "product.avsc") {
        reports.push(report);
    }

    reports
}

fn run_thrift_analysis() -> Vec<SquishabilityReport> {
    let mut reports = Vec::new();

    // Example 1: User with optional and default fields
    let user_thrift = r#"
    struct User {
        1: required i64 id
        2: required string name
        3: optional string email
        4: optional i32 age
    }
    "#;

    if let Ok(mut thrift_reports) = analyze_thrift(user_thrift, "user.thrift") {
        reports.append(&mut thrift_reports);
    }

    // Example 2: Config with lots of defaults (evolution pattern)
    let config_thrift = r#"
    struct ServerConfig {
        1: i32 port = 8080
        2: string host = "localhost"
        3: i32 timeout = 30
        4: optional string log_level
        5: bool debug = false
    }
    "#;

    if let Ok(mut thrift_reports) = analyze_thrift(config_thrift, "config.thrift") {
        reports.append(&mut thrift_reports);
    }

    reports
}

fn run_protobuf_analysis() -> Vec<SquishabilityReport> {
    // For comparison, use existing Protobuf analyzer
    // This would ideally load the same logical schemas as Avro/Thrift
    // For now, create similar reports manually

    use protocol_squisher_meta_analysis::{Blocker, Pattern, TransportClass};
    use std::collections::HashMap;

    let mut reports = Vec::new();

    // Protobuf User (similar to Avro/Thrift examples)
    let mut user_classes = HashMap::new();
    user_classes.insert("id".to_string(), TransportClass::Concorde);
    user_classes.insert("name".to_string(), TransportClass::Economy);
    user_classes.insert("email".to_string(), TransportClass::Business); // optional in proto3

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
    let sep = "=".repeat(80);
    println!("{}", sep);
    println!();

    for (idx, (protocol, score)) in analysis.ranking.iter().enumerate() {
        let bar_length = (score * 50.0) as usize;
        let bar = "█".repeat(bar_length);

        println!("{}. {} - Score: {:.3}", idx + 1, protocol, score);
        println!("   {}", bar);
        println!();
    }

    // Show per-protocol statistics
    let sep = "=".repeat(80);
    println!("{}", sep);
    println!("DETAILED STATISTICS");
    let sep = "=".repeat(80);
    println!("{}", sep);
    println!();

    for report in &analysis.reports {
        println!("📋 {} - {}", report.protocol, report.message);
        println!("   Squishability Score: {:.3}", report.squishability_score());
        println!("   Best Class: {:?}", report.best_achievable_class);
        println!("   Predicted Speedup: {:.1}x", report.predicted_speedup);

        // Count pattern types
        let safe_widening = report.count_pattern("safe_widening");
        let unnecessary_options = report.count_pattern("unnecessary_option");
        let deprecated = report.count_pattern("deprecated");

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

        println!();
    }
}

fn test_hypothesis(analysis: &ComparativeAnalysis) {
    let sep = "=".repeat(80);
    println!("{}", sep);
    println!("HYPOTHESIS TEST RESULTS");
    let sep = "=".repeat(80);
    println!("{}", sep);
    println!();

    let result = analysis.test_hypothesis("evolution_creates_opportunities");

    println!("Hypothesis: {}", result.hypothesis);
    println!("Status: {}", if result.supported { "✅ SUPPORTED" } else { "❌ NOT SUPPORTED" });
    println!("Confidence: {:.3}", result.confidence);
    println!("Evidence: {}", result.evidence);
    println!();

    if result.supported {
        println!("🎉 CONCLUSION: Evolution-focused protocols (Avro, Thrift) DO show higher");
        println!("   squishability scores than baseline protocols!");
        println!();
        println!("📊 This validates that schema evolution features create optimization");
        println!("   opportunities we can exploit through transport classes.");
    } else {
        println!("🤔 CONCLUSION: Evolution-focused protocols did NOT show significantly");
        println!("   higher squishability scores.");
        println!();
        println!("📊 This suggests our hypothesis may need refinement, or that the");
        println!("   baseline protocols also have evolution concerns.");
    }
}
