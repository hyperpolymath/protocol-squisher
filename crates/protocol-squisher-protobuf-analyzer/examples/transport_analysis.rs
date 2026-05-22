// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! Example: Analyze transport compatibility between protobuf types
//!
//! Run with: cargo run --example transport_analysis

use protocol_squisher_protobuf_analyzer::{ProtobufAnalyzer, TransportAnalysis};
use protocol_squisher_transport_primitives::{IRContext, TransportClass};

fn main() {
    let source_proto = r#"
        syntax = "proto3";

        message SourceData {
            int32 id = 1;
            string name = 2;
            int64 timestamp = 3;
            repeated string tags = 4;
        }
    "#;

    let target_proto = r#"
        syntax = "proto3";

        message TargetData {
            int64 id = 1;        // Widened from int32
            string name = 2;     // Same
            int32 timestamp = 3; // Narrowed from int64!
            repeated string tags = 4; // Same
        }
    "#;

    let analyzer = ProtobufAnalyzer::new();

    let source_schema = analyzer
        .analyze_str(source_proto, "source")
        .expect("Failed to analyze source proto");
    let target_schema = analyzer
        .analyze_str(target_proto, "target")
        .expect("Failed to analyze target proto");

    let source_type = source_schema
        .types
        .get("SourceData")
        .expect("SourceData not found");
    let target_type = target_schema
        .types
        .get("TargetData")
        .expect("TargetData not found");

    println!("Transport Compatibility Analysis");
    println!("=================================\n");

    // Analyze field-by-field
    if let (
        protocol_squisher_ir::TypeDef::Struct(source_struct),
        protocol_squisher_ir::TypeDef::Struct(target_struct),
    ) = (source_type, target_type)
    {
        let ctx = IRContext::new();

        for (source_field, target_field) in
            source_struct.fields.iter().zip(target_struct.fields.iter())
        {
            println!("Field: {} -> {}", source_field.name, target_field.name);
            println!("  Source type: {:?}", source_field.ty);
            println!("  Target type: {:?}", target_field.ty);

            match TransportAnalysis::new(&ctx, &source_field.ty, &target_field.ty) {
                Ok(analysis) => {
                    print!("  Transport class: ");
                    match analysis.class {
                        TransportClass::Concorde => println!("✈️  Concorde (zero-copy)"),
                        TransportClass::Business => println!("🛫 Business (safe widening)"),
                        TransportClass::Economy => println!("🚗 Economy (lossy)"),
                        TransportClass::Wheelbarrow => println!("🛒 Wheelbarrow (incompatible)"),
                    }
                    println!("  Fidelity: {}%", analysis.fidelity);
                    println!("  Overhead: {}%", analysis.overhead);

                    if analysis.is_zero_copy() {
                        println!("  ✓ Zero-copy path available!");
                    } else if analysis.is_safe() {
                        println!("  ✓ Safe conversion (no data loss)");
                    } else if analysis.requires_json_fallback() {
                        println!("  ⚠️  JSON fallback required (potential data loss)");
                    }
                },
                Err(e) => {
                    println!("  ❌ Analysis error: {}", e);
                },
            }
            println!();
        }
    }

    println!("\nSummary:");
    println!("--------");
    println!("✈️  Concorde: Exact match, zero overhead");
    println!("🛫 Business: Safe widening (i32->i64), minor overhead");
    println!("🚗 Economy: Lossy conversion, moderate overhead");
    println!("🛒 Wheelbarrow: Incompatible, requires JSON serialization");
}
