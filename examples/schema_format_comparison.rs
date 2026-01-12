// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! # Schema Format Comparison Demo
//!
//! This example demonstrates analyzing the same conceptual schema from
//! different source formats (JSON Schema, Protobuf, Rust) and comparing
//! them for compatibility.
//!
//! Run with: `cargo run --example schema_format_comparison`

use protocol_squisher_compat::{CompatibilityAnalyzer, TransportClass};
use protocol_squisher_ir::TypeDef;
use protocol_squisher_json_schema_analyzer::JsonSchemaAnalyzer;
use protocol_squisher_protobuf_analyzer::ProtobufAnalyzer;
use protocol_squisher_rust_analyzer::RustAnalyzer;

fn main() {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║      Protocol Squisher: Schema Format Comparison Demo       ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    // Define a "User" schema in three different formats

    // 1. JSON Schema
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│ Format 1: JSON Schema                                       │");
    println!("└─────────────────────────────────────────────────────────────┘");

    let json_schema = r##"{
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "type": "object",
        "title": "User",
        "properties": {
            "id": { "type": "integer" },
            "name": { "type": "string", "minLength": 1 },
            "email": { "type": "string", "format": "email" },
            "age": { "type": "integer", "minimum": 0, "maximum": 150 }
        },
        "required": ["id", "name"]
    }"##;

    let json_analyzer = JsonSchemaAnalyzer::new();
    let json_ir = json_analyzer.analyze_str(json_schema, "user").unwrap();

    println!("\nJSON Schema analyzed:");
    print_schema_summary(&json_ir);

    // 2. Protobuf
    println!("\n┌─────────────────────────────────────────────────────────────┐");
    println!("│ Format 2: Protocol Buffers (proto3)                         │");
    println!("└─────────────────────────────────────────────────────────────┘");

    let protobuf = r#"
        syntax = "proto3";

        message User {
            int64 id = 1;
            string name = 2;
            optional string email = 3;
            optional int32 age = 4;
        }
    "#;

    let proto_analyzer = ProtobufAnalyzer::new();
    let proto_ir = proto_analyzer.analyze_str(protobuf, "user").unwrap();

    println!("\nProtobuf analyzed:");
    print_schema_summary(&proto_ir);

    // 3. Rust serde
    println!("\n┌─────────────────────────────────────────────────────────────┐");
    println!("│ Format 3: Rust (serde)                                      │");
    println!("└─────────────────────────────────────────────────────────────┘");

    let rust_source = r#"
        use serde::{Serialize, Deserialize};

        #[derive(Serialize, Deserialize)]
        struct User {
            id: i64,
            name: String,
            email: Option<String>,
            age: Option<u32>,
        }
    "#;

    let rust_analyzer = RustAnalyzer::new();
    let rust_ir = rust_analyzer.analyze_source(rust_source).unwrap();

    println!("\nRust serde analyzed:");
    print_schema_summary(&rust_ir);

    // Compare all formats
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║              Compatibility Matrix                            ║");
    println!("╚══════════════════════════════════════════════════════════════╝");

    let analyzer = CompatibilityAnalyzer::new();

    // Create comparison matrix
    let schemas = [
        ("JSON Schema", &json_ir),
        ("Protobuf", &proto_ir),
        ("Rust", &rust_ir),
    ];

    println!("\n                    Target Format");
    println!("                    ┌──────────────┬──────────────┬──────────────┐");
    println!("                    │ JSON Schema  │  Protobuf    │    Rust      │");
    println!("   ┌────────────────┼──────────────┼──────────────┼──────────────┤");

    for (source_name, source_schema) in &schemas {
        print!("   │ {:14} │", source_name);
        for (_target_name, target_schema) in &schemas {
            let class = analyzer.classify(source_schema, target_schema);
            let symbol = match class {
                TransportClass::Concorde => "✓ Concorde",
                TransportClass::BusinessClass => "~ Business",
                TransportClass::Economy => "△ Economy",
                TransportClass::Wheelbarrow => "⚠ Wheelbarr",
                TransportClass::Incompatible => "✗ Incompat",
            };
            print!(" {:12} │", symbol);
        }
        println!();
    }
    println!("   └────────────────┴──────────────┴──────────────┴──────────────┘");

    // Show detailed comparison between Protobuf and Rust (commonly used together)
    println!("\n┌─────────────────────────────────────────────────────────────┐");
    println!("│ Detailed: Protobuf -> Rust                                  │");
    println!("└─────────────────────────────────────────────────────────────┘");

    let proto_to_rust = analyzer.compare(&proto_ir, &rust_ir);
    println!("\nTransport Class: {:?}", proto_to_rust.class);
    println!("Total conversion notes: {}", proto_to_rust.all_losses.len());

    if !proto_to_rust.all_losses.is_empty() {
        println!("\nDetails:");
        for loss in &proto_to_rust.all_losses {
            let icon = match loss.severity {
                protocol_squisher_compat::LossSeverity::Info => "ℹ",
                protocol_squisher_compat::LossSeverity::Minor => "•",
                protocol_squisher_compat::LossSeverity::Moderate => "◦",
                protocol_squisher_compat::LossSeverity::Major => "⚠",
                protocol_squisher_compat::LossSeverity::Critical => "✗",
            };
            println!("  {} {}: {}", icon, loss.path, loss.description);
        }
    }

    // Show detailed comparison between JSON Schema and Rust
    println!("\n┌─────────────────────────────────────────────────────────────┐");
    println!("│ Detailed: JSON Schema -> Rust                               │");
    println!("└─────────────────────────────────────────────────────────────┘");

    let json_to_rust = analyzer.compare(&json_ir, &rust_ir);
    println!("\nTransport Class: {:?}", json_to_rust.class);
    println!("Total conversion notes: {}", json_to_rust.all_losses.len());

    if !json_to_rust.all_losses.is_empty() {
        println!("\nDetails:");
        for loss in &json_to_rust.all_losses {
            let icon = match loss.severity {
                protocol_squisher_compat::LossSeverity::Info => "ℹ",
                protocol_squisher_compat::LossSeverity::Minor => "•",
                protocol_squisher_compat::LossSeverity::Moderate => "◦",
                protocol_squisher_compat::LossSeverity::Major => "⚠",
                protocol_squisher_compat::LossSeverity::Critical => "✗",
            };
            println!("  {} {}: {}", icon, loss.path, loss.description);
        }
    }

    // Summary
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║                         Summary                              ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!();
    println!("Protocol Squisher analyzed the same 'User' schema defined in");
    println!("three different formats and compared their compatibility.");
    println!();
    println!("Transport Class Legend:");
    println!("  ✓ Concorde     - Zero-copy, full fidelity (identical types)");
    println!("  ~ Business     - Minor overhead, full fidelity (safe widening)");
    println!("  △ Economy      - Moderate overhead, documented losses");
    println!("  ⚠ Wheelbarrow  - High overhead, significant losses");
    println!("  ✗ Incompatible - Cannot convert");
    println!();
    println!("This enables informed decisions about which format to use as");
    println!("the source of truth and what conversions are safe to perform.");
}

fn print_schema_summary(schema: &protocol_squisher_ir::IrSchema) {
    println!("  Types found: {}", schema.types.len());
    for (name, type_def) in &schema.types {
        match type_def {
            TypeDef::Struct(s) => {
                println!("    struct {}", name);
                for field in &s.fields {
                    let opt = if field.optional { "?" } else { "" };
                    println!("      - {}{}: {:?}", field.name, opt, field.ty);
                }
            }
            TypeDef::Enum(e) => {
                println!("    enum {} ({} variants)", name, e.variants.len());
            }
            TypeDef::Newtype(n) => {
                println!("    newtype {}: {:?}", name, n.inner);
            }
            TypeDef::Alias(a) => {
                println!("    alias {}: {:?}", name, a.target);
            }
            TypeDef::Union(u) => {
                println!("    union {} ({} variants)", name, u.variants.len());
            }
        }
    }
}
