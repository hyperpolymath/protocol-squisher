// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! Example: Analyze a protobuf schema and print the IR
//!
//! Run with: cargo run --example analyze_proto

use protocol_squisher_protobuf_analyzer::ProtobufAnalyzer;

fn main() {
    let proto = r#"
        syntax = "proto3";
        package example.api.v1;

        // User account information
        message User {
            int32 id = 1;
            string username = 2;
            string email = 3;
            optional string bio = 4;
            repeated string tags = 5;
            map<string, string> metadata = 6;
            UserStatus status = 7;

            enum UserStatus {
                UNKNOWN = 0;
                ACTIVE = 1;
                SUSPENDED = 2;
                DELETED = 3;
            }
        }

        message Post {
            int32 id = 1;
            string title = 2;
            string content = 3;
            int32 author_id = 4;  // References User.id
            repeated string tags = 5;
        }
    "#;

    println!("Analyzing protobuf schema...\n");

    let analyzer = ProtobufAnalyzer::new();
    match analyzer.analyze_str(proto, "example") {
        Ok(schema) => {
            println!("Schema: {}", schema.name);
            println!("Source format: {}", schema.source_format);
            println!("\nTypes found: {}\n", schema.types.len());

            for (name, type_def) in &schema.types {
                println!("Type: {}", name);
                match type_def {
                    protocol_squisher_ir::TypeDef::Struct(s) => {
                        println!("  Kind: Struct");
                        println!("  Fields: {}", s.fields.len());
                        for field in &s.fields {
                            println!("    - {} : {:?} (optional: {})",
                                field.name, field.ty, field.optional);
                        }
                    }
                    protocol_squisher_ir::TypeDef::Enum(e) => {
                        println!("  Kind: Enum");
                        println!("  Variants: {}", e.variants.len());
                        for variant in &e.variants {
                            println!("    - {}", variant.name);
                        }
                    }
                    _ => println!("  Kind: Other"),
                }
                println!();
            }

            // Show summary statistics
            println!("Summary:");
            println!("  Total types: {}", schema.types.len());
            println!("  Root types: {}", schema.roots.len());
        }
        Err(e) => {
            eprintln!("Error analyzing protobuf: {}", e);
        }
    }
}
