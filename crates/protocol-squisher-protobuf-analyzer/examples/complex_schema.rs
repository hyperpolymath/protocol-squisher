// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! Example: Analyze a complex protobuf schema with nested types and oneofs
//!
//! Run with: cargo run --example complex_schema

use protocol_squisher_protobuf_analyzer::ProtobufAnalyzer;

fn main() {
    let proto = r#"
        syntax = "proto3";
        package ecommerce.v1;

        // E-commerce order system
        message Order {
            int32 order_id = 1;
            int32 customer_id = 2;
            repeated OrderItem items = 3;
            Address shipping_address = 4;
            PaymentInfo payment = 5;
            OrderStatus status = 6;
            map<string, string> metadata = 7;

            message OrderItem {
                int32 product_id = 1;
                string product_name = 2;
                int32 quantity = 3;
                int64 price_cents = 4;  // Price in cents
                repeated string options = 5;  // e.g., ["size:L", "color:blue"]
            }

            message Address {
                string street = 1;
                string city = 2;
                string state = 3;
                string zip_code = 4;
                string country = 5;
            }

            message PaymentInfo {
                oneof method {
                    CreditCard credit_card = 1;
                    string paypal_email = 2;
                    string crypto_wallet = 3;
                }

                message CreditCard {
                    string last_four_digits = 1;
                    string card_type = 2;  // e.g., "VISA", "MASTERCARD"
                    int32 expiry_month = 3;
                    int32 expiry_year = 4;
                }
            }

            enum OrderStatus {
                PENDING = 0;
                PROCESSING = 1;
                SHIPPED = 2;
                DELIVERED = 3;
                CANCELLED = 4;
                REFUNDED = 5;
            }
        }
    "#;

    println!("Analyzing complex e-commerce protobuf schema...\n");

    let analyzer = ProtobufAnalyzer::new();
    match analyzer.analyze_str(proto, "ecommerce") {
        Ok(schema) => {
            println!("Schema: {}", schema.name);
            println!("Total types: {}\n", schema.types.len());

            // List all types in dependency order
            println!("Type hierarchy:");
            println!("===============\n");

            for (name, type_def) in &schema.types {
                let indent = name.matches('_').count();
                let prefix = "  ".repeat(indent);

                match type_def {
                    protocol_squisher_ir::TypeDef::Struct(s) => {
                        println!(
                            "{}📦 {} (struct with {} fields)",
                            prefix,
                            name,
                            s.fields.len()
                        );

                        // Show interesting fields
                        for field in &s.fields {
                            if let protocol_squisher_ir::IrType::Container(_) = &field.ty {
                                println!("{}    └─ {} : {:?}", prefix, field.name, field.ty);
                            }
                        }
                    },
                    protocol_squisher_ir::TypeDef::Enum(e) => {
                        println!(
                            "{}🔖 {} (enum with {} variants)",
                            prefix,
                            name,
                            e.variants.len()
                        );
                        for variant in &e.variants {
                            print!("{}    ", prefix);
                            if variant.payload.is_some() {
                                println!("└─ {}(...)", variant.name);
                            } else {
                                println!("└─ {}", variant.name);
                            }
                        }
                    },
                    _ => {},
                }
            }

            println!("\n✓ Successfully analyzed {} types", schema.types.len());
            println!(
                "  - Structs: {}",
                schema
                    .types
                    .values()
                    .filter(|t| matches!(t, protocol_squisher_ir::TypeDef::Struct(_)))
                    .count()
            );
            println!(
                "  - Enums: {}",
                schema
                    .types
                    .values()
                    .filter(|t| matches!(t, protocol_squisher_ir::TypeDef::Enum(_)))
                    .count()
            );
        },
        Err(e) => {
            eprintln!("Error: {}", e);
        },
    }
}
