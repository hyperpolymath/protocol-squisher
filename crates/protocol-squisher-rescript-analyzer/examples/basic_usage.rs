// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Basic usage example for ReScript analyzer

use protocol_squisher_rescript_analyzer::ReScriptAnalyzer;
use protocol_squisher_ephapax_ir::IRContext;
use protocol_squisher_rescript_analyzer::TransportAnalysis;
use protocol_squisher_ir::{IrType, PrimitiveType, ContainerType};

fn main() {
    println!("=== ReScript Analyzer Example ===\n");

    // Example 1: Parse simple record type
    example_simple_record();

    // Example 2: Parse variant type
    example_variant_type();

    // Example 3: Parse complex nested type
    example_nested_type();

    // Example 4: Analyze transport compatibility
    example_transport_analysis();

    // Example 5: JS interop
    example_js_interop();
}

fn example_simple_record() {
    println!("Example 1: Simple Record Type");
    println!("==============================");

    let rescript = r#"
        type user = {
          id: int,
          name: string,
          email: string,
          active: bool,
        }
    "#;

    let analyzer = ReScriptAnalyzer::new();
    let schema = analyzer.analyze_str(rescript, "user").unwrap();

    println!("Schema name: {}", schema.name);
    println!("Source format: {}", schema.source_format);
    println!("Number of types: {}", schema.types.len());

    for (name, type_def) in &schema.types {
        println!("\nType: {}", name);
        println!("{:#?}", type_def);
    }

    println!();
}

fn example_variant_type() {
    println!("Example 2: Variant Type (Enum/ADT)");
    println!("===================================");

    let rescript = r#"
        type userStatus =
          | Active
          | Inactive
          | Suspended
          | Deleted

        type result<'a, 'e> =
          | Ok('a)
          | Error('e)
    "#;

    let analyzer = ReScriptAnalyzer::new();
    let schema = analyzer.analyze_str(rescript, "enums").unwrap();

    println!("Found {} types:", schema.types.len());

    for (name, type_def) in &schema.types {
        if let protocol_squisher_ir::TypeDef::Enum(enum_def) = type_def {
            println!("\nEnum: {}", name);
            println!("Variants:");
            for variant in &enum_def.variants {
                match &variant.payload {
                    Some(payload) => println!("  - {} (payload: {:?})", variant.name, payload),
                    None => println!("  - {} (unit variant)", variant.name),
                }
            }
        }
    }

    println!();
}

fn example_nested_type() {
    println!("Example 3: Complex Nested Type");
    println!("================================");

    let rescript = r#"
        type userId = int

        type address = {
          street: string,
          city: string,
          zipCode: string,
        }

        type user = {
          id: userId,
          name: string,
          email: option<string>,
          address: address,
          tags: array<string>,
        }
    "#;

    let analyzer = ReScriptAnalyzer::new();
    let schema = analyzer.analyze_str(rescript, "complex").unwrap();

    println!("Schema contains {} types:", schema.types.len());

    for (name, type_def) in &schema.types {
        println!("\n- {}", name);

        if let protocol_squisher_ir::TypeDef::Struct(struct_def) = type_def {
            for field in &struct_def.fields {
                println!("  - {}: {:?}", field.name, field.ty);
            }
        }
    }

    println!();
}

fn example_transport_analysis() {
    println!("Example 4: Transport Compatibility Analysis");
    println!("============================================");

    let ctx = IRContext::new();

    // Concorde: Zero-copy
    println!("\nConcorde (Zero-Copy):");
    let rescript_int = IrType::Primitive(PrimitiveType::I64);
    let rust_i64 = IrType::Primitive(PrimitiveType::I64);
    let analysis = TransportAnalysis::new(&ctx, &rescript_int, &rust_i64).unwrap();
    println!("  ReScript int → Rust i64");
    println!("  Fidelity: {}%", analysis.fidelity);
    println!("  Overhead: {}%", analysis.overhead);
    println!("  Zero-copy: {}", analysis.is_zero_copy());

    // Business: Safe widening
    println!("\nBusiness (Safe Widening):");
    let rescript_int = IrType::Primitive(PrimitiveType::I32);
    let rust_i64 = IrType::Primitive(PrimitiveType::I64);
    let analysis = TransportAnalysis::new(&ctx, &rescript_int, &rust_i64).unwrap();
    println!("  ReScript int (as i32) → Rust i64");
    println!("  Fidelity: {}%", analysis.fidelity);
    println!("  Overhead: {}%", analysis.overhead);
    println!("  Safe: {}", analysis.is_safe());

    // Wheelbarrow: Incompatible
    println!("\nWheelbarrow (JSON Fallback):");
    let rescript_int = IrType::Primitive(PrimitiveType::I64);
    let rust_string = IrType::Primitive(PrimitiveType::String);
    let analysis = TransportAnalysis::new(&ctx, &rescript_int, &rust_string).unwrap();
    println!("  ReScript int → Rust String");
    println!("  Fidelity: {}%", analysis.fidelity);
    println!("  Overhead: {}%", analysis.overhead);
    println!("  Requires JSON: {}", analysis.requires_json_fallback());

    // Container types
    println!("\nContainer Types:");
    let rescript_array = IrType::Container(ContainerType::Vec(Box::new(
        IrType::Primitive(PrimitiveType::String)
    )));
    let rust_vec = IrType::Container(ContainerType::Vec(Box::new(
        IrType::Primitive(PrimitiveType::String)
    )));
    let analysis = TransportAnalysis::new(&ctx, &rescript_array, &rust_vec).unwrap();
    println!("  ReScript array<string> → Rust Vec<String>");
    println!("  Zero-copy: {}", analysis.is_zero_copy());

    println!();
}

fn example_js_interop() {
    println!("Example 5: JavaScript Interop");
    println!("==============================");

    let rescript = r#"
        type apiUser = {
          @as("user_id") id: int,
          @as("user_name") name: string,
          @as("email_address") email: string,
        }

        type config = {
          appName: string,
          settings: Js.Dict.t<string>,
        }
    "#;

    let analyzer = ReScriptAnalyzer::new();
    let schema = analyzer.analyze_str(rescript, "js_interop").unwrap();

    println!("JS Interop Features:");

    for (name, type_def) in &schema.types {
        if let protocol_squisher_ir::TypeDef::Struct(struct_def) = type_def {
            println!("\nType: {}", name);

            for field in &struct_def.fields {
                print!("  - {}: {:?}", field.name, field.ty);

                if !field.metadata.aliases.is_empty() {
                    print!(" (JS name: {})", field.metadata.aliases[0]);
                }

                println!();
            }
        }
    }

    println!();
}
