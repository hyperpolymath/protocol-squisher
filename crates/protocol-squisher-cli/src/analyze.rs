// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Schema analysis command

use anyhow::{Context, Result};
use colored::Colorize;
use protocol_squisher_compat::EphapaxCompatibilityEngine;
use protocol_squisher_ephapax_ir::TransportClass;
use protocol_squisher_rust_analyzer::RustAnalyzer;
use std::fs;
use std::path::PathBuf;

pub fn run(
    rust_path: PathBuf,
    _python_path: Option<PathBuf>,
    detailed: bool,
    format: String,
) -> Result<()> {
    println!("{}", "🔍 Analyzing schema...".cyan());

    // Parse Rust schema
    let rust_source = fs::read_to_string(&rust_path)
        .with_context(|| format!("Failed to read Rust file: {}", rust_path.display()))?;
    let rust_analyzer = RustAnalyzer::new();
    let rust_schema = rust_analyzer
        .analyze_source(&rust_source)
        .context("Failed to analyze Rust source")?;

    if format == "json" {
        // JSON output
        let json = serde_json::to_string_pretty(&rust_schema)
            .context("Failed to serialize schema to JSON")?;
        println!("{}", json);
        return Ok(());
    }

    // Text output
    println!("\n{}", "Schema Information:".bold());
    println!("  Name: {}", rust_schema.name.cyan());
    println!("  Version: {}", rust_schema.version);
    println!("  Format: {}", rust_schema.source_format);
    println!("  Types: {}", rust_schema.types.len());
    println!("  Roots: {}", rust_schema.roots.len());

    if detailed {
        println!("\n{}", "Type Definitions:".bold());

        for (type_id, type_def) in &rust_schema.types {
            println!("\n  {} {}", "Type:".bold(), type_id.cyan());

            match type_def {
                protocol_squisher_ir::TypeDef::Struct(s) => {
                    println!("    Kind: Struct");
                    println!("    Fields: {}", s.fields.len());

                    for field in &s.fields {
                        println!(
                            "      - {}: {:?}{}",
                            field.name,
                            field.ty,
                            if field.optional { " (optional)" } else { "" }
                        );
                    }
                }
                protocol_squisher_ir::TypeDef::Enum(e) => {
                    println!("    Kind: Enum");
                    println!("    Variants: {}", e.variants.len());

                    for variant in &e.variants {
                        println!("      - {}", variant.name);
                    }
                }
                protocol_squisher_ir::TypeDef::Alias(a) => {
                    println!("    Kind: Alias");
                    println!("    Target: {:?}", a.target);
                }
                protocol_squisher_ir::TypeDef::Newtype(n) => {
                    println!("    Kind: Newtype");
                    println!("    Inner: {:?}", n.inner);
                }
                protocol_squisher_ir::TypeDef::Union(u) => {
                    println!("    Kind: Union");
                    println!("    Variants: {}", u.variants.len());

                    for variant in &u.variants {
                        println!("      - {:?}", variant);
                    }
                }
            }
        }
    }

    // Run compatibility analysis if we have both schemas
    let target_schema = crate::create_target_schema(&rust_schema);
    let engine = EphapaxCompatibilityEngine::new();
    let result = engine.analyze_schemas(&rust_schema, &target_schema);

    println!("\n{}", "Compatibility Analysis:".bold());
    println!("  Overall Class: {}", format_transport_class(&result.overall_class));

    if detailed {
        println!("\n{}", "Field-Level Analysis:".bold());

        for type_analysis in &result.type_analyses {
            println!("\n  {} {}", "Type:".bold(), type_analysis.type_name.cyan());
            println!("    Class: {}", format_transport_class(&type_analysis.class));

            for field in &type_analysis.field_analyses {
                println!(
                    "      {}: {} (fidelity: {}%, overhead: {}%)",
                    field.field_name,
                    format_transport_class(&field.class),
                    field.fidelity,
                    field.overhead
                );
            }
        }
    }

    Ok(())
}

fn format_transport_class(class: &TransportClass) -> String {
    match class {
        TransportClass::Concorde => "Concorde".green().to_string(),
        TransportClass::Business => "Business".cyan().to_string(),
        TransportClass::Economy => "Economy".yellow().to_string(),
        TransportClass::Wheelbarrow => "Wheelbarrow".red().to_string(),
    }
}
