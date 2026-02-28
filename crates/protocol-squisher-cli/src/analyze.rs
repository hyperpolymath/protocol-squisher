// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Schema analysis command

use anyhow::{bail, Context, Result};
use colored::Colorize;
use protocol_squisher_compat::EphapaxCompatibilityEngine;
use protocol_squisher_transport_primitives::TransportClass;
use std::path::PathBuf;

pub fn run(
    rust_path: Option<PathBuf>,
    python_path: Option<PathBuf>,
    detailed: bool,
    format: String,
) -> Result<()> {
    println!("{}", "🔍 Analyzing schema...".cyan());

    let rust_schema = rust_path
        .as_deref()
        .map(crate::analyze_rust_schema)
        .transpose()?;
    let python_schema = python_path
        .as_deref()
        .map(crate::analyze_python_schema)
        .transpose()?;

    if rust_schema.is_none() && python_schema.is_none() {
        bail!("Provide at least one schema path with --rust or --python");
    }

    if format == "json" {
        let schema = match (&rust_schema, &python_schema) {
            (Some(rust), None) => rust,
            (None, Some(python)) => python,
            (Some(_), Some(_)) => {
                bail!("JSON output supports single-schema analysis only; use --format text for paired analysis")
            },
            (None, None) => bail!("Internal error: no schema available for JSON output"),
        };

        let json =
            serde_json::to_string_pretty(schema).context("Failed to serialize schema to JSON")?;
        println!("{}", json);
        return Ok(());
    }

    if let Some(schema) = &rust_schema {
        display_schema("Rust", schema, detailed);
    }

    if let Some(schema) = &python_schema {
        if rust_schema.is_some() {
            println!();
        }
        display_schema("Python", schema, detailed);
    }

    if let (Some(source), Some(target)) = (&rust_schema, &python_schema) {
        let engine = EphapaxCompatibilityEngine::new();
        let result = engine.analyze_schemas(source, target);

        println!("\n{}", "Compatibility Analysis:".bold());
        println!(
            "  Overall Class: {}",
            format_transport_class(&result.overall_class)
        );

        if detailed {
            println!("\n{}", "Field-Level Analysis:".bold());

            for type_analysis in &result.type_analyses {
                println!("\n  {} {}", "Type:".bold(), type_analysis.type_name.cyan());
                println!(
                    "    Class: {}",
                    format_transport_class(&type_analysis.class)
                );

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

        // ECHIDNA proof attempt (non-fatal).
        let mut ctx = crate::integration::IntegrationContext::new();
        if let Some((proven_class, trust_level)) =
            ctx.try_prove_transport_class(source, target)
        {
            println!(
                "  ECHIDNA Trust: {:?} (proven class: {:?})",
                trust_level, proven_class
            );
        }

        // Store analysis result in VeriSimDB (non-fatal).
        let _ = ctx.store_analysis_record(
            &source.name,
            &target.name,
            &format!("{:?}", result.overall_class),
            100.0,
            0.0,
            &source.source_format,
        );
    }

    Ok(())
}

fn display_schema(label: &str, schema: &protocol_squisher_ir::IrSchema, detailed: bool) {
    println!("\n{}", format!("{label} Schema Information:").bold());
    println!("  Name: {}", schema.name.cyan());
    println!("  Version: {}", schema.version);
    println!("  Format: {}", schema.source_format);
    println!("  Types: {}", schema.types.len());
    println!("  Roots: {}", schema.roots.len());

    if !detailed {
        return;
    }

    println!("\n{}", "Type Definitions:".bold());

    for (type_id, type_def) in &schema.types {
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
            },
            protocol_squisher_ir::TypeDef::Enum(e) => {
                println!("    Kind: Enum");
                println!("    Variants: {}", e.variants.len());

                for variant in &e.variants {
                    println!("      - {}", variant.name);
                }
            },
            protocol_squisher_ir::TypeDef::Alias(a) => {
                println!("    Kind: Alias");
                println!("    Target: {:?}", a.target);
            },
            protocol_squisher_ir::TypeDef::Newtype(n) => {
                println!("    Kind: Newtype");
                println!("    Inner: {:?}", n.inner);
            },
            protocol_squisher_ir::TypeDef::Union(u) => {
                println!("    Kind: Union");
                println!("    Variants: {}", u.variants.len());

                for variant in &u.variants {
                    println!("      - {:?}", variant);
                }
            },
        }
    }
}

fn format_transport_class(class: &TransportClass) -> String {
    match class {
        TransportClass::Concorde => "Concorde".green().to_string(),
        TransportClass::Business => "Business".cyan().to_string(),
        TransportClass::Economy => "Economy".yellow().to_string(),
        TransportClass::Wheelbarrow => "Wheelbarrow".red().to_string(),
    }
}
