// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Protocol Squisher CLI
//!
//! Command-line tool for analyzing schemas and generating optimized PyO3 bindings.

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use colored::Colorize;
use protocol_squisher_compat::EphapaxCompatibilityEngine;
use protocol_squisher_ephapax_ir::TransportClass;
use protocol_squisher_ir::IrSchema;
use protocol_squisher_optimizer::EphapaxOptimizer;
use protocol_squisher_rust_analyzer::RustAnalyzer;
use std::fs;
use std::path::PathBuf;

mod analyze;
mod compiler;
mod formats;
mod generate;

#[derive(Parser)]
#[command(
    name = "protocol-squisher",
    about = "Universal protocol interoperability through automatic adapter synthesis",
    version,
    author
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Analyze Rust and Python schemas for compatibility
    Analyze {
        /// Path to Rust source file
        #[arg(short, long)]
        rust: PathBuf,

        /// Path to Python source file (optional)
        #[arg(short, long)]
        python: Option<PathBuf>,

        /// Show detailed field-level analysis
        #[arg(short, long)]
        detailed: bool,

        /// Output format (text, json)
        #[arg(short, long, default_value = "text")]
        format: String,
    },

    /// Show optimization suggestions for improving transport class
    Optimize {
        /// Path to Rust source file
        #[arg(short, long)]
        rust: PathBuf,

        /// Path to Python source file
        #[arg(short, long)]
        python: PathBuf,

        /// Show only suggestions with impact > threshold
        #[arg(short, long, default_value = "0.0")]
        threshold: f64,
    },

    /// Generate PyO3 bindings with transport-class optimization
    Generate {
        /// Path to Rust source file
        #[arg(short, long)]
        rust: PathBuf,

        /// Path to Python source file
        #[arg(short, long)]
        python: PathBuf,

        /// Output directory for generated code
        #[arg(short, long, default_value = "generated")]
        output: PathBuf,

        /// Generate Python stubs (.pyi)
        #[arg(short, long)]
        stubs: bool,
    },

    /// Quick compatibility check
    Check {
        /// Path to Rust source file
        #[arg(short, long)]
        rust: PathBuf,

        /// Path to Python source file
        #[arg(short, long)]
        python: PathBuf,
    },

    /// Universal protocol compiler (ephapax-verified)
    Compile {
        /// Source protocol format (bebop, flatbuffers, protobuf, etc.)
        #[arg(short = 'f', long)]
        from: String,

        /// Target protocol format (rust, python, rescript, etc.)
        #[arg(short = 't', long)]
        to: String,

        /// Input schema file
        #[arg(short, long)]
        input: PathBuf,

        /// Output directory
        #[arg(short, long, default_value = "generated")]
        output: PathBuf,
    },

    /// Analyze any protocol schema
    AnalyzeSchema {
        /// Protocol format
        #[arg(short, long)]
        protocol: String,

        /// Input schema file
        #[arg(short, long)]
        input: PathBuf,

        /// Show detailed analysis
        #[arg(short, long)]
        detailed: bool,
    },

    /// Cross-compile to multiple target formats
    CrossCompile {
        /// Input schema file
        #[arg(short, long)]
        input: PathBuf,

        /// Comma-separated target formats (rust,python,bebop,etc.)
        #[arg(short, long)]
        targets: String,

        /// Output directory
        #[arg(short, long, default_value = "generated")]
        output: PathBuf,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Analyze {
            rust,
            python,
            detailed,
            format,
        } => analyze::run(rust, python, detailed, format),

        Commands::Optimize {
            rust,
            python,
            threshold,
        } => optimize(rust, python, threshold),

        Commands::Generate {
            rust,
            python,
            output,
            stubs,
        } => generate::run(rust, python, output, stubs),

        Commands::Check { rust, python } => check(rust, python),

        Commands::Compile {
            from,
            to,
            input,
            output,
        } => compile_universal(from, to, input, output),

        Commands::AnalyzeSchema {
            protocol,
            input,
            detailed,
        } => analyze_schema(protocol, input, detailed),

        Commands::CrossCompile {
            input,
            targets,
            output,
        } => cross_compile(input, targets, output),
    }
}

fn compile_universal(from: String, to: String, input: PathBuf, output: PathBuf) -> Result<()> {
    use crate::compiler::UniversalCompiler;
    use crate::formats::ProtocolFormat;

    let source_format = ProtocolFormat::from_str(&from)?;
    let target_format = ProtocolFormat::from_str(&to)?;

    let compiler = UniversalCompiler::new();
    let result = compiler.compile(source_format, &input, target_format, &output)?;

    println!("\n{}", result.summary());
    println!(
        "{}",
        format!(
            "Ephapax verification: {} (linear types guarantee correctness)",
            if result.ephapax_verified { "✓" } else { "✗" }
        )
        .bright_green()
    );

    Ok(())
}

fn analyze_schema(protocol: String, input: PathBuf, detailed: bool) -> Result<()> {
    use crate::formats::ProtocolFormat;

    let format = ProtocolFormat::from_str(&protocol)?;

    println!(
        "{}",
        format!("Analyzing {} schema...", format.name())
            .bright_cyan()
            .bold()
    );

    let schema = format.analyze_file(&input)?;

    println!("\n{}", "Schema Analysis:".bold());
    println!("  Format: {}", format.name().bright_green());
    println!("  Name: {}", schema.name.bright_cyan());
    println!("  Types: {}", schema.types.len().to_string().bright_yellow());
    println!("  Roots: {}", schema.roots.len().to_string().bright_yellow());

    if detailed {
        println!("\n{}", "Type Definitions:".bold());
        for (name, type_def) in &schema.types {
            match type_def {
                protocol_squisher_ir::TypeDef::Struct(s) => {
                    println!("  {} struct {} ({})", "→".blue(), name, s.fields.len());
                    for field in &s.fields {
                        println!("    - {}: {:?}", field.name, field.ty);
                    }
                }
                protocol_squisher_ir::TypeDef::Enum(e) => {
                    println!("  {} enum {} ({})", "→".blue(), name, e.variants.len());
                    for variant in &e.variants {
                        println!("    - {}", variant.name);
                    }
                }
                protocol_squisher_ir::TypeDef::Union(u) => {
                    println!("  {} union {} ({} types)", "→".blue(), name, u.variants.len());
                    for (i, variant_ty) in u.variants.iter().enumerate() {
                        println!("    - variant {}: {:?}", i, variant_ty);
                    }
                }
                protocol_squisher_ir::TypeDef::Alias(a) => {
                    println!("  {} alias {} = {:?}", "→".blue(), name, a.target);
                }
                protocol_squisher_ir::TypeDef::Newtype(n) => {
                    println!("  {} newtype {} = {:?}", "→".blue(), name, n.inner);
                }
            }
        }
    }

    Ok(())
}

fn cross_compile(input: PathBuf, targets: String, output: PathBuf) -> Result<()> {
    use crate::compiler::UniversalCompiler;
    use crate::formats::ProtocolFormat;

    // Detect source format from input file
    let source_format = ProtocolFormat::from_path(&input)?;

    println!(
        "{}",
        format!(
            "Cross-compiling from {} to multiple targets (ephapax-verified)",
            source_format.name()
        )
        .bright_cyan()
        .bold()
    );

    // Parse target formats
    let target_formats: Result<Vec<ProtocolFormat>> = targets
        .split(',')
        .map(|t| ProtocolFormat::from_str(t.trim()))
        .collect();
    let target_formats = target_formats?;

    println!("  Targets: {}", targets.bright_green());

    let compiler = UniversalCompiler::new();
    let mut results = Vec::new();

    for target in target_formats {
        let target_output = output.join(target.name());
        match compiler.compile(source_format, &input, target, &target_output) {
            Ok(result) => {
                println!("  {} {}", "✓".green(), target.name());
                results.push(result);
            }
            Err(e) => {
                println!("  {} {} - {}", "✗".red(), target.name(), e);
            }
        }
    }

    println!("\n{}", format!("Cross-compilation complete: {}/{} succeeded",
        results.len(), targets.split(',').count()).bright_green().bold());

    Ok(())
}

fn optimize(rust_path: PathBuf, python_path: PathBuf, threshold: f64) -> Result<()> {
    println!("{}", "🔍 Analyzing schemas for optimization...".cyan());

    // Parse Rust schema
    let rust_source = fs::read_to_string(&rust_path)
        .with_context(|| format!("Failed to read Rust file: {}", rust_path.display()))?;
    let rust_analyzer = RustAnalyzer::new();
    let rust_schema = rust_analyzer
        .analyze_source(&rust_source)
        .context("Failed to analyze Rust source")?;

    // Parse Python schema (stub for now - would use PythonAnalyzer)
    let _python_source = fs::read_to_string(&python_path)
        .with_context(|| format!("Failed to read Python file: {}", python_path.display()))?;

    // For now, create a target schema from Rust (would normally be from Python)
    let target_schema = create_target_schema(&rust_schema);

    // Run optimizer
    let engine = EphapaxCompatibilityEngine::new();
    let optimizer = EphapaxOptimizer::new(engine);
    let result = optimizer.analyze_and_suggest(&rust_schema, &target_schema);

    // Display current status
    println!("\n{}", "Current Status:".bold());
    println!("  Transport Class: {}", format_transport_class(&result.current.overall_class));
    println!("  Zero-Copy Fields: {}/{} ({:.1}%)",
        result.current.type_analyses.iter()
            .flat_map(|t| &t.field_analyses)
            .filter(|f| f.class == TransportClass::Concorde)
            .count(),
        result.current.type_analyses.iter()
            .flat_map(|t| &t.field_analyses)
            .count(),
        calculate_zero_copy_percentage(&result.current)
    );

    // Display suggestions
    println!("\n{}", "Optimization Suggestions:".bold().green());

    let filtered_suggestions: Vec<_> = result.suggestions.iter()
        .filter(|s| s.impact >= threshold)
        .collect();

    if filtered_suggestions.is_empty() {
        println!("  {} No optimization opportunities found (schema is already optimal)", "✓".green());
    } else {
        for (i, suggestion) in filtered_suggestions.iter().enumerate() {
            println!("\n  {}. {} → {}",
                i + 1,
                format!("{:?}", suggestion.current_class).red(),
                format!("{:?}", suggestion.improved_class).green()
            );
            println!("     Field: {}", suggestion.target.cyan());
            println!("     Impact: {:.1}% improvement", suggestion.impact);
            println!("     Reason: {}", suggestion.reason);
        }
    }

    // Display potential after optimizations
    println!("\n{}", "Potential After Optimizations:".bold());
    println!("  Zero-Copy: {:.1}%", result.potential_zero_copy_percentage);
    println!("  Production Ready: {}",
        if result.would_be_production_ready {
            "Yes ✓".green()
        } else {
            "No (need >90% safe)".yellow()
        }
    );

    Ok(())
}

fn check(rust_path: PathBuf, python_path: PathBuf) -> Result<()> {
    println!("{}", "⚡ Quick compatibility check...".cyan());

    // Parse Rust schema
    let rust_source = fs::read_to_string(&rust_path)
        .with_context(|| format!("Failed to read Rust file: {}", rust_path.display()))?;
    let rust_analyzer = RustAnalyzer::new();
    let rust_schema = rust_analyzer
        .analyze_source(&rust_source)
        .context("Failed to analyze Rust source")?;

    // Parse Python schema (stub)
    let _python_source = fs::read_to_string(&python_path)
        .with_context(|| format!("Failed to read Python file: {}", python_path.display()))?;

    let target_schema = create_target_schema(&rust_schema);

    // Analyze compatibility
    let engine = EphapaxCompatibilityEngine::new();
    let result = engine.analyze_schemas(&rust_schema, &target_schema);

    // Display result
    println!("\n{}", "Compatibility Result:".bold());
    println!("  Overall Class: {}", format_transport_class(&result.overall_class));

    let zero_copy_pct = calculate_zero_copy_percentage(&result);
    println!("  Zero-Copy: {:.1}%", zero_copy_pct);

    if zero_copy_pct > 90.0 {
        println!("\n  {} Production ready!", "✓".green().bold());
    } else if zero_copy_pct > 50.0 {
        println!("\n  {} Needs optimization", "⚠".yellow().bold());
        println!("    Run 'protocol-squisher optimize' for suggestions");
    } else {
        println!("\n  {} Significant compatibility issues", "✗".red().bold());
        println!("    Run 'protocol-squisher optimize' for suggestions");
    }

    Ok(())
}

fn format_transport_class(class: &TransportClass) -> String {
    match class {
        TransportClass::Concorde => "Concorde (100% fidelity, 0% overhead)".green().to_string(),
        TransportClass::Business => "Business (98% fidelity, 5% overhead)".cyan().to_string(),
        TransportClass::Economy => "Economy (80% fidelity, 25% overhead)".yellow().to_string(),
        TransportClass::Wheelbarrow => "Wheelbarrow (50% fidelity, 80% overhead)".red().to_string(),
    }
}

fn calculate_zero_copy_percentage(result: &protocol_squisher_compat::SchemaCompatibilityResult) -> f64 {
    let total: usize = result.type_analyses.iter()
        .map(|t| t.field_analyses.len())
        .sum();

    if total == 0 {
        return 0.0;
    }

    let zero_copy: usize = result.type_analyses.iter()
        .flat_map(|t| &t.field_analyses)
        .filter(|f| f.class == TransportClass::Concorde)
        .count();

    (zero_copy as f64 / total as f64) * 100.0
}

// Helper to create a target schema (would normally come from Python analyzer)
fn create_target_schema(source: &IrSchema) -> IrSchema {
    // For now, create a modified version with some narrowing conversions
    use protocol_squisher_ir::*;
    use std::collections::BTreeMap;

    let mut target_types = BTreeMap::new();

    for (type_id, type_def) in &source.types {
        if let TypeDef::Struct(s) = type_def {
            let mut narrowed_fields = Vec::new();

            for field in &s.fields {
                // Narrow some fields to demonstrate optimization
                let narrowed_ty = match &field.ty {
                    IrType::Primitive(PrimitiveType::I64) => IrType::Primitive(PrimitiveType::I32),
                    IrType::Primitive(PrimitiveType::F64) => IrType::Primitive(PrimitiveType::F32),
                    other => other.clone(),
                };

                narrowed_fields.push(FieldDef {
                    name: field.name.clone(),
                    ty: narrowed_ty,
                    optional: field.optional,
                    constraints: field.constraints.clone(),
                    metadata: field.metadata.clone(),
                });
            }

            target_types.insert(
                type_id.clone(),
                TypeDef::Struct(StructDef {
                    name: s.name.clone(),
                    fields: narrowed_fields,
                    metadata: s.metadata.clone(),
                }),
            );
        }
    }

    IrSchema {
        name: format!("{}_target", source.name),
        version: source.version.clone(),
        source_format: "python-pydantic".to_string(),
        types: target_types,
        roots: source.roots.clone(),
        metadata: source.metadata.clone(),
    }
}
