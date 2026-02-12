// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Code generation command

use anyhow::{Context, Result};
use colored::Colorize;
use protocol_squisher_pyo3_codegen::{OptimizedGenConfig, OptimizedPyO3Generator};
use protocol_squisher_rust_analyzer::RustAnalyzer;
use std::fs;
use std::path::PathBuf;

pub fn run(
    rust_path: PathBuf,
    python_path: PathBuf,
    output: PathBuf,
    stubs: bool,
) -> Result<()> {
    println!("{}", "🔧 Generating PyO3 bindings...".cyan());

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

    let target_schema = crate::create_target_schema(&rust_schema);

    // Create output directory
    fs::create_dir_all(&output)
        .with_context(|| format!("Failed to create output directory: {}", output.display()))?;

    // Generate bindings
    let config = OptimizedGenConfig {
        module_name: "bindings".to_string(),
        generate_stubs: stubs,
        add_transport_comments: true,
        production_threshold: 90.0,
        optimization_threshold: 20.0,
    };
    let generator = OptimizedPyO3Generator::with_config(config);

    let result = generator.generate_rust_to_python(&rust_schema, &target_schema);

    // Write Rust code
    let rust_output = output.join("bindings.rs");
    fs::write(&rust_output, &result.rust_code)
        .with_context(|| format!("Failed to write Rust bindings: {}", rust_output.display()))?;

    println!("  {} {}", "✓".green(), rust_output.display());

    // Write Python stubs if requested
    if stubs && result.python_stub.is_some() {
        let stubs_output = output.join("bindings.pyi");
        fs::write(&stubs_output, result.python_stub.as_ref().unwrap())
            .with_context(|| format!("Failed to write Python stubs: {}", stubs_output.display()))?;

        println!("  {} {}", "✓".green(), stubs_output.display());
    }

    // Display statistics
    println!("\n{}", "Generation Statistics:".bold());
    println!("  Transport Class: {}", format_transport_class(&result.analysis.overall_class));

    let zero_copy_pct = if result.stats.total_fields > 0 {
        (result.stats.zero_copy_fields as f64 / result.stats.total_fields as f64) * 100.0
    } else {
        0.0
    };

    println!("  Zero-Copy Fields: {}/{} ({:.1}%)",
        result.stats.zero_copy_fields,
        result.stats.total_fields,
        zero_copy_pct
    );
    println!("  JSON Fallback Fields: {}", result.stats.json_fallback_fields);

    if result.stats.is_production_ready {
        println!("\n  {} Production ready (>90% safe conversions)", "✓".green().bold());
    } else {
        let fallback_pct = if result.stats.total_fields > 0 {
            (result.stats.json_fallback_fields as f64 / result.stats.total_fields as f64) * 100.0
        } else {
            0.0
        };

        if fallback_pct > 20.0 {
            println!("\n  {} Needs optimization (>20% JSON fallback)", "⚠".yellow().bold());
            println!("    Run 'protocol-squisher optimize' for suggestions");
        }
    }

    Ok(())
}

fn format_transport_class(class: &protocol_squisher_transport_primitives::TransportClass) -> String {
    use protocol_squisher_transport_primitives::TransportClass;

    match class {
        TransportClass::Concorde => "Concorde".green().to_string(),
        TransportClass::Business => "Business".cyan().to_string(),
        TransportClass::Economy => "Economy".yellow().to_string(),
        TransportClass::Wheelbarrow => "Wheelbarrow".red().to_string(),
    }
}
