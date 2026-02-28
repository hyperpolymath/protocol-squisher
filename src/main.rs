// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Protocol Squisher CLI
//!
//! ```bash
//! protocol-squisher analyze schema-a.rs schema-b.py
//! protocol-squisher generate --from schema.rs --output ./bindings/
//! protocol-squisher compare schema-a.rs schema-b.rs
//! ```

use protocol_squisher::compat::{CompatibilityAnalyzer, TransportClass, LossSeverity};
use protocol_squisher::ir::IrSchema;
use protocol_squisher::json_fallback::{generate_fallback, FallbackConfig};
use protocol_squisher::pyo3_codegen::{generate_module, ModuleGenConfig};
use protocol_squisher::python_analyzer::PythonAnalyzer;
use protocol_squisher::rust_analyzer::RustAnalyzer;
use std::env;
use std::fs;
use std::path::Path;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        print_usage();
        return ExitCode::from(1);
    }

    match args[1].as_str() {
        "analyze" => cmd_analyze(&args[2..]),
        "compare" => cmd_compare(&args[2..]),
        "generate" => cmd_generate(&args[2..]),
        "fallback" => cmd_fallback(&args[2..]),
        "version" | "--version" | "-V" => {
            println!("protocol-squisher {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        "help" | "--help" | "-h" => {
            print_usage();
            ExitCode::SUCCESS
        }
        other => {
            eprintln!("Unknown command: {other}");
            eprintln!();
            print_usage();
            ExitCode::from(1)
        }
    }
}

fn print_usage() {
    println!(
        r#"protocol-squisher - Universal protocol interoperability

USAGE:
    protocol-squisher <COMMAND> [OPTIONS]

COMMANDS:
    analyze     Parse a schema file and show its IR representation
    compare     Compare two schemas for compatibility
    generate    Generate PyO3 binding code from a Rust schema
    fallback    Generate JSON fallback transport (Rust + Python)
    version     Show version information
    help        Show this help message

EXAMPLES:
    protocol-squisher analyze models.rs
    protocol-squisher analyze models.py
    protocol-squisher compare rust_types.rs python_models.py
    protocol-squisher generate --from schema.rs --module my_bindings -o ./src/
    protocol-squisher fallback --from schema.rs --module transport -o ./bindings/

The Invariant: If it compiles, it carries.
"#
    );
}

/// Analyze a single schema file and display its IR
fn cmd_analyze(args: &[String]) -> ExitCode {
    if args.is_empty() {
        eprintln!("Usage: protocol-squisher analyze <schema-file>");
        eprintln!();
        eprintln!("Supported formats:");
        eprintln!("  .rs   - Rust (serde derive)");
        eprintln!("  .py   - Python (Pydantic models)");
        eprintln!("  .json - Pydantic introspection JSON");
        return ExitCode::from(1);
    }

    let path = &args[0];

    match analyze_file(path) {
        Ok(schema) => {
            println!("=== Schema Analysis: {} ===", path);
            println!();
            println!("Name: {}", schema.name);
            println!("Source: {}", schema.source_format);
            println!("Types: {}", schema.types.len());
            println!();

            for (name, type_def) in &schema.types {
                println!("  {} - {:?}", name, type_def_summary(type_def));
            }

            if !schema.roots.is_empty() {
                println!();
                println!("Root types: {:?}", schema.roots);
            }

            println!();
            println!("Full IR (JSON):");
            match serde_json::to_string_pretty(&schema) {
                Ok(json) => println!("{}", json),
                Err(e) => eprintln!("Failed to serialize IR: {}", e),
            }

            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("Error analyzing {}: {}", path, e);
            ExitCode::from(1)
        }
    }
}

/// Compare two schemas for compatibility
fn cmd_compare(args: &[String]) -> ExitCode {
    if args.len() < 2 {
        eprintln!("Usage: protocol-squisher compare <schema-a> <schema-b>");
        return ExitCode::from(1);
    }

    let path_a = &args[0];
    let path_b = &args[1];

    let schema_a = match analyze_file(path_a) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error analyzing {}: {}", path_a, e);
            return ExitCode::from(1);
        }
    };

    let schema_b = match analyze_file(path_b) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error analyzing {}: {}", path_b, e);
            return ExitCode::from(1);
        }
    };

    println!("=== Compatibility Analysis ===");
    println!();
    println!("Source: {} ({} types)", path_a, schema_a.types.len());
    println!("Target: {} ({} types)", path_b, schema_b.types.len());
    println!();

    let analyzer = CompatibilityAnalyzer::new();
    let result = analyzer.compare(&schema_a, &schema_b);

    // Display transport class with emoji
    let class_display = match result.class {
        TransportClass::Concorde => "Concorde (zero-copy, full fidelity)",
        TransportClass::BusinessClass => "Business Class (minor overhead)",
        TransportClass::Economy => "Economy (moderate overhead)",
        TransportClass::Wheelbarrow => "Wheelbarrow (high overhead, but works)",
        TransportClass::Incompatible => "Incompatible (cannot transport)",
    };

    println!("Transport Class: {}", class_display);
    println!();

    // Display losses
    if result.all_losses.is_empty() {
        println!("Losses: None (lossless conversion)");
    } else {
        println!("Losses ({}):", result.all_losses.len());
        for loss in &result.all_losses {
            let severity_icon = match loss.severity {
                LossSeverity::Info => "[info]",
                LossSeverity::Minor => "[minor]",
                LossSeverity::Moderate => "[moderate]",
                LossSeverity::Major => "[MAJOR]",
                LossSeverity::Critical => "[CRITICAL]",
            };
            println!(
                "  {} {:?} at {}: {}",
                severity_icon, loss.kind, loss.path, loss.description
            );
        }
    }

    println!();

    // Summary
    if result.is_compatible() {
        println!("TRANSPORT VIABLE");
        if result.all_losses.is_empty() {
            println!("   Perfect fidelity - no data loss");
        } else {
            println!("   {} documented loss(es)", result.all_losses.len());
        }
    } else {
        println!("TRANSPORT NOT VIABLE");
        println!("   Schemas are incompatible");
    }

    ExitCode::SUCCESS
}

/// Generate PyO3 bindings from a Rust schema
fn cmd_generate(args: &[String]) -> ExitCode {
    let mut from_path: Option<String> = None;
    let mut module_name = "generated".to_string();
    let mut output_path: Option<String> = None;

    // Parse arguments
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--from" | "-f" => {
                if i + 1 < args.len() {
                    from_path = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("--from requires a path argument");
                    return ExitCode::from(1);
                }
            }
            "--module" | "-m" => {
                if i + 1 < args.len() {
                    module_name = args[i + 1].clone();
                    i += 2;
                } else {
                    eprintln!("--module requires a name argument");
                    return ExitCode::from(1);
                }
            }
            "--output" | "-o" => {
                if i + 1 < args.len() {
                    output_path = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("--output requires a path argument");
                    return ExitCode::from(1);
                }
            }
            other => {
                // Positional argument - treat as from_path if not set
                if from_path.is_none() {
                    from_path = Some(other.to_string());
                }
                i += 1;
            }
        }
    }

    let from_path = match from_path {
        Some(p) => p,
        None => {
            eprintln!("Usage: protocol-squisher generate --from <schema.rs> [--module name] [--output dir]");
            return ExitCode::from(1);
        }
    };

    // Analyze the source schema
    let schema = match analyze_file(&from_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error analyzing {}: {}", from_path, e);
            return ExitCode::from(1);
        }
    };

    println!("=== PyO3 Code Generation ===");
    println!();
    println!("Source: {} ({} types)", from_path, schema.types.len());
    println!("Module: {}", module_name);
    println!();

    // Generate code
    let config = ModuleGenConfig::new(&module_name)
        .with_doc(format!("Generated from {} by protocol-squisher", from_path));
    let result = generate_module(&schema, &config);

    // Output
    if let Some(output_dir) = output_path {
        let output_path = Path::new(&output_dir);

        // Create directory if needed
        if let Err(e) = fs::create_dir_all(output_path) {
            eprintln!("Failed to create output directory: {}", e);
            return ExitCode::from(1);
        }

        // Write Rust code
        let rust_path = output_path.join(format!("{}.rs", module_name));
        if let Err(e) = fs::write(&rust_path, &result.rust_code) {
            eprintln!("Failed to write {}: {}", rust_path.display(), e);
            return ExitCode::from(1);
        }
        println!("Generated: {}", rust_path.display());

        // Write Python stubs if available
        if let Some(stub) = &result.python_stub {
            let stub_path = output_path.join(format!("{}.pyi", module_name));
            if let Err(e) = fs::write(&stub_path, stub) {
                eprintln!("Failed to write {}: {}", stub_path.display(), e);
                return ExitCode::from(1);
            }
            println!("Generated: {}", stub_path.display());
        }

        println!();
        println!("Types generated: {:?}", result.generated_types);

        if !result.missing_types.is_empty() {
            println!("⚠️  Missing types (referenced but not defined): {:?}", result.missing_types);
        }
    } else {
        // Print to stdout
        println!("--- Rust Code ({}.rs) ---", module_name);
        println!("{}", result.rust_code);

        if let Some(stub) = &result.python_stub {
            println!();
            println!("--- Python Stub ({}.pyi) ---", module_name);
            println!("{}", stub);
        }
    }

    ExitCode::SUCCESS
}

/// Generate JSON fallback transport code (Rust + Python)
fn cmd_fallback(args: &[String]) -> ExitCode {
    let mut from_path: Option<String> = None;
    let mut module_name = "fallback".to_string();
    let mut output_path: Option<String> = None;
    let mut pretty_json = false;

    // Parse arguments
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--from" | "-f" => {
                if i + 1 < args.len() {
                    from_path = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("--from requires a path argument");
                    return ExitCode::from(1);
                }
            }
            "--module" | "-m" => {
                if i + 1 < args.len() {
                    module_name = args[i + 1].clone();
                    i += 2;
                } else {
                    eprintln!("--module requires a name argument");
                    return ExitCode::from(1);
                }
            }
            "--output" | "-o" => {
                if i + 1 < args.len() {
                    output_path = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("--output requires a path argument");
                    return ExitCode::from(1);
                }
            }
            "--pretty" => {
                pretty_json = true;
                i += 1;
            }
            other => {
                // Positional argument - treat as from_path if not set
                if from_path.is_none() {
                    from_path = Some(other.to_string());
                }
                i += 1;
            }
        }
    }

    let from_path = match from_path {
        Some(p) => p,
        None => {
            eprintln!("Usage: protocol-squisher fallback --from <schema> [--module name] [--output dir] [--pretty]");
            eprintln!();
            eprintln!("Generates JSON fallback transport code for both Rust and Python.");
            eprintln!("The guaranteed wheelbarrow: slow but unbreakable.");
            return ExitCode::from(1);
        }
    };

    // Analyze the source schema
    let schema = match analyze_file(&from_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error analyzing {}: {}", from_path, e);
            return ExitCode::from(1);
        }
    };

    println!("=== JSON Fallback Generation ===");
    println!();
    println!("Source: {} ({} types)", from_path, schema.types.len());
    println!("Module: {}", module_name);
    println!("Pretty JSON: {}", if pretty_json { "yes" } else { "no" });
    println!();

    // Generate code
    let config = FallbackConfig::new(&module_name)
        .with_pretty_json(pretty_json);
    let result = generate_fallback(&schema, &config);

    // Report results
    println!("Generated {} types", result.generated_types.len());
    if !result.skipped_types.is_empty() {
        println!("Skipped {} types:", result.skipped_types.len());
        for (type_id, reason) in &result.skipped_types {
            println!("  {} - {}", type_id, reason);
        }
    }
    println!();

    // Output
    if let Some(output_dir) = output_path {
        let output_path = Path::new(&output_dir);

        // Create directory if needed
        if let Err(e) = fs::create_dir_all(output_path) {
            eprintln!("Failed to create output directory: {}", e);
            return ExitCode::from(1);
        }

        // Write Rust code
        let rust_path = output_path.join(format!("{}.rs", module_name));
        if let Err(e) = fs::write(&rust_path, &result.rust_code) {
            eprintln!("Failed to write {}: {}", rust_path.display(), e);
            return ExitCode::from(1);
        }
        println!("Generated: {}", rust_path.display());

        // Write Python code
        let python_path = output_path.join(format!("{}.py", module_name));
        if let Err(e) = fs::write(&python_path, &result.python_code) {
            eprintln!("Failed to write {}: {}", python_path.display(), e);
            return ExitCode::from(1);
        }
        println!("Generated: {}", python_path.display());

        println!();
        println!("The wheelbarrow is ready. Transport guaranteed.");
    } else {
        // Print to stdout
        println!("--- Rust Code ({}.rs) ---", module_name);
        println!("{}", result.rust_code);

        println!();
        println!("--- Python Code ({}.py) ---", module_name);
        println!("{}", result.python_code);
    }

    ExitCode::SUCCESS
}

/// Analyze a file and return its IR schema
fn analyze_file(path: &str) -> Result<IrSchema, String> {
    let path_obj = Path::new(path);
    let extension = path_obj
        .extension()
        .and_then(|e| e.to_str())
        .unwrap_or("");

    match extension {
        "rs" => analyze_rust(path),
        "py" => analyze_python(path),
        "json" => analyze_python_json(path),
        _ => Err(format!(
            "Unknown file extension: .{} (expected .rs, .py, or .json)",
            extension
        )),
    }
}

/// Analyze a Rust file
fn analyze_rust(path: &str) -> Result<IrSchema, String> {
    let content = fs::read_to_string(path)
        .map_err(|e| format!("Failed to read {}: {}", path, e))?;

    let analyzer = RustAnalyzer::new();
    analyzer
        .analyze_source(&content)
        .map_err(|e| format!("Failed to analyze Rust: {}", e))
}

/// Analyze a Python file (runs introspection)
fn analyze_python(path: &str) -> Result<IrSchema, String> {
    let analyzer = PythonAnalyzer::new();
    analyzer
        .analyze_file(Path::new(path))
        .map_err(|e| format!("Failed to analyze Python: {}", e))
}

/// Analyze Pydantic introspection JSON
fn analyze_python_json(path: &str) -> Result<IrSchema, String> {
    let content = fs::read_to_string(path)
        .map_err(|e| format!("Failed to read {}: {}", path, e))?;

    let analyzer = PythonAnalyzer::new();
    analyzer
        .analyze_json(&content)
        .map_err(|e| format!("Failed to analyze Python JSON: {}", e))
}

/// Get a brief summary of a type definition
fn type_def_summary(type_def: &protocol_squisher::ir::TypeDef) -> &'static str {
    match type_def {
        protocol_squisher::ir::TypeDef::Struct(s) => {
            if s.fields.is_empty() {
                "struct (empty)"
            } else {
                "struct"
            }
        }
        protocol_squisher::ir::TypeDef::Enum(e) => {
            if e.variants.iter().all(|v| v.payload.is_none()) {
                "enum (simple)"
            } else {
                "enum (complex)"
            }
        }
        protocol_squisher::ir::TypeDef::Alias(_) => "alias",
        protocol_squisher::ir::TypeDef::Newtype(_) => "newtype",
        protocol_squisher::ir::TypeDef::Union(_) => "union",
    }
}
