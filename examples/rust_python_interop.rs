// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! # Rust <-> Python Interoperability Demo
//!
//! This example demonstrates the complete protocol-squisher workflow:
//!
//! 1. Analyze Rust types with serde derives
//! 2. Analyze Python Pydantic models (via JSON introspection output)
//! 3. Compare schemas for compatibility
//! 4. Generate PyO3 binding code for seamless interop
//!
//! Run with: `cargo run --example rust_python_interop`

use protocol_squisher_compat::{CompatibilityAnalyzer, TransportClass};
use protocol_squisher_ir::TypeDef;
use protocol_squisher_pyo3_codegen::PyO3Generator;
use protocol_squisher_rust_analyzer::RustAnalyzer;

fn main() {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║          Protocol Squisher: Rust <-> Python Demo            ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    // Step 1: Analyze Rust types
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│ Step 1: Analyzing Rust Types                                │");
    println!("└─────────────────────────────────────────────────────────────┘");

    let rust_source = r#"
        use serde::{Serialize, Deserialize};

        /// A user in the system
        #[derive(Serialize, Deserialize)]
        struct User {
            /// Unique identifier
            id: u64,
            /// User's display name
            name: String,
            /// Email address (optional)
            email: Option<String>,
            /// Account status
            status: Status,
            /// Tags for categorization
            tags: Vec<String>,
        }

        /// Account status enumeration
        #[derive(Serialize, Deserialize)]
        enum Status {
            Active,
            Inactive,
            Pending,
        }
    "#;

    let rust_analyzer = RustAnalyzer::new();
    let rust_schema = rust_analyzer.analyze_source(rust_source).unwrap();

    println!("\nRust source analyzed successfully!");
    println!("Found {} types:", rust_schema.types.len());
    for (name, type_def) in &rust_schema.types {
        match type_def {
            TypeDef::Struct(s) => {
                println!("  • struct {} ({} fields)", name, s.fields.len());
            },
            TypeDef::Enum(e) => {
                println!("  • enum {} ({} variants)", name, e.variants.len());
            },
            _ => {},
        }
    }

    // Step 2: Simulate Python Pydantic analysis
    println!("\n┌─────────────────────────────────────────────────────────────┐");
    println!("│ Step 2: Analyzing Python Pydantic Models                    │");
    println!("└─────────────────────────────────────────────────────────────┘");

    // In a real scenario, this would come from running the Python introspection script
    // Here we simulate the JSON output that Pydantic introspection would produce
    let python_introspection_json = r#"{
        "module": "myapp.models",
        "pydantic_version": 2,
        "types": [
            {
                "kind": "model",
                "name": "User",
                "module": "myapp.models",
                "doc": "A user in the system",
                "fields": [
                    {
                        "name": "id",
                        "type": {"kind": "primitive", "type": "int"},
                        "optional": false,
                        "constraints": {"ge": 0}
                    },
                    {
                        "name": "name",
                        "type": {"kind": "primitive", "type": "string"},
                        "optional": false,
                        "constraints": {"min_length": 1, "max_length": 100}
                    },
                    {
                        "name": "email",
                        "type": {"kind": "optional", "inner": {"kind": "primitive", "type": "string"}},
                        "optional": true,
                        "default": null,
                        "constraints": {"pattern": "^[\\w.-]+@[\\w.-]+$"}
                    },
                    {
                        "name": "status",
                        "type": {"kind": "enum", "name": "Status", "module": "myapp.models", "variants": []},
                        "optional": false,
                        "constraints": {}
                    },
                    {
                        "name": "tags",
                        "type": {"kind": "list", "inner": {"kind": "primitive", "type": "string"}},
                        "optional": false,
                        "constraints": {}
                    }
                ],
                "config": {}
            },
            {
                "kind": "enum",
                "name": "Status",
                "module": "myapp.models",
                "doc": "Account status enumeration",
                "variants": [
                    {"name": "ACTIVE", "value": "active"},
                    {"name": "INACTIVE", "value": "inactive"},
                    {"name": "PENDING", "value": "pending"}
                ]
            }
        ]
    }"#;

    let python_analyzer = protocol_squisher_python_analyzer::PythonAnalyzer::new();
    let python_schema = python_analyzer
        .analyze_json(python_introspection_json)
        .unwrap();

    println!("\nPython Pydantic models analyzed successfully!");
    println!("Found {} types:", python_schema.types.len());
    for (name, type_def) in &python_schema.types {
        match type_def {
            TypeDef::Struct(s) => {
                println!("  • class {} ({} fields)", name, s.fields.len());
            },
            TypeDef::Enum(e) => {
                println!("  • Enum {} ({} variants)", name, e.variants.len());
            },
            _ => {},
        }
    }

    // Step 3: Compare schemas
    println!("\n┌─────────────────────────────────────────────────────────────┐");
    println!("│ Step 3: Comparing Schemas for Compatibility                 │");
    println!("└─────────────────────────────────────────────────────────────┘");

    let compat_analyzer = CompatibilityAnalyzer::new();
    let comparison = compat_analyzer.compare(&rust_schema, &python_schema);

    let class_description = match comparison.class {
        TransportClass::Concorde => "Zero-copy, perfect fidelity",
        TransportClass::BusinessClass => "Minor overhead, full fidelity",
        TransportClass::Economy => "Moderate overhead, documented losses",
        TransportClass::Wheelbarrow => "High overhead, significant losses",
        TransportClass::Incompatible => "Not convertible",
    };

    println!("\nRust -> Python conversion analysis:");
    println!("  Transport Class: {:?}", comparison.class);
    println!("  Description: {}", class_description);
    println!("  Total losses: {}", comparison.all_losses.len());

    if !comparison.all_losses.is_empty() {
        println!("\nConversion notes:");
        for loss in &comparison.all_losses {
            println!(
                "  • {}: {} ({:?})",
                loss.path, loss.description, loss.severity
            );
        }
    }

    // Also check Python -> Rust
    let reverse_comparison = compat_analyzer.compare(&python_schema, &rust_schema);
    println!("\nPython -> Rust conversion analysis:");
    println!("  Transport Class: {:?}", reverse_comparison.class);
    println!("  Total losses: {}", reverse_comparison.all_losses.len());

    // Step 4: Generate PyO3 binding code
    println!("\n┌─────────────────────────────────────────────────────────────┐");
    println!("│ Step 4: Generating PyO3 Bindings                            │");
    println!("└─────────────────────────────────────────────────────────────┘");

    let generator = PyO3Generator::with_module_name("user_models")
        .doc("Generated bindings for user models")
        .with_serde(true)
        .with_stubs(true);

    let generated = generator.generate(&rust_schema);

    println!("\nGenerated PyO3 module 'user_models'");
    println!("Generated types: {:?}", generated.generated_types);

    println!("\n═══════════════════════════════════════════════════════════════");
    println!("Generated Rust Code (PyO3 bindings):");
    println!("═══════════════════════════════════════════════════════════════");
    println!("{}", generated.rust_code);

    if let Some(stub) = &generated.python_stub {
        println!("\n═══════════════════════════════════════════════════════════════");
        println!("Generated Python Type Stub (.pyi):");
        println!("═══════════════════════════════════════════════════════════════");
        println!("{}", stub);
    }

    // Summary
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║                         Summary                              ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!();
    println!("Protocol Squisher analyzed types from both Rust and Python,");
    println!("compared them for compatibility, and generated interop code.");
    println!();
    println!("Key capabilities demonstrated:");
    println!("  ✓ Rust serde struct/enum analysis");
    println!("  ✓ Python Pydantic model introspection");
    println!("  ✓ Schema compatibility analysis with loss documentation");
    println!("  ✓ PyO3 binding code generation");
    println!("  ✓ Python type stub (.pyi) generation");
    println!();
    println!("The generated code can be used in a maturin/PyO3 project to");
    println!("create native Python modules from Rust types with full type");
    println!("safety and zero-copy performance where possible.");
}
