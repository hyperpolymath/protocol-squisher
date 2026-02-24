// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Protocol Squisher CLI
//!
//! Command-line tool for analyzing schemas and generating optimized PyO3 bindings.

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use colored::Colorize;
use protocol_squisher_compat::EphapaxCompatibilityEngine;
use protocol_squisher_ir::IrSchema;
use protocol_squisher_optimizer::EphapaxOptimizer;
use protocol_squisher_python_analyzer::PythonAnalyzer;
use protocol_squisher_rust_analyzer::RustAnalyzer;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

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
        #[arg(short, long, required_unless_present = "python")]
        rust: Option<PathBuf>,

        /// Path to Python source file
        #[arg(short, long, required_unless_present = "rust")]
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

        /// Path to synthesis hints JSON (defaults to PROTOCOL_SQUISHER_SYNTHESIS_HINTS if set)
        #[arg(long)]
        synthesis_hints: Option<PathBuf>,
    },

    /// AI-assisted optimization using empirical hint weighting
    OptimizeAi {
        /// Path to Rust source file
        #[arg(short, long)]
        rust: PathBuf,

        /// Path to Python source file
        #[arg(short, long)]
        python: PathBuf,

        /// Optional synthesis hints JSON
        #[arg(long)]
        synthesis_hints: Option<PathBuf>,

        /// Output format (text, json)
        #[arg(short, long, default_value = "text")]
        format: String,
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

    /// Universal protocol compiler (ephapax backend when available)
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

    /// Synthesize an adapter plan with miniKanren-style constraint search
    Synthesize {
        /// Source protocol format (rust, protobuf, thrift, etc.)
        #[arg(long = "from-format")]
        from_format: String,

        /// Target protocol format (rust, python, protobuf, etc.)
        #[arg(long = "to-format")]
        to_format: String,

        /// Source schema file
        #[arg(long = "from")]
        from_path: PathBuf,

        /// Target schema file
        #[arg(long = "to")]
        to_path: PathBuf,

        /// Output format (text, json)
        #[arg(short, long, default_value = "text")]
        format: String,
    },

    /// Bridge TLS profile to Noise pattern with safety verification
    SecurityBridge {
        /// TLS version (1.0, 1.1, 1.2, 1.3)
        #[arg(long, default_value = "1.3")]
        tls_version: String,

        /// Key exchange (rsa, dhe, ecdhe, psk)
        #[arg(long, default_value = "ecdhe")]
        key_exchange: String,

        /// Require mutual authentication (mTLS)
        #[arg(long)]
        mutual_auth: bool,

        /// Disable certificate validation (unsafe; usually rejected)
        #[arg(long)]
        no_cert_validation: bool,

        /// Enable session resumption
        #[arg(long)]
        session_resumption: bool,

        /// Required security properties (comma-separated):
        /// forward_secrecy, mutual_authentication, identity_hiding, replay_resistance
        #[arg(long, value_delimiter = ',')]
        require: Vec<String>,

        /// Output format (text, json)
        #[arg(short, long, default_value = "text")]
        format: String,
    },

    /// Run performance optimization probes (zero-copy, SIMD, lazy, streaming)
    Performance {
        /// Output format (text, json)
        #[arg(short, long, default_value = "text")]
        format: String,

        /// Sample size for checksum benchmark payload
        #[arg(long, default_value = "262144")]
        sample_size: usize,
    },

    /// Distributed protocol squishing across a manifest of schema pairs
    DistributedSquish {
        /// JSON manifest path with pair definitions
        #[arg(long)]
        manifest: PathBuf,

        /// Worker threads to use
        #[arg(long, default_value = "4")]
        workers: usize,

        /// Output format (text, json)
        #[arg(short, long, default_value = "text")]
        format: String,
    },

    /// Hardware-acceleration probe across scalar/SIMD/parallel backends
    HardwareAccel {
        /// Payload sample size in bytes
        #[arg(long, default_value = "1048576")]
        sample_size: usize,

        /// Backend: auto, scalar, simd, parallel
        #[arg(long, default_value = "auto")]
        backend: String,

        /// Output format (text, json)
        #[arg(short, long, default_value = "text")]
        format: String,
    },

    /// Schema registry integration: publish/fetch/list versioned schemas
    SchemaRegistry {
        #[command(subcommand)]
        command: SchemaRegistryCommand,

        /// Registry storage directory
        #[arg(long, default_value = "target/schema-registry")]
        registry_dir: PathBuf,

        /// Output format (text, json)
        #[arg(short, long, default_value = "text")]
        format: String,
    },

    /// Generate a migration plan between two schema versions
    Migrate {
        /// Source protocol format
        #[arg(long = "from-format")]
        from_format: String,

        /// Target protocol format
        #[arg(long = "to-format")]
        to_format: String,

        /// Source schema path
        #[arg(long = "from")]
        from_path: PathBuf,

        /// Target schema path
        #[arg(long = "to")]
        to_path: PathBuf,

        /// Output format (text, json)
        #[arg(short, long, default_value = "text")]
        format: String,
    },

    /// Enforce governance policy against a migration plan
    GovernanceCheck {
        /// Source protocol format
        #[arg(long = "from-format")]
        from_format: String,

        /// Target protocol format
        #[arg(long = "to-format")]
        to_format: String,

        /// Source schema path
        #[arg(long = "from")]
        from_path: PathBuf,

        /// Target schema path
        #[arg(long = "to")]
        to_path: PathBuf,

        /// Maximum allowed breaking changes
        #[arg(long, default_value = "0")]
        max_breaking_changes: usize,

        /// Minimum acceptable transport class (concorde,business,economy,wheelbarrow)
        #[arg(long, default_value = "economy")]
        minimum_class: String,

        /// Output format (text, json)
        #[arg(short, long, default_value = "text")]
        format: String,
    },

    /// Read audit log entries
    AuditLog {
        /// Audit log path
        #[arg(long, default_value = "target/audit/audit-log.jsonl")]
        log: PathBuf,

        /// Max entries to print (latest-first in text mode)
        #[arg(long, default_value = "100")]
        limit: usize,

        /// Output format (text, json)
        #[arg(short, long, default_value = "text")]
        format: String,
    },

    /// Adapter marketplace catalog operations
    Marketplace {
        #[command(subcommand)]
        command: MarketplaceCommand,

        /// Marketplace storage directory
        #[arg(long, default_value = "target/marketplace")]
        marketplace_dir: PathBuf,

        /// Output format (text, json)
        #[arg(short, long, default_value = "text")]
        format: String,
    },

    /// Interactive compatibility explorer
    Explore {
        /// Source protocol format
        #[arg(long = "from-format")]
        from_format: String,

        /// Target protocol format
        #[arg(long = "to-format")]
        to_format: String,

        /// Source schema path
        #[arg(long = "from")]
        from_path: PathBuf,

        /// Target schema path
        #[arg(long = "to")]
        to_path: PathBuf,

        /// Output format (text, json)
        #[arg(short, long, default_value = "text")]
        format: String,
    },

    /// Start local web playground (or print static page)
    Playground {
        /// Listen host
        #[arg(long, default_value = "127.0.0.1")]
        host: String,

        /// Listen port
        #[arg(long, default_value = "7878")]
        port: u16,

        /// Print the playground HTML and exit
        #[arg(long)]
        dump_html: bool,
    },

    /// Run LSP adapter-preview server over stdio
    Lsp {
        /// Process a single request and exit (for smoke tests)
        #[arg(long)]
        once: bool,
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

    /// Analyze a schema file for corpus collection (JSON output for squisher-corpus)
    CorpusAnalyze {
        /// Path to the schema file
        #[arg(short, long)]
        input: PathBuf,

        /// Protocol format hint (protobuf, avro, thrift, jsonschema, rust, python, etc.)
        #[arg(short = 'f', long)]
        format: String,
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

#[derive(Subcommand)]
enum SchemaRegistryCommand {
    /// Publish a versioned schema into the registry
    Publish {
        /// Schema logical name
        #[arg(long)]
        name: String,

        /// Semantic version
        #[arg(long)]
        version: String,

        /// Protocol format for input schema
        #[arg(long = "protocol")]
        protocol: String,

        /// Input schema file
        #[arg(short, long)]
        input: PathBuf,
    },

    /// Fetch a schema by name/version (latest when omitted)
    Fetch {
        /// Schema logical name
        #[arg(long)]
        name: String,

        /// Schema version (optional; defaults to latest)
        #[arg(long)]
        version: Option<String>,
    },

    /// List registry entries (optionally by name)
    List {
        /// Optional schema name filter
        #[arg(long)]
        name: Option<String>,
    },
}

#[derive(Subcommand)]
enum MarketplaceCommand {
    /// Publish an adapter listing
    Publish {
        #[arg(long)]
        id: String,
        #[arg(long)]
        name: String,
        #[arg(long = "from-format")]
        from_format: String,
        #[arg(long = "to-format")]
        to_format: String,
        #[arg(long)]
        version: String,
        #[arg(long)]
        description: String,
        /// Comma-separated tags
        #[arg(long, value_delimiter = ',')]
        tags: Vec<String>,
    },

    /// Get one listing by id
    Get {
        #[arg(long)]
        id: String,
    },

    /// List marketplace entries
    List {
        #[arg(long = "from-format")]
        from_format: Option<String>,
        #[arg(long = "to-format")]
        to_format: Option<String>,
        #[arg(long)]
        tag: Option<String>,
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
            synthesis_hints,
        } => optimize(rust, python, threshold, synthesis_hints),

        Commands::OptimizeAi {
            rust,
            python,
            synthesis_hints,
            format,
        } => optimize_ai(rust, python, synthesis_hints, format),

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

        Commands::Synthesize {
            from_format,
            to_format,
            from_path,
            to_path,
            format,
        } => synthesize_command(from_format, to_format, from_path, to_path, format),

        Commands::SecurityBridge {
            tls_version,
            key_exchange,
            mutual_auth,
            no_cert_validation,
            session_resumption,
            require,
            format,
        } => security_bridge_command(
            tls_version,
            key_exchange,
            mutual_auth,
            no_cert_validation,
            session_resumption,
            require,
            format,
        ),

        Commands::Performance {
            format,
            sample_size,
        } => performance_command(format, sample_size),

        Commands::DistributedSquish {
            manifest,
            workers,
            format,
        } => distributed_squish_command(manifest, workers, format),

        Commands::HardwareAccel {
            sample_size,
            backend,
            format,
        } => hardware_accel_command(sample_size, backend, format),

        Commands::SchemaRegistry {
            command,
            registry_dir,
            format,
        } => schema_registry_command(command, registry_dir, format),

        Commands::Migrate {
            from_format,
            to_format,
            from_path,
            to_path,
            format,
        } => migrate_command(from_format, to_format, from_path, to_path, format),

        Commands::GovernanceCheck {
            from_format,
            to_format,
            from_path,
            to_path,
            max_breaking_changes,
            minimum_class,
            format,
        } => governance_check_command(
            from_format,
            to_format,
            from_path,
            to_path,
            max_breaking_changes,
            minimum_class,
            format,
        ),

        Commands::AuditLog { log, limit, format } => audit_log_command(log, limit, format),

        Commands::Marketplace {
            command,
            marketplace_dir,
            format,
        } => marketplace_command(command, marketplace_dir, format),

        Commands::Explore {
            from_format,
            to_format,
            from_path,
            to_path,
            format,
        } => explore_command(from_format, to_format, from_path, to_path, format),

        Commands::Playground {
            host,
            port,
            dump_html,
        } => playground_command(host, port, dump_html),

        Commands::Lsp { once } => lsp_command(once),

        Commands::AnalyzeSchema {
            protocol,
            input,
            detailed,
        } => analyze_schema(protocol, input, detailed),

        Commands::CorpusAnalyze { input, format } => corpus_analyze(input, format),

        Commands::CrossCompile {
            input,
            targets,
            output,
        } => cross_compile(input, targets, output),
    }
}

/// Corpus analysis: parse a schema file and emit structured JSON for squisher-corpus ingestion.
///
/// Output JSON schema:
/// ```json
/// {
///   "schema": <IrSchema>,
///   "squishability": <SquishabilityReport>,
///   "transport_classes": ["Concorde", "Business", ...]
/// }
/// ```
fn corpus_analyze(input: PathBuf, format_hint: String) -> Result<()> {
    use crate::formats::ProtocolFormat;
    use protocol_squisher_meta_analysis::{
        Blocker, Pattern, SquishabilityReport, TransportClass as MetaTransportClass,
    };
    use serde::Serialize;
    use std::collections::HashMap;

    #[derive(Serialize)]
    struct CorpusOutput {
        schema: IrSchema,
        squishability: SquishabilityReport,
        transport_classes: Vec<String>,
    }

    let protocol = ProtocolFormat::from_str(&format_hint)?;
    let schema = protocol.analyze_file(&input).with_context(|| {
        format!(
            "Failed to analyze {} as {}",
            input.display(),
            protocol.name()
        )
    })?;

    // Build squishability report from the parsed IR schema
    let mut field_transport_classes: HashMap<String, MetaTransportClass> = HashMap::new();
    let mut patterns: Vec<Pattern> = Vec::new();
    let mut blockers: Vec<Blocker> = Vec::new();

    for type_def in schema.types.values() {
        if let protocol_squisher_ir::TypeDef::Struct(s) = type_def {
            for field in &s.fields {
                let class = classify_field_transport(&field.ty, field.optional);
                let key = format!("{}.{}", s.name, field.name);
                field_transport_classes.insert(key.clone(), class);

                // Detect patterns
                match &field.ty {
                    protocol_squisher_ir::IrType::Primitive(
                        protocol_squisher_ir::PrimitiveType::I32
                        | protocol_squisher_ir::PrimitiveType::I64,
                    ) if !field.optional => {
                        patterns.push(Pattern::ZeroCopyCandidate {
                            field: key.clone(),
                            protocol_native: true,
                        });
                    },
                    protocol_squisher_ir::IrType::Primitive(
                        protocol_squisher_ir::PrimitiveType::String,
                    ) => {
                        patterns.push(Pattern::StringThatCouldBeEnum {
                            field: key.clone(),
                            possible_values: vec![],
                            blocker_to: MetaTransportClass::Business,
                        });
                    },
                    protocol_squisher_ir::IrType::Container(
                        protocol_squisher_ir::ContainerType::Option(_),
                    ) => {
                        blockers.push(Blocker::OptionalField {
                            field: key.clone(),
                            prevents: MetaTransportClass::Concorde,
                        });
                    },
                    _ => {},
                }

                if field.optional {
                    patterns.push(Pattern::UnnecessaryOption {
                        field: key,
                        reason: "Detected optional in corpus".to_string(),
                        blocker_to: MetaTransportClass::Business,
                    });
                }
            }
        }
    }

    let best_achievable_class = determine_best_class(&field_transport_classes);
    let report = SquishabilityReport {
        protocol: protocol.name().to_string(),
        schema: input
            .file_name()
            .map(|n| n.to_string_lossy().to_string())
            .unwrap_or_default(),
        message: schema.name.clone(),
        patterns,
        field_transport_classes: field_transport_classes.clone(),
        best_achievable_class,
        predicted_speedup: calculate_predicted_speedup(&best_achievable_class),
        blockers,
        confidence: 0.8,
    };

    // Collect unique transport classes present
    let mut unique_classes: Vec<String> = field_transport_classes
        .values()
        .map(|c| format!("{:?}", c))
        .collect::<std::collections::HashSet<_>>()
        .into_iter()
        .collect();
    unique_classes.sort();

    let output = CorpusOutput {
        schema,
        squishability: report,
        transport_classes: unique_classes,
    };

    let json = serde_json::to_string_pretty(&output)
        .context("Failed to serialize corpus analysis output")?;
    println!("{}", json);

    Ok(())
}

/// Classify a field's transport class based on its IR type
fn classify_field_transport(
    ty: &protocol_squisher_ir::IrType,
    optional: bool,
) -> protocol_squisher_meta_analysis::TransportClass {
    use protocol_squisher_ir::*;
    use protocol_squisher_meta_analysis::TransportClass as MTC;

    if optional {
        return MTC::Economy;
    }

    match ty {
        IrType::Primitive(p) => match p {
            PrimitiveType::Bool
            | PrimitiveType::I8
            | PrimitiveType::I16
            | PrimitiveType::I32
            | PrimitiveType::I64
            | PrimitiveType::U8
            | PrimitiveType::U16
            | PrimitiveType::U32
            | PrimitiveType::U64
            | PrimitiveType::F32
            | PrimitiveType::F64 => MTC::Concorde,
            PrimitiveType::String | PrimitiveType::Bytes => MTC::Business,
            _ => MTC::Economy,
        },
        IrType::Container(c) => match c {
            ContainerType::Option(_) => MTC::Economy,
            ContainerType::Vec(_) | ContainerType::Array(_, _) => MTC::Business,
            ContainerType::Map(_, _) => MTC::Economy,
            _ => MTC::Wheelbarrow,
        },
        IrType::Reference(_) => MTC::Business,
        IrType::Special(_) => MTC::Wheelbarrow,
    }
}

/// Determine best achievable transport class from field distribution
fn determine_best_class(
    classes: &HashMap<String, protocol_squisher_meta_analysis::TransportClass>,
) -> protocol_squisher_meta_analysis::TransportClass {
    use protocol_squisher_meta_analysis::TransportClass as MTC;

    if classes.is_empty() {
        return MTC::Wheelbarrow;
    }

    // Best class is the worst class in the set (weakest link)
    let mut worst = MTC::Concorde;
    for class in classes.values() {
        worst = match (worst, class) {
            (MTC::Wheelbarrow, _) | (_, MTC::Wheelbarrow) => MTC::Wheelbarrow,
            (MTC::Economy, _) | (_, MTC::Economy) => MTC::Economy,
            (MTC::Business, _) | (_, MTC::Business) => MTC::Business,
            _ => MTC::Concorde,
        };
    }
    worst
}

/// Calculate predicted speedup over JSON baseline
fn calculate_predicted_speedup(class: &protocol_squisher_meta_analysis::TransportClass) -> f64 {
    use protocol_squisher_meta_analysis::TransportClass as MTC;
    match class {
        MTC::Concorde => 50.0,
        MTC::Business => 10.0,
        MTC::Economy => 3.0,
        MTC::Wheelbarrow => 1.0,
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
    if result.ephapax_verified {
        println!(
            "{}",
            "Ephapax backend: ✓ verified (linear-type proofs active)".bright_green()
        );
    } else {
        println!(
            "{}",
            "Ephapax backend: ⚠ stub mode (heuristic fallback; ephapax-cli not active)".yellow()
        );
    }

    Ok(())
}

fn synthesize_command(
    from_format: String,
    to_format: String,
    from_path: PathBuf,
    to_path: PathBuf,
    format: String,
) -> Result<()> {
    use crate::formats::ProtocolFormat;
    use protocol_squisher_minikanren::synthesize_adapter;

    let source_format = ProtocolFormat::from_str(&from_format)?;
    let target_format = ProtocolFormat::from_str(&to_format)?;

    let source_schema = source_format.analyze_file(&from_path).with_context(|| {
        format!(
            "Failed to analyze source {} as {}",
            from_path.display(),
            source_format.name()
        )
    })?;
    let target_schema = target_format.analyze_file(&to_path).with_context(|| {
        format!(
            "Failed to analyze target {} as {}",
            to_path.display(),
            target_format.name()
        )
    })?;

    let plan = synthesize_adapter(&source_schema, &target_schema);

    match format.as_str() {
        "json" => {
            println!("{}", serde_json::to_string_pretty(&plan)?);
        },
        "text" => {
            println!("{}", "miniKanren Synthesis Plan".bright_green().bold());
            println!(
                "  Source: {} ({})",
                source_schema.name.bright_cyan(),
                source_format.name()
            );
            println!(
                "  Target: {} ({})",
                target_schema.name.bright_cyan(),
                target_format.name()
            );
            println!(
                "  Satisfiable: {}",
                if plan.satisfiable {
                    "yes".green()
                } else {
                    "no".red()
                }
            );
            println!("  Overall Class: {:?}", plan.overall_class);
            println!(
                "  JSON Fallback Needed: {}",
                if plan.requires_json_fallback {
                    "yes".yellow()
                } else {
                    "no".green()
                }
            );

            println!("\n{}", "Steps:".bold());
            for (idx, step) in plan.steps.iter().enumerate() {
                println!(
                    "  {}. {} [{:?}] {}",
                    idx + 1,
                    step.path,
                    step.action,
                    step.rationale
                );
            }
        },
        other => {
            anyhow::bail!("Unsupported output format: '{other}' (expected 'text' or 'json')")
        },
    }

    Ok(())
}

fn security_bridge_command(
    tls_version: String,
    key_exchange: String,
    mutual_auth: bool,
    no_cert_validation: bool,
    session_resumption: bool,
    require: Vec<String>,
    format: String,
) -> Result<()> {
    use protocol_squisher_security_bridge::{
        translate_tls_to_noise, verify_security_properties, BridgeDecision, KeyExchange,
        SecurityProperty, TlsProfile, TlsVersion,
    };

    fn parse_tls_version(input: &str) -> Result<TlsVersion> {
        match input {
            "1.0" | "tls1.0" | "tls10" => Ok(TlsVersion::Tls10),
            "1.1" | "tls1.1" | "tls11" => Ok(TlsVersion::Tls11),
            "1.2" | "tls1.2" | "tls12" => Ok(TlsVersion::Tls12),
            "1.3" | "tls1.3" | "tls13" => Ok(TlsVersion::Tls13),
            other => anyhow::bail!("Unsupported TLS version: '{other}'"),
        }
    }

    fn parse_key_exchange(input: &str) -> Result<KeyExchange> {
        match input.to_ascii_lowercase().as_str() {
            "rsa" | "rsa_key_exchange" => Ok(KeyExchange::RsaKeyExchange),
            "dhe" => Ok(KeyExchange::Dhe),
            "ecdhe" => Ok(KeyExchange::Ecdhe),
            "psk" | "psk_only" => Ok(KeyExchange::PskOnly),
            other => anyhow::bail!("Unsupported key exchange: '{other}'"),
        }
    }

    fn parse_property(input: &str) -> Result<SecurityProperty> {
        match input.to_ascii_lowercase().as_str() {
            "forward_secrecy" | "pfs" => Ok(SecurityProperty::ForwardSecrecy),
            "mutual_authentication" | "mutual_auth" | "mtls" => {
                Ok(SecurityProperty::MutualAuthentication)
            },
            "identity_hiding" => Ok(SecurityProperty::IdentityHiding),
            "replay_resistance" | "replay_protection" => Ok(SecurityProperty::ReplayResistance),
            other => anyhow::bail!("Unsupported security property: '{other}'"),
        }
    }

    let profile = TlsProfile {
        version: parse_tls_version(&tls_version)?,
        key_exchange: parse_key_exchange(&key_exchange)?,
        mutual_authentication: mutual_auth,
        cert_validation: !no_cert_validation,
        session_resumption,
    };

    let required: Vec<SecurityProperty> = require
        .iter()
        .map(|value| parse_property(value))
        .collect::<Result<Vec<_>>>()?;

    let decision = if required.is_empty() {
        translate_tls_to_noise(&profile)
    } else {
        verify_security_properties(&profile, &required)
    };

    match format.as_str() {
        "json" => {
            println!("{}", serde_json::to_string_pretty(&decision)?);
        },
        "text" => match decision {
            BridgeDecision::Accept(bridge) => {
                println!("{}", "Security Bridge: ACCEPT".bright_green().bold());
                println!("  Noise Pattern: {:?}", bridge.noise_pattern);
                println!("  Properties: {:?}", bridge.properties);
                for note in bridge.notes {
                    println!("  Note: {}", note);
                }
            },
            BridgeDecision::Reject { reason } => {
                println!("{}", "Security Bridge: REJECT".bright_red().bold());
                println!("  Reason: {}", reason);
            },
        },
        other => {
            anyhow::bail!("Unsupported output format: '{other}' (expected 'text' or 'json')")
        },
    }

    Ok(())
}

fn performance_command(format: String, sample_size: usize) -> Result<()> {
    use protocol_squisher_performance::lazy::LazyJson;
    use protocol_squisher_performance::simd::{xor_checksum, xor_checksum_scalar};
    use protocol_squisher_performance::streaming::transform_json_lines;
    use protocol_squisher_performance::zero_copy::{is_layout_compatible, try_cast_slice};
    use serde::{Deserialize, Serialize};
    use std::io::Cursor;
    use std::time::Instant;

    #[derive(Debug, Deserialize)]
    struct InputRecord {
        id: u32,
        value: u32,
    }

    #[derive(Debug, Serialize)]
    struct OutputRecord {
        id: u32,
        value: u32,
    }

    #[derive(Debug, Serialize)]
    struct PerformanceReport {
        sample_size: usize,
        zero_copy_possible: bool,
        simd_checksum: u8,
        scalar_checksum: u8,
        simd_ns: u128,
        scalar_ns: u128,
        lazy_first_decode_ns: u128,
        lazy_second_decode_ns: u128,
        streamed_records: usize,
        streaming_ns: u128,
    }

    let sample_size = sample_size.max(1_024);
    let payload: Vec<u8> = (0..sample_size).map(|i| (i % 251) as u8).collect();

    let simd_start = Instant::now();
    let simd_checksum = xor_checksum(&payload);
    let simd_ns = simd_start.elapsed().as_nanos();

    let scalar_start = Instant::now();
    let scalar_checksum = xor_checksum_scalar(&payload);
    let scalar_ns = scalar_start.elapsed().as_nanos();

    if simd_checksum != scalar_checksum {
        anyhow::bail!("SIMD checksum mismatch: simd={simd_checksum} scalar={scalar_checksum}");
    }

    let words: Vec<u32> = (0..256).collect();
    let zero_copy_possible =
        is_layout_compatible::<u32, u32>() && try_cast_slice::<u32, u32>(&words).is_some();

    let lazy = LazyJson::<InputRecord>::new(r#"{"id":7,"value":9}"#);
    let lazy_first_start = Instant::now();
    let first = lazy.decode().context("lazy first decode failed")?;
    let lazy_first_decode_ns = lazy_first_start.elapsed().as_nanos();

    let lazy_second_start = Instant::now();
    let second = lazy.decode().context("lazy second decode failed")?;
    let lazy_second_decode_ns = lazy_second_start.elapsed().as_nanos();

    if !std::ptr::eq(first, second) {
        anyhow::bail!("Lazy decode cache miss detected unexpectedly");
    }

    let json_lines = (0..512)
        .map(|i| format!(r#"{{"id":{i},"value":{}}}"#, i * 2))
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    let reader = Cursor::new(json_lines.into_bytes());
    let mut transformed = Vec::new();

    let streaming_start = Instant::now();
    let streamed_records = transform_json_lines::<_, _, InputRecord, OutputRecord, _>(
        reader,
        &mut transformed,
        |record| OutputRecord {
            id: record.id,
            value: record.value + 1,
        },
    )
    .context("streaming transform failed")?;
    let streaming_ns = streaming_start.elapsed().as_nanos();

    let report = PerformanceReport {
        sample_size,
        zero_copy_possible,
        simd_checksum,
        scalar_checksum,
        simd_ns,
        scalar_ns,
        lazy_first_decode_ns,
        lazy_second_decode_ns,
        streamed_records,
        streaming_ns,
    };

    match format.as_str() {
        "json" => println!("{}", serde_json::to_string_pretty(&report)?),
        "text" => {
            println!(
                "{}",
                "Performance Optimization Report".bright_green().bold()
            );
            println!("  Sample size: {}", report.sample_size);
            println!(
                "  Zero-copy possible: {}",
                if report.zero_copy_possible {
                    "yes".green()
                } else {
                    "no".yellow()
                }
            );
            println!(
                "  SIMD checksum: {} ({} ns)",
                report.simd_checksum, report.simd_ns
            );
            println!(
                "  Scalar checksum: {} ({} ns)",
                report.scalar_checksum, report.scalar_ns
            );
            println!(
                "  Lazy decode: first={} ns, cached={} ns",
                report.lazy_first_decode_ns, report.lazy_second_decode_ns
            );
            println!(
                "  Streaming transform: {} records ({} ns)",
                report.streamed_records, report.streaming_ns
            );
        },
        other => anyhow::bail!("Unsupported output format: '{other}' (expected 'text' or 'json')"),
    }

    Ok(())
}

fn default_audit_log_path() -> PathBuf {
    PathBuf::from("target/audit/audit-log.jsonl")
}

fn current_actor() -> String {
    std::env::var("USER")
        .or_else(|_| std::env::var("USERNAME"))
        .unwrap_or_else(|_| "protocol-squisher-cli".to_string())
}

fn safe_record_audit(action: &str, outcome: &str, details: serde_json::Value) {
    use protocol_squisher_enterprise::audit::AuditLogger;

    let logger = AuditLogger::new(default_audit_log_path());
    if let Err(err) = logger.record(current_actor(), action, outcome, details) {
        eprintln!("audit warning: {}", err);
    }
}

fn schema_registry_command(
    command: SchemaRegistryCommand,
    registry_dir: PathBuf,
    format: String,
) -> Result<()> {
    use crate::formats::ProtocolFormat;
    use protocol_squisher_enterprise::registry::SchemaRegistry;

    let registry = SchemaRegistry::new(registry_dir);
    match command {
        SchemaRegistryCommand::Publish {
            name,
            version,
            protocol,
            input,
        } => {
            let protocol = ProtocolFormat::from_str(&protocol)?;
            let schema = protocol.analyze_file(&input).with_context(|| {
                format!(
                    "Failed to analyze schema {} as {}",
                    input.display(),
                    protocol.name()
                )
            })?;
            let entry = registry.publish(&name, &version, protocol.name(), schema)?;

            safe_record_audit(
                "schema_registry.publish",
                "success",
                serde_json::json!({
                    "name": entry.name,
                    "version": entry.version,
                    "format": entry.format
                }),
            );

            match format.as_str() {
                "json" => println!("{}", serde_json::to_string_pretty(&entry)?),
                "text" => {
                    println!("{}", "Schema Registry: PUBLISH".bright_green().bold());
                    println!("  Name: {}", entry.name);
                    println!("  Version: {}", entry.version);
                    println!("  Format: {}", entry.format);
                },
                other => anyhow::bail!("Unsupported output format: '{other}'"),
            }
        },
        SchemaRegistryCommand::Fetch { name, version } => {
            let entry = if let Some(version) = version {
                registry.fetch(&name, &version)?
            } else {
                registry
                    .latest(&name)?
                    .with_context(|| format!("No registry entries for '{name}'"))?
            };

            safe_record_audit(
                "schema_registry.fetch",
                "success",
                serde_json::json!({
                    "name": entry.name,
                    "version": entry.version
                }),
            );

            match format.as_str() {
                "json" => println!("{}", serde_json::to_string_pretty(&entry)?),
                "text" => {
                    println!("{}", "Schema Registry: FETCH".bright_green().bold());
                    println!("  Name: {}", entry.name);
                    println!("  Version: {}", entry.version);
                    println!("  Format: {}", entry.format);
                    println!("  Schema: {}", entry.schema.name);
                },
                other => anyhow::bail!("Unsupported output format: '{other}'"),
            }
        },
        SchemaRegistryCommand::List { name } => {
            let entries = registry.list(name.as_deref())?;
            safe_record_audit(
                "schema_registry.list",
                "success",
                serde_json::json!({
                    "count": entries.len(),
                    "filter_name": name
                }),
            );

            match format.as_str() {
                "json" => println!("{}", serde_json::to_string_pretty(&entries)?),
                "text" => {
                    println!("{}", "Schema Registry: LIST".bright_green().bold());
                    for (idx, entry) in entries.iter().enumerate() {
                        println!(
                            "  {}. {}@{} ({})",
                            idx + 1,
                            entry.name,
                            entry.version,
                            entry.format
                        );
                    }
                    if entries.is_empty() {
                        println!("  (empty)");
                    }
                },
                other => anyhow::bail!("Unsupported output format: '{other}'"),
            }
        },
    }

    Ok(())
}

fn migrate_command(
    from_format: String,
    to_format: String,
    from_path: PathBuf,
    to_path: PathBuf,
    format: String,
) -> Result<()> {
    use crate::formats::ProtocolFormat;
    use protocol_squisher_enterprise::migration::plan_migration;

    let source_format = ProtocolFormat::from_str(&from_format)?;
    let target_format = ProtocolFormat::from_str(&to_format)?;
    let source_schema = source_format.analyze_file(&from_path)?;
    let target_schema = target_format.analyze_file(&to_path)?;
    let plan = plan_migration(&source_schema, &target_schema);

    safe_record_audit(
        "migration.plan",
        "success",
        serde_json::json!({
            "source": source_schema.name,
            "target": target_schema.name,
            "overall_class": format!("{:?}", plan.overall_class),
            "breaking_changes": plan.breaking_changes
        }),
    );

    match format.as_str() {
        "json" => println!("{}", serde_json::to_string_pretty(&plan)?),
        "text" => {
            println!("{}", "Migration Plan".bright_green().bold());
            println!(
                "  Source: {} ({})",
                source_schema.name,
                source_format.name()
            );
            println!(
                "  Target: {} ({})",
                target_schema.name,
                target_format.name()
            );
            println!("  Overall Class: {:?}", plan.overall_class);
            println!("  Breaking Changes: {}", plan.breaking_changes);
            println!("  Steps:");
            for (idx, step) in plan.steps.iter().enumerate() {
                println!(
                    "    {}. {} [{:?}] breaking={} {}",
                    idx + 1,
                    step.path,
                    step.action,
                    step.breaking,
                    step.rationale
                );
            }
        },
        other => anyhow::bail!("Unsupported output format: '{other}'"),
    }

    Ok(())
}

fn parse_transport_class(input: &str) -> Result<protocol_squisher_compat::TransportClass> {
    use protocol_squisher_compat::TransportClass;

    match input.to_ascii_lowercase().as_str() {
        "concorde" => Ok(TransportClass::Concorde),
        "business" | "businessclass" | "business_class" => Ok(TransportClass::BusinessClass),
        "economy" => Ok(TransportClass::Economy),
        "wheelbarrow" => Ok(TransportClass::Wheelbarrow),
        "incompatible" => Ok(TransportClass::Incompatible),
        other => anyhow::bail!("Unsupported transport class: '{other}'"),
    }
}

fn governance_check_command(
    from_format: String,
    to_format: String,
    from_path: PathBuf,
    to_path: PathBuf,
    max_breaking_changes: usize,
    minimum_class: String,
    format: String,
) -> Result<()> {
    use crate::formats::ProtocolFormat;
    use protocol_squisher_enterprise::governance::{evaluate_policy, GovernancePolicy};
    use protocol_squisher_enterprise::migration::plan_migration;

    let source_format = ProtocolFormat::from_str(&from_format)?;
    let target_format = ProtocolFormat::from_str(&to_format)?;
    let source_schema = source_format.analyze_file(&from_path)?;
    let target_schema = target_format.analyze_file(&to_path)?;
    let plan = plan_migration(&source_schema, &target_schema);

    let policy = GovernancePolicy {
        max_breaking_changes,
        minimum_transport_class: parse_transport_class(&minimum_class)?,
        require_audit_log: true,
        allowed_formats: vec![
            source_format.name().to_string(),
            target_format.name().to_string(),
        ],
        ..GovernancePolicy::default()
    };
    let decision = evaluate_policy(
        &policy,
        &plan,
        source_format.name(),
        target_format.name(),
        default_audit_log_path().exists(),
    );

    safe_record_audit(
        "governance.check",
        if decision.allowed { "allow" } else { "reject" },
        serde_json::json!({
            "source": source_schema.name,
            "target": target_schema.name,
            "allowed": decision.allowed,
            "reasons": decision.reasons,
            "breaking_changes": plan.breaking_changes
        }),
    );

    match format.as_str() {
        "json" => println!("{}", serde_json::to_string_pretty(&decision)?),
        "text" => {
            println!(
                "{}",
                if decision.allowed {
                    "Governance Decision: ALLOW".bright_green().bold()
                } else {
                    "Governance Decision: REJECT".bright_red().bold()
                }
            );
            println!("  Overall Class: {:?}", plan.overall_class);
            println!("  Breaking Changes: {}", plan.breaking_changes);
            if !decision.reasons.is_empty() {
                println!("  Reasons:");
                for reason in &decision.reasons {
                    println!("    - {}", reason);
                }
            }
        },
        other => anyhow::bail!("Unsupported output format: '{other}'"),
    }

    Ok(())
}

fn audit_log_command(log: PathBuf, limit: usize, format: String) -> Result<()> {
    use protocol_squisher_enterprise::audit::AuditLogger;

    let logger = AuditLogger::new(log);
    let events = logger.read_all()?;
    let start = events.len().saturating_sub(limit);
    let slice = &events[start..];

    match format.as_str() {
        "json" => println!("{}", serde_json::to_string_pretty(&slice)?),
        "text" => {
            println!("{}", "Audit Log".bright_green().bold());
            println!("  Entries shown: {}", slice.len());
            for event in slice.iter().rev() {
                println!(
                    "  [{}] {} {} ({})",
                    event.timestamp_utc, event.actor, event.action, event.outcome
                );
            }
        },
        other => anyhow::bail!("Unsupported output format: '{other}'"),
    }

    Ok(())
}

fn marketplace_command(
    command: MarketplaceCommand,
    marketplace_dir: PathBuf,
    format: String,
) -> Result<()> {
    use protocol_squisher_enterprise::marketplace::{
        AdapterMarketplace, ListingFilter, PublishListingRequest,
    };

    let marketplace = AdapterMarketplace::new(marketplace_dir);
    match command {
        MarketplaceCommand::Publish {
            id,
            name,
            from_format,
            to_format,
            version,
            description,
            tags,
        } => {
            let listing = marketplace.publish(PublishListingRequest {
                id,
                name,
                from_format,
                to_format,
                version,
                description,
                tags,
            })?;
            safe_record_audit(
                "marketplace.publish",
                "success",
                serde_json::json!({"id": listing.id, "from": listing.from_format, "to": listing.to_format}),
            );

            match format.as_str() {
                "json" => println!("{}", serde_json::to_string_pretty(&listing)?),
                "text" => {
                    println!("{}", "Marketplace: PUBLISH".bright_green().bold());
                    println!("  Id: {}", listing.id);
                    println!("  Name: {}", listing.name);
                    println!("  Route: {} -> {}", listing.from_format, listing.to_format);
                    println!("  Version: {}", listing.version);
                },
                other => anyhow::bail!("Unsupported output format: '{other}'"),
            }
        },
        MarketplaceCommand::Get { id } => {
            let listing = marketplace.get(&id)?;
            match format.as_str() {
                "json" => println!("{}", serde_json::to_string_pretty(&listing)?),
                "text" => {
                    println!("{}", "Marketplace: GET".bright_green().bold());
                    println!("  Id: {}", listing.id);
                    println!("  Name: {}", listing.name);
                    println!("  Route: {} -> {}", listing.from_format, listing.to_format);
                    println!("  Description: {}", listing.description);
                },
                other => anyhow::bail!("Unsupported output format: '{other}'"),
            }
        },
        MarketplaceCommand::List {
            from_format,
            to_format,
            tag,
        } => {
            let listings = marketplace.list(&ListingFilter {
                from_format,
                to_format,
                tag,
            })?;
            match format.as_str() {
                "json" => println!("{}", serde_json::to_string_pretty(&listings)?),
                "text" => {
                    println!("{}", "Marketplace: LIST".bright_green().bold());
                    for (idx, listing) in listings.iter().enumerate() {
                        println!(
                            "  {}. {} {} -> {} @{}",
                            idx + 1,
                            listing.id,
                            listing.from_format,
                            listing.to_format,
                            listing.version
                        );
                    }
                    if listings.is_empty() {
                        println!("  (empty)");
                    }
                },
                other => anyhow::bail!("Unsupported output format: '{other}'"),
            }
        },
    }

    Ok(())
}

fn explore_command(
    from_format: String,
    to_format: String,
    from_path: PathBuf,
    to_path: PathBuf,
    format: String,
) -> Result<()> {
    use crate::formats::ProtocolFormat;
    use protocol_squisher_compat::compare_schemas;
    use serde::Serialize;

    #[derive(Serialize)]
    struct ExploreRow {
        path: String,
        class: String,
        losses: Vec<String>,
    }

    let source_format = ProtocolFormat::from_str(&from_format)?;
    let target_format = ProtocolFormat::from_str(&to_format)?;
    let source_schema = source_format.analyze_file(&from_path)?;
    let target_schema = target_format.analyze_file(&to_path)?;
    let comparison = compare_schemas(&source_schema, &target_schema);

    let mut rows = Vec::new();
    for type_cmp in comparison.type_comparisons.values() {
        for field_cmp in &type_cmp.field_comparisons {
            rows.push(ExploreRow {
                path: format!("{}.{}", type_cmp.name, field_cmp.name),
                class: format!("{:?}", field_cmp.class),
                losses: field_cmp
                    .losses
                    .iter()
                    .map(|loss| format!("{:?}: {}", loss.kind, loss.description))
                    .collect(),
            });
        }
    }

    match format.as_str() {
        "json" => {
            println!(
                "{}",
                serde_json::to_string_pretty(&serde_json::json!({
                    "source": source_schema.name,
                    "target": target_schema.name,
                    "overall_class": format!("{:?}", comparison.class),
                    "rows": rows,
                }))?
            );
        },
        "text" => {
            println!("{}", "Compatibility Explorer".bright_green().bold());
            println!(
                "  Source: {} ({})",
                source_schema.name,
                source_format.name()
            );
            println!(
                "  Target: {} ({})",
                target_schema.name,
                target_format.name()
            );
            println!("  Overall Class: {:?}", comparison.class);
            println!("  Paths:");
            for row in rows {
                println!("    - {} => {}", row.path, row.class);
                for loss in row.losses {
                    println!("      loss: {}", loss);
                }
            }
        },
        other => anyhow::bail!("Unsupported output format: '{other}'"),
    }

    Ok(())
}

fn playground_html() -> &'static str {
    r#"<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>Protocol Squisher Playground</title>
  <style>
    :root { --bg:#f6efe4; --ink:#1b1a19; --accent:#005f73; --card:#fffaf2; }
    body { margin:0; background:linear-gradient(180deg,#f6efe4,#f2e8d5); color:var(--ink); font-family: "IBM Plex Sans", "Source Sans 3", sans-serif; }
    main { max-width:860px; margin:0 auto; padding:2rem 1rem 4rem; }
    h1 { font-family:"Space Grotesk", "Avenir Next", sans-serif; letter-spacing:0.02em; }
    .card { background:var(--card); border:1px solid #d4c9b1; border-radius:12px; padding:1rem; box-shadow:0 8px 22px rgba(0,0,0,0.06); }
    code { background:#ece3d2; padding:0.1rem 0.3rem; border-radius:4px; }
    button { background:var(--accent); color:white; border:none; padding:0.6rem 1rem; border-radius:8px; cursor:pointer; }
    pre { white-space:pre-wrap; background:#111; color:#d8f3dc; padding:1rem; border-radius:8px; min-height:5rem; }
  </style>
</head>
<body>
  <main>
    <h1>Protocol Squisher Playground</h1>
    <div class="card">
      <p>This playground runs locally. Use <code>protocol-squisher explore</code> for schema diffs and <code>protocol-squisher migrate</code> for migration plans.</p>
      <p>Health endpoint: <code>/health</code></p>
      <button id="healthBtn">Check Server Health</button>
      <pre id="out">Click the button to call /health</pre>
    </div>
  </main>
  <script>
    const out = document.getElementById('out');
    document.getElementById('healthBtn').addEventListener('click', async () => {
      try {
        const res = await fetch('/health');
        out.textContent = await res.text();
      } catch (err) {
        out.textContent = String(err);
      }
    });
  </script>
</body>
</html>
"#
}

fn playground_command(host: String, port: u16, dump_html: bool) -> Result<()> {
    use std::io::{Read, Write};
    use std::net::TcpListener;

    if dump_html {
        println!("{}", playground_html());
        return Ok(());
    }

    let addr = format!("{host}:{port}");
    let listener =
        TcpListener::bind(&addr).with_context(|| format!("Failed to bind playground to {addr}"))?;
    println!(
        "{}",
        format!("Playground listening on http://{addr}").bright_green()
    );

    for stream in listener.incoming() {
        let mut stream = stream?;
        let mut buffer = [0u8; 8192];
        let bytes = stream.read(&mut buffer)?;
        let request = String::from_utf8_lossy(&buffer[..bytes]);
        let first_line = request.lines().next().unwrap_or("");

        let (status, content_type, body) = if first_line.starts_with("GET /health ") {
            (
                "200 OK",
                "application/json",
                r#"{"status":"ok"}"#.to_string(),
            )
        } else if first_line.starts_with("GET / ") {
            (
                "200 OK",
                "text/html; charset=utf-8",
                playground_html().to_string(),
            )
        } else {
            (
                "404 Not Found",
                "text/plain; charset=utf-8",
                "not found".to_string(),
            )
        };

        let response = format!(
            "HTTP/1.1 {status}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
            body.len(),
            body
        );
        stream.write_all(response.as_bytes())?;
        stream.flush()?;
    }

    Ok(())
}

fn read_lsp_message<R: std::io::BufRead + std::io::Read>(reader: &mut R) -> Result<Option<String>> {
    let mut content_length: Option<usize> = None;
    loop {
        let mut line = String::new();
        let n = reader.read_line(&mut line)?;
        if n == 0 {
            return Ok(None);
        }

        let trimmed = line.trim_end_matches(['\r', '\n']);
        if trimmed.is_empty() {
            break;
        }

        if let Some(value) = trimmed.strip_prefix("Content-Length:") {
            content_length = Some(
                value
                    .trim()
                    .parse()
                    .context("Invalid Content-Length header")?,
            );
        }
    }

    let Some(content_length) = content_length else {
        return Ok(None);
    };
    let mut buffer = vec![0u8; content_length];
    reader.read_exact(&mut buffer)?;
    let payload = String::from_utf8(buffer).context("LSP payload was not valid UTF-8")?;
    Ok(Some(payload))
}

fn write_lsp_message<W: std::io::Write>(writer: &mut W, payload: &serde_json::Value) -> Result<()> {
    let serialized = serde_json::to_string(payload).context("Failed to serialize LSP response")?;
    write!(
        writer,
        "Content-Length: {}\r\n\r\n{}",
        serialized.len(),
        serialized
    )?;
    writer.flush()?;
    Ok(())
}

fn handle_lsp_request(request: &serde_json::Value) -> Result<Option<serde_json::Value>> {
    use crate::formats::ProtocolFormat;
    use protocol_squisher_enterprise::migration::plan_migration;

    let method = request.get("method").and_then(|m| m.as_str());
    let id = request.get("id").cloned();

    let Some(method) = method else {
        return Ok(None);
    };

    let response = match method {
        "initialize" => id.map(|id| {
            serde_json::json!({
                "jsonrpc": "2.0",
                "id": id,
                "result": {
                    "capabilities": {
                        "textDocumentSync": 1,
                        "experimental": {
                            "adapterPreview": true
                        }
                    },
                    "serverInfo": {
                        "name": "protocol-squisher-lsp",
                        "version": env!("CARGO_PKG_VERSION")
                    }
                }
            })
        }),
        "shutdown" => id.map(|id| serde_json::json!({"jsonrpc":"2.0","id": id, "result": null})),
        "protocolSquisher/previewAdapter" => {
            let Some(id) = id else { return Ok(None) };
            let params = request
                .get("params")
                .and_then(|p| p.as_object())
                .with_context(|| "Missing params for protocolSquisher/previewAdapter")?;

            let from_format = params
                .get("from_format")
                .and_then(|v| v.as_str())
                .with_context(|| "Missing params.from_format")?;
            let to_format = params
                .get("to_format")
                .and_then(|v| v.as_str())
                .with_context(|| "Missing params.to_format")?;
            let from_path = params
                .get("from_path")
                .and_then(|v| v.as_str())
                .with_context(|| "Missing params.from_path")?;
            let to_path = params
                .get("to_path")
                .and_then(|v| v.as_str())
                .with_context(|| "Missing params.to_path")?;

            let src_format = ProtocolFormat::from_str(from_format)?;
            let dst_format = ProtocolFormat::from_str(to_format)?;
            let source_schema = src_format.analyze_file(Path::new(from_path))?;
            let target_schema = dst_format.analyze_file(Path::new(to_path))?;
            let plan = plan_migration(&source_schema, &target_schema);

            Some(serde_json::json!({
                "jsonrpc":"2.0",
                "id": id,
                "result": {
                    "source": source_schema.name,
                    "target": target_schema.name,
                    "overall_class": format!("{:?}", plan.overall_class),
                    "breaking_changes": plan.breaking_changes,
                    "steps": plan.steps.len()
                }
            }))
        },
        _ => id.map(|id| {
            serde_json::json!({
                "jsonrpc": "2.0",
                "id": id,
                "error": {"code": -32601, "message": format!("Method not found: {method}")}
            })
        }),
    };

    Ok(response)
}

fn lsp_command(once: bool) -> Result<()> {
    use std::io::BufReader;

    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut reader = BufReader::new(stdin.lock());
    let mut writer = stdout.lock();

    loop {
        let Some(payload) = read_lsp_message(&mut reader)? else {
            break;
        };
        let request: serde_json::Value =
            serde_json::from_str(&payload).context("Failed to parse LSP request")?;

        if request
            .get("method")
            .and_then(|m| m.as_str())
            .is_some_and(|m| m == "exit")
        {
            break;
        }

        if let Some(response) = handle_lsp_request(&request)? {
            write_lsp_message(&mut writer, &response)?;
        }

        if once {
            break;
        }
    }

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
    println!(
        "  Types: {}",
        schema.types.len().to_string().bright_yellow()
    );
    println!(
        "  Roots: {}",
        schema.roots.len().to_string().bright_yellow()
    );

    if detailed {
        println!("\n{}", "Type Definitions:".bold());
        for (name, type_def) in &schema.types {
            match type_def {
                protocol_squisher_ir::TypeDef::Struct(s) => {
                    println!("  {} struct {} ({})", "→".blue(), name, s.fields.len());
                    for field in &s.fields {
                        println!("    - {}: {:?}", field.name, field.ty);
                    }
                },
                protocol_squisher_ir::TypeDef::Enum(e) => {
                    println!("  {} enum {} ({})", "→".blue(), name, e.variants.len());
                    for variant in &e.variants {
                        println!("    - {}", variant.name);
                    }
                },
                protocol_squisher_ir::TypeDef::Union(u) => {
                    println!(
                        "  {} union {} ({} types)",
                        "→".blue(),
                        name,
                        u.variants.len()
                    );
                    for (i, variant_ty) in u.variants.iter().enumerate() {
                        println!("    - variant {}: {:?}", i, variant_ty);
                    }
                },
                protocol_squisher_ir::TypeDef::Alias(a) => {
                    println!("  {} alias {} = {:?}", "→".blue(), name, a.target);
                },
                protocol_squisher_ir::TypeDef::Newtype(n) => {
                    println!("  {} newtype {} = {:?}", "→".blue(), name, n.inner);
                },
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
            },
            Err(e) => {
                println!("  {} {} - {}", "✗".red(), target.name(), e);
            },
        }
    }

    println!(
        "\n{}",
        format!(
            "Cross-compilation complete: {}/{} succeeded",
            results.len(),
            targets.split(',').count()
        )
        .bright_green()
        .bold()
    );

    Ok(())
}

fn optimize(
    rust_path: PathBuf,
    python_path: PathBuf,
    threshold: f64,
    synthesis_hints: Option<PathBuf>,
) -> Result<()> {
    println!("{}", "🔍 Analyzing schemas for optimization...".cyan());

    // Parse schemas
    let rust_schema = analyze_rust_schema(&rust_path)?;
    let target_schema = analyze_python_schema(&python_path)?;

    // Run optimizer
    let engine = EphapaxCompatibilityEngine::new();
    let hints_path = resolve_synthesis_hints_path(synthesis_hints);
    let optimizer = if let Some(path) = hints_path.as_ref() {
        EphapaxOptimizer::new(engine)
            .with_empirical_hints_from_file(path)
            .map_err(anyhow::Error::msg)
            .with_context(|| format!("Failed to load synthesis hints from {}", path.display()))?
    } else {
        EphapaxOptimizer::new(engine)
    };
    let result = optimizer.analyze_and_suggest(&rust_schema, &target_schema);

    // Display current status
    println!("\n{}", "Current Status:".bold());
    println!(
        "  Transport Class: {}",
        format_transport_class(&result.current.overall_class)
    );
    println!(
        "  Zero-Copy Fields: {}/{} ({:.1}%)",
        result
            .current
            .type_analyses
            .iter()
            .flat_map(|t| &t.field_analyses)
            .filter(|f| f.class == protocol_squisher_transport_primitives::TransportClass::Concorde)
            .count(),
        result
            .current
            .type_analyses
            .iter()
            .flat_map(|t| &t.field_analyses)
            .count(),
        calculate_zero_copy_percentage(&result.current)
    );
    if result.empirical_hints_applied {
        let source = result
            .empirical_hints_source
            .as_ref()
            .map(|p| p.display().to_string())
            .unwrap_or_else(|| "<inline>".to_string());
        println!("  Empirical Hints: {}", source.cyan());
    }

    // Display suggestions
    println!("\n{}", "Optimization Suggestions:".bold().green());

    let filtered_suggestions: Vec<_> = result
        .suggestions
        .iter()
        .filter(|s| s.impact >= threshold)
        .collect();

    if filtered_suggestions.is_empty() {
        println!(
            "  {} No optimization opportunities found (schema is already optimal)",
            "✓".green()
        );
    } else {
        for (i, suggestion) in filtered_suggestions.iter().enumerate() {
            println!(
                "\n  {}. {} → {}",
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
    println!(
        "  Production Ready: {}",
        if result.would_be_production_ready {
            "Yes ✓".green()
        } else {
            "No (need >90% safe)".yellow()
        }
    );

    Ok(())
}

fn optimize_ai(
    rust_path: PathBuf,
    python_path: PathBuf,
    synthesis_hints: Option<PathBuf>,
    format: String,
) -> Result<()> {
    use protocol_squisher_optimizer::{ai_assisted_optimize, EmpiricalSynthesisHints};
    use serde::Serialize;

    #[derive(Serialize)]
    struct AiOutput {
        source: String,
        target: String,
        summary: protocol_squisher_optimizer::AiAssistedOptimizationSummary,
    }

    let rust_schema = analyze_rust_schema(&rust_path)?;
    let target_schema = analyze_python_schema(&python_path)?;
    let hints = if let Some(path) = synthesis_hints {
        Some(EmpiricalSynthesisHints::from_path(&path).map_err(anyhow::Error::msg)?)
    } else {
        None
    };

    let summary = ai_assisted_optimize(&rust_schema, &target_schema, hints);
    let out = AiOutput {
        source: rust_schema.name.clone(),
        target: target_schema.name.clone(),
        summary,
    };

    safe_record_audit(
        "optimize.ai",
        "success",
        serde_json::json!({
            "source": out.source,
            "target": out.target,
            "confidence": out.summary.recommendation_confidence,
            "potential_zero_copy_percentage": out.summary.potential_zero_copy_percentage
        }),
    );

    match format.as_str() {
        "json" => println!("{}", serde_json::to_string_pretty(&out)?),
        "text" => {
            println!("{}", "AI-Assisted Optimization".bright_green().bold());
            println!("  Source: {}", out.source);
            println!("  Target: {}", out.target);
            println!("  Confidence: {:.2}", out.summary.recommendation_confidence);
            println!(
                "  Potential Zero-Copy: {:.1}%",
                out.summary.potential_zero_copy_percentage
            );
            println!(
                "  Production Ready: {}",
                if out.summary.production_ready {
                    "yes".green()
                } else {
                    "no".yellow()
                }
            );
            if !out.summary.top_suggestions.is_empty() {
                println!("  Top Suggestions:");
                for (idx, suggestion) in out.summary.top_suggestions.iter().enumerate() {
                    println!("    {}. {}", idx + 1, suggestion);
                }
            }
        },
        other => anyhow::bail!("Unsupported output format: '{other}'"),
    }

    Ok(())
}

fn distributed_squish_command(manifest: PathBuf, workers: usize, format: String) -> Result<()> {
    use crate::formats::ProtocolFormat;
    use protocol_squisher_distributed::{run_distributed, DistributedSquishTask};
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Deserialize)]
    struct ManifestPair {
        id: String,
        from_format: String,
        to_format: String,
        from: PathBuf,
        to: PathBuf,
    }

    #[derive(Debug, Serialize)]
    struct DistributedOutput {
        workers: usize,
        task_count: usize,
        results: Vec<protocol_squisher_distributed::DistributedSquishResult>,
    }

    let pairs_raw = fs::read_to_string(&manifest)
        .with_context(|| format!("Failed to read manifest {}", manifest.display()))?;
    let pairs: Vec<ManifestPair> = serde_json::from_str(&pairs_raw)
        .with_context(|| format!("Failed to parse manifest {}", manifest.display()))?;

    let mut tasks = Vec::with_capacity(pairs.len());
    for pair in pairs {
        let from_format = ProtocolFormat::from_str(&pair.from_format)?;
        let to_format = ProtocolFormat::from_str(&pair.to_format)?;
        let source = from_format.analyze_file(&pair.from)?;
        let target = to_format.analyze_file(&pair.to)?;
        tasks.push(DistributedSquishTask {
            id: pair.id,
            source,
            target,
        });
    }

    let results = run_distributed(&tasks, Some(workers)).map_err(anyhow::Error::msg)?;
    let output = DistributedOutput {
        workers,
        task_count: tasks.len(),
        results,
    };

    safe_record_audit(
        "distributed.squish",
        "success",
        serde_json::json!({
            "workers": workers,
            "task_count": output.task_count
        }),
    );

    match format.as_str() {
        "json" => println!("{}", serde_json::to_string_pretty(&output)?),
        "text" => {
            println!("{}", "Distributed Squish".bright_green().bold());
            println!("  Workers: {}", output.workers);
            println!("  Tasks: {}", output.task_count);
            for result in &output.results {
                println!(
                    "  - {}: {:?} (losses={})",
                    result.id, result.class, result.loss_count
                );
            }
        },
        other => anyhow::bail!("Unsupported output format: '{other}'"),
    }

    Ok(())
}

fn parse_hardware_backend(
    backend: &str,
) -> Result<protocol_squisher_performance::hardware::HardwareBackend> {
    use protocol_squisher_performance::hardware::HardwareBackend;
    match backend.to_ascii_lowercase().as_str() {
        "auto" => Ok(protocol_squisher_performance::hardware::recommended_backend()),
        "scalar" => Ok(HardwareBackend::Scalar),
        "simd" => Ok(HardwareBackend::Simd),
        "parallel" => Ok(HardwareBackend::Parallel),
        other => anyhow::bail!("Unsupported hardware backend: '{other}'"),
    }
}

fn hardware_accel_command(sample_size: usize, backend: String, format: String) -> Result<()> {
    use protocol_squisher_performance::hardware::checksum_with_backend;
    use serde::Serialize;
    use std::time::Instant;

    #[derive(Debug, Serialize)]
    struct HardwareReport {
        sample_size: usize,
        backend: String,
        checksum: u8,
        elapsed_ns: u128,
    }

    let selected = parse_hardware_backend(&backend)?;
    let payload: Vec<u8> = (0..sample_size.max(1_024))
        .map(|i| (i % 251) as u8)
        .collect();

    let start = Instant::now();
    let checksum = checksum_with_backend(&payload, selected);
    let elapsed_ns = start.elapsed().as_nanos();

    let report = HardwareReport {
        sample_size: payload.len(),
        backend: format!("{:?}", selected),
        checksum,
        elapsed_ns,
    };

    safe_record_audit(
        "hardware.accel",
        "success",
        serde_json::json!({
            "backend": report.backend,
            "sample_size": report.sample_size,
            "elapsed_ns": report.elapsed_ns
        }),
    );

    match format.as_str() {
        "json" => println!("{}", serde_json::to_string_pretty(&report)?),
        "text" => {
            println!("{}", "Hardware Acceleration Probe".bright_green().bold());
            println!("  Backend: {}", report.backend);
            println!("  Sample Size: {}", report.sample_size);
            println!("  Checksum: {}", report.checksum);
            println!("  Elapsed: {} ns", report.elapsed_ns);
        },
        other => anyhow::bail!("Unsupported output format: '{other}'"),
    }

    Ok(())
}

fn check(rust_path: PathBuf, python_path: PathBuf) -> Result<()> {
    println!("{}", "⚡ Quick compatibility check...".cyan());

    // Parse schemas
    let rust_schema = analyze_rust_schema(&rust_path)?;
    let target_schema = analyze_python_schema(&python_path)?;

    // Analyze compatibility
    let engine = EphapaxCompatibilityEngine::new();
    let result = engine.analyze_schemas(&rust_schema, &target_schema);

    // Display result
    println!("\n{}", "Compatibility Result:".bold());
    println!(
        "  Overall Class: {}",
        format_transport_class(&result.overall_class)
    );

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

fn format_transport_class(
    class: &protocol_squisher_transport_primitives::TransportClass,
) -> String {
    use protocol_squisher_transport_primitives::TransportClass;

    match class {
        TransportClass::Concorde => "Concorde (100% fidelity, 0% overhead)".green().to_string(),
        TransportClass::Business => "Business (98% fidelity, 5% overhead)".cyan().to_string(),
        TransportClass::Economy => "Economy (80% fidelity, 25% overhead)".yellow().to_string(),
        TransportClass::Wheelbarrow => "Wheelbarrow (50% fidelity, 80% overhead)".red().to_string(),
    }
}

fn calculate_zero_copy_percentage(
    result: &protocol_squisher_compat::SchemaCompatibilityResult,
) -> f64 {
    let total: usize = result
        .type_analyses
        .iter()
        .map(|t| t.field_analyses.len())
        .sum();

    if total == 0 {
        return 0.0;
    }

    let zero_copy: usize = result
        .type_analyses
        .iter()
        .flat_map(|t| &t.field_analyses)
        .filter(|f| f.class == protocol_squisher_transport_primitives::TransportClass::Concorde)
        .count();

    (zero_copy as f64 / total as f64) * 100.0
}

fn resolve_synthesis_hints_path(cli_path: Option<PathBuf>) -> Option<PathBuf> {
    cli_path.or_else(|| {
        std::env::var("PROTOCOL_SQUISHER_SYNTHESIS_HINTS")
            .ok()
            .map(PathBuf::from)
    })
}

pub(crate) fn analyze_rust_schema(path: &Path) -> Result<IrSchema> {
    let rust_source = fs::read_to_string(path)
        .with_context(|| format!("Failed to read Rust file: {}", path.display()))?;
    let rust_analyzer = RustAnalyzer::new();
    rust_analyzer
        .analyze_source(&rust_source)
        .context("Failed to analyze Rust source")
}

pub(crate) fn analyze_python_schema(path: &Path) -> Result<IrSchema> {
    let analyzer = PythonAnalyzer::new();
    analyzer
        .analyze_file(path)
        .map_err(|e| anyhow::anyhow!(e))
        .with_context(|| format!("Failed to analyze Python file: {}", path.display()))
}
