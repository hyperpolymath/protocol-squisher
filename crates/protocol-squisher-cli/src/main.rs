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

    for (_type_id, type_def) in &schema.types {
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
                    "  {}. {} [{}] {}",
                    idx + 1,
                    step.path,
                    format!("{:?}", step.action),
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
            println!("{}", "Performance Optimization Report".bright_green().bold());
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
