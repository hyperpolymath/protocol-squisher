// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell

//! # Protocol Squisher — Universal Interoperability Engine.
//!
//! Protocol Squisher automates the synthesis of data adapters between
//! disparate serialization formats. It allows high-level languages
//! (Python, JS) to talk to low-level systems (Rust, Zig) without manual
//! FFI boilerplate.
//!
//! THE SQUISHER INVARIANT: "If it compiles, it carries."
//! This system guarantees that ANY two schemas can be bridged, even if the
//! transport is lossy or requires fallback to JSON.
//!
//! ## Quick Start
//!
//! ```rust,ignore
//! use protocol_squisher::prelude::*;
//!
//! // Analyze a Protobuf schema
//! let analyzer = protobuf_analyzer::ProtobufAnalyzer::new();
//! let schema = analyzer.analyze_str("syntax = \"proto3\"; ...", "user")?;
//!
//! // Compare two schemas
//! let compat = compat::CompatibilityAnalyzer::new();
//! let result = compat.compare(&schema_a, &schema_b);
//! println!("Transport class: {:?}", result.class);
//! ```
//!
//! ## Modules
//!
//! - [`ir`] — Intermediate Representation: Schema, Constraint, Field types, SchemaAnalyzer trait
//! - [`compat`] — Compatibility engine with transport class scoring
//! - [`meta_analysis`] — Squishability analysis across protocol families
//! - [`optimizer`] — Concorde-class adapter generation
//! - **13 Analyzers** — One per supported serialization format

// ─── Core ────────────────────────────────────────────────────────────────────

pub mod ir {
    //! Intermediate Representation (IR) for schema definitions.
    //!
    //! Re-exports the `SchemaAnalyzer` trait used by all 13 analyzers.
    pub use protocol_squisher_ir::*;
}

pub mod compat {
    //! Compatibility engine — transport class scoring and loss documentation.
    pub use protocol_squisher_compat::*;
}

pub mod meta_analysis {
    //! Meta-analysis framework — squishability patterns across protocols.
    pub use protocol_squisher_meta_analysis::*;
}

pub mod optimizer {
    //! Optimization layer — Concorde-class adapter generation.
    pub use protocol_squisher_optimizer::*;
}

pub mod json_fallback {
    //! JSON fallback — guaranteed Wheelbarrow-class transport for any pair.
    pub use protocol_squisher_json_fallback::*;
}

pub mod pyo3_codegen {
    //! PyO3 code generation — automatic Rust-Python binding synthesis.
    pub use protocol_squisher_pyo3_codegen::*;
}

// ─── Analyzers ───────────────────────────────────────────────────────────────

pub mod rust_analyzer {
    //! Rust serde type analyzer.
    pub use protocol_squisher_rust_analyzer::*;
}

pub mod python_analyzer {
    //! Python Pydantic model analyzer.
    pub use protocol_squisher_python_analyzer::*;
}

pub mod json_schema_analyzer {
    //! JSON Schema analyzer (Draft 04-2020-12).
    pub use protocol_squisher_json_schema_analyzer::*;
}

pub mod protobuf_analyzer {
    //! Protocol Buffers (proto2/proto3) analyzer.
    pub use protocol_squisher_protobuf_analyzer::*;
}

pub mod avro_analyzer {
    //! Apache Avro schema analyzer.
    pub use protocol_squisher_avro_analyzer::*;
}

pub mod thrift_analyzer {
    //! Apache Thrift IDL analyzer.
    pub use protocol_squisher_thrift_analyzer::*;
}

pub mod bebop_analyzer {
    //! Bebop schema analyzer.
    pub use protocol_squisher_bebop_analyzer::*;
}

pub mod capnproto_analyzer {
    //! Cap'n Proto schema analyzer.
    pub use protocol_squisher_capnproto_analyzer::*;
}

pub mod flatbuffers_analyzer {
    //! FlatBuffers schema analyzer.
    pub use protocol_squisher_flatbuffers_analyzer::*;
}

pub mod messagepack_analyzer {
    //! MessagePack schema analyzer.
    pub use protocol_squisher_messagepack_analyzer::*;
}

pub mod rescript_analyzer {
    //! ReScript type definition analyzer.
    pub use protocol_squisher_rescript_analyzer::*;
}

pub mod graphql_analyzer {
    //! GraphQL SDL analyzer.
    pub use protocol_squisher_graphql_analyzer::*;
}

pub mod toml_analyzer {
    //! TOML structural type inference analyzer.
    pub use protocol_squisher_toml_analyzer::*;
}

// ─── Prelude ─────────────────────────────────────────────────────────────────

/// Convenience re-exports for common usage.
pub mod prelude {
    pub use crate::ir::{IrSchema, SchemaAnalyzer};
}

// ─── Analyzer Registry ───────────────────────────────────────────────────────

/// Returns a list of all available analyzers as trait objects.
///
/// Enables dynamic dispatch for PanLL integration and CLI auto-detection.
///
/// # Example
///
/// ```rust,ignore
/// use protocol_squisher::ir::SchemaAnalyzer;
///
/// for analyzer in protocol_squisher::all_analyzers() {
///     println!("{}: {:?}", analyzer.analyzer_name(), analyzer.supported_extensions());
/// }
/// ```
pub fn all_analyzers() -> Vec<Box<dyn ir::SchemaAnalyzer<Error = AnalyzerError>>> {
    // Return analyzers wrapped in error-erasing adapters
    vec![
        Box::new(ErasedAnalyzer(rust_analyzer::RustAnalyzer::new())),
        Box::new(ErasedAnalyzer(python_analyzer::PythonAnalyzer::new())),
        Box::new(ErasedAnalyzer(
            json_schema_analyzer::JsonSchemaAnalyzer::new(),
        )),
        Box::new(ErasedAnalyzer(protobuf_analyzer::ProtobufAnalyzer::new())),
        Box::new(ErasedAnalyzer(avro_analyzer::AvroAnalyzer::new())),
        Box::new(ErasedAnalyzer(thrift_analyzer::ThriftAnalyzer::new())),
        Box::new(ErasedAnalyzer(bebop_analyzer::BebopAnalyzer::new())),
        Box::new(ErasedAnalyzer(capnproto_analyzer::CapnProtoAnalyzer::new())),
        Box::new(ErasedAnalyzer(
            flatbuffers_analyzer::FlatBuffersAnalyzer::new(),
        )),
        Box::new(ErasedAnalyzer(
            messagepack_analyzer::MessagePackAnalyzer::new(),
        )),
        Box::new(ErasedAnalyzer(rescript_analyzer::ReScriptAnalyzer::new())),
        Box::new(ErasedAnalyzer(graphql_analyzer::GraphqlAnalyzer::new())),
        Box::new(ErasedAnalyzer(toml_analyzer::TomlAnalyzer::new())),
    ]
}

/// Error wrapper that implements `std::error::Error` for type-erased analyzer errors.
#[derive(Debug)]
pub struct AnalyzerError(Box<dyn std::error::Error + Send + Sync>);

impl std::fmt::Display for AnalyzerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::error::Error for AnalyzerError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.0.source()
    }
}

/// Wrapper that erases the concrete error type.
struct ErasedAnalyzer<A>(A);

impl<A> ir::SchemaAnalyzer for ErasedAnalyzer<A>
where
    A: ir::SchemaAnalyzer,
    A::Error: 'static,
{
    type Error = AnalyzerError;

    fn analyzer_name(&self) -> &str {
        self.0.analyzer_name()
    }

    fn supported_extensions(&self) -> &[&str] {
        self.0.supported_extensions()
    }

    fn analyze_file(&self, path: &std::path::Path) -> Result<ir::IrSchema, Self::Error> {
        self.0
            .analyze_file(path)
            .map_err(|e| AnalyzerError(Box::new(e)))
    }

    fn analyze_str(&self, content: &str, name: &str) -> Result<ir::IrSchema, Self::Error> {
        self.0
            .analyze_str(content, name)
            .map_err(|e| AnalyzerError(Box::new(e)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_analyzers_returns_13() {
        let analyzers = all_analyzers();
        assert_eq!(analyzers.len(), 13);
    }

    #[test]
    fn test_all_analyzer_names_unique() {
        let analyzers = all_analyzers();
        let names: Vec<&str> = analyzers.iter().map(|a| a.analyzer_name()).collect();
        let mut deduped = names.clone();
        deduped.sort();
        deduped.dedup();
        assert_eq!(names.len(), deduped.len(), "Duplicate analyzer names found");
    }

    #[test]
    fn test_prelude_imports() {
        use prelude::*;
        let _schema = IrSchema::new("test", "test");
        // SchemaAnalyzer trait is in scope
        fn _accepts_analyzer(_a: &dyn SchemaAnalyzer<Error = super::AnalyzerError>) {}
    }
}
