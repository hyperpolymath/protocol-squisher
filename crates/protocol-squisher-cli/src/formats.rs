// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Protocol format detection and analyzer factory

use anyhow::{anyhow, Result};
use protocol_squisher_ir::IrSchema;
use std::path::Path;
use strsim::jaro_winkler;

/// Supported protocol formats
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProtocolFormat {
    Rust,
    Python,
    Bebop,
    FlatBuffers,
    MessagePack,
    Avro,
    Thrift,
    CapnProto,
    ReScript,
    Protobuf,
    JsonSchema,
}

impl ProtocolFormat {
    /// Get all supported formats
    pub fn all() -> Vec<Self> {
        vec![
            Self::Rust,
            Self::Python,
            Self::Bebop,
            Self::FlatBuffers,
            Self::MessagePack,
            Self::Avro,
            Self::Thrift,
            Self::CapnProto,
            Self::ReScript,
            Self::Protobuf,
            Self::JsonSchema,
        ]
    }

    /// Get format name
    pub fn name(&self) -> &'static str {
        match self {
            Self::Rust => "rust",
            Self::Python => "python",
            Self::Bebop => "bebop",
            Self::FlatBuffers => "flatbuffers",
            Self::MessagePack => "messagepack",
            Self::Avro => "avro",
            Self::Thrift => "thrift",
            Self::CapnProto => "capnproto",
            Self::ReScript => "rescript",
            Self::Protobuf => "protobuf",
            Self::JsonSchema => "json-schema",
        }
    }

    /// Get file extensions for this format
    pub fn extensions(&self) -> &[&'static str] {
        match self {
            Self::Rust => &["rs"],
            Self::Python => &["py"],
            Self::Bebop => &["bop"],
            Self::FlatBuffers => &["fbs"],
            Self::MessagePack => &["msgpack"],
            Self::Avro => &["avsc", "avdl"],
            Self::Thrift => &["thrift"],
            Self::CapnProto => &["capnp"],
            Self::ReScript => &["res", "resi"],
            Self::Protobuf => &["proto"],
            Self::JsonSchema => &["json"],
        }
    }

    /// Parse format from string
    pub fn from_str(s: &str) -> Result<Self> {
        let s_lower = s.to_lowercase();
        match s_lower.as_str() {
            "rust" | "rs" => Ok(Self::Rust),
            "python" | "py" => Ok(Self::Python),
            "bebop" | "bop" => Ok(Self::Bebop),
            "flatbuffers" | "flatbuffer" | "fbs" => Ok(Self::FlatBuffers),
            "messagepack" | "msgpack" => Ok(Self::MessagePack),
            "avro" | "avsc" => Ok(Self::Avro),
            "thrift" => Ok(Self::Thrift),
            "capnproto" | "capnp" | "cap'n proto" => Ok(Self::CapnProto),
            "rescript" | "res" => Ok(Self::ReScript),
            "protobuf" | "proto" | "pb" => Ok(Self::Protobuf),
            "json-schema" | "jsonschema" | "json" => Ok(Self::JsonSchema),
            _ => {
                // Try to find similar format
                let similar = Self::find_similar(&s_lower);
                Err(anyhow!(
                    "Unknown protocol format: '{}'. {}",
                    s,
                    similar
                ))
            }
        }
    }

    /// Find similar format names for suggestions
    fn find_similar(input: &str) -> String {
        let mut suggestions: Vec<(f64, &str)> = Self::all()
            .iter()
            .map(|f| (jaro_winkler(input, f.name()), f.name()))
            .collect();

        suggestions.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());

        let best_matches: Vec<&str> = suggestions
            .iter()
            .filter(|(score, _)| *score > 0.7)
            .take(3)
            .map(|(_, name)| *name)
            .collect();

        if best_matches.is_empty() {
            format!("Supported formats: {}", Self::supported_formats())
        } else {
            format!(
                "Did you mean one of: {}?\nSupported formats: {}",
                best_matches.join(", "),
                Self::supported_formats()
            )
        }
    }

    /// Get comma-separated list of supported formats
    pub fn supported_formats() -> String {
        Self::all()
            .iter()
            .map(|f| f.name())
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// Detect format from file extension
    pub fn from_path(path: &Path) -> Result<Self> {
        let ext = path
            .extension()
            .and_then(|s| s.to_str())
            .ok_or_else(|| anyhow!("No file extension found for: {}", path.display()))?;

        for format in Self::all() {
            if format.extensions().contains(&ext) {
                return Ok(format);
            }
        }

        Err(anyhow!(
            "Unknown file extension: '{}'. Supported extensions: {}",
            ext,
            Self::all()
                .iter()
                .flat_map(|f| f.extensions())
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ))
    }

    /// Analyze a file with the appropriate analyzer
    pub fn analyze_file(&self, path: &Path) -> Result<IrSchema> {
        match self {
            Self::Rust => {
                let analyzer = protocol_squisher_rust_analyzer::RustAnalyzer::new();
                let source = std::fs::read_to_string(path)?;
                Ok(analyzer.analyze_source(&source)?)
            }
            Self::Python => {
                let analyzer = protocol_squisher_python_analyzer::PythonAnalyzer::new();
                let source = std::fs::read_to_string(path)?;
                Ok(analyzer.analyze_module(&source)?)
            }
            Self::Bebop => {
                let analyzer = protocol_squisher_bebop_analyzer::BebopAnalyzer::new();
                Ok(analyzer.analyze_file(path)?)
            }
            Self::FlatBuffers => {
                let analyzer = protocol_squisher_flatbuffers_analyzer::FlatBuffersAnalyzer::new();
                Ok(analyzer.analyze_file(path)?)
            }
            Self::MessagePack => {
                let analyzer =
                    protocol_squisher_messagepack_analyzer::MessagePackAnalyzer::new();
                Ok(analyzer.analyze_file(path)?)
            }
            Self::Avro => {
                let analyzer = protocol_squisher_avro_analyzer::AvroAnalyzer::new();
                Ok(analyzer.analyze_file(path)?)
            }
            Self::Thrift => {
                let analyzer = protocol_squisher_thrift_analyzer::ThriftAnalyzer::new();
                Ok(analyzer.analyze_file(path)?)
            }
            Self::CapnProto => {
                let analyzer = protocol_squisher_capnproto_analyzer::CapnProtoAnalyzer::new();
                Ok(analyzer.analyze_file(path)?)
            }
            Self::ReScript => {
                let analyzer = protocol_squisher_rescript_analyzer::ReScriptAnalyzer::new();
                Ok(analyzer.analyze_file(path)?)
            }
            Self::Protobuf => {
                let analyzer = protocol_squisher_protobuf_analyzer::ProtobufAnalyzer::new();
                Ok(analyzer.analyze_file(path)?)
            }
            Self::JsonSchema => {
                let analyzer = protocol_squisher_json_schema_analyzer::JsonSchemaAnalyzer::new();
                Ok(analyzer.analyze_file(path)?)
            }
        }
    }

    /// Analyze a string with the appropriate analyzer
    pub fn analyze_str(&self, content: &str, name: &str) -> Result<IrSchema> {
        match self {
            Self::Rust => {
                let analyzer = protocol_squisher_rust_analyzer::RustAnalyzer::new();
                Ok(analyzer.analyze_source(content)?)
            }
            Self::Python => {
                let analyzer = protocol_squisher_python_analyzer::PythonAnalyzer::new();
                Ok(analyzer.analyze_module(content)?)
            }
            Self::Bebop => {
                let analyzer = protocol_squisher_bebop_analyzer::BebopAnalyzer::new();
                Ok(analyzer.analyze_str(content, name)?)
            }
            Self::FlatBuffers => {
                let analyzer = protocol_squisher_flatbuffers_analyzer::FlatBuffersAnalyzer::new();
                Ok(analyzer.analyze_str(content, name)?)
            }
            Self::MessagePack => {
                let analyzer =
                    protocol_squisher_messagepack_analyzer::MessagePackAnalyzer::new();
                Ok(analyzer.analyze_str(content, name)?)
            }
            Self::Avro => {
                let analyzer = protocol_squisher_avro_analyzer::AvroAnalyzer::new();
                Ok(analyzer.analyze_str(content, name)?)
            }
            Self::Thrift => {
                let analyzer = protocol_squisher_thrift_analyzer::ThriftAnalyzer::new();
                Ok(analyzer.analyze_str(content, name)?)
            }
            Self::CapnProto => {
                let analyzer = protocol_squisher_capnproto_analyzer::CapnProtoAnalyzer::new();
                Ok(analyzer.analyze_str(content, name)?)
            }
            Self::ReScript => {
                let analyzer = protocol_squisher_rescript_analyzer::ReScriptAnalyzer::new();
                Ok(analyzer.analyze_str(content, name)?)
            }
            Self::Protobuf => {
                let analyzer = protocol_squisher_protobuf_analyzer::ProtobufAnalyzer::new();
                Ok(analyzer.analyze_str(content, name)?)
            }
            Self::JsonSchema => {
                let analyzer = protocol_squisher_json_schema_analyzer::JsonSchemaAnalyzer::new();
                Ok(analyzer.analyze_str(content, name)?)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_from_str() {
        assert_eq!(
            ProtocolFormat::from_str("rust").unwrap(),
            ProtocolFormat::Rust
        );
        assert_eq!(
            ProtocolFormat::from_str("bebop").unwrap(),
            ProtocolFormat::Bebop
        );
        assert_eq!(
            ProtocolFormat::from_str("protobuf").unwrap(),
            ProtocolFormat::Protobuf
        );
    }

    #[test]
    fn test_format_from_path() {
        assert_eq!(
            ProtocolFormat::from_path(Path::new("schema.proto")).unwrap(),
            ProtocolFormat::Protobuf
        );
        assert_eq!(
            ProtocolFormat::from_path(Path::new("schema.bop")).unwrap(),
            ProtocolFormat::Bebop
        );
    }

    #[test]
    fn test_similar_suggestions() {
        let err = ProtocolFormat::from_str("protobufs").unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("protobuf"));
    }
}
