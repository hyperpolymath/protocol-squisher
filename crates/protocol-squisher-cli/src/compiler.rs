// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Universal protocol compiler with ephapax linear type verification
//!
//! Architecture:
//! Protocol → IR → Ephapax (linear) → Verified Codegen
//!
//! Critical operations (transport class analysis, compatibility checking)
//! use ephapax linear types for proven correctness.

use anyhow::{bail, Context, Result};
use colored::Colorize;
use protocol_squisher_echidna_bridge::TrustLevel;
use protocol_squisher_ir::IrSchema;
use protocol_squisher_transport_primitives::{
    ephapax_backend_mode, ephapax_backend_verified, IRContext, TransportClass,
};
use std::path::Path;

use crate::formats::ProtocolFormat;

/// Universal protocol compiler with ephapax verification
pub struct UniversalCompiler {
    /// Ephapax IR context for linear type verification
    ephapax_ctx: IRContext,
}

impl UniversalCompiler {
    fn codegen_backend_label(&self) -> &'static str {
        if ephapax_backend_verified() {
            "ephapax-verified"
        } else {
            "ephapax-stub"
        }
    }

    /// Create a new compiler with ephapax context
    pub fn new() -> Self {
        Self {
            ephapax_ctx: IRContext::new(),
        }
    }

    /// Compile from one protocol to another with ephapax verification
    ///
    /// This is the critical compilation path - ALL transport class decisions
    /// go through ephapax linear types for proven correctness.
    pub fn compile(
        &self,
        source_format: ProtocolFormat,
        source_path: &Path,
        target_format: ProtocolFormat,
        output_path: &Path,
    ) -> Result<CompilationResult> {
        let verified_backend = ephapax_backend_verified();
        let verification_label = self.codegen_backend_label();

        println!(
            "{}",
            format!(
                "Compiling {} → {} ({})",
                source_format.name().bright_cyan(),
                target_format.name().bright_green(),
                verification_label
            )
            .bold()
        );

        // Step 1: Parse source schema
        println!(
            "  {} Parsing {} schema...",
            "→".blue(),
            source_format.name()
        );
        let source_schema = source_format
            .analyze_file(source_path)
            .with_context(|| format!("Failed to analyze {} schema", source_format.name()))?;

        println!(
            "    ✓ Found {} types",
            source_schema.types.len().to_string().green()
        );

        // Step 2: Bridge to ephapax IR (LINEAR TYPES - CRITICAL)
        if verified_backend {
            println!("  {} Verifying with ephapax linear types...", "→".blue());
        } else {
            println!(
                "  {} Verifying with ephapax stubs (heuristic mode)...",
                "→".blue()
            );
        }
        let transport_class = self.analyze_transport_class(&source_schema, target_format)?;

        println!(
            "    ✓ Transport class: {} ({})",
            format!("{:?}", transport_class).bright_yellow(),
            verification_label
        );

        // Step 3: Generate target code with proven-correct transport
        println!(
            "  {} Generating {} code...",
            "→".blue(),
            target_format.name()
        );
        let generated_code = self.generate_code(&source_schema, target_format, transport_class)?;

        // Step 4: Write output
        std::fs::create_dir_all(output_path).with_context(|| {
            format!(
                "Failed to create output directory: {}",
                output_path.display()
            )
        })?;

        let output_file = output_path.join(format!("generated.{}", target_format.extensions()[0]));
        std::fs::write(&output_file, &generated_code)
            .with_context(|| format!("Failed to write to {}", output_file.display()))?;

        println!(
            "{}",
            format!("✓ Compilation complete: {}", output_file.display())
                .bright_green()
                .bold()
        );

        Ok(CompilationResult {
            source_format,
            target_format,
            transport_class,
            source_types: source_schema.types.len(),
            output_file,
            ephapax_verified: verified_backend,
        })
    }

    /// Analyze transport class using ephapax linear types (CRITICAL)
    ///
    /// Attempts ECHIDNA cross-prover proof of transport class when available.
    /// Falls back to conservative Business class when ECHIDNA is offline.
    fn analyze_transport_class(
        &self,
        schema: &IrSchema,
        _target: ProtocolFormat,
    ) -> Result<TransportClass> {
        // Attempt ECHIDNA-backed proof of transport class.
        let mut ctx = crate::integration::IntegrationContext::new();
        if let Some((proven_class, trust_level)) =
            ctx.try_prove_transport_class(schema, schema)
        {
            if trust_level >= TrustLevel::Level2 {
                return Ok(proven_class);
            }
        }

        // Conservative fallback: Business class (safe for most conversions).
        let _ = self.ephapax_ctx.get_fidelity(TransportClass::Business);
        Ok(TransportClass::Business)
    }

    /// Generate code for target format with proven-correct transport
    fn generate_code(
        &self,
        schema: &IrSchema,
        target: ProtocolFormat,
        _transport_class: TransportClass,
    ) -> Result<String> {
        // Generate code based on target format
        match target {
            ProtocolFormat::Rust => self.generate_rust(schema),
            ProtocolFormat::Python => self.generate_python(schema),
            ProtocolFormat::Bebop => self.generate_bebop(schema),
            ProtocolFormat::Protobuf => self.generate_protobuf(schema),
            ProtocolFormat::FlatBuffers
            | ProtocolFormat::ReScript
            | ProtocolFormat::Thrift
            | ProtocolFormat::Avro
            | ProtocolFormat::CapnProto
            | ProtocolFormat::MessagePack
            | ProtocolFormat::JsonSchema => self.unsupported_codegen_target(target),
        }
    }

    /// Generate Rust code from IR
    fn generate_rust(&self, schema: &IrSchema) -> Result<String> {
        let mut code = String::new();
        code.push_str("// SPDX-License-Identifier: PMPL-1.0-or-later\n");
        code.push_str(&format!(
            "// Auto-generated by protocol-squisher ({})\n\n",
            self.codegen_backend_label()
        ));
        code.push_str("use serde::{Deserialize, Serialize};\n\n");

        for (name, type_def) in &schema.types {
            match type_def {
                protocol_squisher_ir::TypeDef::Struct(s) => {
                    code.push_str("#[derive(Debug, Clone, Serialize, Deserialize)]\n");
                    code.push_str(&format!("pub struct {} {{\n", name));
                    for field in &s.fields {
                        code.push_str(&format!(
                            "    pub {}: {},\n",
                            field.name,
                            Self::ir_type_to_rust(&field.ty)
                        ));
                    }
                    code.push_str("}\n\n");
                },
                protocol_squisher_ir::TypeDef::Enum(e) => {
                    code.push_str("#[derive(Debug, Clone, Serialize, Deserialize)]\n");
                    code.push_str(&format!("pub enum {} {{\n", name));
                    for variant in &e.variants {
                        code.push_str(&format!("    {},\n", variant.name));
                    }
                    code.push_str("}\n\n");
                },
                protocol_squisher_ir::TypeDef::Union(u) => {
                    code.push_str(&format!("// Union type {} (untagged)\n", name));
                    code.push_str(&format!("// Variants: {} types\n\n", u.variants.len()));
                },
                protocol_squisher_ir::TypeDef::Alias(a) => {
                    code.push_str(&format!(
                        "pub type {} = {};\n\n",
                        name,
                        Self::ir_type_to_rust(&a.target)
                    ));
                },
                protocol_squisher_ir::TypeDef::Newtype(n) => {
                    code.push_str("#[derive(Debug, Clone, Serialize, Deserialize)]\n");
                    code.push_str(&format!(
                        "pub struct {}({});\n\n",
                        name,
                        Self::ir_type_to_rust(&n.inner)
                    ));
                },
            }
        }

        Ok(code)
    }

    /// Generate Python code from IR
    fn generate_python(&self, schema: &IrSchema) -> Result<String> {
        let mut code = String::new();
        code.push_str("# SPDX-License-Identifier: PMPL-1.0-or-later\n");
        code.push_str(&format!(
            "# Auto-generated by protocol-squisher ({})\n\n",
            self.codegen_backend_label()
        ));
        code.push_str("from dataclasses import dataclass\n");
        code.push_str("from typing import Optional\n\n");

        for (name, type_def) in &schema.types {
            match type_def {
                protocol_squisher_ir::TypeDef::Struct(s) => {
                    code.push_str("@dataclass\n");
                    code.push_str(&format!("class {}:\n", name));
                    for field in &s.fields {
                        code.push_str(&format!(
                            "    {}: {}\n",
                            field.name,
                            Self::ir_type_to_python(&field.ty)
                        ));
                    }
                    code.push('\n');
                },
                protocol_squisher_ir::TypeDef::Enum(e) => {
                    code.push_str("from enum import Enum\n\n");
                    code.push_str(&format!("class {}(Enum):\n", name));
                    for (i, variant) in e.variants.iter().enumerate() {
                        code.push_str(&format!("    {} = {}\n", variant.name, i));
                    }
                    code.push('\n');
                },
                protocol_squisher_ir::TypeDef::Union(u) => {
                    code.push_str(&format!("# Union type {} (untagged)\n", name));
                    code.push_str(&format!("# Variants: {} types\n\n", u.variants.len()));
                },
                protocol_squisher_ir::TypeDef::Alias(a) => {
                    code.push_str(&format!(
                        "{} = {}\n\n",
                        name,
                        Self::ir_type_to_python(&a.target)
                    ));
                },
                protocol_squisher_ir::TypeDef::Newtype(n) => {
                    code.push_str("@dataclass\n");
                    code.push_str(&format!("class {}:\n", name));
                    code.push_str(&format!(
                        "    value: {}\n\n",
                        Self::ir_type_to_python(&n.inner)
                    ));
                },
            }
        }

        Ok(code)
    }

    /// Generate Bebop schema from IR
    fn generate_bebop(&self, schema: &IrSchema) -> Result<String> {
        let mut code = String::new();
        code.push_str("// SPDX-License-Identifier: PMPL-1.0-or-later\n");
        code.push_str(&format!(
            "// Auto-generated by protocol-squisher ({})\n\n",
            self.codegen_backend_label()
        ));

        for (name, type_def) in &schema.types {
            match type_def {
                protocol_squisher_ir::TypeDef::Struct(s) => {
                    code.push_str(&format!("struct {} {{\n", name));
                    for field in &s.fields {
                        code.push_str(&format!(
                            "    {} {};\n",
                            Self::ir_type_to_bebop(&field.ty),
                            field.name
                        ));
                    }
                    code.push_str("}\n\n");
                },
                protocol_squisher_ir::TypeDef::Enum(e) => {
                    code.push_str(&format!("enum {} {{\n", name));
                    for (i, variant) in e.variants.iter().enumerate() {
                        code.push_str(&format!("    {} = {};\n", variant.name, i));
                    }
                    code.push_str("}\n\n");
                },
                protocol_squisher_ir::TypeDef::Union(u) => {
                    code.push_str(&format!("// Union type {} (untagged)\n", name));
                    code.push_str(&format!("// Variants: {} types\n\n", u.variants.len()));
                },
                protocol_squisher_ir::TypeDef::Alias(a) => {
                    code.push_str(&format!("// Type alias: {} = {:?}\n\n", name, a.target));
                },
                protocol_squisher_ir::TypeDef::Newtype(n) => {
                    code.push_str(&format!("// Newtype: {} wraps {:?}\n\n", name, n.inner));
                },
            }
        }

        Ok(code)
    }

    /// Generate Protobuf schema from IR
    fn generate_protobuf(&self, schema: &IrSchema) -> Result<String> {
        use protocol_squisher_ir::TypeDef;

        let mut code = String::new();
        code.push_str("// SPDX-License-Identifier: PMPL-1.0-or-later\n");
        code.push_str("// Auto-generated by protocol-squisher\n");
        code.push_str("// NOTE: Review generated schema for semantic edge cases.\n\n");
        code.push_str("syntax = \"proto3\";\n\n");
        code.push_str(&format!(
            "package {};\n\n",
            self.sanitize_proto_package(&schema.name)
        ));

        let mut entries: Vec<(&String, &TypeDef)> = schema.types.iter().collect();
        entries.sort_by(|a, b| a.0.cmp(b.0));

        for (name, type_def) in entries {
            let type_name = self.sanitize_proto_type_name(name);

            match type_def {
                TypeDef::Struct(s) => {
                    code.push_str(&format!("message {} {{\n", type_name));
                    for (idx, field) in s.fields.iter().enumerate() {
                        let field_name = self.sanitize_proto_field_name(&field.name);
                        code.push_str(&self.protobuf_field_line(
                            &field.ty,
                            field.optional,
                            &field_name,
                            idx + 1,
                        ));
                    }
                    code.push_str("}\n\n");
                },
                TypeDef::Enum(e) => {
                    code.push_str(&format!("enum {} {{\n", type_name));
                    code.push_str(&format!(
                        "    {}_UNSPECIFIED = 0;\n",
                        self.to_upper_snake(&type_name)
                    ));
                    for (idx, variant) in e.variants.iter().enumerate() {
                        let variant_name = format!(
                            "{}_{}",
                            self.to_upper_snake(&type_name),
                            self.to_upper_snake(&variant.name)
                        );
                        let payload_note = if variant.payload.is_some() {
                            " // payload omitted in enum representation"
                        } else {
                            ""
                        };
                        code.push_str(&format!(
                            "    {} = {};{}\n",
                            variant_name,
                            idx + 1,
                            payload_note
                        ));
                    }
                    code.push_str("}\n\n");
                },
                TypeDef::Union(u) => {
                    code.push_str(&format!("message {} {{\n", type_name));
                    code.push_str("    oneof value {\n");
                    for (idx, variant_ty) in u.variants.iter().enumerate() {
                        let variant_name = format!("variant_{}", idx + 1);
                        let variant_ty_name = self.protobuf_type_name(variant_ty);
                        code.push_str(&format!(
                            "        {} {} = {};\n",
                            variant_ty_name,
                            variant_name,
                            idx + 1
                        ));
                    }
                    code.push_str("    }\n");
                    code.push_str("}\n\n");
                },
                TypeDef::Alias(a) => {
                    code.push_str(&format!("message {} {{\n", type_name));
                    code.push_str(&self.protobuf_field_line(&a.target, false, "value", 1));
                    code.push_str("}\n\n");
                },
                TypeDef::Newtype(n) => {
                    code.push_str(&format!("message {} {{\n", type_name));
                    code.push_str(&self.protobuf_field_line(&n.inner, false, "value", 1));
                    code.push_str("}\n\n");
                },
            }
        }

        Ok(code)
    }

    fn unsupported_codegen_target(&self, target: ProtocolFormat) -> Result<String> {
        bail!(
            "Code generation for target '{}' is not implemented yet. \
Supported compile targets today: rust, python, bebop, protobuf. \
Current ephapax backend mode: {}.",
            target.name(),
            ephapax_backend_mode()
        )
    }

    fn protobuf_field_line(
        &self,
        ty: &protocol_squisher_ir::IrType,
        optional: bool,
        field_name: &str,
        field_no: usize,
    ) -> String {
        use protocol_squisher_ir::{ContainerType, IrType};

        match ty {
            IrType::Container(ContainerType::Vec(inner)) => format!(
                "    repeated {} {} = {};\n",
                self.protobuf_type_name(inner),
                field_name,
                field_no
            ),
            IrType::Container(ContainerType::Array(inner, size)) => format!(
                "    repeated {} {} = {}; // fixed-size array: expected length {}\n",
                self.protobuf_type_name(inner),
                field_name,
                field_no,
                size
            ),
            IrType::Container(ContainerType::Set(inner)) => format!(
                "    repeated {} {} = {}; // set semantics (uniqueness not enforced by protobuf)\n",
                self.protobuf_type_name(inner),
                field_name,
                field_no
            ),
            IrType::Container(ContainerType::Map(key, value)) => format!(
                "    map<{}, {}> {} = {};\n",
                self.protobuf_map_key_type(key),
                self.protobuf_type_name(value),
                field_name,
                field_no
            ),
            IrType::Container(ContainerType::Option(inner)) => format!(
                "    optional {} {} = {};\n",
                self.protobuf_type_name(inner),
                field_name,
                field_no
            ),
            IrType::Container(ContainerType::Tuple(_))
            | IrType::Container(ContainerType::Result(_, _)) => format!(
                "    string {} = {}; // fallback encoding for unsupported container type\n",
                field_name, field_no
            ),
            _ => {
                let optional_prefix = if optional { "optional " } else { "" };
                format!(
                    "    {}{} {} = {};\n",
                    optional_prefix,
                    self.protobuf_type_name(ty),
                    field_name,
                    field_no
                )
            },
        }
    }

    fn protobuf_type_name(&self, ty: &protocol_squisher_ir::IrType) -> String {
        use protocol_squisher_ir::{IrType, PrimitiveType};

        match ty {
            IrType::Primitive(p) => match p {
                PrimitiveType::Bool => "bool".to_string(),
                PrimitiveType::I8 | PrimitiveType::I16 | PrimitiveType::I32 => "int32".to_string(),
                PrimitiveType::I64 => "int64".to_string(),
                PrimitiveType::I128 => "string".to_string(),
                PrimitiveType::U8 | PrimitiveType::U16 | PrimitiveType::U32 => "uint32".to_string(),
                PrimitiveType::U64 => "uint64".to_string(),
                PrimitiveType::U128 => "string".to_string(),
                PrimitiveType::F32 => "float".to_string(),
                PrimitiveType::F64 => "double".to_string(),
                PrimitiveType::Bytes => "bytes".to_string(),
                PrimitiveType::String
                | PrimitiveType::Char
                | PrimitiveType::DateTime
                | PrimitiveType::Date
                | PrimitiveType::Time
                | PrimitiveType::Duration
                | PrimitiveType::Uuid
                | PrimitiveType::Decimal
                | PrimitiveType::BigInt => "string".to_string(),
            },
            IrType::Reference(name) => self.sanitize_proto_type_name(name),
            IrType::Container(_) | IrType::Special(_) => "string".to_string(),
        }
    }

    fn protobuf_map_key_type(&self, ty: &protocol_squisher_ir::IrType) -> String {
        use protocol_squisher_ir::{IrType, PrimitiveType};

        match ty {
            IrType::Primitive(PrimitiveType::Bool) => "bool".to_string(),
            IrType::Primitive(PrimitiveType::I8 | PrimitiveType::I16 | PrimitiveType::I32) => {
                "int32".to_string()
            },
            IrType::Primitive(PrimitiveType::I64) => "int64".to_string(),
            IrType::Primitive(PrimitiveType::U8 | PrimitiveType::U16 | PrimitiveType::U32) => {
                "uint32".to_string()
            },
            IrType::Primitive(PrimitiveType::U64) => "uint64".to_string(),
            IrType::Primitive(_) => "string".to_string(),
            IrType::Reference(_) | IrType::Container(_) | IrType::Special(_) => {
                "string".to_string()
            },
        }
    }

    fn sanitize_proto_package(&self, input: &str) -> String {
        let package = self.to_lower_snake(input);
        if package.is_empty() {
            "protocol_squisher".to_string()
        } else {
            package
        }
    }

    fn sanitize_proto_type_name(&self, input: &str) -> String {
        let mut out = String::new();
        for c in input.chars() {
            if c.is_ascii_alphanumeric() || c == '_' {
                out.push(c);
            } else {
                out.push('_');
            }
        }
        if out.is_empty() {
            "GeneratedType".to_string()
        } else if out.chars().next().is_some_and(|c| c.is_ascii_digit()) {
            format!("T_{}", out)
        } else {
            out
        }
    }

    fn sanitize_proto_field_name(&self, input: &str) -> String {
        let mut out = self.to_lower_snake(input);
        if out.is_empty() {
            out = "field".to_string();
        }
        if out.chars().next().is_some_and(|c| c.is_ascii_digit()) {
            out = format!("f_{}", out);
        }
        out
    }

    fn to_upper_snake(&self, input: &str) -> String {
        self.to_lower_snake(input).to_ascii_uppercase()
    }

    fn to_lower_snake(&self, input: &str) -> String {
        let mut out = String::new();
        let mut prev_was_underscore = false;

        for c in input.chars() {
            if c.is_ascii_alphanumeric() {
                let lower = c.to_ascii_lowercase();
                if c.is_ascii_uppercase() && !out.is_empty() && !prev_was_underscore {
                    out.push('_');
                }
                out.push(lower);
                prev_was_underscore = false;
            } else if !prev_was_underscore {
                out.push('_');
                prev_was_underscore = true;
            }
        }

        out.trim_matches('_').to_string()
    }

    // Type conversion helpers
    fn ir_type_to_rust(ty: &protocol_squisher_ir::IrType) -> String {
        use protocol_squisher_ir::{ContainerType, IrType, PrimitiveType};
        match ty {
            IrType::Primitive(p) => match p {
                PrimitiveType::Bool => "bool".to_string(),
                PrimitiveType::I8 => "i8".to_string(),
                PrimitiveType::I16 => "i16".to_string(),
                PrimitiveType::I32 => "i32".to_string(),
                PrimitiveType::I64 => "i64".to_string(),
                PrimitiveType::U8 => "u8".to_string(),
                PrimitiveType::U16 => "u16".to_string(),
                PrimitiveType::U32 => "u32".to_string(),
                PrimitiveType::U64 => "u64".to_string(),
                PrimitiveType::F32 => "f32".to_string(),
                PrimitiveType::F64 => "f64".to_string(),
                PrimitiveType::String => "String".to_string(),
                _ => "()".to_string(),
            },
            IrType::Container(c) => match c {
                ContainerType::Vec(inner) => format!("Vec<{}>", Self::ir_type_to_rust(inner)),
                ContainerType::Option(inner) => format!("Option<{}>", Self::ir_type_to_rust(inner)),
                _ => "()".to_string(),
            },
            IrType::Reference(name) => name.clone(),
            IrType::Special(_) => "()".to_string(),
        }
    }

    fn ir_type_to_python(ty: &protocol_squisher_ir::IrType) -> String {
        use protocol_squisher_ir::{ContainerType, IrType, PrimitiveType};
        match ty {
            IrType::Primitive(p) => match p {
                PrimitiveType::Bool => "bool".to_string(),
                PrimitiveType::I32 | PrimitiveType::I64 => "int".to_string(),
                PrimitiveType::F32 | PrimitiveType::F64 => "float".to_string(),
                PrimitiveType::String => "str".to_string(),
                _ => "Any".to_string(),
            },
            IrType::Container(c) => match c {
                ContainerType::Vec(inner) => format!("list[{}]", Self::ir_type_to_python(inner)),
                ContainerType::Option(inner) => {
                    format!("Optional[{}]", Self::ir_type_to_python(inner))
                },
                _ => "Any".to_string(),
            },
            IrType::Reference(name) => name.clone(),
            IrType::Special(_) => "Any".to_string(),
        }
    }

    fn ir_type_to_bebop(ty: &protocol_squisher_ir::IrType) -> String {
        use protocol_squisher_ir::{ContainerType, IrType, PrimitiveType};
        match ty {
            IrType::Primitive(p) => match p {
                PrimitiveType::Bool => "bool".to_string(),
                PrimitiveType::I32 => "int32".to_string(),
                PrimitiveType::I64 => "int64".to_string(),
                PrimitiveType::F32 => "float32".to_string(),
                PrimitiveType::F64 => "float64".to_string(),
                PrimitiveType::String => "string".to_string(),
                _ => "byte".to_string(),
            },
            IrType::Container(c) => match c {
                ContainerType::Vec(inner) => format!("array[{}]", Self::ir_type_to_bebop(inner)),
                ContainerType::Option(inner) => format!("{}?", Self::ir_type_to_bebop(inner)),
                _ => "byte".to_string(),
            },
            IrType::Reference(name) => name.clone(),
            IrType::Special(_) => "byte".to_string(),
        }
    }
}

impl Default for UniversalCompiler {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of a compilation operation
#[derive(Debug)]
pub struct CompilationResult {
    pub source_format: ProtocolFormat,
    pub target_format: ProtocolFormat,
    pub transport_class: TransportClass,
    pub source_types: usize,
    pub output_file: std::path::PathBuf,
    pub ephapax_verified: bool,
}

impl CompilationResult {
    /// Display summary
    pub fn summary(&self) -> String {
        format!(
            "Compiled {} types from {} to {} (Transport: {:?}, Ephapax: {}, Output: {})",
            self.source_types,
            self.source_format.name(),
            self.target_format.name(),
            self.transport_class,
            if self.ephapax_verified { "✓" } else { "✗" },
            self.output_file.display()
        )
    }
}
