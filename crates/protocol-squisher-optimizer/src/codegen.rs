// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Code generation for optimized adapters
//!
//! Generates Rust code for conversion paths that avoid JSON fallback.

use crate::{ConversionPath, ConversionStrategy, FieldMapping};

/// Behavior for checked numeric casts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckedCastBehavior {
    /// Preserve fail-fast behavior by aborting on overflow.
    Panic,
    /// Return `Result` and propagate conversion errors.
    Result,
}

/// Configuration for code generation
#[derive(Debug, Clone)]
pub struct CodegenConfig {
    /// Generate checked numeric casts (behavior controlled by `checked_cast_behavior`)
    pub checked_casts: bool,
    /// Behavior used when checked casts are enabled.
    pub checked_cast_behavior: CheckedCastBehavior,
    /// Include debug assertions
    pub debug_assertions: bool,
    /// Generate inline functions
    pub inline_functions: bool,
}

impl Default for CodegenConfig {
    fn default() -> Self {
        Self {
            checked_casts: true,
            checked_cast_behavior: CheckedCastBehavior::Panic,
            debug_assertions: cfg!(debug_assertions),
            inline_functions: true,
        }
    }
}

/// Generated code output
#[derive(Debug, Clone)]
pub struct GeneratedCode {
    /// The generated Rust code
    pub code: String,
    /// Required imports
    pub imports: Vec<String>,
    /// Whether the generated code uses unsafe
    pub uses_unsafe: bool,
}

/// Code generator for optimized conversions
#[derive(Debug, Default)]
pub struct CodeGenerator {
    config: CodegenConfig,
}

impl CodeGenerator {
    /// Create a new code generator with default config
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a code generator with custom config
    pub fn with_config(config: CodegenConfig) -> Self {
        Self { config }
    }

    /// Generate code for a conversion path
    pub fn generate(&self, path: &ConversionPath) -> GeneratedCode {
        match &path.strategy {
            ConversionStrategy::Identity => self.generate_identity(),
            ConversionStrategy::NumericCast { checked } => self.generate_numeric_cast(*checked),
            ConversionStrategy::StringConvert => self.generate_string_convert(),
            ConversionStrategy::OptionWrap => self.generate_option_wrap(),
            ConversionStrategy::ContainerMap => self.generate_container_map(path),
            ConversionStrategy::StructConvert { field_mappings } => {
                self.generate_struct_convert(field_mappings)
            },
            ConversionStrategy::EnumConvert { variant_mappings } => {
                self.generate_enum_convert(variant_mappings)
            },
            ConversionStrategy::JsonFallback => self.generate_json_fallback(),
        }
    }

    fn generate_identity(&self) -> GeneratedCode {
        let code = if self.config.inline_functions {
            "#[inline]\npub fn convert(value: T) -> T { value }".to_string()
        } else {
            "pub fn convert(value: T) -> T { value }".to_string()
        };

        GeneratedCode {
            code,
            imports: vec![],
            uses_unsafe: false,
        }
    }

    fn generate_numeric_cast(&self, checked: bool) -> GeneratedCode {
        let code = if checked && self.config.checked_casts {
            match self.config.checked_cast_behavior {
                CheckedCastBehavior::Panic => r#"#[inline]
pub fn convert<S, T>(value: S) -> T
where
    S: TryInto<T>,
{
    match value.try_into() {
        Ok(converted) => converted,
        Err(_) => std::process::abort(),
    }
}"#
                .to_string(),
                CheckedCastBehavior::Result => r#"#[inline]
pub fn convert<S, T>(value: S) -> Result<T, S::Error>
where
    S: TryInto<T>,
{
    value.try_into()
}"#
                .to_string(),
            }
        } else {
            r#"#[inline]
pub fn convert<S, T>(value: S) -> T
where
    S: Into<T>,
{
    value.into()
}"#
            .to_string()
        };

        GeneratedCode {
            code,
            imports: vec![],
            uses_unsafe: false,
        }
    }

    fn generate_string_convert(&self) -> GeneratedCode {
        GeneratedCode {
            code: r#"#[inline]
pub fn convert(value: impl AsRef<str>) -> String {
    value.as_ref().to_string()
}"#
            .to_string(),
            imports: vec![],
            uses_unsafe: false,
        }
    }

    fn generate_option_wrap(&self) -> GeneratedCode {
        GeneratedCode {
            code: r#"#[inline]
pub fn convert<T>(value: T) -> Option<T> {
    Some(value)
}"#
            .to_string(),
            imports: vec![],
            uses_unsafe: false,
        }
    }

    fn generate_container_map(&self, path: &ConversionPath) -> GeneratedCode {
        // For containers, we generate a map over elements
        let has_nested = !path.nested.is_empty();

        let code = if has_nested {
            r#"pub fn convert<I, O, F>(container: Vec<I>, convert_elem: F) -> Vec<O>
where
    F: Fn(I) -> O,
{
    container.into_iter().map(convert_elem).collect()
}"#
            .to_string()
        } else {
            r#"#[inline]
pub fn convert<T>(container: Vec<T>) -> Vec<T> {
    container
}"#
            .to_string()
        };

        GeneratedCode {
            code,
            imports: vec![],
            uses_unsafe: false,
        }
    }

    fn generate_struct_convert(&self, field_mappings: &[FieldMapping]) -> GeneratedCode {
        let mut field_lines = Vec::new();

        for mapping in field_mappings {
            if mapping.source_name.is_empty() {
                // Optional field with no source
                field_lines.push(format!("    {}: None,", mapping.target_name));
            } else {
                field_lines.push(format!(
                    "    {}: convert_field(source.{}),",
                    mapping.target_name, mapping.source_name
                ));
            }
        }

        let code = format!(
            r#"pub fn convert<S, T, F>(source: S, convert_field: F) -> T
where
    F: Fn(S) -> T,
{{
    T {{
{}
    }}
}}"#,
            field_lines.join("\n")
        );

        GeneratedCode {
            code,
            imports: vec![],
            uses_unsafe: false,
        }
    }

    fn generate_enum_convert(&self, variant_mappings: &[crate::VariantMapping]) -> GeneratedCode {
        let mut arms = Vec::new();

        for mapping in variant_mappings {
            let arm = if mapping.payload_conversion.is_some() {
                format!(
                    "        Source::{}(payload) => Target::{}(convert_payload(payload)),",
                    mapping.source_name, mapping.target_name
                )
            } else {
                format!(
                    "        Source::{}  => Target::{},",
                    mapping.source_name, mapping.target_name
                )
            };
            arms.push(arm);
        }

        let code = format!(
            r#"pub fn convert<Source, Target, F>(source: Source, convert_payload: F) -> Target
where
    F: Fn(Source) -> Target,
{{
    match source {{
{}
    }}
}}"#,
            arms.join("\n")
        );

        GeneratedCode {
            code,
            imports: vec![],
            uses_unsafe: false,
        }
    }

    fn generate_json_fallback(&self) -> GeneratedCode {
        GeneratedCode {
            code: r#"pub fn convert<S, T>(source: S) -> Result<T, serde_json::Error>
where
    S: serde::Serialize,
    T: serde::de::DeserializeOwned,
{
    let json = serde_json::to_string(&source)?;
    serde_json::from_str(&json)
}"#
            .to_string(),
            imports: vec!["use serde;".to_string(), "use serde_json;".to_string()],
            uses_unsafe: false,
        }
    }
}

/// Generate a complete adapter module for a conversion
pub fn generate_adapter_module(
    source_name: &str,
    target_name: &str,
    path: &ConversionPath,
) -> String {
    let generator = CodeGenerator::new();
    let generated = generator.generate(path);

    let imports = if generated.imports.is_empty() {
        String::new()
    } else {
        generated.imports.join("\n") + "\n\n"
    };

    format!(
        r#"// Auto-generated adapter: {} -> {}
// Optimization level: {:?}

{}{}
"#,
        source_name, target_name, path.level, imports, generated.code
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    #[test]
    fn test_identity_codegen() {
        let generator = CodeGenerator::new();
        let path = ConversionPath {
            source: IrType::Primitive(PrimitiveType::I32),
            target: IrType::Primitive(PrimitiveType::I32),
            level: OptimizationLevel::ZeroCopy,
            strategy: ConversionStrategy::Identity,
            nested: vec![],
        };

        let result = generator.generate(&path);
        assert!(result.code.contains("value"));
        assert!(!result.uses_unsafe);
    }

    #[test]
    fn test_numeric_cast_codegen() {
        let generator = CodeGenerator::new();
        let path = ConversionPath {
            source: IrType::Primitive(PrimitiveType::I32),
            target: IrType::Primitive(PrimitiveType::I64),
            level: OptimizationLevel::DirectCast,
            strategy: ConversionStrategy::NumericCast { checked: false },
            nested: vec![],
        };

        let result = generator.generate(&path);
        assert!(result.code.contains("into"));
    }

    #[test]
    fn test_checked_cast_codegen() {
        let generator = CodeGenerator::new();
        let path = ConversionPath {
            source: IrType::Primitive(PrimitiveType::I64),
            target: IrType::Primitive(PrimitiveType::I32),
            level: OptimizationLevel::DirectCast,
            strategy: ConversionStrategy::NumericCast { checked: true },
            nested: vec![],
        };

        let result = generator.generate(&path);
        assert!(result.code.contains("try_into"));
        assert!(result.code.contains("std::process::abort()"));
    }

    #[test]
    fn test_checked_cast_codegen_result_mode() {
        let generator = CodeGenerator::with_config(CodegenConfig {
            checked_cast_behavior: CheckedCastBehavior::Result,
            ..CodegenConfig::default()
        });
        let path = ConversionPath {
            source: IrType::Primitive(PrimitiveType::I64),
            target: IrType::Primitive(PrimitiveType::I32),
            level: OptimizationLevel::DirectCast,
            strategy: ConversionStrategy::NumericCast { checked: true },
            nested: vec![],
        };

        let result = generator.generate(&path);
        assert!(result.code.contains("Result<T, S::Error>"));
        assert!(result.code.contains("value.try_into()"));
        assert!(!result.code.contains("std::process::abort()"));
    }

    #[test]
    fn test_json_fallback_codegen() {
        let generator = CodeGenerator::new();
        let path = ConversionPath {
            source: IrType::Special(SpecialType::Any),
            target: IrType::Special(SpecialType::Any),
            level: OptimizationLevel::Fallback,
            strategy: ConversionStrategy::JsonFallback,
            nested: vec![],
        };

        let result = generator.generate(&path);
        assert!(result.code.contains("serde_json"));
        assert!(!result.imports.is_empty());
    }

    #[test]
    fn test_adapter_module_generation() {
        let path = ConversionPath {
            source: IrType::Primitive(PrimitiveType::I32),
            target: IrType::Primitive(PrimitiveType::I32),
            level: OptimizationLevel::ZeroCopy,
            strategy: ConversionStrategy::Identity,
            nested: vec![],
        };

        let module = generate_adapter_module("Source", "Target", &path);
        assert!(module.contains("Source -> Target"));
        assert!(module.contains("ZeroCopy"));
    }
}
