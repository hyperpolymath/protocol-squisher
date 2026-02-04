// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! # JSON Fallback Transport
//!
//! The guaranteed wheelbarrow. Slow but unbreakable.
//!
//! This crate generates JSON-based transport code that ensures the invariant:
//! **If it compiles, it carries.**
//!
//! JSON may not be the fastest, but it can represent any data structure
//! that both Rust serde and Python can handle. This is the universal fallback
//! when optimized paths aren't available.

use protocol_squisher_ir::{
    ContainerType, IrSchema, IrType, PrimitiveType, SpecialType, TypeDef, TypeId,
};
use std::collections::HashSet;

mod rust_codegen;
mod python_codegen;
pub mod ephapax_fallback;

pub use rust_codegen::*;
pub use python_codegen::*;
pub use ephapax_fallback::{
    EphapaxFallbackGenerator, EphapaxFallbackConfig, EphapaxFallbackResult, FallbackStats,
};

/// Configuration for JSON fallback code generation
#[derive(Debug, Clone)]
pub struct FallbackConfig {
    /// Module name for generated code
    pub module_name: String,
    /// Whether to generate validation code
    pub validate: bool,
    /// Whether to pretty-print JSON (slower but debuggable)
    pub pretty_json: bool,
    /// Include type hints in Python code
    pub python_type_hints: bool,
}

impl Default for FallbackConfig {
    fn default() -> Self {
        Self {
            module_name: "fallback".to_string(),
            validate: true,
            pretty_json: false,
            python_type_hints: true,
        }
    }
}

impl FallbackConfig {
    pub fn new(module_name: &str) -> Self {
        Self {
            module_name: module_name.to_string(),
            ..Default::default()
        }
    }

    pub fn with_validation(mut self, validate: bool) -> Self {
        self.validate = validate;
        self
    }

    pub fn with_pretty_json(mut self, pretty: bool) -> Self {
        self.pretty_json = pretty;
        self
    }

    pub fn with_python_type_hints(mut self, hints: bool) -> Self {
        self.python_type_hints = hints;
        self
    }
}

/// Result of generating fallback transport code
#[derive(Debug, Clone)]
pub struct FallbackResult {
    /// Rust code for serialization/deserialization
    pub rust_code: String,
    /// Python code for serialization/deserialization
    pub python_code: String,
    /// Types that were successfully generated
    pub generated_types: Vec<TypeId>,
    /// Types that couldn't be generated (with reasons)
    pub skipped_types: Vec<(TypeId, String)>,
}

/// Generate JSON fallback transport code for a schema
pub fn generate_fallback(schema: &IrSchema, config: &FallbackConfig) -> FallbackResult {
    let mut generated_types = Vec::new();
    let mut skipped_types = Vec::new();

    // Collect all type IDs we'll generate
    let type_ids: Vec<_> = schema.types.keys().cloned().collect();

    for type_id in &type_ids {
        if can_generate_fallback(schema, type_id) {
            generated_types.push(type_id.clone());
        } else {
            skipped_types.push((type_id.clone(), "Contains unsupported type".to_string()));
        }
    }

    // Generate Rust code
    let rust_code = rust_codegen::generate_rust_fallback(schema, &generated_types, config);

    // Generate Python code
    let python_code = python_codegen::generate_python_fallback(schema, &generated_types, config);

    FallbackResult {
        rust_code,
        python_code,
        generated_types,
        skipped_types,
    }
}

/// Check if we can generate fallback code for a type
fn can_generate_fallback(schema: &IrSchema, type_id: &TypeId) -> bool {
    let mut visited = HashSet::new();
    can_generate_fallback_recursive(schema, type_id, &mut visited)
}

fn can_generate_fallback_recursive(
    schema: &IrSchema,
    type_id: &TypeId,
    visited: &mut HashSet<TypeId>,
) -> bool {
    if visited.contains(type_id) {
        // Recursive types are fine with JSON (use Option/Box)
        return true;
    }
    visited.insert(type_id.clone());

    match schema.types.get(type_id) {
        Some(type_def) => match type_def {
            TypeDef::Struct(s) => {
                s.fields.iter().all(|f| can_serialize_type(schema, &f.ty, visited))
            }
            TypeDef::Enum(e) => {
                e.variants.iter().all(|v| {
                    v.payload.as_ref().map_or(true, |p| {
                        match p {
                            protocol_squisher_ir::VariantPayload::Tuple(types) => {
                                types.iter().all(|t| can_serialize_type(schema, t, visited))
                            }
                            protocol_squisher_ir::VariantPayload::Struct(fields) => {
                                fields.iter().all(|f| can_serialize_type(schema, &f.ty, visited))
                            }
                        }
                    })
                })
            }
            TypeDef::Alias(a) => can_serialize_type(schema, &a.target, visited),
            TypeDef::Newtype(n) => can_serialize_type(schema, &n.inner, visited),
            TypeDef::Union(u) => {
                u.variants.iter().all(|v| can_serialize_type(schema, v, visited))
            }
        },
        None => false,
    }
}

fn can_serialize_type(schema: &IrSchema, ir_type: &IrType, visited: &mut HashSet<TypeId>) -> bool {
    match ir_type {
        IrType::Primitive(_) => true,
        IrType::Container(c) => match c {
            ContainerType::Option(inner) => can_serialize_type(schema, inner, visited),
            ContainerType::Vec(inner) => can_serialize_type(schema, inner, visited),
            ContainerType::Array(inner, _) => can_serialize_type(schema, inner, visited),
            ContainerType::Set(inner) => can_serialize_type(schema, inner, visited),
            ContainerType::Map(key, value) => {
                // JSON only supports string keys
                matches!(key.as_ref(), IrType::Primitive(PrimitiveType::String))
                    && can_serialize_type(schema, value, visited)
            }
            ContainerType::Tuple(elements) => {
                elements.iter().all(|e| can_serialize_type(schema, e, visited))
            }
            ContainerType::Result(ok, err) => {
                can_serialize_type(schema, ok, visited) && can_serialize_type(schema, err, visited)
            }
        },
        IrType::Reference(type_id) => can_generate_fallback_recursive(schema, type_id, visited),
        IrType::Special(s) => match s {
            SpecialType::Any | SpecialType::Unit | SpecialType::Json => true,
            SpecialType::Never => false,
            SpecialType::Opaque(_) => false,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::*;

    fn create_test_schema() -> IrSchema {
        let mut schema = IrSchema::new("test", "test");

        // Add a simple struct
        schema.add_type(
            "User".to_string(),
            TypeDef::Struct(StructDef {
                name: "User".to_string(),
                fields: vec![
                    FieldDef {
                        name: "id".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "name".to_string(),
                        ty: IrType::Primitive(PrimitiveType::String),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "email".to_string(),
                        ty: IrType::Container(ContainerType::Option(Box::new(
                            IrType::Primitive(PrimitiveType::String),
                        ))),
                        optional: true,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );

        // Add a simple enum
        schema.add_type(
            "Status".to_string(),
            TypeDef::Enum(EnumDef {
                name: "Status".to_string(),
                variants: vec![
                    VariantDef {
                        name: "Active".to_string(),
                        payload: None,
                        metadata: VariantMetadata::default(),
                    },
                    VariantDef {
                        name: "Inactive".to_string(),
                        payload: None,
                        metadata: VariantMetadata::default(),
                    },
                    VariantDef {
                        name: "Pending".to_string(),
                        payload: Some(VariantPayload::Tuple(vec![IrType::Primitive(
                            PrimitiveType::String,
                        )])),
                        metadata: VariantMetadata::default(),
                    },
                ],
                tag_style: TagStyle::External,
                metadata: TypeMetadata::default(),
            }),
        );

        schema
    }

    #[test]
    fn test_can_generate_fallback_simple_struct() {
        let schema = create_test_schema();
        assert!(can_generate_fallback(&schema, &"User".to_string()));
    }

    #[test]
    fn test_can_generate_fallback_simple_enum() {
        let schema = create_test_schema();
        assert!(can_generate_fallback(&schema, &"Status".to_string()));
    }

    #[test]
    fn test_generate_fallback_produces_code() {
        let schema = create_test_schema();
        let config = FallbackConfig::new("test_module");
        let result = generate_fallback(&schema, &config);

        assert!(!result.rust_code.is_empty());
        assert!(!result.python_code.is_empty());
        assert_eq!(result.generated_types.len(), 2);
        assert!(result.skipped_types.is_empty());
    }

    #[test]
    fn test_config_builder() {
        let config = FallbackConfig::new("my_module")
            .with_validation(false)
            .with_pretty_json(true)
            .with_python_type_hints(false);

        assert_eq!(config.module_name, "my_module");
        assert!(!config.validate);
        assert!(config.pretty_json);
        assert!(!config.python_type_hints);
    }
}
