// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Enum code generation for PyO3
//!
//! Generates PyO3 enum definitions from IR enum definitions.

use crate::mapping::{MappingContext, PyO3Type};
use protocol_squisher_ir::{EnumDef, TagStyle, VariantDef, VariantPayload};

/// Configuration for enum generation
#[derive(Debug, Clone)]
pub struct EnumGenConfig {
    /// Generate __repr__ method
    pub generate_repr: bool,
    /// Generate __eq__ method
    pub generate_eq: bool,
    /// Generate to_dict/from_dict methods
    pub generate_dict_methods: bool,
    /// Generate JSON serialization methods
    pub generate_json_methods: bool,
}

impl Default for EnumGenConfig {
    fn default() -> Self {
        Self {
            generate_repr: true,
            generate_eq: true,
            generate_dict_methods: true,
            generate_json_methods: true,
        }
    }
}

/// Generate PyO3 enum code
///
/// PyO3 enums are represented as a base class with static methods
/// returning variant instances, since Python enums work differently.
pub fn generate_enum(
    enum_def: &EnumDef,
    config: &EnumGenConfig,
    ctx: &mut MappingContext,
) -> String {
    let mut code = String::new();

    // Check if this is a simple enum (all unit variants)
    let is_simple = enum_def.variants.iter().all(|v| v.payload.is_none());

    if is_simple {
        code.push_str(&generate_simple_enum(enum_def, config));
    } else {
        code.push_str(&generate_complex_enum(enum_def, config, ctx));
    }

    ctx.mark_mapped(&enum_def.name);
    code
}

/// Generate a simple enum (all unit variants) using IntEnum pattern
fn generate_simple_enum(enum_def: &EnumDef, config: &EnumGenConfig) -> String {
    let mut code = String::new();

    // Use IntEnum-style representation
    code.push_str(&format!(
        "#[pyclass{}]\n",
        if config.generate_eq { ", eq, hash" } else { "" }
    ));
    code.push_str("#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]\n");
    code.push_str(&format!("pub enum {} {{\n", enum_def.name));

    for (i, variant) in enum_def.variants.iter().enumerate() {
        code.push_str(&format!("    {} = {},\n", variant.name, i));
    }

    code.push_str("}\n\n");

    // Generate pymethods
    code.push_str("#[pymethods]\n");
    code.push_str(&format!("impl {} {{\n", enum_def.name));

    // Generate variant constructors as class methods
    for variant in &enum_def.variants {
        code.push_str(&format!(
            "    #[classattr]\n    fn {}() -> Self {{ Self::{} }}\n\n",
            variant.name.to_lowercase(),
            variant.name
        ));
    }

    // Generate __repr__
    if config.generate_repr {
        code.push_str("    fn __repr__(&self) -> String {\n");
        code.push_str("        match self {\n");
        for variant in &enum_def.variants {
            code.push_str(&format!(
                "            Self::{} => \"{}.{}\".to_string(),\n",
                variant.name, enum_def.name, variant.name
            ));
        }
        code.push_str("        }\n");
        code.push_str("    }\n\n");
    }

    // Generate name property
    code.push_str("    #[getter]\n");
    code.push_str("    fn name(&self) -> &'static str {\n");
    code.push_str("        match self {\n");
    for variant in &enum_def.variants {
        code.push_str(&format!(
            "            Self::{} => \"{}\",\n",
            variant.name, variant.name
        ));
    }
    code.push_str("        }\n");
    code.push_str("    }\n\n");

    // Generate value property
    code.push_str("    #[getter]\n");
    code.push_str("    fn value(&self) -> usize {\n");
    code.push_str("        *self as usize\n");
    code.push_str("    }\n");

    code.push_str("}\n");

    code
}

/// Generate a complex enum (has variants with payloads) using tagged union pattern
fn generate_complex_enum(
    enum_def: &EnumDef,
    config: &EnumGenConfig,
    ctx: &mut MappingContext,
) -> String {
    let mut code = String::new();

    // Generate a Rust enum with serde support
    code.push_str("#[pyclass]\n");
    code.push_str("#[derive(Clone, Debug)]\n");

    // Determine serde tag attribute based on IR tag style
    let tag_attr = match &enum_def.tag_style {
        TagStyle::External => String::new(),
        TagStyle::Internal { tag_field } => format!("#[serde(tag = \"{}\")]\n", tag_field),
        TagStyle::Adjacent {
            tag_field,
            content_field,
        } => {
            format!(
                "#[serde(tag = \"{}\", content = \"{}\")]\n",
                tag_field, content_field
            )
        },
        TagStyle::Untagged => "#[serde(untagged)]\n".to_string(),
    };
    code.push_str(&tag_attr);

    code.push_str(&format!("pub enum {} {{\n", enum_def.name));

    for variant in &enum_def.variants {
        code.push_str(&generate_variant_definition(variant, ctx));
    }

    code.push_str("}\n\n");

    // Generate pymethods
    code.push_str("#[pymethods]\n");
    code.push_str(&format!("impl {} {{\n", enum_def.name));

    // Generate variant constructors
    for variant in &enum_def.variants {
        code.push_str(&generate_variant_constructor(variant, &enum_def.name));
    }

    // Generate is_* methods for variant checking
    for variant in &enum_def.variants {
        code.push_str(&format!(
            "    /// Check if this is the {} variant\n",
            variant.name
        ));
        code.push_str(&format!(
            "    pub fn is_{}(&self) -> bool {{\n",
            variant.name.to_lowercase()
        ));
        code.push_str(&format!(
            "        matches!(self, Self::{}{{ .. }})\n",
            variant.name
        ));
        code.push_str("    }\n\n");
    }

    // Generate __repr__
    if config.generate_repr {
        code.push_str(&generate_enum_repr(enum_def));
    }

    // Generate to_dict
    if config.generate_dict_methods {
        code.push_str(&generate_enum_to_dict(enum_def));
    }

    // Generate JSON methods
    if config.generate_json_methods {
        code.push_str(&generate_enum_json_methods(enum_def));
    }

    code.push_str("}\n");

    code
}

/// Generate a single variant definition
fn generate_variant_definition(variant: &VariantDef, ctx: &mut MappingContext) -> String {
    match &variant.payload {
        None => format!("    {},\n", variant.name),
        Some(VariantPayload::Tuple(types)) => {
            let type_strs: Vec<String> = types
                .iter()
                .map(|t| {
                    if let protocol_squisher_ir::IrType::Reference(ref name) = t {
                        ctx.reference(name);
                    }
                    PyO3Type::from_ir(t).rust_type()
                })
                .collect();
            format!("    {}({}),\n", variant.name, type_strs.join(", "))
        },
        Some(VariantPayload::Struct(fields)) => {
            let mut field_strs = Vec::new();
            for field in fields {
                if let protocol_squisher_ir::IrType::Reference(ref name) = field.ty {
                    ctx.reference(name);
                }
                let pyo3_type = PyO3Type::from_ir(&field.ty);
                field_strs.push(format!("{}: {}", field.name, pyo3_type.rust_type()));
            }
            format!("    {} {{ {} }},\n", variant.name, field_strs.join(", "))
        },
    }
}

/// Generate a variant constructor
fn generate_variant_constructor(variant: &VariantDef, _enum_name: &str) -> String {
    let mut code = String::new();

    match &variant.payload {
        None => {
            code.push_str(&format!(
                "    #[staticmethod]\n    pub fn {}() -> Self {{ Self::{} }}\n\n",
                variant.name.to_lowercase(),
                variant.name
            ));
        },
        Some(VariantPayload::Tuple(types)) => {
            let params: Vec<String> = types
                .iter()
                .enumerate()
                .map(|(i, t)| format!("v{}: {}", i, PyO3Type::from_ir(t).rust_type()))
                .collect();
            let args: Vec<String> = (0..types.len()).map(|i| format!("v{}", i)).collect();

            code.push_str(&format!(
                "    #[staticmethod]\n    pub fn {}({}) -> Self {{\n        Self::{}({})\n    }}\n\n",
                variant.name.to_lowercase(),
                params.join(", "),
                variant.name,
                args.join(", ")
            ));
        },
        Some(VariantPayload::Struct(fields)) => {
            let params: Vec<String> = fields
                .iter()
                .map(|f| format!("{}: {}", f.name, PyO3Type::from_ir(&f.ty).rust_type()))
                .collect();
            let args: Vec<String> = fields.iter().map(|f| f.name.clone()).collect();

            code.push_str(&format!(
                "    #[staticmethod]\n    pub fn {}({}) -> Self {{\n        Self::{} {{ {} }}\n    }}\n\n",
                variant.name.to_lowercase(),
                params.join(", "),
                variant.name,
                args.join(", ")
            ));
        },
    }

    code
}

/// Generate __repr__ for complex enum
fn generate_enum_repr(enum_def: &EnumDef) -> String {
    let mut code = String::new();

    code.push_str("    fn __repr__(&self) -> String {\n");
    code.push_str("        match self {\n");

    for variant in &enum_def.variants {
        match &variant.payload {
            None => {
                code.push_str(&format!(
                    "            Self::{} => \"{}.{}\".to_string(),\n",
                    variant.name, enum_def.name, variant.name
                ));
            },
            Some(VariantPayload::Tuple(types)) => {
                let patterns: Vec<String> = (0..types.len()).map(|i| format!("v{}", i)).collect();
                let format_args: Vec<String> =
                    (0..types.len()).map(|i| format!("v{}", i)).collect();
                code.push_str(&format!(
                    "            Self::{}({}) => format!(\"{}.{}({{:?}})\", ({})),\n",
                    variant.name,
                    patterns.join(", "),
                    enum_def.name,
                    variant.name,
                    format_args.join(", ")
                ));
            },
            Some(VariantPayload::Struct(fields)) => {
                let patterns: Vec<String> = fields.iter().map(|f| f.name.clone()).collect();
                code.push_str(&format!(
                    "            Self::{} {{ {} }} => format!(\"{}.{}({{:?}})\", ({})),\n",
                    variant.name,
                    patterns.join(", "),
                    enum_def.name,
                    variant.name,
                    patterns.join(", ")
                ));
            },
        }
    }

    code.push_str("        }\n");
    code.push_str("    }\n\n");

    code
}

/// Generate to_dict for enum
fn generate_enum_to_dict(enum_def: &EnumDef) -> String {
    let mut code = String::new();

    code.push_str("    /// Convert to a Python dictionary\n");
    code.push_str(
        "    pub fn to_dict(&self, py: pyo3::Python<'_>) -> pyo3::PyResult<pyo3::PyObject> {\n",
    );
    code.push_str("        let dict = pyo3::types::PyDict::new(py);\n");
    code.push_str("        match self {\n");

    for variant in &enum_def.variants {
        match &variant.payload {
            None => {
                code.push_str(&format!(
                    "            Self::{} => {{ dict.set_item(\"type\", \"{}\")?; }}\n",
                    variant.name, variant.name
                ));
            },
            Some(VariantPayload::Tuple(types)) => {
                let patterns: Vec<String> = (0..types.len()).map(|i| format!("v{}", i)).collect();
                code.push_str(&format!(
                    "            Self::{}({}) => {{\n",
                    variant.name,
                    patterns.join(", ")
                ));
                code.push_str(&format!(
                    "                dict.set_item(\"type\", \"{}\")?;\n",
                    variant.name
                ));
                for i in 0..types.len() {
                    code.push_str(&format!(
                        "                dict.set_item(\"value{}\", v{}.clone())?;\n",
                        i, i
                    ));
                }
                code.push_str("            }\n");
            },
            Some(VariantPayload::Struct(fields)) => {
                let patterns: Vec<String> = fields.iter().map(|f| f.name.clone()).collect();
                code.push_str(&format!(
                    "            Self::{} {{ {} }} => {{\n",
                    variant.name,
                    patterns.join(", ")
                ));
                code.push_str(&format!(
                    "                dict.set_item(\"type\", \"{}\")?;\n",
                    variant.name
                ));
                for field in fields {
                    code.push_str(&format!(
                        "                dict.set_item(\"{}\", {}.clone())?;\n",
                        field.name, field.name
                    ));
                }
                code.push_str("            }\n");
            },
        }
    }

    code.push_str("        }\n");
    code.push_str("        Ok(dict.into())\n");
    code.push_str("    }\n\n");

    code
}

/// Generate JSON methods for enum
fn generate_enum_json_methods(enum_def: &EnumDef) -> String {
    let mut code = String::new();

    code.push_str("    /// Serialize to JSON string\n");
    code.push_str("    pub fn to_json(&self) -> pyo3::PyResult<String> {\n");
    code.push_str("        serde_json::to_string(self).map_err(|e| pyo3::exceptions::PyValueError::new_err(e.to_string()))\n");
    code.push_str("    }\n\n");

    code.push_str("    /// Deserialize from JSON string\n");
    code.push_str("    #[staticmethod]\n");
    code.push_str(&format!(
        "    pub fn from_json(json: &str) -> pyo3::PyResult<{}> {{\n",
        enum_def.name
    ));
    code.push_str("        serde_json::from_str(json).map_err(|e| pyo3::exceptions::PyValueError::new_err(e.to_string()))\n");
    code.push_str("    }\n\n");

    code
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{FieldDef, FieldMetadata, IrType, PrimitiveType, TypeMetadata};

    #[test]
    fn test_simple_enum_generation() {
        let enum_def = EnumDef {
            name: "Status".to_string(),
            variants: vec![
                VariantDef {
                    name: "Pending".to_string(),
                    payload: None,
                    metadata: Default::default(),
                },
                VariantDef {
                    name: "Active".to_string(),
                    payload: None,
                    metadata: Default::default(),
                },
                VariantDef {
                    name: "Completed".to_string(),
                    payload: None,
                    metadata: Default::default(),
                },
            ],
            tag_style: TagStyle::External,
            metadata: TypeMetadata::default(),
        };

        let mut ctx = MappingContext::new();
        let code = generate_enum(&enum_def, &EnumGenConfig::default(), &mut ctx);

        assert!(code.contains("pub enum Status"));
        assert!(code.contains("Pending = 0"));
        assert!(code.contains("Active = 1"));
        assert!(code.contains("Completed = 2"));
        assert!(code.contains("#[classattr]"));
    }

    #[test]
    fn test_complex_enum_generation() {
        let enum_def = EnumDef {
            name: "Message".to_string(),
            variants: vec![
                VariantDef {
                    name: "Text".to_string(),
                    payload: Some(VariantPayload::Tuple(vec![IrType::Primitive(
                        PrimitiveType::String,
                    )])),
                    metadata: Default::default(),
                },
                VariantDef {
                    name: "Image".to_string(),
                    payload: Some(VariantPayload::Struct(vec![
                        FieldDef {
                            name: "url".to_string(),
                            ty: IrType::Primitive(PrimitiveType::String),
                            optional: false,
                            constraints: vec![],
                            metadata: FieldMetadata::default(),
                        },
                        FieldDef {
                            name: "width".to_string(),
                            ty: IrType::Primitive(PrimitiveType::I32),
                            optional: false,
                            constraints: vec![],
                            metadata: FieldMetadata::default(),
                        },
                    ])),
                    metadata: Default::default(),
                },
            ],
            tag_style: TagStyle::External,
            metadata: TypeMetadata::default(),
        };

        let mut ctx = MappingContext::new();
        let code = generate_enum(&enum_def, &EnumGenConfig::default(), &mut ctx);

        assert!(code.contains("pub enum Message"));
        assert!(code.contains("Text(String)"));
        assert!(code.contains("Image { url: String, width: i64 }"));
        assert!(code.contains("pub fn is_text(&self)"));
        assert!(code.contains("pub fn is_image(&self)"));
    }

    #[test]
    fn test_internal_tag_style() {
        let enum_def = EnumDef {
            name: "Event".to_string(),
            variants: vec![VariantDef {
                name: "Click".to_string(),
                payload: None,
                metadata: Default::default(),
            }],
            tag_style: TagStyle::Internal {
                tag_field: "event_type".to_string(),
            },
            metadata: TypeMetadata::default(),
        };

        let mut ctx = MappingContext::new();
        let code = generate_enum(&enum_def, &EnumGenConfig::default(), &mut ctx);

        // Simple enum doesn't use serde attributes
        assert!(code.contains("pub enum Event"));
    }
}
