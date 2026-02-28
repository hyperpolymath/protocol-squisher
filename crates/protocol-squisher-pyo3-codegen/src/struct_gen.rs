// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Struct code generation for PyO3
//!
//! Generates PyO3 class definitions from IR struct definitions.

use crate::mapping::{MappingContext, PyO3Type};
use protocol_squisher_ir::{IrType, StructDef};

/// Configuration for struct generation
#[derive(Debug, Clone)]
pub struct StructGenConfig {
    /// Generate __init__ method
    pub generate_init: bool,
    /// Generate __repr__ method
    pub generate_repr: bool,
    /// Generate __eq__ method
    pub generate_eq: bool,
    /// Generate __hash__ method (requires all fields hashable)
    pub generate_hash: bool,
    /// Generate to_dict/from_dict methods
    pub generate_dict_methods: bool,
    /// Generate JSON serialization methods
    pub generate_json_methods: bool,
    /// Use slots for memory efficiency
    pub use_slots: bool,
}

impl Default for StructGenConfig {
    fn default() -> Self {
        Self {
            generate_init: true,
            generate_repr: true,
            generate_eq: true,
            generate_hash: false,
            generate_dict_methods: true,
            generate_json_methods: true,
            use_slots: true,
        }
    }
}

/// Generate PyO3 class code for a struct
pub fn generate_struct(
    struct_def: &StructDef,
    config: &StructGenConfig,
    ctx: &mut MappingContext,
) -> String {
    let mut code = String::new();

    // Class definition with pyclass attribute
    code.push_str(&format!(
        "#[pyclass{}]\n",
        if config.generate_eq { ", eq, hash" } else { "" }
    ));
    code.push_str("#[derive(Clone, Debug)]\n");
    code.push_str(&format!("pub struct {} {{\n", struct_def.name));

    // Generate fields
    for field in &struct_def.fields {
        let pyo3_type = PyO3Type::from_ir(&field.ty);

        // Track referenced types
        if let IrType::Reference(ref name) = field.ty {
            ctx.reference(name);
        }

        // Wrap optional fields in Option<>
        let rust_type = if field.optional {
            format!("Option<{}>", pyo3_type.rust_type())
        } else {
            pyo3_type.rust_type()
        };

        code.push_str(&format!(
            "    #[pyo3(get, set)]\n    pub {}: {},\n",
            sanitize_field_name(&field.name),
            rust_type
        ));
    }

    code.push_str("}\n\n");

    // Generate pymethods impl
    code.push_str("#[pymethods]\n");
    code.push_str(&format!("impl {} {{\n", struct_def.name));

    // Generate __new__ method
    if config.generate_init {
        code.push_str(&generate_new_method(struct_def));
    }

    // Generate __repr__ method
    if config.generate_repr {
        code.push_str(&generate_repr_method(struct_def));
    }

    // Generate to_dict method
    if config.generate_dict_methods {
        code.push_str(&generate_to_dict_method(struct_def));
        code.push_str(&generate_from_dict_method(struct_def));
    }

    // Generate JSON methods
    if config.generate_json_methods {
        code.push_str(&generate_to_json_method(struct_def));
        code.push_str(&generate_from_json_method(struct_def));
    }

    code.push_str("}\n");

    ctx.mark_mapped(&struct_def.name);
    code
}

/// Generate the __new__ method
fn generate_new_method(struct_def: &StructDef) -> String {
    let mut code = String::new();

    // Build parameter list
    let params: Vec<String> = struct_def
        .fields
        .iter()
        .map(|f| {
            let pyo3_type = PyO3Type::from_ir(&f.ty);
            let name = sanitize_field_name(&f.name);
            if f.optional {
                format!("{}: Option<{}>", name, pyo3_type.rust_type())
            } else {
                format!("{}: {}", name, pyo3_type.rust_type())
            }
        })
        .collect();

    code.push_str("    #[new]\n");
    code.push_str(&format!(
        "    pub fn new({}) -> Self {{\n",
        params.join(", ")
    ));
    code.push_str("        Self {\n");

    for field in &struct_def.fields {
        let name = sanitize_field_name(&field.name);
        code.push_str(&format!("            {},\n", name));
    }

    code.push_str("        }\n");
    code.push_str("    }\n\n");

    code
}

/// Generate the __repr__ method
fn generate_repr_method(struct_def: &StructDef) -> String {
    let mut code = String::new();

    code.push_str("    fn __repr__(&self) -> String {\n");
    code.push_str(&format!("        format!(\"{}({{}})\",\n", struct_def.name));

    let field_formats: Vec<String> = struct_def
        .fields
        .iter()
        .map(|f| {
            let name = sanitize_field_name(&f.name);
            format!("            \"{}={{:?}}\"", name)
        })
        .collect();

    code.push_str("            vec![\n");
    for (i, fmt) in field_formats.iter().enumerate() {
        let name = sanitize_field_name(&struct_def.fields[i].name);
        code.push_str(&format!(
            "                format!({}, self.{}),\n",
            fmt, name
        ));
    }
    code.push_str("            ].join(\", \")\n");
    code.push_str("        )\n");
    code.push_str("    }\n\n");

    code
}

/// Generate the to_dict method
fn generate_to_dict_method(struct_def: &StructDef) -> String {
    let mut code = String::new();

    code.push_str("    /// Convert to a Python dictionary\n");
    code.push_str(
        "    pub fn to_dict(&self, py: pyo3::Python<'_>) -> pyo3::PyResult<pyo3::PyObject> {\n",
    );
    code.push_str("        let dict = pyo3::types::PyDict::new(py);\n");

    for field in &struct_def.fields {
        let name = sanitize_field_name(&field.name);
        let key = &field.name;
        code.push_str(&format!(
            "        dict.set_item(\"{}\", self.{}.clone())?;\n",
            key, name
        ));
    }

    code.push_str("        Ok(dict.into())\n");
    code.push_str("    }\n\n");

    code
}

/// Generate the from_dict class method
fn generate_from_dict_method(struct_def: &StructDef) -> String {
    let mut code = String::new();

    code.push_str("    /// Create from a Python dictionary\n");
    code.push_str("    #[staticmethod]\n");
    code.push_str(&format!(
        "    pub fn from_dict(dict: &pyo3::types::PyDict) -> pyo3::PyResult<{}> {{\n",
        struct_def.name
    ));

    for field in &struct_def.fields {
        let name = sanitize_field_name(&field.name);
        let key = &field.name;
        let pyo3_type = PyO3Type::from_ir(&field.ty);

        if field.optional {
            code.push_str(&format!(
                "        let {}: Option<{}> = dict.get_item(\"{}\")?.map(|v| v.extract()).transpose()?;\n",
                name, pyo3_type.rust_type(), key
            ));
        } else {
            code.push_str(&format!(
                "        let {}: {} = dict.get_item(\"{}\")?.ok_or_else(|| pyo3::exceptions::PyKeyError::new_err(\"{}\"))?.extract()?;\n",
                name, pyo3_type.rust_type(), key, key
            ));
        }
    }

    code.push_str(&format!("        Ok({} {{\n", struct_def.name));
    for field in &struct_def.fields {
        let name = sanitize_field_name(&field.name);
        code.push_str(&format!("            {},\n", name));
    }
    code.push_str("        })\n");
    code.push_str("    }\n\n");

    code
}

/// Generate the to_json method
fn generate_to_json_method(_struct_def: &StructDef) -> String {
    let mut code = String::new();

    code.push_str("    /// Serialize to JSON string\n");
    code.push_str("    pub fn to_json(&self) -> pyo3::PyResult<String> {\n");
    code.push_str(
        "        serde_json::to_string(self).map_err(|e| pyo3::exceptions::PyValueError::new_err(e.to_string()))\n",
    );
    code.push_str("    }\n\n");

    code
}

/// Generate the from_json class method
fn generate_from_json_method(struct_def: &StructDef) -> String {
    let mut code = String::new();

    code.push_str("    /// Deserialize from JSON string\n");
    code.push_str("    #[staticmethod]\n");
    code.push_str(&format!(
        "    pub fn from_json(json: &str) -> pyo3::PyResult<{}> {{\n",
        struct_def.name
    ));
    code.push_str("        serde_json::from_str(json).map_err(|e| pyo3::exceptions::PyValueError::new_err(e.to_string()))\n");
    code.push_str("    }\n\n");

    code
}

/// Sanitize field names that are Python/Rust keywords
fn sanitize_field_name(name: &str) -> String {
    match name {
        // Python keywords
        "type" => "type_".to_string(),
        "class" => "class_".to_string(),
        "import" => "import_".to_string(),
        "from" => "from_".to_string(),
        "as" => "as_".to_string(),
        "def" => "def_".to_string(),
        "return" => "return_".to_string(),
        "yield" => "yield_".to_string(),
        "lambda" => "lambda_".to_string(),
        "pass" => "pass_".to_string(),
        "break" => "break_".to_string(),
        "continue" => "continue_".to_string(),
        "raise" => "raise_".to_string(),
        "try" => "try_".to_string(),
        "except" => "except_".to_string(),
        "finally" => "finally_".to_string(),
        "with" => "with_".to_string(),
        "assert" => "assert_".to_string(),
        "global" => "global_".to_string(),
        "nonlocal" => "nonlocal_".to_string(),
        "del" => "del_".to_string(),
        "not" => "not_".to_string(),
        "and" => "and_".to_string(),
        "or" => "or_".to_string(),
        "is" => "is_".to_string(),
        "in" => "in_".to_string(),
        "for" => "for_".to_string(),
        "while" => "while_".to_string(),
        "if" => "if_".to_string(),
        "elif" => "elif_".to_string(),
        "else" => "else_".to_string(),
        // Rust keywords
        "self" => "self_".to_string(),
        "Self" => "self_type".to_string(),
        "super" => "super_".to_string(),
        "crate" => "crate_".to_string(),
        "mod" => "mod_".to_string(),
        "pub" => "pub_".to_string(),
        "fn" => "fn_".to_string(),
        "let" => "let_".to_string(),
        "mut" => "mut_".to_string(),
        "const" => "const_".to_string(),
        "static" => "static_".to_string(),
        "ref" => "ref_".to_string(),
        "match" => "match_".to_string(),
        "loop" => "loop_".to_string(),
        "move" => "move_".to_string(),
        "impl" => "impl_".to_string(),
        "trait" => "trait_".to_string(),
        "struct" => "struct_".to_string(),
        "enum" => "enum_".to_string(),
        "union" => "union_".to_string(),
        "where" => "where_".to_string(),
        "async" => "async_".to_string(),
        "await" => "await_".to_string(),
        "dyn" => "dyn_".to_string(),
        "abstract" => "abstract_".to_string(),
        "become" => "become_".to_string(),
        "box" => "box_".to_string(),
        "do" => "do_".to_string(),
        "final" => "final_".to_string(),
        "macro" => "macro_".to_string(),
        "override" => "override_".to_string(),
        "priv" => "priv_".to_string(),
        "typeof" => "typeof_".to_string(),
        "unsized" => "unsized_".to_string(),
        "virtual" => "virtual_".to_string(),
        _ => name.to_string(),
    }
}

/// Check if a type is hashable for Python
pub fn is_hashable(ir_type: &IrType) -> bool {
    match ir_type {
        IrType::Primitive(_) => true,
        IrType::Reference(_) => false, // Custom types may not be hashable
        IrType::Container(c) => match c {
            protocol_squisher_ir::ContainerType::Option(inner) => is_hashable(inner),
            protocol_squisher_ir::ContainerType::Tuple(items) => items.iter().all(is_hashable),
            // Mutable containers are not hashable
            _ => false,
        },
        IrType::Special(s) => matches!(
            s,
            protocol_squisher_ir::SpecialType::Unit | protocol_squisher_ir::SpecialType::Never
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{FieldDef, FieldMetadata, PrimitiveType, TypeMetadata};

    fn make_field(name: &str, ty: IrType, optional: bool) -> FieldDef {
        FieldDef {
            name: name.to_string(),
            ty,
            optional,
            constraints: vec![],
            metadata: FieldMetadata::default(),
        }
    }

    #[test]
    fn test_simple_struct_generation() {
        let struct_def = StructDef {
            name: "User".to_string(),
            fields: vec![
                make_field("id", IrType::Primitive(PrimitiveType::I64), false),
                make_field("name", IrType::Primitive(PrimitiveType::String), false),
            ],
            metadata: TypeMetadata::default(),
        };

        let mut ctx = MappingContext::new();
        let code = generate_struct(&struct_def, &StructGenConfig::default(), &mut ctx);

        assert!(code.contains("#[pyclass"));
        assert!(code.contains("pub struct User"));
        assert!(code.contains("pub id: i64"));
        assert!(code.contains("pub name: String"));
        assert!(code.contains("#[new]"));
        assert!(code.contains("fn __repr__"));
    }

    #[test]
    fn test_optional_field() {
        let struct_def = StructDef {
            name: "Config".to_string(),
            fields: vec![
                make_field("port", IrType::Primitive(PrimitiveType::I32), false),
                make_field("host", IrType::Primitive(PrimitiveType::String), true),
            ],
            metadata: TypeMetadata::default(),
        };

        let mut ctx = MappingContext::new();
        let code = generate_struct(&struct_def, &StructGenConfig::default(), &mut ctx);

        assert!(code.contains("host: Option<String>"));
    }

    #[test]
    fn test_sanitize_keywords() {
        assert_eq!(sanitize_field_name("type"), "type_");
        assert_eq!(sanitize_field_name("class"), "class_");
        assert_eq!(sanitize_field_name("self"), "self_");
        assert_eq!(sanitize_field_name("name"), "name");
    }

    #[test]
    fn test_reference_tracking() {
        let struct_def = StructDef {
            name: "Order".to_string(),
            fields: vec![
                make_field("id", IrType::Primitive(PrimitiveType::I64), false),
                make_field("user", IrType::Reference("User".to_string()), false),
            ],
            metadata: TypeMetadata::default(),
        };

        let mut ctx = MappingContext::new();
        let _ = generate_struct(&struct_def, &StructGenConfig::default(), &mut ctx);

        assert!(ctx.pending_types.contains(&"User".to_string()));
        assert!(ctx.mapped_types.contains(&"Order".to_string()));
    }
}
