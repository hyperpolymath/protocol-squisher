// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! # Protocol Squisher PyO3 Code Generator
//!
//! Generates PyO3 binding code from IR schemas for Rust-Python interoperability.
//!
//! ## Features
//!
//! - **Type Mapping**: Converts IR types to PyO3-compatible Rust types
//! - **Struct Generation**: Creates PyO3 classes with getters, setters, and methods
//! - **Enum Generation**: Supports both simple and complex enums
//! - **Module Generation**: Produces complete PyO3 modules with registration
//! - **Type Stubs**: Generates `.pyi` files for Python type checking
//!
//! ## Usage
//!
//! ```rust,ignore
//! use protocol_squisher_pyo3_codegen::{generate_module, ModuleGenConfig};
//! use protocol_squisher_ir::IrSchema;
//!
//! let schema = IrSchema::new("example", "example");
//! // ... populate schema ...
//!
//! let config = ModuleGenConfig::new("my_module");
//! let result = generate_module(&schema, &config);
//!
//! println!("Rust code:\n{}", result.rust_code);
//! if let Some(stub) = result.python_stub {
//!     println!("Python stub:\n{}", stub);
//! }
//! ```
//!
//! ## Generated Code
//!
//! For a struct like:
//! ```rust,ignore
//! struct User {
//!     id: i64,
//!     name: String,
//! }
//! ```
//!
//! The generator produces:
//! ```rust,ignore
//! #[pyclass]
//! #[derive(Clone, Debug)]
//! pub struct User {
//!     #[pyo3(get, set)]
//!     pub id: i64,
//!     #[pyo3(get, set)]
//!     pub name: String,
//! }
//!
//! #[pymethods]
//! impl User {
//!     #[new]
//!     pub fn new(id: i64, name: String) -> Self { ... }
//!     fn __repr__(&self) -> String { ... }
//!     pub fn to_dict(&self, py: Python) -> PyResult<PyObject> { ... }
//!     pub fn to_json(&self) -> PyResult<String> { ... }
//!     // ... more methods
//! }
//! ```

pub mod mapping;
pub mod struct_gen;
pub mod enum_gen;
pub mod module_gen;
pub mod optimized_gen;

pub use mapping::{MappingContext, PyO3Primitive, PyO3Type};
pub use struct_gen::{generate_struct, is_hashable, StructGenConfig};
pub use enum_gen::{generate_enum, EnumGenConfig};
pub use module_gen::{generate_module, GeneratedModule, ModuleGenConfig};
pub use optimized_gen::{
    OptimizedPyO3Generator, OptimizedGenConfig, OptimizedGeneratedCode, GenerationStats,
};

use protocol_squisher_ir::IrSchema;

/// Code generator for PyO3 bindings
pub struct PyO3Generator {
    /// Module generation configuration
    config: ModuleGenConfig,
}

impl Default for PyO3Generator {
    fn default() -> Self {
        Self::new()
    }
}

impl PyO3Generator {
    /// Create a new generator with default configuration
    pub fn new() -> Self {
        Self {
            config: ModuleGenConfig::default(),
        }
    }

    /// Create a generator with a specific module name
    pub fn with_module_name(name: impl Into<String>) -> Self {
        Self {
            config: ModuleGenConfig::new(name),
        }
    }

    /// Set the module name
    pub fn module_name(mut self, name: impl Into<String>) -> Self {
        self.config.module_name = name.into();
        self
    }

    /// Set module documentation
    pub fn doc(mut self, doc: impl Into<String>) -> Self {
        self.config.module_doc = Some(doc.into());
        self
    }

    /// Configure struct generation
    pub fn struct_config(mut self, config: StructGenConfig) -> Self {
        self.config.struct_config = config;
        self
    }

    /// Configure enum generation
    pub fn enum_config(mut self, config: EnumGenConfig) -> Self {
        self.config.enum_config = config;
        self
    }

    /// Enable or disable serde derive
    pub fn with_serde(mut self, enabled: bool) -> Self {
        self.config.add_serde_derive = enabled;
        self
    }

    /// Enable or disable stub generation
    pub fn with_stubs(mut self, enabled: bool) -> Self {
        self.config.generate_stubs = enabled;
        self
    }

    /// Generate code from a schema
    pub fn generate(&self, schema: &IrSchema) -> GeneratedModule {
        generate_module(schema, &self.config)
    }
}

/// Quick function to generate PyO3 module code
pub fn quick_generate(schema: &IrSchema, module_name: &str) -> String {
    let config = ModuleGenConfig::new(module_name);
    generate_module(schema, &config).rust_code
}

/// Generate PyO3 module with Python stubs
pub fn generate_with_stubs(
    schema: &IrSchema,
    module_name: &str,
) -> (String, String) {
    let config = ModuleGenConfig::new(module_name);
    let result = generate_module(schema, &config);
    (result.rust_code, result.python_stub.unwrap_or_default())
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{
        ContainerType, EnumDef, FieldDef, FieldMetadata, IrType, PrimitiveType,
        StructDef, TagStyle, TypeDef, TypeMetadata, VariantDef,
    };

    fn make_user_schema() -> IrSchema {
        let mut schema = IrSchema::new("users", "test");
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
                        ty: IrType::Primitive(PrimitiveType::String),
                        optional: true,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );
        schema
    }

    #[test]
    fn test_generator_creation() {
        let gen = PyO3Generator::new();
        assert_eq!(gen.config.module_name, "generated");
    }

    #[test]
    fn test_generator_with_module_name() {
        let gen = PyO3Generator::with_module_name("my_module");
        assert_eq!(gen.config.module_name, "my_module");
    }

    #[test]
    fn test_generator_builder() {
        let gen = PyO3Generator::new()
            .module_name("custom")
            .doc("My module docs")
            .with_serde(true)
            .with_stubs(true);

        assert_eq!(gen.config.module_name, "custom");
        assert_eq!(gen.config.module_doc, Some("My module docs".to_string()));
    }

    #[test]
    fn test_generate_user_module() {
        let schema = make_user_schema();
        let gen = PyO3Generator::with_module_name("users");
        let result = gen.generate(&schema);

        assert!(result.rust_code.contains("pub struct User"));
        assert!(result.rust_code.contains("pub id: i64"));
        assert!(result.rust_code.contains("pub name: String"));
        assert!(result.rust_code.contains("pub email: Option<String>"));
        assert!(result.rust_code.contains("#[pymodule]"));
        assert!(result.generated_types.contains(&"User".to_string()));
    }

    #[test]
    fn test_quick_generate() {
        let schema = make_user_schema();
        let code = quick_generate(&schema, "users");

        assert!(code.contains("pub struct User"));
        assert!(code.contains("fn users("));
    }

    #[test]
    fn test_generate_with_stubs() {
        let schema = make_user_schema();
        let (rust_code, python_stub) = generate_with_stubs(&schema, "users");

        assert!(rust_code.contains("pub struct User"));
        assert!(python_stub.contains("class User:"));
        assert!(python_stub.contains("id: int"));
        assert!(python_stub.contains("name: str"));
    }

    #[test]
    fn test_complex_schema() {
        let mut schema = IrSchema::new("complex", "test");

        // Add a struct
        schema.add_type(
            "Order".to_string(),
            TypeDef::Struct(StructDef {
                name: "Order".to_string(),
                fields: vec![
                    FieldDef {
                        name: "id".to_string(),
                        ty: IrType::Primitive(PrimitiveType::I64),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                    FieldDef {
                        name: "items".to_string(),
                        ty: IrType::Container(ContainerType::Vec(Box::new(
                            IrType::Primitive(PrimitiveType::String),
                        ))),
                        optional: false,
                        constraints: vec![],
                        metadata: FieldMetadata::default(),
                    },
                ],
                metadata: TypeMetadata::default(),
            }),
        );

        // Add an enum
        schema.add_type(
            "Status".to_string(),
            TypeDef::Enum(EnumDef {
                name: "Status".to_string(),
                variants: vec![
                    VariantDef {
                        name: "Pending".to_string(),
                        payload: None,
                        metadata: Default::default(),
                    },
                    VariantDef {
                        name: "Shipped".to_string(),
                        payload: None,
                        metadata: Default::default(),
                    },
                ],
                tag_style: TagStyle::External,
                metadata: TypeMetadata::default(),
            }),
        );

        let gen = PyO3Generator::with_module_name("orders");
        let result = gen.generate(&schema);

        assert!(result.rust_code.contains("pub struct Order"));
        assert!(result.rust_code.contains("pub enum Status"));
        assert!(result.rust_code.contains("items: Vec<String>"));
    }

    #[test]
    fn test_type_mapping() {
        let int_type = PyO3Type::from_ir(&IrType::Primitive(PrimitiveType::I32));
        assert_eq!(int_type, PyO3Type::Primitive(PyO3Primitive::Int));
        assert_eq!(int_type.python_annotation(), "int");
        assert_eq!(int_type.rust_type(), "i64");
    }

    #[test]
    fn test_container_mapping() {
        let list_type = PyO3Type::from_ir(&IrType::Container(ContainerType::Vec(
            Box::new(IrType::Primitive(PrimitiveType::String)),
        )));
        assert_eq!(list_type.python_annotation(), "list[str]");
        assert_eq!(list_type.rust_type(), "Vec<String>");
    }

    #[test]
    fn test_dict_mapping() {
        let dict_type = PyO3Type::from_ir(&IrType::Container(ContainerType::Map(
            Box::new(IrType::Primitive(PrimitiveType::String)),
            Box::new(IrType::Primitive(PrimitiveType::I64)),
        )));
        assert_eq!(dict_type.python_annotation(), "dict[str, int]");
    }

    #[test]
    fn test_optional_mapping() {
        let opt_type = PyO3Type::from_ir(&IrType::Container(ContainerType::Option(
            Box::new(IrType::Primitive(PrimitiveType::String)),
        )));
        assert_eq!(opt_type.python_annotation(), "str | None");
        assert_eq!(opt_type.rust_type(), "Option<String>");
    }
}
