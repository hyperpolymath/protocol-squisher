// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Type mapping from IR to PyO3
//!
//! Defines how IR types are represented in PyO3 bindings.

use protocol_squisher_ir::{ContainerType, IrType, PrimitiveType, SpecialType};

/// PyO3 type representation
#[derive(Debug, Clone, PartialEq)]
pub enum PyO3Type {
    /// Python primitive (int, float, str, bool, bytes)
    Primitive(PyO3Primitive),
    /// Python list
    List(Box<PyO3Type>),
    /// Python dict
    Dict(Box<PyO3Type>, Box<PyO3Type>),
    /// Python set
    Set(Box<PyO3Type>),
    /// Python tuple
    Tuple(Vec<PyO3Type>),
    /// Optional (Option<T> in Rust, Optional[T] in Python)
    Optional(Box<PyO3Type>),
    /// Reference to a custom class
    Class(String),
    /// Python Any (for dynamic/unknown types)
    Any,
    /// Python None
    None,
}

/// Python primitive types
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PyO3Primitive {
    /// Python int (maps to i8, i16, i32, i64, i128, u8, u16, u32, u64, u128)
    Int,
    /// Python float (maps to f32, f64)
    Float,
    /// Python str (maps to String, char)
    Str,
    /// Python bool
    Bool,
    /// Python bytes (maps to Vec<u8>, [u8; N])
    Bytes,
}

impl PyO3Type {
    /// Convert an IR type to a PyO3 type
    pub fn from_ir(ir_type: &IrType) -> Self {
        match ir_type {
            IrType::Primitive(p) => Self::from_primitive(p),
            IrType::Container(c) => Self::from_container(c),
            IrType::Special(s) => Self::from_special(s),
            IrType::Reference(name) => PyO3Type::Class(name.clone()),
        }
    }

    fn from_primitive(prim: &PrimitiveType) -> Self {
        match prim {
            PrimitiveType::Bool => PyO3Type::Primitive(PyO3Primitive::Bool),
            PrimitiveType::I8
            | PrimitiveType::I16
            | PrimitiveType::I32
            | PrimitiveType::I64
            | PrimitiveType::I128
            | PrimitiveType::U8
            | PrimitiveType::U16
            | PrimitiveType::U32
            | PrimitiveType::U64
            | PrimitiveType::U128
            | PrimitiveType::BigInt => PyO3Type::Primitive(PyO3Primitive::Int),
            PrimitiveType::F32 | PrimitiveType::F64 => {
                PyO3Type::Primitive(PyO3Primitive::Float)
            }
            PrimitiveType::Char | PrimitiveType::String => {
                PyO3Type::Primitive(PyO3Primitive::Str)
            }
            PrimitiveType::Bytes => PyO3Type::Primitive(PyO3Primitive::Bytes),
            // Temporal and special primitives - represent as strings
            PrimitiveType::DateTime
            | PrimitiveType::Date
            | PrimitiveType::Time
            | PrimitiveType::Uuid
            | PrimitiveType::Decimal => PyO3Type::Primitive(PyO3Primitive::Str),
            // Duration as float (seconds)
            PrimitiveType::Duration => PyO3Type::Primitive(PyO3Primitive::Float),
        }
    }

    fn from_container(container: &ContainerType) -> Self {
        match container {
            ContainerType::Vec(inner) => {
                // Special case: Vec<u8> -> bytes
                if matches!(inner.as_ref(), IrType::Primitive(PrimitiveType::U8)) {
                    PyO3Type::Primitive(PyO3Primitive::Bytes)
                } else {
                    PyO3Type::List(Box::new(PyO3Type::from_ir(inner)))
                }
            }
            ContainerType::Array(inner, _size) => {
                // Special case: [u8; N] -> bytes
                if matches!(inner.as_ref(), IrType::Primitive(PrimitiveType::U8)) {
                    PyO3Type::Primitive(PyO3Primitive::Bytes)
                } else {
                    PyO3Type::List(Box::new(PyO3Type::from_ir(inner)))
                }
            }
            ContainerType::Set(inner) => {
                PyO3Type::Set(Box::new(PyO3Type::from_ir(inner)))
            }
            ContainerType::Map(key, value) => PyO3Type::Dict(
                Box::new(PyO3Type::from_ir(key)),
                Box::new(PyO3Type::from_ir(value)),
            ),
            ContainerType::Option(inner) => {
                PyO3Type::Optional(Box::new(PyO3Type::from_ir(inner)))
            }
            ContainerType::Tuple(items) => {
                PyO3Type::Tuple(items.iter().map(PyO3Type::from_ir).collect())
            }
            ContainerType::Result(ok, _err) => {
                // Result<T, E> maps to just T in Python (exceptions for errors)
                PyO3Type::from_ir(ok)
            }
        }
    }

    fn from_special(special: &SpecialType) -> Self {
        match special {
            SpecialType::Any => PyO3Type::Any,
            SpecialType::Unit => PyO3Type::None,
            SpecialType::Never => PyO3Type::None,
            SpecialType::Json => PyO3Type::Any,
            SpecialType::Opaque(_) => PyO3Type::Primitive(PyO3Primitive::Bytes),
        }
    }

    /// Generate the Python type annotation string
    pub fn python_annotation(&self) -> String {
        match self {
            PyO3Type::Primitive(p) => p.python_name().to_string(),
            PyO3Type::List(inner) => format!("list[{}]", inner.python_annotation()),
            PyO3Type::Dict(key, value) => {
                format!("dict[{}, {}]", key.python_annotation(), value.python_annotation())
            }
            PyO3Type::Set(inner) => format!("set[{}]", inner.python_annotation()),
            PyO3Type::Tuple(items) => {
                if items.is_empty() {
                    "tuple[()]".to_string()
                } else {
                    let inner: Vec<_> = items.iter().map(|t| t.python_annotation()).collect();
                    format!("tuple[{}]", inner.join(", "))
                }
            }
            PyO3Type::Optional(inner) => format!("{} | None", inner.python_annotation()),
            PyO3Type::Class(name) => name.clone(),
            PyO3Type::Any => "Any".to_string(),
            PyO3Type::None => "None".to_string(),
        }
    }

    /// Generate the Rust type string for PyO3
    pub fn rust_type(&self) -> String {
        match self {
            PyO3Type::Primitive(p) => p.rust_type().to_string(),
            PyO3Type::List(inner) => format!("Vec<{}>", inner.rust_type()),
            PyO3Type::Dict(key, value) => {
                format!("std::collections::HashMap<{}, {}>", key.rust_type(), value.rust_type())
            }
            PyO3Type::Set(inner) => {
                format!("std::collections::HashSet<{}>", inner.rust_type())
            }
            PyO3Type::Tuple(items) => {
                if items.is_empty() {
                    "()".to_string()
                } else {
                    let inner: Vec<_> = items.iter().map(|t| t.rust_type()).collect();
                    format!("({})", inner.join(", "))
                }
            }
            PyO3Type::Optional(inner) => format!("Option<{}>", inner.rust_type()),
            PyO3Type::Class(name) => name.clone(),
            PyO3Type::Any => "pyo3::PyObject".to_string(),
            PyO3Type::None => "()".to_string(),
        }
    }
}

impl PyO3Primitive {
    /// Get the Python type name
    pub fn python_name(&self) -> &'static str {
        match self {
            PyO3Primitive::Int => "int",
            PyO3Primitive::Float => "float",
            PyO3Primitive::Str => "str",
            PyO3Primitive::Bool => "bool",
            PyO3Primitive::Bytes => "bytes",
        }
    }

    /// Get the Rust type for PyO3
    pub fn rust_type(&self) -> &'static str {
        match self {
            PyO3Primitive::Int => "i64",
            PyO3Primitive::Float => "f64",
            PyO3Primitive::Str => "String",
            PyO3Primitive::Bool => "bool",
            PyO3Primitive::Bytes => "Vec<u8>",
        }
    }
}

/// Mapping context for tracking referenced types
#[derive(Debug, Default)]
pub struct MappingContext {
    /// Types that are referenced but not yet defined
    pub pending_types: Vec<String>,
    /// Types that have been mapped
    pub mapped_types: Vec<String>,
}

impl MappingContext {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a type reference
    pub fn reference(&mut self, name: &str) {
        if !self.mapped_types.contains(&name.to_string())
            && !self.pending_types.contains(&name.to_string())
        {
            self.pending_types.push(name.to_string());
        }
    }

    /// Mark a type as mapped
    pub fn mark_mapped(&mut self, name: &str) {
        self.mapped_types.push(name.to_string());
        self.pending_types.retain(|n| n != name);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_primitive_mapping() {
        assert_eq!(
            PyO3Type::from_ir(&IrType::Primitive(PrimitiveType::I32)),
            PyO3Type::Primitive(PyO3Primitive::Int)
        );
        assert_eq!(
            PyO3Type::from_ir(&IrType::Primitive(PrimitiveType::F64)),
            PyO3Type::Primitive(PyO3Primitive::Float)
        );
        assert_eq!(
            PyO3Type::from_ir(&IrType::Primitive(PrimitiveType::String)),
            PyO3Type::Primitive(PyO3Primitive::Str)
        );
        assert_eq!(
            PyO3Type::from_ir(&IrType::Primitive(PrimitiveType::Bool)),
            PyO3Type::Primitive(PyO3Primitive::Bool)
        );
    }

    #[test]
    fn test_container_mapping() {
        let vec_i32 = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
            PrimitiveType::I32,
        ))));
        assert_eq!(
            PyO3Type::from_ir(&vec_i32),
            PyO3Type::List(Box::new(PyO3Type::Primitive(PyO3Primitive::Int)))
        );
    }

    #[test]
    fn test_vec_u8_is_bytes() {
        let vec_u8 = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
            PrimitiveType::U8,
        ))));
        assert_eq!(
            PyO3Type::from_ir(&vec_u8),
            PyO3Type::Primitive(PyO3Primitive::Bytes)
        );
    }

    #[test]
    fn test_optional_mapping() {
        let opt_str = IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
            PrimitiveType::String,
        ))));
        assert_eq!(
            PyO3Type::from_ir(&opt_str),
            PyO3Type::Optional(Box::new(PyO3Type::Primitive(PyO3Primitive::Str)))
        );
    }

    #[test]
    fn test_reference_mapping() {
        let reference = IrType::Reference("User".to_string());
        assert_eq!(
            PyO3Type::from_ir(&reference),
            PyO3Type::Class("User".to_string())
        );
    }

    #[test]
    fn test_python_annotation() {
        assert_eq!(PyO3Type::Primitive(PyO3Primitive::Int).python_annotation(), "int");
        assert_eq!(
            PyO3Type::List(Box::new(PyO3Type::Primitive(PyO3Primitive::Str))).python_annotation(),
            "list[str]"
        );
        assert_eq!(
            PyO3Type::Optional(Box::new(PyO3Type::Primitive(PyO3Primitive::Int))).python_annotation(),
            "int | None"
        );
    }

    #[test]
    fn test_rust_type() {
        assert_eq!(PyO3Type::Primitive(PyO3Primitive::Int).rust_type(), "i64");
        assert_eq!(
            PyO3Type::List(Box::new(PyO3Type::Primitive(PyO3Primitive::Str))).rust_type(),
            "Vec<String>"
        );
    }
}
