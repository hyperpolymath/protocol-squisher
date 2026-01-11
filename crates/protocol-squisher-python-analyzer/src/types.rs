// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Types representing the JSON output from the Python introspection script

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Root output from the introspection script
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IntrospectionResult {
    /// Module path that was introspected
    pub module: String,
    /// Pydantic version (1 or 2)
    pub pydantic_version: u8,
    /// Extracted types (models and enums)
    pub types: Vec<PydanticType>,
    /// Error message if introspection failed
    #[serde(default)]
    pub error: Option<String>,
}

/// A type extracted from Python
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum PydanticType {
    /// A Pydantic model (struct-like)
    #[serde(rename = "model")]
    Model(PydanticModel),
    /// An enum type
    #[serde(rename = "enum")]
    Enum(PydanticEnum),
    /// Error extracting this type
    #[serde(rename = "error")]
    Error {
        name: String,
        error: String,
    },
}

/// A Pydantic BaseModel definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PydanticModel {
    /// Model class name
    pub name: String,
    /// Module where the model is defined
    pub module: String,
    /// Docstring
    #[serde(default)]
    pub doc: Option<String>,
    /// Model fields
    pub fields: Vec<PydanticField>,
    /// Model configuration
    #[serde(default)]
    pub config: BTreeMap<String, serde_json::Value>,
}

/// A field in a Pydantic model
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PydanticField {
    /// Field name
    pub name: String,
    /// Field type annotation
    #[serde(rename = "type")]
    pub field_type: PythonType,
    /// Whether the field is optional (has default)
    #[serde(default)]
    pub optional: bool,
    /// Default value (if any)
    #[serde(default)]
    pub default: Option<serde_json::Value>,
    /// Alias for serialization
    #[serde(default)]
    pub alias: Option<String>,
    /// Field title
    #[serde(default)]
    pub title: Option<String>,
    /// Field description
    #[serde(default)]
    pub description: Option<String>,
    /// Validation constraints
    #[serde(default)]
    pub constraints: FieldConstraints,
}

/// Validation constraints on a field
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct FieldConstraints {
    /// Greater than
    #[serde(default)]
    pub gt: Option<f64>,
    /// Greater than or equal
    #[serde(default)]
    pub ge: Option<f64>,
    /// Less than
    #[serde(default)]
    pub lt: Option<f64>,
    /// Less than or equal
    #[serde(default)]
    pub le: Option<f64>,
    /// Must be multiple of
    #[serde(default)]
    pub multiple_of: Option<f64>,
    /// Minimum string/collection length
    #[serde(default)]
    pub min_length: Option<usize>,
    /// Maximum string/collection length
    #[serde(default)]
    pub max_length: Option<usize>,
    /// Regex pattern
    #[serde(default)]
    pub pattern: Option<String>,
}

/// A Python Enum definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PydanticEnum {
    /// Enum class name
    pub name: String,
    /// Module where the enum is defined
    pub module: String,
    /// Docstring
    #[serde(default)]
    pub doc: Option<String>,
    /// Enum variants
    pub variants: Vec<EnumVariant>,
}

/// A variant in a Python Enum
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnumVariant {
    /// Variant name
    pub name: String,
    /// Variant value
    pub value: serde_json::Value,
}

/// Python type annotation representation
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum PythonType {
    /// Primitive types (str, int, float, bool, bytes, etc)
    #[serde(rename = "primitive")]
    Primitive {
        #[serde(rename = "type")]
        prim_type: String,
    },
    /// None type
    #[serde(rename = "none")]
    None,
    /// Any type
    #[serde(rename = "any")]
    Any,
    /// Optional[T]
    #[serde(rename = "optional")]
    Optional {
        inner: Box<PythonType>,
    },
    /// Union[A, B, ...]
    #[serde(rename = "union")]
    Union {
        variants: Vec<PythonType>,
    },
    /// List[T]
    #[serde(rename = "list")]
    List {
        inner: Box<PythonType>,
    },
    /// Set[T]
    #[serde(rename = "set")]
    Set {
        inner: Box<PythonType>,
    },
    /// Dict[K, V]
    #[serde(rename = "map")]
    Map {
        key: Box<PythonType>,
        value: Box<PythonType>,
    },
    /// Tuple[A, B, ...]
    #[serde(rename = "tuple")]
    Tuple {
        elements: Vec<PythonType>,
    },
    /// Enum reference
    #[serde(rename = "enum")]
    Enum {
        name: String,
        module: String,
        #[serde(default)]
        variants: Vec<EnumVariant>,
    },
    /// Reference to another type (model, class)
    #[serde(rename = "reference")]
    Reference {
        name: String,
        #[serde(default)]
        module: Option<String>,
    },
    /// Unknown type
    #[serde(rename = "unknown")]
    Unknown {
        #[serde(default)]
        repr: Option<String>,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_primitive() {
        let json = r#"{"kind": "primitive", "type": "string"}"#;
        let ty: PythonType = serde_json::from_str(json).unwrap();
        assert!(matches!(ty, PythonType::Primitive { prim_type } if prim_type == "string"));
    }

    #[test]
    fn test_parse_optional() {
        let json = r#"{"kind": "optional", "inner": {"kind": "primitive", "type": "int"}}"#;
        let ty: PythonType = serde_json::from_str(json).unwrap();
        if let PythonType::Optional { inner } = ty {
            assert!(matches!(*inner, PythonType::Primitive { prim_type } if prim_type == "int"));
        } else {
            panic!("Expected Optional");
        }
    }

    #[test]
    fn test_parse_model() {
        let json = r#"{
            "kind": "model",
            "name": "User",
            "module": "myapp.models",
            "doc": "A user model",
            "fields": [
                {
                    "name": "id",
                    "type": {"kind": "primitive", "type": "int"},
                    "optional": false
                },
                {
                    "name": "name",
                    "type": {"kind": "primitive", "type": "string"},
                    "optional": false
                }
            ],
            "config": {}
        }"#;
        let ty: PydanticType = serde_json::from_str(json).unwrap();
        if let PydanticType::Model(model) = ty {
            assert_eq!(model.name, "User");
            assert_eq!(model.fields.len(), 2);
        } else {
            panic!("Expected Model");
        }
    }

    #[test]
    fn test_parse_introspection_result() {
        let json = r#"{
            "module": "myapp.models",
            "pydantic_version": 2,
            "types": [
                {
                    "kind": "model",
                    "name": "User",
                    "module": "myapp.models",
                    "fields": [],
                    "config": {}
                }
            ]
        }"#;
        let result: IntrospectionResult = serde_json::from_str(json).unwrap();
        assert_eq!(result.module, "myapp.models");
        assert_eq!(result.pydantic_version, 2);
        assert_eq!(result.types.len(), 1);
    }
}
