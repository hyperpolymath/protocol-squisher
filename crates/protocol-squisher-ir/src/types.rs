// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! IR Type System
//!
//! The type system is organized into three categories:
//! - **Primitives**: Basic scalar types (integers, floats, strings, etc.)
//! - **Containers**: Generic wrappers (Option, Vec, Map, etc.)
//! - **Composites**: User-defined structures (structs, enums, unions)

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

use crate::{constraints::Constraint, FieldId, TypeId};

/// The core IR type enumeration
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum IrType {
    /// Primitive scalar types
    Primitive(PrimitiveType),

    /// Container types (parameterized)
    Container(ContainerType),

    /// Reference to a named type in the schema
    Reference(TypeId),

    /// Special types
    Special(SpecialType),
}

impl IrType {
    /// Check if this type is nullable/optional at the top level
    pub fn is_optional(&self) -> bool {
        matches!(self, IrType::Container(ContainerType::Option(_)))
    }

    /// Get the inner type if this is a container
    pub fn inner_type(&self) -> Option<&IrType> {
        match self {
            IrType::Container(c) => c.inner_type(),
            _ => None,
        }
    }
}

/// Primitive scalar types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PrimitiveType {
    // Booleans
    Bool,

    // Signed integers
    I8,
    I16,
    I32,
    I64,
    I128,

    // Unsigned integers
    U8,
    U16,
    U32,
    U64,
    U128,

    // Floating point
    F32,
    F64,

    // Text
    String,
    Char,

    // Binary
    Bytes,

    // Temporal (ISO 8601 compatible)
    DateTime,
    Date,
    Time,
    Duration,

    // Identifiers
    Uuid,

    // Numeric
    Decimal,
    BigInt,
}

impl PrimitiveType {
    /// Get the byte size of this primitive (if fixed-size)
    pub fn byte_size(&self) -> Option<usize> {
        match self {
            PrimitiveType::Bool => Some(1),
            PrimitiveType::I8 | PrimitiveType::U8 => Some(1),
            PrimitiveType::I16 | PrimitiveType::U16 | PrimitiveType::Char => Some(2),
            PrimitiveType::I32 | PrimitiveType::U32 | PrimitiveType::F32 => Some(4),
            PrimitiveType::I64 | PrimitiveType::U64 | PrimitiveType::F64 => Some(8),
            PrimitiveType::I128 | PrimitiveType::U128 | PrimitiveType::Uuid => Some(16),
            // Variable-size types
            PrimitiveType::String
            | PrimitiveType::Bytes
            | PrimitiveType::DateTime
            | PrimitiveType::Date
            | PrimitiveType::Time
            | PrimitiveType::Duration
            | PrimitiveType::Decimal
            | PrimitiveType::BigInt => None,
        }
    }

    /// Check if this is a numeric type
    pub fn is_numeric(&self) -> bool {
        matches!(
            self,
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
                | PrimitiveType::F32
                | PrimitiveType::F64
                | PrimitiveType::Decimal
                | PrimitiveType::BigInt
        )
    }
}

/// Container types (generic wrappers)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ContainerType {
    /// Optional value (nullable)
    Option(Box<IrType>),

    /// Ordered sequence
    Vec(Box<IrType>),

    /// Fixed-size array
    Array(Box<IrType>, usize),

    /// Unordered unique set
    Set(Box<IrType>),

    /// Key-value mapping
    Map(Box<IrType>, Box<IrType>),

    /// Tuple of heterogeneous types
    Tuple(Vec<IrType>),

    /// Result type (success or error)
    Result(Box<IrType>, Box<IrType>),
}

impl ContainerType {
    /// Get the primary inner type
    pub fn inner_type(&self) -> Option<&IrType> {
        match self {
            ContainerType::Option(t) => Some(t),
            ContainerType::Vec(t) => Some(t),
            ContainerType::Array(t, _) => Some(t),
            ContainerType::Set(t) => Some(t),
            ContainerType::Map(_, v) => Some(v), // Value type is "primary"
            ContainerType::Tuple(ts) => ts.first(),
            ContainerType::Result(ok, _) => Some(ok),
        }
    }
}

/// Special types that don't fit other categories
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum SpecialType {
    /// Any type (dynamic, untyped)
    Any,

    /// Unit type (void, null, none)
    Unit,

    /// Never type (unreachable, bottom)
    Never,

    /// Raw JSON value
    Json,

    /// Opaque binary blob with format hint
    Opaque(String),
}

/// Type definition (named type in the schema)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TypeDef {
    /// Struct/record/object
    Struct(StructDef),

    /// Tagged union/enum with variants
    Enum(EnumDef),

    /// Untagged union (one of several types)
    Union(UnionDef),

    /// Type alias
    Alias(AliasDef),

    /// Newtype wrapper
    Newtype(NewtypeDef),
}

impl TypeDef {
    /// Get the name of this type
    pub fn name(&self) -> &str {
        match self {
            TypeDef::Struct(s) => &s.name,
            TypeDef::Enum(e) => &e.name,
            TypeDef::Union(u) => &u.name,
            TypeDef::Alias(a) => &a.name,
            TypeDef::Newtype(n) => &n.name,
        }
    }
}

/// Struct/record/object definition
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct StructDef {
    /// Type name
    pub name: String,

    /// Fields in definition order
    pub fields: Vec<FieldDef>,

    /// Type-level metadata
    pub metadata: TypeMetadata,
}

/// Field definition within a struct
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FieldDef {
    /// Field name
    pub name: FieldId,

    /// Field type
    pub ty: IrType,

    /// Whether the field is optional (can be omitted)
    pub optional: bool,

    /// Field-level constraints
    pub constraints: Vec<Constraint>,

    /// Field metadata
    pub metadata: FieldMetadata,
}

/// Tagged union/enum definition
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EnumDef {
    /// Type name
    pub name: String,

    /// Variants
    pub variants: Vec<VariantDef>,

    /// How the tag is represented in serialization
    pub tag_style: TagStyle,

    /// Type-level metadata
    pub metadata: TypeMetadata,
}

/// Enum variant definition
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct VariantDef {
    /// Variant name
    pub name: String,

    /// Variant payload type (None for unit variants)
    pub payload: Option<VariantPayload>,

    /// Variant metadata
    pub metadata: VariantMetadata,
}

/// Enum variant payload
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VariantPayload {
    /// Single unnamed value
    Tuple(Vec<IrType>),

    /// Named fields (struct variant)
    Struct(Vec<FieldDef>),
}

/// Tag representation style for enums
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TagStyle {
    /// External: {"VariantName": {...}}
    External,

    /// Internal: {"type": "VariantName", ...}
    Internal { tag_field: String },

    /// Adjacent: {"tag": "VariantName", "content": {...}}
    Adjacent { tag_field: String, content_field: String },

    /// Untagged: {...} (discriminated by shape)
    Untagged,
}

impl Default for TagStyle {
    fn default() -> Self {
        TagStyle::External
    }
}

/// Untagged union definition
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct UnionDef {
    /// Type name
    pub name: String,

    /// Possible types (tried in order)
    pub variants: Vec<IrType>,

    /// Type-level metadata
    pub metadata: TypeMetadata,
}

/// Type alias definition
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AliasDef {
    /// Alias name
    pub name: String,

    /// Target type
    pub target: IrType,

    /// Type-level metadata
    pub metadata: TypeMetadata,
}

/// Newtype wrapper definition
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct NewtypeDef {
    /// Newtype name
    pub name: String,

    /// Wrapped type
    pub inner: IrType,

    /// Constraints on the wrapper
    pub constraints: Vec<Constraint>,

    /// Type-level metadata
    pub metadata: TypeMetadata,
}

/// Type-level metadata
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct TypeMetadata {
    /// Documentation string
    pub doc: Option<String>,

    /// Deprecation notice
    pub deprecated: Option<String>,

    /// Serialization hints from source
    pub serde_hints: BTreeMap<String, String>,

    /// Additional key-value metadata
    pub extra: BTreeMap<String, String>,
}

/// Field-level metadata
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct FieldMetadata {
    /// Documentation string
    pub doc: Option<String>,

    /// Default value (as JSON)
    pub default: Option<serde_json::Value>,

    /// Alternate names for deserialization
    pub aliases: Vec<String>,

    /// Whether to flatten this field
    pub flatten: bool,

    /// Whether to skip serialization
    pub skip: bool,

    /// Serialization hints from source
    pub serde_hints: BTreeMap<String, String>,
}

/// Variant-level metadata
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct VariantMetadata {
    /// Documentation string
    pub doc: Option<String>,

    /// Alternate names for deserialization
    pub aliases: Vec<String>,

    /// Serialization hints from source
    pub serde_hints: BTreeMap<String, String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_primitive_sizes() {
        assert_eq!(PrimitiveType::U8.byte_size(), Some(1));
        assert_eq!(PrimitiveType::U64.byte_size(), Some(8));
        assert_eq!(PrimitiveType::String.byte_size(), None);
    }

    #[test]
    fn test_container_inner() {
        let opt = ContainerType::Option(Box::new(IrType::Primitive(PrimitiveType::String)));
        assert!(opt.inner_type().is_some());
    }

    #[test]
    fn test_ir_type_serialization() {
        let ty = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
            PrimitiveType::I32,
        ))));
        let json = serde_json::to_string(&ty).unwrap();
        let parsed: IrType = serde_json::from_str(&json).unwrap();
        assert_eq!(ty, parsed);
    }
}
