// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! # Protocol Squisher Intermediate Representation
//!
//! The canonical IR is the heart of protocol-squisher. Every serialization
//! format maps to this common representation, enabling universal compatibility
//! analysis and adapter synthesis.
//!
//! ## Design Principles
//!
//! 1. **Language-agnostic**: No assumptions about source/target languages
//! 2. **Semantic preservation**: Captures meaning, not just structure
//! 3. **Constraint-aware**: Represents validation rules and invariants
//! 4. **Serializable**: IR itself can be stored/transmitted as JSON

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub mod constraints;
pub mod schema;
pub mod types;

pub use constraints::*;
pub use schema::*;
pub use types::*;

/// Unique identifier for types within a schema
pub type TypeId = String;

/// Unique identifier for fields within a type
pub type FieldId = String;

/// The root IR structure representing a complete schema
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct IrSchema {
    /// Schema name/identifier
    pub name: String,

    /// Schema version (semver)
    pub version: String,

    /// Source format (e.g., "rust-serde", "python-pydantic", "protobuf")
    pub source_format: String,

    /// All type definitions in this schema
    pub types: BTreeMap<TypeId, TypeDef>,

    /// Root/entry types (types that can be serialized directly)
    pub roots: Vec<TypeId>,

    /// Schema-level metadata
    pub metadata: SchemaMetadata,
}

impl IrSchema {
    /// Create a new empty schema
    pub fn new(name: impl Into<String>, source_format: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            version: "0.1.0".to_string(),
            source_format: source_format.into(),
            types: BTreeMap::new(),
            roots: Vec::new(),
            metadata: SchemaMetadata::default(),
        }
    }

    /// Add a type definition to the schema
    pub fn add_type(&mut self, id: TypeId, def: TypeDef) {
        self.types.insert(id, def);
    }

    /// Mark a type as a root type
    pub fn add_root(&mut self, id: TypeId) {
        if !self.roots.contains(&id) {
            self.roots.push(id);
        }
    }

    /// Serialize to JSON
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Deserialize from JSON
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }
}

/// Schema-level metadata
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct SchemaMetadata {
    /// Human-readable description
    pub description: Option<String>,

    /// Documentation URL
    pub docs_url: Option<String>,

    /// Original source file path
    pub source_path: Option<String>,

    /// Additional key-value metadata
    pub extra: BTreeMap<String, String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_schema_creation() {
        let mut schema = IrSchema::new("test-schema", "rust-serde");

        let user_type = TypeDef::Struct(StructDef {
            name: "User".to_string(),
            fields: vec![
                FieldDef {
                    name: "id".to_string(),
                    ty: IrType::Primitive(PrimitiveType::U64),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                },
                FieldDef {
                    name: "name".to_string(),
                    ty: IrType::Primitive(PrimitiveType::String),
                    optional: false,
                    constraints: vec![Constraint::MinLength(1)],
                    metadata: FieldMetadata::default(),
                },
            ],
            metadata: TypeMetadata::default(),
        });

        schema.add_type("User".to_string(), user_type);
        schema.add_root("User".to_string());

        assert_eq!(schema.types.len(), 1);
        assert_eq!(schema.roots.len(), 1);
    }

    #[test]
    fn test_json_roundtrip() {
        let schema = IrSchema::new("roundtrip-test", "json");
        let json = schema.to_json().unwrap();
        let parsed = IrSchema::from_json(&json).unwrap();
        assert_eq!(schema, parsed);
    }
}
