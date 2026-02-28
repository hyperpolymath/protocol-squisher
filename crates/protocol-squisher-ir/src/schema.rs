// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Schema utilities and operations
//!
//! Functions for working with IR schemas, including validation,
//! normalization, and comparison.

use crate::{IrSchema, IrType, TypeDef, TypeId};
use std::collections::HashSet;

/// Errors that can occur during schema operations
#[derive(Debug, Clone, PartialEq)]
pub enum SchemaError {
    /// A type reference points to an undefined type
    UndefinedReference {
        type_id: TypeId,
        referenced_by: String,
    },

    /// A root type is not defined
    UndefinedRoot { type_id: TypeId },

    /// Circular type reference detected
    CircularReference { path: Vec<TypeId> },

    /// Duplicate type definition
    DuplicateType { type_id: TypeId },

    /// Invalid schema structure
    InvalidStructure { message: String },
}

impl std::fmt::Display for SchemaError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SchemaError::UndefinedReference {
                type_id,
                referenced_by,
            } => {
                write!(
                    f,
                    "Undefined type reference '{type_id}' in '{referenced_by}'"
                )
            },
            SchemaError::UndefinedRoot { type_id } => {
                write!(f, "Root type '{type_id}' is not defined")
            },
            SchemaError::CircularReference { path } => {
                write!(f, "Circular type reference: {}", path.join(" -> "))
            },
            SchemaError::DuplicateType { type_id } => {
                write!(f, "Duplicate type definition: '{type_id}'")
            },
            SchemaError::InvalidStructure { message } => {
                write!(f, "Invalid schema structure: {message}")
            },
        }
    }
}

impl std::error::Error for SchemaError {}

/// Validate a schema for correctness
pub fn validate_schema(schema: &IrSchema) -> Result<(), Vec<SchemaError>> {
    let mut errors = Vec::new();

    // Check that all roots are defined
    for root in &schema.roots {
        if !schema.types.contains_key(root) {
            errors.push(SchemaError::UndefinedRoot {
                type_id: root.clone(),
            });
        }
    }

    // Check that all type references are valid
    for (type_id, type_def) in &schema.types {
        check_references(type_def, type_id, &schema.types, &mut errors);
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// Check type references within a type definition
fn check_references(
    type_def: &TypeDef,
    context: &str,
    types: &std::collections::BTreeMap<TypeId, TypeDef>,
    errors: &mut Vec<SchemaError>,
) {
    match type_def {
        TypeDef::Struct(s) => {
            for field in &s.fields {
                check_type_references(&field.ty, context, types, errors);
            }
        },
        TypeDef::Enum(e) => {
            for variant in &e.variants {
                if let Some(payload) = &variant.payload {
                    match payload {
                        crate::types::VariantPayload::Tuple(tys) => {
                            for ty in tys {
                                check_type_references(ty, context, types, errors);
                            }
                        },
                        crate::types::VariantPayload::Struct(fields) => {
                            for field in fields {
                                check_type_references(&field.ty, context, types, errors);
                            }
                        },
                    }
                }
            }
        },
        TypeDef::Union(u) => {
            for ty in &u.variants {
                check_type_references(ty, context, types, errors);
            }
        },
        TypeDef::Alias(a) => {
            check_type_references(&a.target, context, types, errors);
        },
        TypeDef::Newtype(n) => {
            check_type_references(&n.inner, context, types, errors);
        },
    }
}

/// Check references within an IrType
fn check_type_references(
    ty: &IrType,
    context: &str,
    types: &std::collections::BTreeMap<TypeId, TypeDef>,
    errors: &mut Vec<SchemaError>,
) {
    match ty {
        IrType::Reference(ref_id) => {
            if !types.contains_key(ref_id) {
                errors.push(SchemaError::UndefinedReference {
                    type_id: ref_id.clone(),
                    referenced_by: context.to_string(),
                });
            }
        },
        IrType::Container(c) => {
            if let Some(inner) = c.inner_type() {
                check_type_references(inner, context, types, errors);
            }
            // Handle Map key type
            if let crate::types::ContainerType::Map(k, v) = c {
                check_type_references(k, context, types, errors);
                check_type_references(v, context, types, errors);
            }
            // Handle Tuple
            if let crate::types::ContainerType::Tuple(tys) = c {
                for t in tys {
                    check_type_references(t, context, types, errors);
                }
            }
            // Handle Result
            if let crate::types::ContainerType::Result(ok, err) = c {
                check_type_references(ok, context, types, errors);
                check_type_references(err, context, types, errors);
            }
        },
        _ => {},
    }
}

/// Get all type IDs referenced by a type
pub fn get_referenced_types(ty: &IrType) -> HashSet<TypeId> {
    let mut refs = HashSet::new();
    collect_references(ty, &mut refs);
    refs
}

fn collect_references(ty: &IrType, refs: &mut HashSet<TypeId>) {
    match ty {
        IrType::Reference(id) => {
            refs.insert(id.clone());
        },
        IrType::Container(c) => match c {
            crate::types::ContainerType::Option(t)
            | crate::types::ContainerType::Vec(t)
            | crate::types::ContainerType::Array(t, _)
            | crate::types::ContainerType::Set(t) => {
                collect_references(t, refs);
            },
            crate::types::ContainerType::Map(k, v) => {
                collect_references(k, refs);
                collect_references(v, refs);
            },
            crate::types::ContainerType::Tuple(tys) => {
                for t in tys {
                    collect_references(t, refs);
                }
            },
            crate::types::ContainerType::Result(ok, err) => {
                collect_references(ok, refs);
                collect_references(err, refs);
            },
        },
        _ => {},
    }
}

/// Calculate the topological order of types (dependencies first)
pub fn topological_sort(schema: &IrSchema) -> Result<Vec<TypeId>, SchemaError> {
    let mut result = Vec::new();
    let mut visited = HashSet::new();
    let mut in_progress = HashSet::new();

    for type_id in schema.types.keys() {
        if !visited.contains(type_id) {
            visit_type(type_id, schema, &mut visited, &mut in_progress, &mut result)?;
        }
    }

    Ok(result)
}

fn visit_type(
    type_id: &TypeId,
    schema: &IrSchema,
    visited: &mut HashSet<TypeId>,
    in_progress: &mut HashSet<TypeId>,
    result: &mut Vec<TypeId>,
) -> Result<(), SchemaError> {
    if in_progress.contains(type_id) {
        return Err(SchemaError::CircularReference {
            path: vec![type_id.clone()],
        });
    }

    if visited.contains(type_id) {
        return Ok(());
    }

    in_progress.insert(type_id.clone());

    if let Some(type_def) = schema.types.get(type_id) {
        let refs = get_type_def_references(type_def);
        for ref_id in refs {
            if schema.types.contains_key(&ref_id) {
                visit_type(&ref_id, schema, visited, in_progress, result)?;
            }
        }
    }

    in_progress.remove(type_id);
    visited.insert(type_id.clone());
    result.push(type_id.clone());

    Ok(())
}

fn get_type_def_references(type_def: &TypeDef) -> HashSet<TypeId> {
    let mut refs = HashSet::new();

    match type_def {
        TypeDef::Struct(s) => {
            for field in &s.fields {
                refs.extend(get_referenced_types(&field.ty));
            }
        },
        TypeDef::Enum(e) => {
            for variant in &e.variants {
                if let Some(payload) = &variant.payload {
                    match payload {
                        crate::types::VariantPayload::Tuple(tys) => {
                            for ty in tys {
                                refs.extend(get_referenced_types(ty));
                            }
                        },
                        crate::types::VariantPayload::Struct(fields) => {
                            for field in fields {
                                refs.extend(get_referenced_types(&field.ty));
                            }
                        },
                    }
                }
            }
        },
        TypeDef::Union(u) => {
            for ty in &u.variants {
                refs.extend(get_referenced_types(ty));
            }
        },
        TypeDef::Alias(a) => {
            refs.extend(get_referenced_types(&a.target));
        },
        TypeDef::Newtype(n) => {
            refs.extend(get_referenced_types(&n.inner));
        },
    }

    refs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::*;

    #[test]
    fn test_validate_empty_schema() {
        let schema = IrSchema::new("empty", "test");
        assert!(validate_schema(&schema).is_ok());
    }

    #[test]
    fn test_validate_undefined_root() {
        let mut schema = IrSchema::new("test", "test");
        schema.add_root("NonExistent".to_string());

        let errors = validate_schema(&schema).unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(matches!(errors[0], SchemaError::UndefinedRoot { .. }));
    }

    #[test]
    fn test_validate_undefined_reference() {
        let mut schema = IrSchema::new("test", "test");

        let type_def = TypeDef::Struct(StructDef {
            name: "Test".to_string(),
            fields: vec![FieldDef {
                name: "field".to_string(),
                ty: IrType::Reference("Unknown".to_string()),
                optional: false,
                constraints: vec![],
                metadata: FieldMetadata::default(),
            }],
            metadata: TypeMetadata::default(),
        });

        schema.add_type("Test".to_string(), type_def);

        let errors = validate_schema(&schema).unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(matches!(errors[0], SchemaError::UndefinedReference { .. }));
    }
}
