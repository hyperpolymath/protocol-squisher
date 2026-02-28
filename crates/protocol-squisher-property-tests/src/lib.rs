// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Property-based tests for protocol-squisher
//!
//! Tests invariants across all type combinations using proptest.

#![cfg(test)]

pub mod container_combinations;
pub mod edge_cases;
pub mod primitive_matrix;

use protocol_squisher_compat::EphapaxCompatibilityEngine;
use protocol_squisher_ir::*;
use protocol_squisher_transport_primitives::TransportClass;
use std::collections::BTreeMap;

/// Helper to create a simple schema with one field
pub fn make_schema(field_type: IrType) -> IrSchema {
    let field = FieldDef {
        name: "value".to_string(),
        ty: field_type,
        optional: false,
        constraints: vec![],
        metadata: FieldMetadata::default(),
    };

    let struct_def = StructDef {
        name: "TestStruct".to_string(),
        fields: vec![field],
        metadata: TypeMetadata::default(),
    };

    let mut types = BTreeMap::new();
    types.insert("TestStruct".to_string(), TypeDef::Struct(struct_def));

    IrSchema {
        name: "test-schema".to_string(),
        version: "1.0.0".to_string(),
        source_format: "test".to_string(),
        types,
        roots: vec!["TestStruct".to_string()],
        metadata: SchemaMetadata::default(),
    }
}

/// Analyze transport class for a type pair
pub fn analyze_transport_class(source: IrType, target: IrType) -> TransportClass {
    let source_schema = make_schema(source);
    let target_schema = make_schema(target);

    let engine = EphapaxCompatibilityEngine::new();
    let result = engine.analyze_schemas(&source_schema, &target_schema);

    result.overall_class
}

/// Check if a type conversion should be Concorde (zero-copy)
pub fn is_concorde(source: &PrimitiveType, target: &PrimitiveType) -> bool {
    source == target
}

/// Check if a type conversion should be Business (safe widening)
///
/// Matches the actual ephapax-ir implementation in ffi.rs
pub fn is_business(source: &PrimitiveType, target: &PrimitiveType) -> bool {
    use PrimitiveType::*;

    matches!(
        (source, target),
        // Signed integer widening
        (I8, I16 | I32 | I64 | I128)
            | (I16, I32 | I64 | I128)
            | (I32, I64 | I128)
            | (I64, I128)
            // Unsigned integer widening
            | (U8, U16 | U32 | U64 | U128)
            | (U16, U32 | U64 | U128)
            | (U32, U64 | U128)
            | (U64, U128)
            // Float widening
            | (F32, F64)
    )
}

/// Check if a type conversion should be Wheelbarrow (narrowing/lossy)
///
/// Everything that's not Concorde or Business is Wheelbarrow in the current implementation
pub fn is_wheelbarrow(source: &PrimitiveType, target: &PrimitiveType) -> bool {
    !is_concorde(source, target) && !is_business(source, target)
}
