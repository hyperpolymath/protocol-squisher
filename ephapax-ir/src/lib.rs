// SPDX-License-Identifier: PMPL-1.0-or-later
//! FFI wrapper for ephapax IR compiled to WASM
//!
//! This crate provides a Rust interface to the ephapax-based canonical IR
//! for protocol-squisher. The IR is written in ephapax and compiled to WASM,
//! then called via FFI from Rust analyzers and generators.

use anyhow::{Context, Result};
use std::sync::Arc;

/// Handle to the ephapax IR WASM runtime
pub struct IRContext {
    // TODO: Initialize wasmtime runtime when ephapax compilation is ready
    // For now, this is a stub that will be filled in once ephapax is mature
    _phantom: std::marker::PhantomData<()>,
}

impl IRContext {
    /// Create a new IR context (loads compiled ephapax WASM modules)
    pub fn new() -> Result<Self> {
        // TODO: Load ephapax IR WASM modules
        // let types_wasm = include_bytes!(concat!(env!("OUT_DIR"), "/types.wasm"));
        // let compat_wasm = include_bytes!(concat!(env!("OUT_DIR"), "/compat.wasm"));

        println!("IR Context: ephapax compilation not yet available, using stub");

        Ok(Self {
            _phantom: std::marker::PhantomData,
        })
    }
}

impl Default for IRContext {
    fn default() -> Self {
        Self::new().expect("Failed to create IR context")
    }
}

/// Primitive types in the IR
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Primitive {
    I8, I16, I32, I64,
    U8, U16, U32, U64,
    F32, F64,
    Bool,
    Char,
    String,
    Unit,
}

/// Transport class classification
#[derive(Debug, Clone, PartialEq)]
pub enum TransportClass {
    /// Zero-copy, full fidelity, maximum performance
    Concorde {
        fidelity: u8,
        overhead: f32,
    },
    /// Minor overhead, full fidelity
    Business {
        fidelity: u8,
        overhead: f32,
    },
    /// Moderate overhead, documented losses
    Economy {
        fidelity: u8,
        overhead: f32,
        losses: Vec<String>,
    },
    /// High overhead, significant losses, but works
    Wheelbarrow {
        fidelity: u8,
        overhead: f32,
        losses: Vec<String>,
        fallback: String,
    },
}

/// Compatibility analysis result
#[derive(Debug, Clone)]
pub struct CompatibilityResult {
    pub source_type: String,
    pub target_type: String,
    pub transport_class: TransportClass,
    pub conversion_path: Vec<String>,
    pub guarantees: Vec<String>,
}

/// IR type representation (mirrors ephapax types.eph)
#[derive(Debug, Clone)]
pub enum IRType {
    Prim(Primitive),
    Vec(Box<IRType>),
    Map(Box<IRType>, Box<IRType>),
    Optional(Box<IRType>),
    Struct(Vec<FieldDef>),
    Enum(Vec<VariantDef>),
}

/// Field definition for struct types
#[derive(Debug, Clone)]
pub struct FieldDef {
    pub name: String,
    pub ty: IRType,
    pub required: bool,
}

/// Variant definition for enum types
#[derive(Debug, Clone)]
pub struct VariantDef {
    pub name: String,
    pub payload: IRType,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ir_context_creation() {
        let ctx = IRContext::new();
        assert!(ctx.is_ok(), "Should create IR context stub");
    }

    #[test]
    fn test_primitive_types() {
        let i32_ty = IRType::Prim(Primitive::I32);
        matches!(i32_ty, IRType::Prim(Primitive::I32));
    }

    #[test]
    fn test_transport_class_construction() {
        let concorde = TransportClass::Concorde {
            fidelity: 100,
            overhead: 0.0,
        };

        match concorde {
            TransportClass::Concorde { fidelity, overhead } => {
                assert_eq!(fidelity, 100);
                assert_eq!(overhead, 0.0);
            },
            _ => panic!("Expected Concorde class"),
        }
    }
}
