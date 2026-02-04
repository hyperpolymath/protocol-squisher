// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! Protocol Squisher - Canonical IR with Linear Types (ephapax)
//!
//! This crate provides the canonical intermediate representation for protocol-squisher,
//! implemented in Idris2 with dependent types and linear type guarantees.
//!
//! ## Architecture
//!
//! - **Types**: IR type system (primitives, containers, composites)
//! - **Compatibility**: Transport class analysis with totality-checked proofs
//! - **Linear Safety**: Zero-copy paths proven safe at compile-time
//! - **Backend**: Idris2 implementation with Rust FFI bindings
//!
//! ## Transport Classes
//!
//! - **Concorde**: Zero-copy, 100% fidelity
//! - **Business**: Minor overhead, 98% fidelity
//! - **Economy**: Moderate overhead, 80% fidelity
//! - **Wheelbarrow**: High overhead (50%), JSON fallback
//!
//! ## The Invariant
//!
//! **"If it compiles, it carries AND cannot crash"**
//!
//! Proven by:
//! - Idris2 totality checking (all cases handled)
//! - Dependent types (types encode proofs)
//! - Linear types (resource safety)

mod ffi;

use std::marker::PhantomData;

/// Primitive types in the IR
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum PrimitiveType {
    I8 = 0,
    I16 = 1,
    I32 = 2,
    I64 = 3,
    I128 = 4,
    U8 = 5,
    U16 = 6,
    U32 = 7,
    U64 = 8,
    U128 = 9,
    F32 = 10,
    F64 = 11,
    Bool = 12,
    Char = 13,
    String = 14,
    Unit = 15,
}

/// Container types in the IR
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContainerType {
    Array,
    Vec,
    Map,
    Set,
    Optional,
}

/// Composite types in the IR
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompositeType {
    Struct,
    Enum,
    Tuple,
}

/// Transport class classification
///
/// Represents the quality of type conversion:
/// - **Concorde**: Perfect match, zero overhead
/// - **Business**: Safe conversion, minor overhead
/// - **Economy**: Lossy conversion, moderate overhead
/// - **Wheelbarrow**: Major incompatibility, high overhead
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum TransportClass {
    /// Zero-copy, 100% fidelity
    Concorde = 100,
    /// Minor overhead, 98% fidelity
    Business = 101,
    /// Moderate overhead, 80% fidelity
    Economy = 102,
    /// High overhead, 50% fidelity (JSON fallback)
    Wheelbarrow = 103,
}

impl TransportClass {
    /// Get fidelity percentage (0-100)
    pub fn fidelity(&self) -> u8 {
        ffi::get_fidelity(*self)
    }

    /// Get overhead percentage (0-100)
    pub fn overhead(&self) -> u8 {
        ffi::get_overhead(*self)
    }
}

/// Canonical IR context (ephapax linear state)
///
/// This context provides access to the Idris2-proven transport class analysis.
pub struct IRContext {
    _phantom: PhantomData<()>,
}

impl IRContext {
    /// Create new IR context
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    /// Analyze compatibility between two primitive types
    ///
    /// Returns the transport class representing the quality of conversion.
    /// This function's correctness is proven by Idris2's totality checker.
    pub fn analyze_compatibility(
        &self,
        source: PrimitiveType,
        target: PrimitiveType,
    ) -> TransportClass {
        ffi::analyze_primitive_compat(source, target)
    }

    /// Get fidelity percentage for a transport class
    pub fn get_fidelity(&self, class: TransportClass) -> u8 {
        class.fidelity()
    }

    /// Get overhead percentage for a transport class
    pub fn get_overhead(&self, class: TransportClass) -> u8 {
        class.overhead()
    }
}

impl Default for IRContext {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_exact_match() {
        let ctx = IRContext::new();
        let class = ctx.analyze_compatibility(PrimitiveType::I32, PrimitiveType::I32);
        assert_eq!(class, TransportClass::Concorde);
        assert_eq!(class.fidelity(), 100);
        assert_eq!(class.overhead(), 0);
    }

    #[test]
    fn test_safe_widening() {
        let ctx = IRContext::new();
        let class = ctx.analyze_compatibility(PrimitiveType::I32, PrimitiveType::I64);
        assert_eq!(class, TransportClass::Business);
        assert_eq!(class.fidelity(), 98);
        assert_eq!(class.overhead(), 5);
    }

    #[test]
    fn test_incompatible() {
        let ctx = IRContext::new();
        let class = ctx.analyze_compatibility(PrimitiveType::I32, PrimitiveType::String);
        assert_eq!(class, TransportClass::Wheelbarrow);
        assert_eq!(class.fidelity(), 50);
        assert_eq!(class.overhead(), 80);
    }

    #[test]
    fn test_float_widening() {
        let ctx = IRContext::new();
        let class = ctx.analyze_compatibility(PrimitiveType::F32, PrimitiveType::F64);
        assert_eq!(class, TransportClass::Business);
    }

    #[test]
    fn test_i128_exact_match() {
        let ctx = IRContext::new();
        let class = ctx.analyze_compatibility(PrimitiveType::I128, PrimitiveType::I128);
        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_i64_to_i128_widening() {
        let ctx = IRContext::new();
        let class = ctx.analyze_compatibility(PrimitiveType::I64, PrimitiveType::I128);
        assert_eq!(class, TransportClass::Business);
    }

    #[test]
    fn test_i32_to_i128_widening() {
        let ctx = IRContext::new();
        let class = ctx.analyze_compatibility(PrimitiveType::I32, PrimitiveType::I128);
        assert_eq!(class, TransportClass::Business);
    }

    #[test]
    fn test_u128_exact_match() {
        let ctx = IRContext::new();
        let class = ctx.analyze_compatibility(PrimitiveType::U128, PrimitiveType::U128);
        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_u64_to_u128_widening() {
        let ctx = IRContext::new();
        let class = ctx.analyze_compatibility(PrimitiveType::U64, PrimitiveType::U128);
        assert_eq!(class, TransportClass::Business);
    }

    #[test]
    fn test_i128_to_i64_narrowing() {
        let ctx = IRContext::new();
        let class = ctx.analyze_compatibility(PrimitiveType::I128, PrimitiveType::I64);
        assert_eq!(class, TransportClass::Wheelbarrow);
    }
}
