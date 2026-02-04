// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! FFI bindings to Idris2 ephapax IR
//!
//! This module provides Rust bindings to the Idris2-compiled ephapax IR.
//! The Idris2 code provides proven-correct transport class analysis.

use crate::{PrimitiveType, TransportClass};

// TODO: These will link to the Idris2 refc-generated C library once we have
// the Idris2 runtime properly set up. For now, we use pure Rust implementations
// that match the Idris2 semantics.

/// Analyze compatibility between two primitive types
///
/// Returns the transport class (as integer):
/// - 100: Concorde (zero-copy)
/// - 101: Business (minor overhead)
/// - 102: Economy (moderate overhead)
/// - 103: Wheelbarrow (JSON fallback)
pub fn analyze_primitive_compat(source: PrimitiveType, target: PrimitiveType) -> TransportClass {
    if source == target {
        TransportClass::Concorde
    } else if is_safe_widening(source, target) {
        TransportClass::Business
    } else {
        TransportClass::Wheelbarrow
    }
}

/// Check if widening conversion is safe
fn is_safe_widening(source: PrimitiveType, target: PrimitiveType) -> bool {
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

/// Get fidelity percentage for a transport class
pub fn get_fidelity(class: TransportClass) -> u8 {
    match class {
        TransportClass::Concorde => 100,
        TransportClass::Business => 98,
        TransportClass::Economy => 80,
        TransportClass::Wheelbarrow => 50,
    }
}

/// Get overhead percentage for a transport class
pub fn get_overhead(class: TransportClass) -> u8 {
    match class {
        TransportClass::Concorde => 0,
        TransportClass::Business => 5,
        TransportClass::Economy => 25,
        TransportClass::Wheelbarrow => 80,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_exact_match() {
        assert_eq!(
            analyze_primitive_compat(PrimitiveType::I32, PrimitiveType::I32),
            TransportClass::Concorde
        );
    }

    #[test]
    fn test_safe_widening() {
        assert_eq!(
            analyze_primitive_compat(PrimitiveType::I32, PrimitiveType::I64),
            TransportClass::Business
        );
    }

    #[test]
    fn test_incompatible() {
        assert_eq!(
            analyze_primitive_compat(PrimitiveType::I32, PrimitiveType::String),
            TransportClass::Wheelbarrow
        );
    }

    #[test]
    fn test_fidelity() {
        assert_eq!(get_fidelity(TransportClass::Concorde), 100);
        assert_eq!(get_fidelity(TransportClass::Business), 98);
        assert_eq!(get_fidelity(TransportClass::Economy), 80);
        assert_eq!(get_fidelity(TransportClass::Wheelbarrow), 50);
    }

    #[test]
    fn test_overhead() {
        assert_eq!(get_overhead(TransportClass::Concorde), 0);
        assert_eq!(get_overhead(TransportClass::Business), 5);
        assert_eq!(get_overhead(TransportClass::Economy), 25);
        assert_eq!(get_overhead(TransportClass::Wheelbarrow), 80);
    }
}
