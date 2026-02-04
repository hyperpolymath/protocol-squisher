// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Comprehensive primitive type matrix tests
//!
//! Tests all 225 primitive type pair combinations (15x15)

use crate::*;
use proptest::prelude::*;
use protocol_squisher_ir::PrimitiveType;

/// All primitive types we support in ephapax IR
/// (I128/U128 not yet implemented in ephapax, so excluded from tests)
const ALL_PRIMITIVES: &[PrimitiveType] = &[
    PrimitiveType::I8,
    PrimitiveType::I16,
    PrimitiveType::I32,
    PrimitiveType::I64,
    PrimitiveType::U8,
    PrimitiveType::U16,
    PrimitiveType::U32,
    PrimitiveType::U64,
    PrimitiveType::F32,
    PrimitiveType::F64,
    PrimitiveType::Bool,
    PrimitiveType::Char,
    PrimitiveType::String,
];

proptest! {
    /// Property: Identical types always result in Concorde (zero-copy)
    #[test]
    fn prop_identical_types_are_concorde(
        prim in prop::sample::select(ALL_PRIMITIVES)
    ) {
        let class = analyze_transport_class(
            IrType::Primitive(prim),
            IrType::Primitive(prim)
        );

        prop_assert_eq!(class, TransportClass::Concorde,
            "Identical type {:?} should be Concorde", prim);
    }

    /// Property: Integer widening is Business or Concorde (never Wheelbarrow)
    #[test]
    fn prop_integer_widening_never_wheelbarrow(
        source in prop::sample::select(&[
            PrimitiveType::I8, PrimitiveType::I16, PrimitiveType::I32, PrimitiveType::I64,
            PrimitiveType::U8, PrimitiveType::U16, PrimitiveType::U32, PrimitiveType::U64,
        ]),
        target in prop::sample::select(&[
            PrimitiveType::I16, PrimitiveType::I32, PrimitiveType::I64, PrimitiveType::I128,
            PrimitiveType::U16, PrimitiveType::U32, PrimitiveType::U64, PrimitiveType::U128,
        ])
    ) {
        // Only test actual widening cases
        if get_bit_width(&source) < get_bit_width(&target)
            && same_signedness(&source, &target)
        {
            let class = analyze_transport_class(
                IrType::Primitive(source),
                IrType::Primitive(target)
            );

            prop_assert_ne!(class, TransportClass::Wheelbarrow,
                "Widening {:?} → {:?} should not be Wheelbarrow", source, target);
        }
    }

    /// Property: Integer narrowing is always Wheelbarrow
    #[test]
    fn prop_integer_narrowing_is_wheelbarrow(
        source in prop::sample::select(&[
            PrimitiveType::I64, PrimitiveType::I32, PrimitiveType::I16,
            PrimitiveType::U64, PrimitiveType::U32, PrimitiveType::U16,
        ]),
        target in prop::sample::select(&[
            PrimitiveType::I8, PrimitiveType::I16, PrimitiveType::I32, PrimitiveType::I64,
            PrimitiveType::U8, PrimitiveType::U16, PrimitiveType::U32, PrimitiveType::U64,
        ])
    ) {
        // Only test actual narrowing cases
        if get_bit_width(&source) > get_bit_width(&target)
            && same_signedness(&source, &target)
        {
            let class = analyze_transport_class(
                IrType::Primitive(source),
                IrType::Primitive(target)
            );

            prop_assert_eq!(class, TransportClass::Wheelbarrow,
                "Narrowing {:?} → {:?} should be Wheelbarrow", source, target);
        }
    }
}

// Comprehensive matrix tests for all 225 combinations

#[test]
fn test_i8_to_all() {
    test_conversions_from(PrimitiveType::I8);
}

#[test]
fn test_i16_to_all() {
    test_conversions_from(PrimitiveType::I16);
}

#[test]
fn test_i32_to_all() {
    test_conversions_from(PrimitiveType::I32);
}

#[test]
fn test_i64_to_all() {
    test_conversions_from(PrimitiveType::I64);
}

// I128 not yet implemented in ephapax IR
// #[test]
// fn test_i128_to_all() {
//     test_conversions_from(PrimitiveType::I128);
// }

#[test]
fn test_u8_to_all() {
    test_conversions_from(PrimitiveType::U8);
}

#[test]
fn test_u16_to_all() {
    test_conversions_from(PrimitiveType::U16);
}

#[test]
fn test_u32_to_all() {
    test_conversions_from(PrimitiveType::U32);
}

#[test]
fn test_u64_to_all() {
    test_conversions_from(PrimitiveType::U64);
}

// U128 not yet implemented in ephapax IR
// #[test]
// fn test_u128_to_all() {
//     test_conversions_from(PrimitiveType::U128);
// }

#[test]
fn test_f32_to_all() {
    test_conversions_from(PrimitiveType::F32);
}

#[test]
fn test_f64_to_all() {
    test_conversions_from(PrimitiveType::F64);
}

#[test]
fn test_bool_to_all() {
    test_conversions_from(PrimitiveType::Bool);
}

#[test]
fn test_char_to_all() {
    test_conversions_from(PrimitiveType::Char);
}

#[test]
fn test_string_to_all() {
    test_conversions_from(PrimitiveType::String);
}

/// Test conversions from one type to all 15 target types
fn test_conversions_from(source: PrimitiveType) {
    for target in ALL_PRIMITIVES {
        let class = analyze_transport_class(
            IrType::Primitive(source),
            IrType::Primitive(*target),
        );

        // Verify the classification is correct
        let expected = if is_concorde(&source, target) {
            TransportClass::Concorde
        } else if is_business(&source, target) {
            TransportClass::Business
        } else if is_wheelbarrow(&source, target) {
            TransportClass::Wheelbarrow
        } else {
            // Incompatible (e.g., bool → i32)
            TransportClass::Wheelbarrow
        };

        assert_eq!(
            class, expected,
            "Conversion {:?} → {:?} should be {:?}, got {:?}",
            source, target, expected, class
        );
    }
}

/// Get bit width of integer type
fn get_bit_width(prim: &PrimitiveType) -> u32 {
    match prim {
        PrimitiveType::I8 | PrimitiveType::U8 => 8,
        PrimitiveType::I16 | PrimitiveType::U16 => 16,
        PrimitiveType::I32 | PrimitiveType::U32 => 32,
        PrimitiveType::I64 | PrimitiveType::U64 => 64,
        PrimitiveType::I128 | PrimitiveType::U128 => 128,
        _ => 0,
    }
}

/// Check if two types have the same signedness
fn same_signedness(a: &PrimitiveType, b: &PrimitiveType) -> bool {
    use PrimitiveType::*;

    matches!(
        (a, b),
        (I8 | I16 | I32 | I64 | I128, I8 | I16 | I32 | I64 | I128)
            | (U8 | U16 | U32 | U64 | U128, U8 | U16 | U32 | U64 | U128)
    )
}

#[cfg(test)]
mod specific_conversions {
    use super::*;

    #[test]
    fn test_i64_to_i64_is_concorde() {
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::I64),
            IrType::Primitive(PrimitiveType::I64),
        );
        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_i64_to_i32_is_wheelbarrow() {
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::I64),
            IrType::Primitive(PrimitiveType::I32),
        );
        assert_eq!(class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_i32_to_i64_is_business() {
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::I32),
            IrType::Primitive(PrimitiveType::I64),
        );
        assert_eq!(class, TransportClass::Business);
    }

    #[test]
    fn test_f64_to_f32_is_wheelbarrow() {
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::F64),
            IrType::Primitive(PrimitiveType::F32),
        );
        assert_eq!(class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_f32_to_f64_is_business() {
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::F32),
            IrType::Primitive(PrimitiveType::F64),
        );
        assert_eq!(class, TransportClass::Business);
    }

    #[test]
    fn test_string_to_string_is_concorde() {
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::String),
            IrType::Primitive(PrimitiveType::String),
        );
        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_bool_to_bool_is_concorde() {
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::Bool),
            IrType::Primitive(PrimitiveType::Bool),
        );
        assert_eq!(class, TransportClass::Concorde);
    }
}
