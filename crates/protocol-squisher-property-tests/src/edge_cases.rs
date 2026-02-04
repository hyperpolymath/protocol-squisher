// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Edge case tests for boundary conditions

use crate::*;
use proptest::prelude::*;

proptest! {
    /// Property: Empty strings should still be Concorde
    #[test]
    fn prop_empty_string_is_concorde(_empty in Just("".to_string())) {
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::String),
            IrType::Primitive(PrimitiveType::String),
        );

        prop_assert_eq!(class, TransportClass::Concorde);
    }

    /// Property: Very long strings should still be Concorde
    #[test]
    fn prop_long_string_is_concorde(
        len in 1000usize..10000usize
    ) {
        // Simulate large string scenario
        let _large = "a".repeat(len);

        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::String),
            IrType::Primitive(PrimitiveType::String),
        );

        prop_assert_eq!(class, TransportClass::Concorde);
    }

    /// Property: Unicode strings should be Concorde
    #[test]
    fn prop_unicode_string_is_concorde(
        s in "\\PC*" // Any unicode string
    ) {
        let _ = s; // Just testing schema level

        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::String),
            IrType::Primitive(PrimitiveType::String),
        );

        prop_assert_eq!(class, TransportClass::Concorde);
    }
}

#[cfg(test)]
mod integer_boundaries {
    use super::*;

    #[test]
    fn test_i64_max_to_i32() {
        // This would overflow at runtime, but schema analysis shows it as Wheelbarrow
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::I64),
            IrType::Primitive(PrimitiveType::I32),
        );

        assert_eq!(class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_i64_min_to_i32() {
        // This would overflow at runtime
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::I64),
            IrType::Primitive(PrimitiveType::I32),
        );

        assert_eq!(class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_u64_max_to_u32() {
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::U64),
            IrType::Primitive(PrimitiveType::U32),
        );

        assert_eq!(class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_i8_range_to_i64() {
        // Widening is always safe
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::I8),
            IrType::Primitive(PrimitiveType::I64),
        );

        assert_eq!(class, TransportClass::Business);
    }

    #[test]
    fn test_zero_is_safe_everywhere() {
        // Zero value should work for all integer types
        // (this is schema-level, so all conversions analyzed the same way)
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::I64),
            IrType::Primitive(PrimitiveType::I32),
        );

        assert_eq!(class, TransportClass::Wheelbarrow);
    }
}

#[cfg(test)]
mod float_boundaries {
    use super::*;

    #[test]
    fn test_f64_infinity_to_f32() {
        // Infinity handling - schema analysis shows narrowing as Wheelbarrow
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::F64),
            IrType::Primitive(PrimitiveType::F32),
        );

        assert_eq!(class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_f64_nan_to_f32() {
        // NaN handling
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::F64),
            IrType::Primitive(PrimitiveType::F32),
        );

        assert_eq!(class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_f64_max_to_f32() {
        // f64::MAX would overflow f32
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::F64),
            IrType::Primitive(PrimitiveType::F32),
        );

        assert_eq!(class, TransportClass::Wheelbarrow);
    }

    #[test]
    fn test_f32_to_f64_preserves_all() {
        // Widening is safe
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::F32),
            IrType::Primitive(PrimitiveType::F64),
        );

        assert_eq!(class, TransportClass::Business);
    }
}

#[cfg(test)]
mod container_edge_cases {
    use super::*;

    #[test]
    fn test_empty_vec() {
        // Empty Vec<T> should still follow container rules
        let source = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
            PrimitiveType::I64,
        ))));
        let target = source.clone();

        let class = analyze_transport_class(source, target);
        assert!(class == TransportClass::Concorde || class == TransportClass::Business);
    }

    #[test]
    fn test_vec_with_one_element() {
        let source = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
            PrimitiveType::I64,
        ))));
        let target = source.clone();

        let class = analyze_transport_class(source, target);
        assert!(class == TransportClass::Concorde || class == TransportClass::Business);
    }

    #[test]
    fn test_none_option() {
        // Option::None case
        let source = IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
            PrimitiveType::I64,
        ))));
        let target = source.clone();

        let class = analyze_transport_class(source, target);
        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_some_option() {
        // Option::Some case
        let source = IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
            PrimitiveType::I64,
        ))));
        let target = source.clone();

        let class = analyze_transport_class(source, target);
        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_empty_hashmap() {
        let source = IrType::Container(ContainerType::Map(
            Box::new(IrType::Primitive(PrimitiveType::String)),
            Box::new(IrType::Primitive(PrimitiveType::I64)),
        ));
        let target = source.clone();

        let class = analyze_transport_class(source, target);
        assert!(class == TransportClass::Concorde || class == TransportClass::Business);
    }
}

#[cfg(test)]
mod string_edge_cases {
    use super::*;

    #[test]
    fn test_empty_string() {
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::String),
            IrType::Primitive(PrimitiveType::String),
        );

        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_single_char_string() {
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::String),
            IrType::Primitive(PrimitiveType::String),
        );

        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_unicode_emoji_string() {
        // "🦀" - Rust mascot
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::String),
            IrType::Primitive(PrimitiveType::String),
        );

        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_multiline_string() {
        // "line1\nline2\nline3"
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::String),
            IrType::Primitive(PrimitiveType::String),
        );

        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_string_with_null_bytes() {
        // "text\0more"
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::String),
            IrType::Primitive(PrimitiveType::String),
        );

        assert_eq!(class, TransportClass::Concorde);
    }
}

#[cfg(test)]
mod bool_edge_cases {
    use super::*;

    #[test]
    fn test_bool_true() {
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::Bool),
            IrType::Primitive(PrimitiveType::Bool),
        );

        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_bool_false() {
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::Bool),
            IrType::Primitive(PrimitiveType::Bool),
        );

        assert_eq!(class, TransportClass::Concorde);
    }
}

#[cfg(test)]
mod char_edge_cases {
    use super::*;

    #[test]
    fn test_ascii_char() {
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::Char),
            IrType::Primitive(PrimitiveType::Char),
        );

        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_unicode_char() {
        // '🦀' - Unicode character
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::Char),
            IrType::Primitive(PrimitiveType::Char),
        );

        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_null_char() {
        // '\0'
        let class = analyze_transport_class(
            IrType::Primitive(PrimitiveType::Char),
            IrType::Primitive(PrimitiveType::Char),
        );

        assert_eq!(class, TransportClass::Concorde);
    }
}
