// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Container combination tests
//!
//! Tests nested and combined container types

use crate::*;
use proptest::prelude::*;
use protocol_squisher_ir::{ContainerType, IrType, PrimitiveType};

proptest! {
    /// Property: Option<T> where T is Concorde → Option<T> is also Concorde
    #[test]
    fn prop_option_preserves_concorde(
        prim in prop::sample::select(&[
            PrimitiveType::I64, PrimitiveType::F64, PrimitiveType::String, PrimitiveType::Bool
        ])
    ) {
        let inner_type = IrType::Primitive(prim);
        let source = IrType::Container(ContainerType::Option(Box::new(inner_type.clone())));
        let target = IrType::Container(ContainerType::Option(Box::new(inner_type)));

        let class = analyze_transport_class(source, target);

        prop_assert_eq!(class, TransportClass::Concorde,
            "Option<{:?}> should preserve Concorde class", prim);
    }

    /// Property: Vec<T> where T is Concorde → Vec<T> has at least Business class
    #[test]
    fn prop_vec_of_concorde_is_at_least_business(
        prim in prop::sample::select(&[
            PrimitiveType::I64, PrimitiveType::F64, PrimitiveType::String
        ])
    ) {
        let inner_type = IrType::Primitive(prim);
        let source = IrType::Container(ContainerType::Vec(Box::new(inner_type.clone())));
        let target = IrType::Container(ContainerType::Vec(Box::new(inner_type)));

        let class = analyze_transport_class(source, target);

        prop_assert!(
            class == TransportClass::Concorde || class == TransportClass::Business,
            "Vec<{:?}> should be Concorde or Business, got {:?}", prim, class
        );
    }
}

#[test]
fn test_option_i64() {
    let source = IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
        PrimitiveType::I64,
    ))));
    let target = source.clone();

    let class = analyze_transport_class(source, target);
    assert_eq!(class, TransportClass::Concorde);
}

#[test]
fn test_option_narrowing() {
    let source = IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
        PrimitiveType::I64,
    ))));
    let target = IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
        PrimitiveType::I32,
    ))));

    let class = analyze_transport_class(source, target);
    assert_eq!(class, TransportClass::Wheelbarrow);
}

#[test]
fn test_vec_i64() {
    let source = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
        PrimitiveType::I64,
    ))));
    let target = source.clone();

    let class = analyze_transport_class(source, target);
    // Vec conversion requires some overhead even if element is Concorde
    assert!(
        class == TransportClass::Concorde || class == TransportClass::Business,
        "Vec<i64> should be Concorde or Business, got {:?}",
        class
    );
}

#[test]
fn test_vec_narrowing() {
    let source = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
        PrimitiveType::I64,
    ))));
    let target = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
        PrimitiveType::I32,
    ))));

    let class = analyze_transport_class(source, target);
    // Element narrowing propagates to container
    assert_eq!(class, TransportClass::Wheelbarrow);
}

#[test]
fn test_nested_option_vec() {
    // Option<Vec<i64>>
    let inner = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
        PrimitiveType::I64,
    ))));
    let source = IrType::Container(ContainerType::Option(Box::new(inner.clone())));
    let target = IrType::Container(ContainerType::Option(Box::new(inner)));

    let class = analyze_transport_class(source, target);
    assert!(
        class == TransportClass::Concorde || class == TransportClass::Business,
        "Option<Vec<i64>> should be Concorde or Business"
    );
}

#[test]
fn test_nested_vec_option() {
    // Vec<Option<i64>>
    let inner = IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
        PrimitiveType::I64,
    ))));
    let source = IrType::Container(ContainerType::Vec(Box::new(inner.clone())));
    let target = IrType::Container(ContainerType::Vec(Box::new(inner)));

    let class = analyze_transport_class(source, target);
    assert!(
        class == TransportClass::Concorde || class == TransportClass::Business,
        "Vec<Option<i64>> should be Concorde or Business"
    );
}

#[test]
fn test_vec_vec() {
    // Vec<Vec<i64>>
    let inner_vec = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
        PrimitiveType::I64,
    ))));
    let source = IrType::Container(ContainerType::Vec(Box::new(inner_vec.clone())));
    let target = IrType::Container(ContainerType::Vec(Box::new(inner_vec)));

    let class = analyze_transport_class(source, target);
    assert!(
        class == TransportClass::Concorde || class == TransportClass::Business,
        "Vec<Vec<i64>> should be Concorde or Business"
    );
}

#[test]
fn test_hashmap_string_i64() {
    let source = IrType::Container(ContainerType::Map(
        Box::new(IrType::Primitive(PrimitiveType::String)),
        Box::new(IrType::Primitive(PrimitiveType::I64)),
    ));
    let target = source.clone();

    let class = analyze_transport_class(source, target);
    assert!(
        class == TransportClass::Concorde || class == TransportClass::Business,
        "HashMap<String, i64> should be Concorde or Business"
    );
}

#[test]
fn test_hashmap_with_narrowing_value() {
    let source = IrType::Container(ContainerType::Map(
        Box::new(IrType::Primitive(PrimitiveType::String)),
        Box::new(IrType::Primitive(PrimitiveType::I64)),
    ));
    let target = IrType::Container(ContainerType::Map(
        Box::new(IrType::Primitive(PrimitiveType::String)),
        Box::new(IrType::Primitive(PrimitiveType::I32)),
    ));

    let class = analyze_transport_class(source, target);
    // Value narrowing propagates
    assert_eq!(class, TransportClass::Wheelbarrow);
}

#[test]
fn test_tuple_i64_string() {
    let source = IrType::Container(ContainerType::Tuple(vec![
        IrType::Primitive(PrimitiveType::I64),
        IrType::Primitive(PrimitiveType::String),
    ]));
    let target = source.clone();

    let class = analyze_transport_class(source, target);
    assert!(
        class == TransportClass::Concorde || class == TransportClass::Business,
        "(i64, String) should be Concorde or Business"
    );
}

#[test]
fn test_tuple_with_narrowing() {
    let source = IrType::Container(ContainerType::Tuple(vec![
        IrType::Primitive(PrimitiveType::I64),
        IrType::Primitive(PrimitiveType::String),
    ]));
    let target = IrType::Container(ContainerType::Tuple(vec![
        IrType::Primitive(PrimitiveType::I32), // Narrowing!
        IrType::Primitive(PrimitiveType::String),
    ]));

    let class = analyze_transport_class(source, target);
    assert_eq!(class, TransportClass::Wheelbarrow);
}

#[test]
fn test_complex_nested() {
    // Option<HashMap<String, Vec<i64>>>
    let vec_i64 = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
        PrimitiveType::I64,
    ))));
    let map = IrType::Container(ContainerType::Map(
        Box::new(IrType::Primitive(PrimitiveType::String)),
        Box::new(vec_i64),
    ));
    let source = IrType::Container(ContainerType::Option(Box::new(map.clone())));
    let target = IrType::Container(ContainerType::Option(Box::new(map)));

    let class = analyze_transport_class(source, target);
    assert!(
        class == TransportClass::Concorde || class == TransportClass::Business,
        "Complex nested type should be Concorde or Business"
    );
}
