// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Tests for Shape construction, equality, and display.

use crate::*;

#[test]
fn unit_is_empty() {
    assert!(Shape::Unit.is_empty());
}

#[test]
fn atom_is_not_empty() {
    assert!(!Shape::Atom(AtomKind::I32).is_empty());
}

#[test]
fn struct_from_builds_right_nested_product() {
    let shape = Shape::struct_from(vec![
        ("x", Shape::Atom(AtomKind::I32)),
        ("y", Shape::Atom(AtomKind::I64)),
    ]);

    // Should be Product("x", I32, Product("y", I64, Unit))
    match &shape {
        Shape::Product { label, left, right } => {
            assert_eq!(label.name, "x");
            assert_eq!(**left, Shape::Atom(AtomKind::I32));
            match right.as_ref() {
                Shape::Product { label, left, right } => {
                    assert_eq!(label.name, "y");
                    assert_eq!(**left, Shape::Atom(AtomKind::I64));
                    assert_eq!(**right, Shape::Unit);
                },
                other => panic!("Expected inner Product, got {:?}", other),
            }
        },
        other => panic!("Expected Product, got {:?}", other),
    }
}

#[test]
fn enum_from_builds_right_nested_sum() {
    let shape = Shape::enum_from(vec![("A", Shape::Atom(AtomKind::I32)), ("B", Shape::Unit)]);

    match &shape {
        Shape::Sum { label, left, right } => {
            assert_eq!(label.name, "A");
            assert_eq!(**left, Shape::Atom(AtomKind::I32));
            match right.as_ref() {
                Shape::Sum { label, left, right } => {
                    assert_eq!(label.name, "B");
                    assert_eq!(**left, Shape::Unit);
                    assert_eq!(**right, Shape::Unit);
                },
                other => panic!("Expected inner Sum, got {:?}", other),
            }
        },
        other => panic!("Expected Sum, got {:?}", other),
    }
}

#[test]
fn field_labels_collects_from_product_chain() {
    let shape = Shape::struct_from(vec![
        ("a", Shape::Atom(AtomKind::Bool)),
        ("b", Shape::Atom(AtomKind::String)),
        ("c", Shape::Atom(AtomKind::I32)),
    ]);
    let labels: Vec<&str> = shape
        .field_labels()
        .iter()
        .map(|l| l.name.as_str())
        .collect();
    assert_eq!(labels, vec!["a", "b", "c"]);
}

#[test]
fn strip_annotations_removes_all_layers() {
    let inner = Shape::Atom(AtomKind::I32);
    let annotated = inner
        .clone()
        .annotated(Annotations::new().with_nullable(true))
        .annotated(Annotations::new().with_deprecated(true));

    assert_eq!(annotated.strip_annotations(), inner);
}

#[test]
fn display_unit() {
    assert_eq!(format!("{}", Shape::Unit), "()");
}

#[test]
fn display_atom() {
    assert_eq!(format!("{}", Shape::Atom(AtomKind::I32)), "i32");
    assert_eq!(format!("{}", Shape::Atom(AtomKind::String)), "string");
}

#[test]
fn display_product() {
    let shape = Shape::struct_from(vec![
        ("x", Shape::Atom(AtomKind::I32)),
        ("y", Shape::Atom(AtomKind::String)),
    ]);
    assert_eq!(format!("{}", shape), "{ x: i32, y: string }");
}

#[test]
fn display_sum() {
    let shape = Shape::enum_from(vec![
        ("Some", Shape::Atom(AtomKind::I32)),
        ("None", Shape::Unit),
    ]);
    assert_eq!(format!("{}", shape), "Some(i32) | None");
}

#[test]
fn display_sequence() {
    let shape = Shape::sequence(Shape::Atom(AtomKind::I32));
    assert_eq!(format!("{}", shape), "[i32]");
}

#[test]
fn display_optional() {
    let shape = Shape::optional(Shape::Atom(AtomKind::String));
    assert_eq!(format!("{}", shape), "string?");
}

#[test]
fn display_map() {
    let shape = Shape::map(Shape::Atom(AtomKind::String), Shape::Atom(AtomKind::I64));
    assert_eq!(format!("{}", shape), "Map<string, i64>");
}

#[test]
fn shape_equality() {
    let a = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    let b = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    assert_eq!(a, b);
}

#[test]
fn shape_inequality_different_types() {
    let a = Shape::Atom(AtomKind::I32);
    let b = Shape::Atom(AtomKind::I64);
    assert_ne!(a, b);
}

#[test]
fn shape_inequality_different_fields() {
    let a = Shape::struct_from(vec![("x", Shape::Atom(AtomKind::I32))]);
    let b = Shape::struct_from(vec![("y", Shape::Atom(AtomKind::I32))]);
    assert_ne!(a, b);
}

#[test]
fn recursive_shape_construction() {
    // List<i32> = Nil | Cons(i32, List)
    let list = Shape::recursive(
        "List",
        Shape::enum_from(vec![
            (
                "Cons",
                Shape::struct_from(vec![
                    ("head", Shape::Atom(AtomKind::I32)),
                    ("tail", Shape::Ref("List".to_string())),
                ]),
            ),
            ("Nil", Shape::Unit),
        ]),
    );

    match &list {
        Shape::Recursive { var, .. } => assert_eq!(var, "List"),
        other => panic!("Expected Recursive, got {:?}", other),
    }
}

#[test]
fn optional_wrapping() {
    let inner = Shape::Atom(AtomKind::I32);
    let opt = Shape::optional(inner.clone());
    match &opt {
        Shape::Optional(i) => assert_eq!(**i, inner),
        other => panic!("Expected Optional, got {:?}", other),
    }
}

#[test]
fn map_construction() {
    let m = Shape::map(Shape::Atom(AtomKind::String), Shape::Atom(AtomKind::I32));
    match &m {
        Shape::Map { key, value } => {
            assert_eq!(**key, Shape::Atom(AtomKind::String));
            assert_eq!(**value, Shape::Atom(AtomKind::I32));
        },
        other => panic!("Expected Map, got {:?}", other),
    }
}

#[test]
fn dependent_construction() {
    let dep = Shape::dependent(
        Shape::Atom(AtomKind::Enum(vec!["A".into(), "B".into()])),
        Shape::Atom(AtomKind::I32),
    );
    match &dep {
        Shape::Dependent { binder, body } => {
            assert!(matches!(binder.as_ref(), Shape::Atom(AtomKind::Enum(_))));
            assert_eq!(**body, Shape::Atom(AtomKind::I32));
        },
        other => panic!("Expected Dependent, got {:?}", other),
    }
}

#[test]
fn serde_roundtrip() {
    let shape = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
        ("scores", Shape::sequence(Shape::Atom(AtomKind::F64))),
    ]);

    let json = serde_json::to_string(&shape).expect("shape should serialize to JSON");
    let parsed: Shape = serde_json::from_str(&json).expect("JSON should deserialize back to Shape");
    assert_eq!(shape, parsed);
}
