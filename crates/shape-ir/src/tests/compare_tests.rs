// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Tests for the shape comparison engine.

use crate::compare::compare;
use crate::*;

// ---------------------------------------------------------------------------
// Identical shapes -> Concorde
// ---------------------------------------------------------------------------

#[test]
fn identical_atoms_are_concorde() {
    let s = Shape::Atom(AtomKind::I32);
    let m = compare(&s, &s);
    assert_eq!(m.transport_class, TransportClass::Concorde);
    assert!(
        m.is_identity()
            || m.steps
                .iter()
                .all(|s| matches!(s, MorphismStep::Identity { .. }))
    );
}

#[test]
fn identical_structs_are_concorde() {
    let s = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    let m = compare(&s, &s);
    assert_eq!(m.transport_class, TransportClass::Concorde);
}

#[test]
fn unit_to_unit_is_concorde() {
    let m = compare(&Shape::Unit, &Shape::Unit);
    assert_eq!(m.transport_class, TransportClass::Concorde);
}

// ---------------------------------------------------------------------------
// Widening -> Business
// ---------------------------------------------------------------------------

#[test]
fn i32_to_i64_is_business() {
    let source = Shape::Atom(AtomKind::I32);
    let target = Shape::Atom(AtomKind::I64);
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Business);
    assert!(m
        .steps
        .iter()
        .any(|s| matches!(s, MorphismStep::Widen { .. })));
}

#[test]
fn f32_to_f64_is_business() {
    let source = Shape::Atom(AtomKind::F32);
    let target = Shape::Atom(AtomKind::F64);
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Business);
}

#[test]
fn struct_with_extra_field_is_business() {
    let source = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]);
    let target = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Business);
    assert!(m
        .steps
        .iter()
        .any(|s| matches!(s, MorphismStep::Pad { .. })));
}

// ---------------------------------------------------------------------------
// Narrowing / Projection -> Economy
// ---------------------------------------------------------------------------

#[test]
fn i64_to_i32_is_economy() {
    let source = Shape::Atom(AtomKind::I64);
    let target = Shape::Atom(AtomKind::I32);
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Economy);
    assert!(m
        .steps
        .iter()
        .any(|s| matches!(s, MorphismStep::Narrow { .. })));
}

#[test]
fn struct_with_dropped_field_is_economy() {
    let source = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    let target = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]);
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Economy);
    assert!(m
        .steps
        .iter()
        .any(|s| matches!(s, MorphismStep::Project { .. })));
}

// ---------------------------------------------------------------------------
// Incompatible types -> Wheelbarrow
// ---------------------------------------------------------------------------

#[test]
fn bool_to_string_is_wheelbarrow() {
    let source = Shape::Atom(AtomKind::Bool);
    let target = Shape::Atom(AtomKind::String);
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Wheelbarrow);
}

#[test]
fn atom_to_sequence_is_wheelbarrow() {
    let source = Shape::Atom(AtomKind::I32);
    let target = Shape::sequence(Shape::Atom(AtomKind::I32));
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Wheelbarrow);
}

// ---------------------------------------------------------------------------
// Complex scenarios
// ---------------------------------------------------------------------------

#[test]
fn struct_field_widened_plus_extra_field() {
    let source = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    let target = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I64)),      // widened
        ("name", Shape::Atom(AtomKind::String)), // same
        ("email", Shape::optional(Shape::Atom(AtomKind::String))), // added
    ]);
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Business);
    assert!(m.information_cost.bits_added > 0);
}

#[test]
fn sequences_compared_by_element() {
    let source = Shape::sequence(Shape::Atom(AtomKind::I32));
    let target = Shape::sequence(Shape::Atom(AtomKind::I64));
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Business);
}

#[test]
fn maps_compared_by_key_and_value() {
    let source = Shape::map(Shape::Atom(AtomKind::String), Shape::Atom(AtomKind::I32));
    let target = Shape::map(Shape::Atom(AtomKind::String), Shape::Atom(AtomKind::I64));
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Business); // Value widened
}

#[test]
fn optionals_compared_by_inner() {
    let source = Shape::optional(Shape::Atom(AtomKind::I32));
    let target = Shape::optional(Shape::Atom(AtomKind::I64));
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Business);
}

#[test]
fn non_optional_to_optional_is_business() {
    let source = Shape::Atom(AtomKind::I32);
    let target = Shape::optional(Shape::Atom(AtomKind::I32));
    let m = compare(&source, &target);
    // Wrapping in Optional adds padding -> Business
    assert!(m.transport_class.is_lossless());
}

#[test]
fn optional_to_non_optional_is_economy() {
    let source = Shape::optional(Shape::Atom(AtomKind::I32));
    let target = Shape::Atom(AtomKind::I32);
    let m = compare(&source, &target);
    // Unwrapping Optional may lose the None case -> Economy
    assert_eq!(m.transport_class, TransportClass::Economy);
}

#[test]
fn sum_variant_comparison() {
    let source = Shape::enum_from(vec![
        ("A", Shape::Atom(AtomKind::I32)),
        ("B", Shape::Atom(AtomKind::String)),
    ]);
    let target = Shape::enum_from(vec![
        ("A", Shape::Atom(AtomKind::I64)),    // widened
        ("B", Shape::Atom(AtomKind::String)), // same
    ]);
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Business);
}

#[test]
fn sum_with_missing_variant_is_economy() {
    let source = Shape::enum_from(vec![
        ("A", Shape::Atom(AtomKind::I32)),
        ("B", Shape::Atom(AtomKind::String)),
    ]);
    let target = Shape::enum_from(vec![
        ("A", Shape::Atom(AtomKind::I32)),
        // B is missing
    ]);
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Economy);
}

#[test]
fn morphism_has_source_and_target() {
    let source = Shape::Atom(AtomKind::I32);
    let target = Shape::Atom(AtomKind::I64);
    let m = compare(&source, &target);
    assert_eq!(m.source, source);
    assert_eq!(m.target, target);
}

#[test]
fn identity_morphism() {
    let s = Shape::Atom(AtomKind::I32);
    let m = Morphism::identity(s.clone());
    assert!(m.is_identity());
    assert_eq!(m.source, s);
    assert_eq!(m.target, s);
}

// ---------------------------------------------------------------------------
// Dependent shapes
// ---------------------------------------------------------------------------

#[test]
fn identical_dependent_is_concorde() {
    let binder = Shape::Atom(AtomKind::U8);
    let body = Shape::Atom(AtomKind::String);
    let source = Shape::dependent(binder.clone(), body.clone());
    let target = Shape::dependent(binder, body);
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Concorde);
}

#[test]
fn dependent_binder_widened_is_business() {
    let source = Shape::dependent(Shape::Atom(AtomKind::U8), Shape::Atom(AtomKind::String));
    let target = Shape::dependent(
        Shape::Atom(AtomKind::U16), // widened binder
        Shape::Atom(AtomKind::String),
    );
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Business);
}

#[test]
fn dependent_body_narrowed_is_economy() {
    let source = Shape::dependent(Shape::Atom(AtomKind::U8), Shape::Atom(AtomKind::I64));
    let target = Shape::dependent(
        Shape::Atom(AtomKind::U8),
        Shape::Atom(AtomKind::I32), // narrowed body
    );
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Economy);
}

#[test]
fn dependent_binder_and_body_both_widened() {
    let source = Shape::dependent(
        Shape::Atom(AtomKind::I32),
        Shape::struct_from(vec![("x", Shape::Atom(AtomKind::F32))]),
    );
    let target = Shape::dependent(
        Shape::Atom(AtomKind::I64),
        Shape::struct_from(vec![("x", Shape::Atom(AtomKind::F64))]),
    );
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Business);
}

#[test]
fn dependent_incompatible_body_is_wheelbarrow() {
    let source = Shape::dependent(Shape::Atom(AtomKind::U8), Shape::Atom(AtomKind::Bool));
    let target = Shape::dependent(
        Shape::Atom(AtomKind::U8),
        Shape::Atom(AtomKind::String), // Bool -> String is Wheelbarrow
    );
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Wheelbarrow);
}

// ---------------------------------------------------------------------------
// Recursive shapes and alpha-equivalence
// ---------------------------------------------------------------------------

#[test]
fn identical_recursive_is_concorde() {
    // List<i32> = mu List. Cons(i32, $List) | Nil
    let list = Shape::recursive(
        "List",
        Shape::enum_from(vec![
            (
                "Cons",
                Shape::struct_from(vec![
                    ("head", Shape::Atom(AtomKind::I32)),
                    ("tail", Shape::Ref("List".into())),
                ]),
            ),
            ("Nil", Shape::Unit),
        ]),
    );
    let m = compare(&list, &list);
    assert_eq!(m.transport_class, TransportClass::Concorde);
}

#[test]
fn alpha_equivalent_recursive_is_concorde() {
    // Same structure, different variable names: "List" vs "L"
    let list_a = Shape::recursive(
        "List",
        Shape::enum_from(vec![
            (
                "Cons",
                Shape::struct_from(vec![
                    ("head", Shape::Atom(AtomKind::I32)),
                    ("tail", Shape::Ref("List".into())),
                ]),
            ),
            ("Nil", Shape::Unit),
        ]),
    );
    let list_b = Shape::recursive(
        "L",
        Shape::enum_from(vec![
            (
                "Cons",
                Shape::struct_from(vec![
                    ("head", Shape::Atom(AtomKind::I32)),
                    ("tail", Shape::Ref("L".into())),
                ]),
            ),
            ("Nil", Shape::Unit),
        ]),
    );
    let m = compare(&list_a, &list_b);
    assert_eq!(m.transport_class, TransportClass::Concorde);
}

#[test]
fn recursive_with_widened_element_is_business() {
    // List<i32> vs List<i64>
    let list_i32 = Shape::recursive(
        "List",
        Shape::enum_from(vec![
            (
                "Cons",
                Shape::struct_from(vec![
                    ("head", Shape::Atom(AtomKind::I32)),
                    ("tail", Shape::Ref("List".into())),
                ]),
            ),
            ("Nil", Shape::Unit),
        ]),
    );
    let list_i64 = Shape::recursive(
        "List",
        Shape::enum_from(vec![
            (
                "Cons",
                Shape::struct_from(vec![
                    ("head", Shape::Atom(AtomKind::I64)),
                    ("tail", Shape::Ref("List".into())),
                ]),
            ),
            ("Nil", Shape::Unit),
        ]),
    );
    let m = compare(&list_i32, &list_i64);
    assert_eq!(m.transport_class, TransportClass::Business);
}

#[test]
fn recursive_with_dropped_variant_is_economy() {
    // Tree with two node types vs tree with one
    let tree_a = Shape::recursive(
        "T",
        Shape::enum_from(vec![
            ("Leaf", Shape::Atom(AtomKind::I32)),
            (
                "Branch",
                Shape::struct_from(vec![
                    ("left", Shape::Ref("T".into())),
                    ("right", Shape::Ref("T".into())),
                ]),
            ),
        ]),
    );
    let tree_b = Shape::recursive(
        "T",
        Shape::enum_from(vec![
            ("Leaf", Shape::Atom(AtomKind::I32)),
            // Branch is gone — can't represent internal nodes
        ]),
    );
    let m = compare(&tree_a, &tree_b);
    assert_eq!(m.transport_class, TransportClass::Economy);
}

#[test]
fn different_recursive_refs_are_wheelbarrow() {
    // Ref("X") vs Ref("Y") where they are NOT alpha-equivalent
    let source = Shape::Ref("X".into());
    let target = Shape::Ref("Y".into());
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Wheelbarrow);
}

#[test]
fn nested_recursive_alpha_equivalence() {
    // mu X. { val: i32, children: [mu Y. { val: string, sub: [$Y] }] }
    // vs same structure with different var names "A" and "B"
    let inner_a = Shape::recursive(
        "Y",
        Shape::struct_from(vec![
            ("val", Shape::Atom(AtomKind::String)),
            ("sub", Shape::sequence(Shape::Ref("Y".into()))),
        ]),
    );
    let outer_a = Shape::recursive(
        "X",
        Shape::struct_from(vec![
            ("val", Shape::Atom(AtomKind::I32)),
            ("children", Shape::sequence(inner_a)),
        ]),
    );

    let inner_b = Shape::recursive(
        "B",
        Shape::struct_from(vec![
            ("val", Shape::Atom(AtomKind::String)),
            ("sub", Shape::sequence(Shape::Ref("B".into()))),
        ]),
    );
    let outer_b = Shape::recursive(
        "A",
        Shape::struct_from(vec![
            ("val", Shape::Atom(AtomKind::I32)),
            ("children", Shape::sequence(inner_b)),
        ]),
    );

    let m = compare(&outer_a, &outer_b);
    assert_eq!(m.transport_class, TransportClass::Concorde);
}

#[test]
fn dependent_inside_recursive() {
    // mu T. Dependent(u8, { val: i32, next: $T? })
    let source = Shape::recursive(
        "T",
        Shape::dependent(
            Shape::Atom(AtomKind::U8),
            Shape::struct_from(vec![
                ("val", Shape::Atom(AtomKind::I32)),
                ("next", Shape::optional(Shape::Ref("T".into()))),
            ]),
        ),
    );
    let target = Shape::recursive(
        "S",
        Shape::dependent(
            Shape::Atom(AtomKind::U8),
            Shape::struct_from(vec![
                ("val", Shape::Atom(AtomKind::I64)), // widened
                ("next", Shape::optional(Shape::Ref("S".into()))),
            ]),
        ),
    );
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Business);
}

// ---------------------------------------------------------------------------
// Annotated shapes -> transport class impact
// ---------------------------------------------------------------------------

#[test]
fn annotated_same_structure_is_concorde() {
    let ann = crate::annotations::Annotations::new()
        .with_constraint(crate::annotations::Constraint::MinValue(0.0));
    let s = Shape::Annotated {
        shape: Box::new(Shape::Atom(AtomKind::I32)),
        annotations: ann.clone(),
    };
    let t = Shape::Annotated {
        shape: Box::new(Shape::Atom(AtomKind::I32)),
        annotations: ann,
    };
    let m = compare(&s, &t);
    assert_eq!(m.transport_class, TransportClass::Concorde);
}

#[test]
fn dropping_annotations_is_concorde() {
    let ann = crate::annotations::Annotations::new()
        .with_constraint(crate::annotations::Constraint::MinLength(1))
        .with_constraint(crate::annotations::Constraint::MaxLength(255));
    let source = Shape::Annotated {
        shape: Box::new(Shape::Atom(AtomKind::String)),
        annotations: ann,
    };
    let target = Shape::Atom(AtomKind::String);
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Concorde);
}

#[test]
fn adding_annotations_is_business() {
    let ann = crate::annotations::Annotations::new()
        .with_constraint(crate::annotations::Constraint::Pattern("^[a-z]+$".into()));
    let source = Shape::Atom(AtomKind::String);
    let target = Shape::Annotated {
        shape: Box::new(Shape::Atom(AtomKind::String)),
        annotations: ann,
    };
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Business);
}

#[test]
fn more_restrictive_target_is_economy() {
    let source_ann = crate::annotations::Annotations::new()
        .with_constraint(crate::annotations::Constraint::MinValue(0.0));
    let target_ann = crate::annotations::Annotations::new()
        .with_constraint(crate::annotations::Constraint::MinValue(0.0))
        .with_constraint(crate::annotations::Constraint::MaxValue(100.0))
        .with_constraint(crate::annotations::Constraint::Custom("positive".into(), "true".into()));
    let source = Shape::Annotated {
        shape: Box::new(Shape::Atom(AtomKind::F64)),
        annotations: source_ann,
    };
    let target = Shape::Annotated {
        shape: Box::new(Shape::Atom(AtomKind::F64)),
        annotations: target_ann,
    };
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Economy);
}

#[test]
fn annotated_with_widened_inner_composes_classes() {
    // Annotation difference (Business) + widening inner (Business) → Business
    let ann = crate::annotations::Annotations::new()
        .with_constraint(crate::annotations::Constraint::MinValue(0.0));
    let source = Shape::Atom(AtomKind::I32);
    let target = Shape::Annotated {
        shape: Box::new(Shape::Atom(AtomKind::I64)),
        annotations: ann,
    };
    let m = compare(&source, &target);
    assert_eq!(m.transport_class, TransportClass::Business);
}
