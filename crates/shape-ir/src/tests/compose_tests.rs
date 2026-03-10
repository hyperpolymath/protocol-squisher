// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Tests for morphism composition.

use crate::compare::compare;
use crate::compose::compose;
use crate::*;

#[test]
fn compose_two_widenings() {
    let a = Shape::Atom(AtomKind::I32);
    let b = Shape::Atom(AtomKind::I64);
    let c = Shape::Atom(AtomKind::I128);

    let f = compare(&a, &b); // i32 -> i64
    let g = compare(&b, &c); // i64 -> i128
    let h = compose(&f, &g).unwrap();

    assert_eq!(h.source, a);
    assert_eq!(h.target, c);
    assert_eq!(h.transport_class, TransportClass::Business);
    assert_eq!(h.steps.len(), f.steps.len() + g.steps.len());
}

#[test]
fn compose_widening_then_narrowing() {
    let a = Shape::Atom(AtomKind::I32);
    let b = Shape::Atom(AtomKind::I64);

    let f = compare(&a, &b); // Business (widen)
    let g = compare(&b, &a); // Economy (narrow)
    let h = compose(&f, &g).unwrap();

    // Worst of Business and Economy is Economy
    assert_eq!(h.transport_class, TransportClass::Economy);
    assert_eq!(h.source, a);
    assert_eq!(h.target, a);
}

#[test]
fn compose_identities() {
    let s = Shape::Atom(AtomKind::I32);
    let f = compare(&s, &s);
    let g = compare(&s, &s);
    let h = compose(&f, &g).unwrap();
    assert_eq!(h.transport_class, TransportClass::Concorde);
}

#[test]
fn compose_mismatched_shapes_fails() {
    let a = Shape::Atom(AtomKind::I32);
    let b = Shape::Atom(AtomKind::I64);
    let c = Shape::Atom(AtomKind::String);

    let f = compare(&a, &b); // i32 -> i64
    let g = compare(&c, &a); // string -> i32 (g.source = string, not i64)

    let result = compose(&f, &g);
    assert!(result.is_err());
}

#[test]
fn compose_preserves_information_cost() {
    let a = Shape::Atom(AtomKind::I32);
    let b = Shape::Atom(AtomKind::I64);
    let c = Shape::Atom(AtomKind::I128);

    let f = compare(&a, &b);
    let g = compare(&b, &c);
    let h = compose(&f, &g).unwrap();

    assert_eq!(
        h.information_cost.bits_added,
        f.information_cost.bits_added + g.information_cost.bits_added
    );
}

#[test]
fn compose_structs() {
    let a = Shape::struct_from(vec![("x", Shape::Atom(AtomKind::I32))]);
    let b = Shape::struct_from(vec![
        ("x", Shape::Atom(AtomKind::I32)),
        ("y", Shape::Atom(AtomKind::String)),
    ]);
    let c = Shape::struct_from(vec![
        ("x", Shape::Atom(AtomKind::I32)),
        ("y", Shape::Atom(AtomKind::String)),
        ("z", Shape::Atom(AtomKind::Bool)),
    ]);

    let f = compare(&a, &b);
    let g = compare(&b, &c);
    let h = compose(&f, &g).unwrap();

    assert_eq!(h.transport_class, TransportClass::Business);
    assert_eq!(h.source, a);
    assert_eq!(h.target, c);
}

#[test]
fn compose_sequences() {
    // [i32] → [i64] → [i128]
    let a = Shape::Sequence(Box::new(Shape::Atom(AtomKind::I32)));
    let b = Shape::Sequence(Box::new(Shape::Atom(AtomKind::I64)));
    let c = Shape::Sequence(Box::new(Shape::Atom(AtomKind::I128)));

    let f = compare(&a, &b);
    let g = compare(&b, &c);
    let h = compose(&f, &g).unwrap();

    assert_eq!(h.transport_class, TransportClass::Business);
    assert_eq!(h.source, a);
    assert_eq!(h.target, c);
}

#[test]
fn compose_maps() {
    // Map<String, I32> → Map<String, I64>
    let a = Shape::map(Shape::Atom(AtomKind::String), Shape::Atom(AtomKind::I32));
    let b = Shape::map(Shape::Atom(AtomKind::String), Shape::Atom(AtomKind::I64));
    let c = Shape::map(Shape::Atom(AtomKind::String), Shape::Atom(AtomKind::I128));

    let f = compare(&a, &b);
    let g = compare(&b, &c);
    let h = compose(&f, &g).unwrap();

    assert_eq!(h.transport_class, TransportClass::Business);
    assert_eq!(h.source, a);
    assert_eq!(h.target, c);
}

#[test]
fn compose_optionals() {
    // Optional<I32> → Optional<I64> → Optional<I128>
    let a = Shape::optional(Shape::Atom(AtomKind::I32));
    let b = Shape::optional(Shape::Atom(AtomKind::I64));
    let c = Shape::optional(Shape::Atom(AtomKind::I128));

    let f = compare(&a, &b);
    let g = compare(&b, &c);
    let h = compose(&f, &g).unwrap();

    assert_eq!(h.transport_class, TransportClass::Business);
    assert_eq!(h.source, a);
    assert_eq!(h.target, c);
}

#[test]
fn compose_sums() {
    // Sum(A, Unit) → Sum(B, Unit) where A→B is Business
    let a = Shape::enum_from(vec![
        ("x", Shape::Atom(AtomKind::I32)),
        ("y", Shape::Unit),
    ]);
    let b = Shape::enum_from(vec![
        ("x", Shape::Atom(AtomKind::I64)),
        ("y", Shape::Unit),
    ]);
    let c = Shape::enum_from(vec![
        ("x", Shape::Atom(AtomKind::I128)),
        ("y", Shape::Unit),
    ]);

    let f = compare(&a, &b);
    let g = compare(&b, &c);
    let h = compose(&f, &g).unwrap();

    assert_eq!(h.transport_class, TransportClass::Business);
}

#[test]
fn compose_annotated() {
    use crate::annotations::{Annotations, Constraint};

    let inner_a = Shape::Atom(AtomKind::I32);
    let inner_b = Shape::Atom(AtomKind::I64);
    let inner_c = Shape::Atom(AtomKind::I128);

    let mut ann = Annotations::new();
    ann.constraints.push(Constraint::MinLength(1));

    let a = inner_a.annotated(ann.clone());
    let b = inner_b.annotated(ann.clone());
    let c = inner_c.annotated(ann);

    let f = compare(&a, &b);
    let g = compare(&b, &c);
    let h = compose(&f, &g).unwrap();

    assert_eq!(h.transport_class, TransportClass::Business);
}

#[test]
fn compose_nested_product_with_widening() {
    // struct { a: struct { x: I32 } } → struct { a: struct { x: I64 } }
    let inner_a = Shape::struct_from(vec![("x", Shape::Atom(AtomKind::I32))]);
    let inner_b = Shape::struct_from(vec![("x", Shape::Atom(AtomKind::I64))]);
    let inner_c = Shape::struct_from(vec![("x", Shape::Atom(AtomKind::I128))]);

    let a = Shape::struct_from(vec![("a", inner_a)]);
    let b = Shape::struct_from(vec![("a", inner_b)]);
    let c = Shape::struct_from(vec![("a", inner_c)]);

    let f = compare(&a, &b);
    let g = compare(&b, &c);
    let h = compose(&f, &g).unwrap();

    assert_eq!(h.transport_class, TransportClass::Business);
}

#[test]
fn compose_cross_constructor_fails() {
    // Atom → Sequence: two morphisms with incompatible intermediate
    let a = Shape::Atom(AtomKind::I32);
    let b = Shape::Atom(AtomKind::I64);
    let c = Shape::Sequence(Box::new(Shape::Atom(AtomKind::I64)));

    let f = compare(&a, &b);
    let g = compare(&b, &c); // b=Atom, c=Sequence → Wheelbarrow

    // Should compose fine (Wheelbarrow composes), but the result
    // should be at least Wheelbarrow
    let h = compose(&f, &g).unwrap();
    assert_eq!(h.transport_class, TransportClass::Wheelbarrow);
}

#[test]
fn compose_identity_left() {
    let s = Shape::Atom(AtomKind::I32);
    let t = Shape::Atom(AtomKind::I64);

    let id = compare(&s, &s);
    let f = compare(&s, &t);
    let h = compose(&id, &f).unwrap();

    assert_eq!(h.transport_class, f.transport_class);
    assert_eq!(h.source, s);
    assert_eq!(h.target, t);
}

#[test]
fn compose_identity_right() {
    let s = Shape::Atom(AtomKind::I32);
    let t = Shape::Atom(AtomKind::I64);

    let f = compare(&s, &t);
    let id = compare(&t, &t);
    let h = compose(&f, &id).unwrap();

    assert_eq!(h.transport_class, f.transport_class);
    assert_eq!(h.source, s);
    assert_eq!(h.target, t);
}
