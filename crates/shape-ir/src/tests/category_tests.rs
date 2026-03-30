// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Tests for the Shape Category — category laws, adapter discovery, and
//! pathfinding.

use crate::category::ShapeCategory;
use crate::compare::compare;
use crate::compose::compose;
use crate::*;

// ---------------------------------------------------------------------------
// Category construction
// ---------------------------------------------------------------------------

/// Build a small category with integer widening chain: i8 → i16 → i32 → i64.
fn int_widening_category() -> ShapeCategory {
    let mut cat = ShapeCategory::new();

    cat.add_object("i8", Shape::Atom(AtomKind::I8));
    cat.add_object("i16", Shape::Atom(AtomKind::I16));
    cat.add_object("i32", Shape::Atom(AtomKind::I32));
    cat.add_object("i64", Shape::Atom(AtomKind::I64));

    // Forward arrows (widening = Business)
    cat.add_arrow(
        "i8",
        "i16",
        compare(&Shape::Atom(AtomKind::I8), &Shape::Atom(AtomKind::I16)),
    );
    cat.add_arrow(
        "i16",
        "i32",
        compare(&Shape::Atom(AtomKind::I16), &Shape::Atom(AtomKind::I32)),
    );
    cat.add_arrow(
        "i32",
        "i64",
        compare(&Shape::Atom(AtomKind::I32), &Shape::Atom(AtomKind::I64)),
    );

    // Reverse arrows (narrowing = Economy)
    cat.add_arrow(
        "i16",
        "i8",
        compare(&Shape::Atom(AtomKind::I16), &Shape::Atom(AtomKind::I8)),
    );
    cat.add_arrow(
        "i32",
        "i16",
        compare(&Shape::Atom(AtomKind::I32), &Shape::Atom(AtomKind::I16)),
    );
    cat.add_arrow(
        "i64",
        "i32",
        compare(&Shape::Atom(AtomKind::I64), &Shape::Atom(AtomKind::I32)),
    );

    cat
}

// ---------------------------------------------------------------------------
// Basic construction
// ---------------------------------------------------------------------------

#[test]
fn empty_category() {
    let cat = ShapeCategory::new();
    assert_eq!(cat.object_count(), 0);
    assert_eq!(cat.arrow_count(), 0);
}

#[test]
fn add_objects_and_arrows() {
    let cat = int_widening_category();
    assert_eq!(cat.object_count(), 4);
    assert_eq!(cat.arrow_count(), 6); // 3 forward + 3 reverse
}

#[test]
fn object_retrieval() {
    let cat = int_widening_category();
    assert!(cat.object("i32").is_some());
    assert!(cat.object("i128").is_none());
}

#[test]
fn arrow_retrieval() {
    let cat = int_widening_category();
    let m = cat.arrow("i8", "i16").expect("arrow i8->i16 should exist");
    assert_eq!(m.transport_class, TransportClass::Business);
}

// ---------------------------------------------------------------------------
// Category law: Identity
// ---------------------------------------------------------------------------

#[test]
fn identity_exists_for_all_objects() {
    let cat = int_widening_category();
    for id in cat.object_ids() {
        let identity = cat.identity(id).expect("identity morphism should exist for every object");
        assert_eq!(identity.transport_class, TransportClass::Concorde);
        assert!(identity.is_identity());
    }
}

#[test]
fn left_identity_law() {
    // id_B ∘ f = f  (transport class and cost)
    let cat = int_widening_category();
    let f = cat.arrow("i8", "i16").expect("arrow i8->i16 should exist for left identity test");
    let id_b = cat.identity("i16").expect("identity for i16 should exist");

    let composed = compose(f, &id_b).expect("composing f with id_B should succeed");
    assert_eq!(composed.transport_class, f.transport_class);
    assert_eq!(composed.source, f.source);
    assert_eq!(composed.target, f.target);
    assert_eq!(
        composed.information_cost.bits_added,
        f.information_cost.bits_added
    );
    assert_eq!(
        composed.information_cost.bits_lost,
        f.information_cost.bits_lost
    );
}

#[test]
fn right_identity_law() {
    // f ∘ id_A = f  (transport class and cost)
    let cat = int_widening_category();
    let f = cat.arrow("i8", "i16").expect("arrow i8->i16 should exist for right identity test");
    let id_a = cat.identity("i8").expect("identity for i8 should exist");

    let composed = compose(&id_a, f).expect("composing id_A with f should succeed");
    assert_eq!(composed.transport_class, f.transport_class);
    assert_eq!(composed.source, f.source);
    assert_eq!(composed.target, f.target);
    assert_eq!(
        composed.information_cost.bits_added,
        f.information_cost.bits_added
    );
    assert_eq!(
        composed.information_cost.bits_lost,
        f.information_cost.bits_lost
    );
}

// ---------------------------------------------------------------------------
// Category law: Associativity
// ---------------------------------------------------------------------------

#[test]
fn composition_associativity() {
    // (h ∘ g) ∘ f = h ∘ (g ∘ f)
    let cat = int_widening_category();
    let f = cat.arrow("i8", "i16").expect("arrow i8->i16 should exist for associativity test");
    let g = cat.arrow("i16", "i32").expect("arrow i16->i32 should exist for associativity test");
    let h = cat.arrow("i32", "i64").expect("arrow i32->i64 should exist for associativity test");

    let gf = compose(f, g).expect("composing f then g should succeed");
    let hg = compose(g, h).expect("composing g then h should succeed");

    let left = compose(&gf, h).expect("composing (g∘f) then h should succeed"); // (g ∘ f) ∘ h
    let right = compose(f, &hg).expect("composing f then (h∘g) should succeed"); // f ∘ (h ∘ g)

    assert_eq!(left.transport_class, right.transport_class);
    assert_eq!(left.source, right.source);
    assert_eq!(left.target, right.target);
}

// ---------------------------------------------------------------------------
// Pathfinding
// ---------------------------------------------------------------------------

#[test]
fn find_path_identity() {
    let cat = int_widening_category();
    let path = cat.find_path("i32", "i32").expect("self-path should always be found");
    assert!(path.is_empty());
}

#[test]
fn find_path_direct() {
    let cat = int_widening_category();
    let path = cat.find_path("i8", "i16").expect("direct path i8->i16 should be found");
    assert_eq!(path.len(), 1);
    assert_eq!(path[0], ("i8".to_string(), "i16".to_string()));
}

#[test]
fn find_path_transitive() {
    let cat = int_widening_category();
    let path = cat.find_path("i8", "i64").expect("transitive path i8->i64 should be found");
    // Should find i8 → i16 → i32 → i64 (3 hops)
    assert_eq!(path.len(), 3);
    assert_eq!(path[0].0, "i8");
    assert_eq!(path[2].1, "i64");
}

#[test]
fn find_path_nonexistent_target() {
    let cat = int_widening_category();
    assert!(cat.find_path("i8", "i128").is_none());
}

#[test]
fn find_path_prefers_better_transport_class() {
    let mut cat = ShapeCategory::new();

    // Three shapes: A, B, C
    let a = Shape::Atom(AtomKind::I32);
    let b = Shape::Atom(AtomKind::I64);
    let c = Shape::Atom(AtomKind::I128);

    cat.add_object("A", a.clone());
    cat.add_object("B", b.clone());
    cat.add_object("C", c.clone());

    // Direct A→C (Economy — narrowing then widening scenario)
    let mut direct = compare(&a, &c);
    // Force it to Economy for test purposes
    direct.transport_class = TransportClass::Economy;
    cat.add_arrow("A", "C", direct);

    // Indirect A→B→C (Business + Business = Business)
    cat.add_arrow("A", "B", compare(&a, &b));
    cat.add_arrow("B", "C", compare(&b, &c));

    let path = cat.find_path("A", "C").expect("path A->C should be found preferring better transport class");
    // Should prefer the indirect path (Business) over direct (Economy)
    assert_eq!(path.len(), 2);
}

// ---------------------------------------------------------------------------
// Compose path
// ---------------------------------------------------------------------------

#[test]
fn compose_path_produces_valid_morphism() {
    let cat = int_widening_category();
    let path = cat.find_path("i8", "i64").expect("path i8->i64 should be found for compose test");
    let composed = cat.compose_path(&path).expect("composing path i8->i64 should produce a valid morphism");

    assert_eq!(composed.transport_class, TransportClass::Business);
    assert_eq!(
        format!("{}", composed.source),
        format!("{}", Shape::Atom(AtomKind::I8))
    );
    assert_eq!(
        format!("{}", composed.target),
        format!("{}", Shape::Atom(AtomKind::I64))
    );
}

#[test]
fn compose_empty_path_returns_none() {
    let cat = int_widening_category();
    assert!(cat.compose_path(&[]).is_none());
}

// ---------------------------------------------------------------------------
// compare_all
// ---------------------------------------------------------------------------

#[test]
fn compare_all_populates_arrows() {
    let mut cat = ShapeCategory::new();
    cat.add_object("i32", Shape::Atom(AtomKind::I32));
    cat.add_object("i64", Shape::Atom(AtomKind::I64));
    cat.add_object("str", Shape::Atom(AtomKind::String));

    assert_eq!(cat.arrow_count(), 0);
    cat.compare_all();
    // 3 objects → 3*2 = 6 directed pairs
    assert_eq!(cat.arrow_count(), 6);
}

// ---------------------------------------------------------------------------
// Lossless reachability
// ---------------------------------------------------------------------------

#[test]
fn lossless_reachable_follows_only_business_and_concorde() {
    let cat = int_widening_category();
    // From i8, lossless reachable should be i16, i32, i64 (all widening = Business)
    let mut reachable = cat.lossless_reachable("i8");
    reachable.sort();
    assert_eq!(reachable, vec!["i16", "i32", "i64"]);
}

#[test]
fn lossless_reachable_excludes_economy() {
    // From i64, narrowing is Economy — no lossless targets
    let mut cat = ShapeCategory::new();
    cat.add_object("i64", Shape::Atom(AtomKind::I64));
    cat.add_object("i32", Shape::Atom(AtomKind::I32));
    cat.add_arrow(
        "i64",
        "i32",
        compare(&Shape::Atom(AtomKind::I64), &Shape::Atom(AtomKind::I32)),
    );

    let reachable = cat.lossless_reachable("i64");
    assert!(reachable.is_empty());
}

// ---------------------------------------------------------------------------
// Outgoing / incoming
// ---------------------------------------------------------------------------

#[test]
fn outgoing_arrows() {
    let cat = int_widening_category();
    let out = cat.outgoing("i16");
    // i16 → i32 (widening) and i16 → i8 (narrowing)
    assert_eq!(out.len(), 2);
}

#[test]
fn incoming_arrows() {
    let cat = int_widening_category();
    let inc = cat.incoming("i32");
    // i16 → i32 (widening) and i64 → i32 (narrowing)
    assert_eq!(inc.len(), 2);
}

// ---------------------------------------------------------------------------
// Display
// ---------------------------------------------------------------------------

#[test]
fn display_category() {
    let cat = int_widening_category();
    let display = format!("{}", cat);
    assert!(display.contains("4 objects"));
    assert!(display.contains("6 arrows"));
}

// ---------------------------------------------------------------------------
// Struct category — more realistic scenario
// ---------------------------------------------------------------------------

#[test]
fn struct_category_with_evolution() {
    let mut cat = ShapeCategory::new();

    // v1: { id: i32, name: String }
    let v1 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);

    // v2: { id: i64, name: String, email: Optional<String> }
    let v2 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I64)),
        ("name", Shape::Atom(AtomKind::String)),
        ("email", Shape::optional(Shape::Atom(AtomKind::String))),
    ]);

    // v3: { id: i64, name: String, email: Optional<String>, active: Bool }
    let v3 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I64)),
        ("name", Shape::Atom(AtomKind::String)),
        ("email", Shape::optional(Shape::Atom(AtomKind::String))),
        ("active", Shape::Atom(AtomKind::Bool)),
    ]);

    cat.add_object("v1", v1.clone());
    cat.add_object("v2", v2.clone());
    cat.add_object("v3", v3.clone());

    cat.add_arrow("v1", "v2", compare(&v1, &v2));
    cat.add_arrow("v2", "v3", compare(&v2, &v3));

    // v1 → v3 should be findable via v2
    let path = cat.find_path("v1", "v3").expect("path v1->v3 should be found via v2");
    assert_eq!(path.len(), 2);

    let composed = cat.compose_path(&path).expect("composing v1->v3 path should produce a valid morphism");
    assert_eq!(composed.transport_class, TransportClass::Business);
}

// ---------------------------------------------------------------------------
// Roundtrip property
// ---------------------------------------------------------------------------

#[test]
fn roundtrip_concorde_is_concorde() {
    // Identical shapes: roundtrip A→A→A should be Concorde
    let mut cat = ShapeCategory::new();
    let s = Shape::Atom(AtomKind::I32);
    cat.add_object("a", s.clone());
    cat.add_object("b", s.clone());
    cat.add_arrow("a", "b", compare(&s, &s));
    cat.add_arrow("b", "a", compare(&s, &s));

    let rt = cat.roundtrip_class("a", "b").expect("roundtrip class a<->b should be computable for identical shapes");
    assert_eq!(rt, TransportClass::Concorde);
}

#[test]
fn roundtrip_widening_is_economy() {
    // i32→i64 (Business) then i64→i32 (Economy) = Economy roundtrip
    let cat = int_widening_category();
    let rt = cat.roundtrip_class("i32", "i64").expect("roundtrip class i32<->i64 should be computable");
    assert_eq!(rt, TransportClass::Economy);
}

#[test]
fn roundtrip_narrowing_is_economy() {
    // i64→i32 (Economy) then i32→i64 (Business) = Economy roundtrip
    let cat = int_widening_category();
    let rt = cat.roundtrip_class("i64", "i32").expect("roundtrip class i64<->i32 should be computable");
    assert_eq!(rt, TransportClass::Economy);
}

// ---------------------------------------------------------------------------
// Isomorphic pairs
// ---------------------------------------------------------------------------

#[test]
fn isomorphic_pairs_finds_identical_shapes() {
    let mut cat = ShapeCategory::new();
    let s = Shape::Atom(AtomKind::I32);
    cat.add_object("a", s.clone());
    cat.add_object("b", s.clone());
    cat.add_object("c", Shape::Atom(AtomKind::I64));
    cat.compare_all();

    let pairs = cat.isomorphic_pairs();
    // a and b are identical → isomorphic
    // a/b and c are not (widening is Business, not Concorde)
    assert_eq!(pairs.len(), 1);
    let (p, q) = &pairs[0];
    assert!((p == "a" && q == "b") || (p == "b" && q == "a"));
}

#[test]
fn no_isomorphic_pairs_for_different_types() {
    let cat = int_widening_category();
    let pairs = cat.isomorphic_pairs();
    assert!(pairs.is_empty());
}

// ---------------------------------------------------------------------------
// Symmetric monoidal: Product (tensor)
// ---------------------------------------------------------------------------

#[test]
fn product_creates_pair_shape() {
    let mut cat = ShapeCategory::new();
    cat.add_object("i32", Shape::Atom(AtomKind::I32));
    cat.add_object("bool", Shape::Atom(AtomKind::Bool));

    cat.add_product("pair", "i32", "bool");

    let pair_shape = cat.object("pair").expect("product object 'pair' should exist after add_product");
    let labels = pair_shape.field_labels();
    assert_eq!(labels.len(), 2);
    assert_eq!(labels[0].name, "fst");
    assert_eq!(labels[1].name, "snd");
}

#[test]
fn product_has_projection_arrows() {
    let mut cat = ShapeCategory::new();
    cat.add_object("i32", Shape::Atom(AtomKind::I32));
    cat.add_object("bool", Shape::Atom(AtomKind::Bool));
    cat.add_product("pair", "i32", "bool");

    // pair → i32 and pair → bool should exist (projections)
    assert!(cat.arrow("pair", "i32").is_some());
    assert!(cat.arrow("pair", "bool").is_some());

    // i32 → pair and bool → pair should exist (embeddings)
    assert!(cat.arrow("i32", "pair").is_some());
    assert!(cat.arrow("bool", "pair").is_some());
}

#[test]
fn unit_is_monoidal_unit() {
    // Product with Unit: {fst: i32, snd: Unit} carries the same information
    // as i32, but structurally they differ (the product has an extra Unit field).
    // The roundtrip class should still be Economy (structural mismatch),
    // but the information cost should be minimal.
    let mut cat = ShapeCategory::new();
    let s = Shape::Atom(AtomKind::I32);
    cat.add_object("i32", s.clone());
    cat.add_object("unit", Shape::Unit);
    cat.add_product("pair", "i32", "unit");

    // pair → i32 exists (projection drops the Unit field)
    let arrow = cat.arrow("pair", "i32").expect("projection arrow pair->i32 should exist");
    // Unit carries zero bits, so bits_lost should be 0
    assert_eq!(arrow.information_cost.bits_lost, 0);
}

// ---------------------------------------------------------------------------
// Symmetric monoidal: Coproduct (sum)
// ---------------------------------------------------------------------------

#[test]
fn coproduct_creates_sum_shape() {
    let mut cat = ShapeCategory::new();
    cat.add_object("i32", Shape::Atom(AtomKind::I32));
    cat.add_object("str", Shape::Atom(AtomKind::String));

    cat.add_coproduct("either", "i32", "str");

    let either = cat.object("either").expect("coproduct object 'either' should exist after add_coproduct");
    // Should be a Sum
    match either {
        Shape::Sum { label, .. } => assert_eq!(label.name, "left"),
        other => panic!("Expected Sum, got {:?}", other),
    }
}

#[test]
fn coproduct_has_injection_arrows() {
    let mut cat = ShapeCategory::new();
    cat.add_object("i32", Shape::Atom(AtomKind::I32));
    cat.add_object("str", Shape::Atom(AtomKind::String));
    cat.add_coproduct("either", "i32", "str");

    // i32 → either and str → either should exist (injections)
    assert!(cat.arrow("i32", "either").is_some());
    assert!(cat.arrow("str", "either").is_some());

    // either → i32 and either → str should exist (case analysis)
    assert!(cat.arrow("either", "i32").is_some());
    assert!(cat.arrow("either", "str").is_some());
}

#[test]
fn compose_arrows_direct() {
    let cat = int_widening_category();
    // i8 → i16, i16 → i32 compose to i8 → i32
    let result = cat.compose_arrows("i8", "i16", "i32");
    assert!(result.is_ok());
    let composed = result.expect("compose_arrows i8->i16->i32 should not error");
    assert!(composed.is_some());
    let m = composed.expect("compose_arrows i8->i16->i32 should produce a morphism");
    assert_eq!(m.transport_class, TransportClass::Business);
}

#[test]
fn compose_arrows_missing_intermediate() {
    let cat = int_widening_category();
    // i8 → nonexistent doesn't have an arrow
    let result = cat.compose_arrows("i8", "nonexistent", "i16");
    // Missing arrows return Ok(None)
    assert!(matches!(result, Ok(None)));
}

#[test]
fn is_lossless_direct() {
    let cat = int_widening_category();
    // i8 → i16 is Business, which is lossless
    let arrow = cat.arrow("i8", "i16").expect("arrow i8->i16 should exist for lossless check");
    assert!(arrow.is_lossless());
}
