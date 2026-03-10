// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Tests for the visual rendering module (Phase 5).

use crate::atom::AtomKind;
use crate::category::ShapeCategory;
use crate::compare::compare;
use crate::information::TransportClass;
use crate::morphism::Morphism;
use crate::render::*;
use crate::shape::Shape;
use crate::temporal::{SchemaTimeline, SemanticVersion};

// ---------------------------------------------------------------------------
// Shape tree rendering
// ---------------------------------------------------------------------------

#[test]
fn tree_unit() {
    let tree = render_shape_tree(&Shape::Unit);
    assert_eq!(tree.trim(), "()");
}

#[test]
fn tree_atom() {
    let tree = render_shape_tree(&Shape::Atom(AtomKind::I32));
    assert!(tree.contains("Atom(i32)"));
    assert!(tree.contains("[32 bits, fixed]"));
}

#[test]
fn tree_product_chain() {
    let shape = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
        ("active", Shape::Atom(AtomKind::Bool)),
    ]);

    let tree = render_shape_tree(&shape);
    assert!(tree.contains("Product \"id\""));
    assert!(tree.contains("Product \"name\""));
    assert!(tree.contains("Product \"active\""));
    assert!(tree.contains("Atom(bool)"));
    // Should have tree connectors
    assert!(tree.contains("├──") || tree.contains("└──"));
}

#[test]
fn tree_sum() {
    let shape = Shape::enum_from(vec![
        ("Success", Shape::Atom(AtomKind::String)),
        ("Error", Shape::Atom(AtomKind::I32)),
    ]);

    let tree = render_shape_tree(&shape);
    assert!(tree.contains("Sum \"Success\""));
    assert!(tree.contains("Sum \"Error\""));
}

#[test]
fn tree_nested_sequence_map() {
    let shape = Shape::struct_from(vec![
        ("tags", Shape::sequence(Shape::Atom(AtomKind::String))),
        (
            "metadata",
            Shape::map(Shape::Atom(AtomKind::String), Shape::Atom(AtomKind::I64)),
        ),
    ]);

    let tree = render_shape_tree(&shape);
    assert!(tree.contains("Sequence"));
    assert!(tree.contains("Map"));
}

#[test]
fn tree_optional() {
    let shape = Shape::optional(Shape::Atom(AtomKind::String));
    let tree = render_shape_tree(&shape);
    assert!(tree.contains("Optional"));
    assert!(tree.contains("Atom(string)"));
}

#[test]
fn tree_dependent() {
    let shape = Shape::dependent(
        Shape::Atom(AtomKind::I32),
        Shape::Atom(AtomKind::String),
    );
    let tree = render_shape_tree(&shape);
    assert!(tree.contains("Dependent"));
}

#[test]
fn tree_recursive_with_ref() {
    let shape = Shape::recursive(
        "Tree",
        Shape::enum_from(vec![
            (
                "Node",
                Shape::struct_from(vec![
                    ("value", Shape::Atom(AtomKind::I32)),
                    ("left", Shape::Ref("Tree".to_string())),
                    ("right", Shape::Ref("Tree".to_string())),
                ]),
            ),
            ("Leaf", Shape::Unit),
        ]),
    );

    let tree = render_shape_tree(&shape);
    assert!(tree.contains("Recursive (mu Tree)"));
    assert!(tree.contains("Ref(Tree)"));
}

// ---------------------------------------------------------------------------
// Morphism step rendering
// ---------------------------------------------------------------------------

#[test]
fn morphism_steps_identity() {
    let shape = Shape::Atom(AtomKind::I32);
    let morphism = Morphism::identity(shape);
    let rendered = render_morphism_steps(&morphism);
    assert!(rendered.contains("Concorde"));
    assert!(rendered.contains("identity — no transformation steps"));
}

#[test]
fn morphism_steps_widening() {
    let source = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    let target = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I64)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);

    let morphism = compare(&source, &target);
    let rendered = render_morphism_steps(&morphism);
    assert!(rendered.contains("Step"));
    assert!(rendered.contains("Class"));
    assert!(rendered.contains("Transformation"));
}

#[test]
fn morphism_steps_with_pad() {
    let source = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]);
    let target = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::optional(Shape::Atom(AtomKind::String))),
    ]);

    let morphism = compare(&source, &target);
    let rendered = render_morphism_steps(&morphism);
    // Should show some steps (pad for the new field)
    assert!(rendered.contains("Step") || rendered.contains("identity"));
}

// ---------------------------------------------------------------------------
// Transport badges
// ---------------------------------------------------------------------------

#[test]
fn badges_all_classes() {
    assert!(render_transport_badge(TransportClass::Concorde).contains("Concorde"));
    assert!(render_transport_badge(TransportClass::Business).contains("Business"));
    assert!(render_transport_badge(TransportClass::Economy).contains("Economy"));
    assert!(render_transport_badge(TransportClass::Wheelbarrow).contains("Wheelbarrow"));
}

#[test]
fn badges_contain_icons() {
    assert!(render_transport_badge(TransportClass::Concorde).contains('≡'));
    assert!(render_transport_badge(TransportClass::Business).contains('↑'));
    assert!(render_transport_badge(TransportClass::Economy).contains('↓'));
    assert!(render_transport_badge(TransportClass::Wheelbarrow).contains('✗'));
}

// ---------------------------------------------------------------------------
// Timeline rendering
// ---------------------------------------------------------------------------

#[test]
fn timeline_empty() {
    let timeline = SchemaTimeline::new("empty");
    let rendered = render_timeline(&timeline);
    assert!(rendered.contains("(empty)"));
}

#[test]
fn timeline_single_version() {
    let mut timeline = SchemaTimeline::new("single");
    timeline.add_version(
        SemanticVersion::new(1, 0, 0),
        Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]),
    );

    let rendered = render_timeline(&timeline);
    assert!(rendered.contains("v1.0.0"));
    assert!(rendered.contains("1 versions"));
}

#[test]
fn timeline_evolution_minor() {
    let mut timeline = SchemaTimeline::new("users");
    timeline.add_version(
        SemanticVersion::new(1, 0, 0),
        Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I32)),
            ("name", Shape::Atom(AtomKind::String)),
        ]),
    );
    timeline.add_version(
        SemanticVersion::new(1, 1, 0),
        Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I32)),
            ("name", Shape::Atom(AtomKind::String)),
            ("email", Shape::optional(Shape::Atom(AtomKind::String))),
        ]),
    );

    let rendered = render_timeline(&timeline);
    assert!(rendered.contains("minor"));
    assert!(rendered.contains("v1.0.0"));
    assert!(rendered.contains("v1.1.0"));
    assert!(rendered.contains("fully backward compatible"));
}

#[test]
fn timeline_breaking_change() {
    let mut timeline = SchemaTimeline::new("breaking");
    timeline.add_version(
        SemanticVersion::new(1, 0, 0),
        Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I32)),
            ("name", Shape::Atom(AtomKind::String)),
        ]),
    );
    timeline.add_version(
        SemanticVersion::new(2, 0, 0),
        Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I64))]),
    );

    let rendered = render_timeline(&timeline);
    assert!(rendered.contains("breaking change"));
}

// ---------------------------------------------------------------------------
// DOT graph rendering
// ---------------------------------------------------------------------------

#[test]
fn dot_empty_category() {
    let cat = ShapeCategory::new();
    let dot = render_category_dot(&cat);
    assert!(dot.contains("digraph ShapeCategory"));
    assert!(dot.contains('}'));
}

#[test]
fn dot_with_objects_and_arrows() {
    let mut cat = ShapeCategory::new();
    cat.add_object("i32", Shape::Atom(AtomKind::I32));
    cat.add_object("i64", Shape::Atom(AtomKind::I64));
    cat.compare_all();

    let dot = render_category_dot(&cat);
    assert!(dot.contains("\"i32\""));
    assert!(dot.contains("\"i64\""));
    assert!(dot.contains("->"));
    assert!(dot.contains("color="));
}

#[test]
fn dot_three_node_category() {
    let mut cat = ShapeCategory::new();
    cat.add_object("i32", Shape::Atom(AtomKind::I32));
    cat.add_object("i64", Shape::Atom(AtomKind::I64));
    cat.add_object("str", Shape::Atom(AtomKind::String));
    cat.compare_all();

    let dot = render_category_dot(&cat);
    // Should have 3 nodes and up to 6 directed edges
    assert!(dot.contains("\"i32\""));
    assert!(dot.contains("\"i64\""));
    assert!(dot.contains("\"str\""));
}

// ---------------------------------------------------------------------------
// ASCII category rendering
// ---------------------------------------------------------------------------

#[test]
fn ascii_category_header() {
    let mut cat = ShapeCategory::new();
    cat.add_object("a", Shape::Atom(AtomKind::I32));
    cat.add_object("b", Shape::Atom(AtomKind::I64));
    cat.compare_all();

    let ascii = render_category_ascii(&cat);
    assert!(ascii.contains("Shape Category: 2 objects"));
    assert!(ascii.contains("Arrows:"));
    assert!(ascii.contains("Lossless reachability:"));
}

// ---------------------------------------------------------------------------
// Evolution strategy rendering
// ---------------------------------------------------------------------------

#[test]
fn evolution_strategy_rendering() {
    let source = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    let target = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I64)),
        ("name", Shape::Atom(AtomKind::String)),
        ("email", Shape::optional(Shape::Atom(AtomKind::String))),
    ]);

    let rendered = render_evolution_strategy("v1.0.0", "v2.0.0", &source, &target);
    assert!(rendered.contains("Evolution: v1.0.0 -> v2.0.0"));
    assert!(rendered.contains("Suggested bump:"));
    assert!(rendered.contains("Transport:"));
}
