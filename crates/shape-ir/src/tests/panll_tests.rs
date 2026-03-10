// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Tests for the PanLL integration module (Phase 5).

use crate::atom::AtomKind;
use crate::category::ShapeCategory;
use crate::compare::compare;
use crate::panll::*;
use crate::shape::Shape;
use crate::temporal::{SchemaTimeline, SemanticVersion};

// ---------------------------------------------------------------------------
// PanLL frame from shape
// ---------------------------------------------------------------------------

#[test]
fn shape_frame_has_three_panels() {
    let shape = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);

    let frame = PanllFrame::from_shape("User", &shape);
    assert_eq!(frame.panel_l.panel, PanelId::L);
    assert_eq!(frame.panel_n.panel, PanelId::N);
    assert_eq!(frame.panel_w.panel, PanelId::W);
}

#[test]
fn shape_frame_l_has_field_count() {
    let shape = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
        ("email", Shape::Atom(AtomKind::String)),
    ]);

    let frame = PanllFrame::from_shape("Contact", &shape);
    let has_field_kv = frame.panel_l.items.iter().any(|item| {
        matches!(item, PanelItem::KeyValue { key, value } if key == "Fields" && value == "3")
    });
    assert!(has_field_kv, "L panel should show field count");
}

#[test]
fn shape_frame_w_has_tree() {
    let shape = Shape::Atom(AtomKind::I64);
    let frame = PanllFrame::from_shape("counter", &shape);

    let has_tree = frame
        .panel_w
        .items
        .iter()
        .any(|item| matches!(item, PanelItem::ShapeTree(tree) if tree.contains("Atom(i64)")));
    assert!(has_tree, "W panel should have shape tree");
}

#[test]
fn shape_frame_l_has_info_content() {
    let shape = Shape::Atom(AtomKind::I32);
    let frame = PanllFrame::from_shape("count", &shape);

    let has_bits = frame.panel_l.items.iter().any(|item| {
        matches!(item, PanelItem::KeyValue { key, .. } if key == "Bits")
    });
    assert!(has_bits, "L panel should show information content");
}

// ---------------------------------------------------------------------------
// PanLL frame from morphism
// ---------------------------------------------------------------------------

#[test]
fn morphism_frame_n_has_metrics() {
    let source = Shape::Atom(AtomKind::I32);
    let target = Shape::Atom(AtomKind::I64);
    let morphism = compare(&source, &target);

    let frame = PanllFrame::from_morphism("i32", "i64", &morphism);

    let has_reversibility = frame.panel_n.items.iter().any(|item| {
        matches!(item, PanelItem::KeyValue { key, .. } if key == "Reversibility")
    });
    assert!(has_reversibility, "N panel should show reversibility");
}

#[test]
fn morphism_frame_l_has_transport_badge() {
    let source = Shape::Atom(AtomKind::I32);
    let target = Shape::Atom(AtomKind::I64);
    let morphism = compare(&source, &target);

    let frame = PanllFrame::from_morphism("i32", "i64", &morphism);

    let has_badge = frame
        .panel_l
        .items
        .iter()
        .any(|item| matches!(item, PanelItem::TransportBadge { .. }));
    assert!(has_badge, "L panel should have transport badge");
}

#[test]
fn morphism_frame_n_has_semver_suggestion() {
    let source = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    let target = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I64)),
        ("name", Shape::Atom(AtomKind::String)),
        ("email", Shape::optional(Shape::Atom(AtomKind::String))),
    ]);
    let morphism = compare(&source, &target);

    let frame = PanllFrame::from_morphism("v1", "v2", &morphism);

    let has_semver = frame
        .panel_n
        .items
        .iter()
        .any(|item| matches!(item, PanelItem::SemverBadge { .. }));
    assert!(has_semver, "N panel should suggest semver bump");
}

#[test]
fn morphism_frame_w_has_step_table() {
    let source = Shape::Atom(AtomKind::I32);
    let target = Shape::Atom(AtomKind::I64);
    let morphism = compare(&source, &target);

    let frame = PanllFrame::from_morphism("i32", "i64", &morphism);

    let has_table = frame
        .panel_w
        .items
        .iter()
        .any(|item| matches!(item, PanelItem::MorphismTable(_)));
    assert!(has_table, "W panel should have morphism step table");
}

// ---------------------------------------------------------------------------
// PanLL frame from timeline
// ---------------------------------------------------------------------------

#[test]
fn timeline_frame_l_has_version_list() {
    let mut timeline = SchemaTimeline::new("orders");
    timeline.add_version(
        SemanticVersion::new(1, 0, 0),
        Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]),
    );
    timeline.add_version(
        SemanticVersion::new(1, 1, 0),
        Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I32)),
            ("total", Shape::Atom(AtomKind::F64)),
        ]),
    );

    let frame = PanllFrame::from_timeline(&timeline);

    let has_versions = frame.panel_l.items.iter().any(|item| {
        matches!(item, PanelItem::List { label, items } if label == "Version history" && items.len() == 2)
    });
    assert!(has_versions, "L panel should list versions");
}

#[test]
fn timeline_frame_n_has_evolution_badges() {
    let mut timeline = SchemaTimeline::new("config");
    timeline.add_version(
        SemanticVersion::new(1, 0, 0),
        Shape::struct_from(vec![("key", Shape::Atom(AtomKind::String))]),
    );
    timeline.add_version(
        SemanticVersion::new(1, 0, 1),
        Shape::struct_from(vec![("key", Shape::Atom(AtomKind::String))]),
    );

    let frame = PanllFrame::from_timeline(&timeline);

    let has_badge = frame
        .panel_n
        .items
        .iter()
        .any(|item| matches!(item, PanelItem::SemverBadge { .. }));
    assert!(has_badge, "N panel should have evolution classification badge");
}

#[test]
fn timeline_frame_w_has_diagram() {
    let mut timeline = SchemaTimeline::new("events");
    timeline.add_version(
        SemanticVersion::new(1, 0, 0),
        Shape::struct_from(vec![("type", Shape::Atom(AtomKind::String))]),
    );

    let frame = PanllFrame::from_timeline(&timeline);

    let has_diagram = frame
        .panel_w
        .items
        .iter()
        .any(|item| matches!(item, PanelItem::TimelineDiagram(_)));
    assert!(has_diagram, "W panel should have timeline diagram");
}

// ---------------------------------------------------------------------------
// PanLL frame from category
// ---------------------------------------------------------------------------

#[test]
fn category_frame_l_has_counts() {
    let mut cat = ShapeCategory::new();
    cat.add_object("i32", Shape::Atom(AtomKind::I32));
    cat.add_object("i64", Shape::Atom(AtomKind::I64));
    cat.add_object("str", Shape::Atom(AtomKind::String));
    cat.compare_all();

    let frame = PanllFrame::from_category(&cat);

    let has_objects = frame.panel_l.items.iter().any(|item| {
        matches!(item, PanelItem::KeyValue { key, value } if key == "Objects" && value == "3")
    });
    assert!(has_objects, "L panel should show object count");
}

#[test]
fn category_frame_w_has_dot_graph() {
    let mut cat = ShapeCategory::new();
    cat.add_object("a", Shape::Atom(AtomKind::I32));
    cat.add_object("b", Shape::Atom(AtomKind::I64));
    cat.compare_all();

    let frame = PanllFrame::from_category(&cat);

    let has_dot = frame
        .panel_w
        .items
        .iter()
        .any(|item| matches!(item, PanelItem::DotGraph(dot) if dot.contains("digraph")));
    assert!(has_dot, "W panel should have DOT graph");
}

// ---------------------------------------------------------------------------
// Text rendering
// ---------------------------------------------------------------------------

#[test]
fn render_text_all_panels_present() {
    let shape = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    let frame = PanllFrame::from_shape("User", &shape);
    let text = frame.render_text();

    assert!(text.contains("Panel-L:"), "Should contain Panel-L header");
    assert!(text.contains("Panel-N:"), "Should contain Panel-N header");
    assert!(text.contains("Panel-W:"), "Should contain Panel-W header");
}

#[test]
fn render_text_contains_box_drawing() {
    let shape = Shape::Atom(AtomKind::I32);
    let frame = PanllFrame::from_shape("count", &shape);
    let text = frame.render_text();

    assert!(text.contains('╔'), "Should use box-drawing chars");
    assert!(text.contains('╚'), "Should close panels");
}

#[test]
fn json_roundtrip() {
    let shape = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]);
    let frame = PanllFrame::from_shape("Test", &shape);

    let json = serde_json::to_string(&frame).expect("serialize");
    let restored: PanllFrame = serde_json::from_str(&json).expect("deserialize");

    assert_eq!(restored.panel_l.panel, PanelId::L);
    assert_eq!(restored.panel_n.panel, PanelId::N);
    assert_eq!(restored.panel_w.panel, PanelId::W);
    assert_eq!(restored.panel_l.items.len(), frame.panel_l.items.len());
}
