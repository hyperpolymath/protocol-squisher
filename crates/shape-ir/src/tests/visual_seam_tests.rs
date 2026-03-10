// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Seam tests — verify Phase 5 (Visual Language) integrates cleanly
//! with all prior phases (1-4).
//!
//! These tests exercise the boundaries between the visual layer and:
//! - Phase 1: Shape IR core (all 11 constructors render correctly)
//! - Phase 2: Category algebra (DOT/ASCII export from real categories)
//! - Phase 3: Domain extractors (rendered shapes from extracted IR)
//! - Phase 4: Temporal algebra (timeline rendering, PanLL timeline frames)

use crate::annotations::{Annotations, Constraint};
use crate::atom::{AtomKind, TimePrecision};
use crate::category::ShapeCategory;
use crate::compare::compare;
use crate::panll::{PanelId, PanelItem, PanllFrame};
use crate::render;
use crate::shape::Shape;
use crate::temporal::{
    forecast_compatibility, plan_evolution, SchemaTimeline, SemanticVersion,
};

// ---------------------------------------------------------------------------
// Phase 1 seam: all 11 constructors render without panic
// ---------------------------------------------------------------------------

#[test]
fn all_11_constructors_render_trees() {
    let shapes: Vec<(&str, Shape)> = vec![
        ("Unit", Shape::Unit),
        ("Atom", Shape::Atom(AtomKind::I64)),
        (
            "Product",
            Shape::struct_from(vec![
                ("a", Shape::Atom(AtomKind::I32)),
                ("b", Shape::Atom(AtomKind::String)),
            ]),
        ),
        (
            "Sum",
            Shape::enum_from(vec![
                ("Ok", Shape::Atom(AtomKind::String)),
                ("Err", Shape::Atom(AtomKind::I32)),
            ]),
        ),
        (
            "Dependent",
            Shape::dependent(Shape::Atom(AtomKind::I32), Shape::Atom(AtomKind::String)),
        ),
        (
            "Recursive",
            Shape::recursive(
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
            ),
        ),
        ("Ref", Shape::Ref("SomeType".to_string())),
        ("Sequence", Shape::sequence(Shape::Atom(AtomKind::Bool))),
        ("Optional", Shape::optional(Shape::Atom(AtomKind::F64))),
        (
            "Map",
            Shape::map(Shape::Atom(AtomKind::String), Shape::Atom(AtomKind::I32)),
        ),
        (
            "Annotated",
            Shape::Atom(AtomKind::String).annotated(Annotations {
                constraints: vec![Constraint::MinLength(1), Constraint::MaxLength(255)],
                ..Default::default()
            }),
        ),
    ];

    for (name, shape) in &shapes {
        let tree = render::render_shape_tree(shape);
        assert!(!tree.is_empty(), "{} should produce non-empty tree", name);
        // Each tree should end with newline
        assert!(tree.ends_with('\n'), "{} tree should end with newline", name);
    }
}

#[test]
fn all_11_constructors_produce_panll_frames() {
    let shapes: Vec<(&str, Shape)> = vec![
        ("Unit", Shape::Unit),
        ("Atom", Shape::Atom(AtomKind::I64)),
        (
            "Product",
            Shape::struct_from(vec![("x", Shape::Atom(AtomKind::I32))]),
        ),
        (
            "Sum",
            Shape::enum_from(vec![("A", Shape::Unit), ("B", Shape::Unit)]),
        ),
        (
            "Dependent",
            Shape::dependent(Shape::Atom(AtomKind::Bool), Shape::Atom(AtomKind::String)),
        ),
        (
            "Recursive",
            Shape::recursive("T", Shape::Ref("T".to_string())),
        ),
        ("Ref", Shape::Ref("X".to_string())),
        ("Sequence", Shape::sequence(Shape::Atom(AtomKind::I32))),
        ("Optional", Shape::optional(Shape::Atom(AtomKind::String))),
        (
            "Map",
            Shape::map(Shape::Atom(AtomKind::String), Shape::Atom(AtomKind::F64)),
        ),
        (
            "Annotated",
            Shape::Atom(AtomKind::I32).annotated(Annotations::default()),
        ),
    ];

    for (name, shape) in &shapes {
        let frame = PanllFrame::from_shape(name, shape);
        assert_eq!(frame.panel_l.panel, PanelId::L);
        assert_eq!(frame.panel_n.panel, PanelId::N);
        assert_eq!(frame.panel_w.panel, PanelId::W);
        // text render should not panic
        let text = frame.render_text();
        assert!(text.contains("Panel-L"), "{} frame missing Panel-L", name);
    }
}

// ---------------------------------------------------------------------------
// Phase 2 seam: category DOT/ASCII from compare_all
// ---------------------------------------------------------------------------

#[test]
fn category_dot_from_real_comparison() {
    let mut cat = ShapeCategory::new();
    cat.add_object(
        "user_struct",
        Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I32)),
            ("name", Shape::Atom(AtomKind::String)),
        ]),
    );
    cat.add_object(
        "user_wide",
        Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I64)),
            ("name", Shape::Atom(AtomKind::String)),
            ("email", Shape::optional(Shape::Atom(AtomKind::String))),
        ]),
    );
    cat.add_object("user_minimal", Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]));
    cat.compare_all();

    let dot = render::render_category_dot(&cat);
    assert!(dot.contains("user_struct"));
    assert!(dot.contains("user_wide"));
    assert!(dot.contains("user_minimal"));
    // Should have edges with color attributes
    assert!(dot.contains("color="));
    // Should be valid DOT syntax
    assert!(dot.starts_with("digraph"));
    assert!(dot.trim().ends_with('}'));

    let ascii = render::render_category_ascii(&cat);
    assert!(ascii.contains("3 objects"));
    assert!(ascii.contains("Arrows:"));
}

#[test]
fn category_panll_frame_has_dot_and_ascii() {
    let mut cat = ShapeCategory::new();
    cat.add_object("a", Shape::Atom(AtomKind::I32));
    cat.add_object("b", Shape::Atom(AtomKind::I64));
    cat.compare_all();

    let frame = PanllFrame::from_category(&cat);

    // W panel should have both DOT and ASCII
    let has_dot = frame
        .panel_w
        .items
        .iter()
        .any(|i| matches!(i, PanelItem::DotGraph(d) if d.contains("digraph")));
    assert!(has_dot);

    // N panel should have lossless reachability
    let n_text = frame.render_text();
    assert!(n_text.contains("losslessly reaches") || n_text.contains("Isomorphic"));
}

// ---------------------------------------------------------------------------
// Phase 3 seam: extracted shapes render correctly
// ---------------------------------------------------------------------------

#[test]
fn timestamp_shapes_render() {
    // Phase 3 domain extractors produce Timestamp atoms
    let shape = Shape::struct_from(vec![
        ("created_at", Shape::Atom(AtomKind::Timestamp(TimePrecision::Microseconds))),
        ("name", Shape::Atom(AtomKind::String)),
    ]);

    let tree = render::render_shape_tree(&shape);
    assert!(tree.contains("timestamp"));
    assert!(tree.contains("Product"));
}

#[test]
fn annotated_shapes_from_extractors_render() {
    // Domain extractors often produce annotated shapes (e.g., NOT NULL → MinLength)
    let shape = Shape::struct_from(vec![(
        "email",
        Shape::Atom(AtomKind::String).annotated(Annotations {
            constraints: vec![Constraint::MinLength(1), Constraint::MaxLength(320)],
            ..Default::default()
        }),
    )]);

    let tree = render::render_shape_tree(&shape);
    assert!(tree.contains("Annotated"));
    assert!(tree.contains("MinLength(1)") || tree.contains("@["));
}

// ---------------------------------------------------------------------------
// Phase 4 seam: timeline rendering and PanLL frames
// ---------------------------------------------------------------------------

#[test]
fn timeline_renders_evolution_steps() {
    let mut timeline = SchemaTimeline::new("orders");

    // v1: simple
    timeline.add_version(
        SemanticVersion::new(1, 0, 0),
        Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I32)),
            ("total", Shape::Atom(AtomKind::F64)),
        ]),
    );

    // v1.1: additive (minor)
    timeline.add_version(
        SemanticVersion::new(1, 1, 0),
        Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I32)),
            ("total", Shape::Atom(AtomKind::F64)),
            ("currency", Shape::optional(Shape::Atom(AtomKind::String))),
        ]),
    );

    // v2.0: breaking (major — widened id + dropped total)
    timeline.add_version(
        SemanticVersion::new(2, 0, 0),
        Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I64)),
            ("currency", Shape::Atom(AtomKind::String)),
        ]),
    );

    let rendered = render::render_timeline(&timeline);
    assert!(rendered.contains("v1.0.0"));
    assert!(rendered.contains("v1.1.0"));
    assert!(rendered.contains("v2.0.0"));
    assert!(rendered.contains("minor") || rendered.contains("additive"));
    assert!(rendered.contains("breaking"));
}

#[test]
fn timeline_panll_frame_detects_breaking_changes() {
    let mut timeline = SchemaTimeline::new("config");

    timeline.add_version(
        SemanticVersion::new(1, 0, 0),
        Shape::struct_from(vec![
            ("key", Shape::Atom(AtomKind::String)),
            ("value", Shape::Atom(AtomKind::String)),
        ]),
    );

    // Breaking: dropped a field
    timeline.add_version(
        SemanticVersion::new(2, 0, 0),
        Shape::struct_from(vec![("key", Shape::Atom(AtomKind::String))]),
    );

    let frame = PanllFrame::from_timeline(&timeline);

    // N panel should warn about breaking change
    let has_warning = frame
        .panel_n
        .items
        .iter()
        .any(|i| matches!(i, PanelItem::Warning(msg) if msg.contains("breaking")));
    assert!(
        has_warning,
        "N panel should warn about breaking change in timeline"
    );
}

#[test]
fn forecast_renders_in_panll() {
    let mut timeline_a = SchemaTimeline::new("api_v1");
    timeline_a.add_version(
        SemanticVersion::new(1, 0, 0),
        Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]),
    );
    timeline_a.add_version(
        SemanticVersion::new(1, 1, 0),
        Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I32)),
            ("name", Shape::optional(Shape::Atom(AtomKind::String))),
        ]),
    );

    let mut timeline_b = SchemaTimeline::new("api_v2");
    timeline_b.add_version(
        SemanticVersion::new(1, 0, 0),
        Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]),
    );
    timeline_b.add_version(
        SemanticVersion::new(2, 0, 0),
        Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I64))]),
    );

    let forecast = forecast_compatibility(&timeline_a, &timeline_b);
    assert!(!forecast.compatibility_matrix.is_empty());

    // Render both timelines
    let rendered_a = render::render_timeline(&timeline_a);
    let rendered_b = render::render_timeline(&timeline_b);
    assert!(rendered_a.contains("api_v1"));
    assert!(rendered_b.contains("api_v2"));
}

#[test]
fn evolution_strategy_renders_with_panll() {
    let source = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    let target = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I64)),
        ("name", Shape::Atom(AtomKind::String)),
        ("email", Shape::optional(Shape::Atom(AtomKind::String))),
    ]);

    // Strategy rendering
    let strategy_text = render::render_evolution_strategy("v1", "v2", &source, &target);
    assert!(strategy_text.contains("Evolution: v1 -> v2"));

    // Morphism PanLL frame
    let morphism = compare(&source, &target);
    let frame = PanllFrame::from_morphism("v1_schema", "v2_schema", &morphism);
    let text = frame.render_text();
    assert!(text.contains("Panel-L"));
    assert!(text.contains("Panel-N"));
    assert!(text.contains("Panel-W"));
}

// ---------------------------------------------------------------------------
// Cross-phase integration: full pipeline
// ---------------------------------------------------------------------------

#[test]
fn full_pipeline_shape_to_timeline_to_panll() {
    // Phase 1: Define shapes
    let v1 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    let v2 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
        ("email", Shape::optional(Shape::Atom(AtomKind::String))),
    ]);
    let v3 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I64)),
        ("name", Shape::Atom(AtomKind::String)),
        ("email", Shape::Atom(AtomKind::String)),
    ]);

    // Phase 2: Build category
    let mut cat = ShapeCategory::new();
    cat.add_object("v1", v1.clone());
    cat.add_object("v2", v2.clone());
    cat.add_object("v3", v3.clone());
    cat.compare_all();

    // Phase 4: Build timeline
    let mut timeline = SchemaTimeline::new("users");
    timeline.add_version(SemanticVersion::new(1, 0, 0), v1);
    timeline.add_version(SemanticVersion::new(1, 1, 0), v2);
    timeline.add_version(SemanticVersion::new(2, 0, 0), v3);

    // Phase 5: Render everything
    let cat_frame = PanllFrame::from_category(&cat);
    let timeline_frame = PanllFrame::from_timeline(&timeline);
    let cat_dot = render::render_category_dot(&cat);
    let timeline_text = render::render_timeline(&timeline);

    // Verify all outputs are non-empty and structurally sound
    assert!(cat_frame.render_text().len() > 100);
    assert!(timeline_frame.render_text().len() > 100);
    assert!(cat_dot.contains("digraph"));
    assert!(timeline_text.contains("v1.0.0"));
    assert!(timeline_text.contains("v2.0.0"));

    // Category frame should show 3 objects
    let has_3_objects = cat_frame.panel_l.items.iter().any(|i| {
        matches!(i, PanelItem::KeyValue { key, value } if key == "Objects" && value == "3")
    });
    assert!(has_3_objects);

    // Timeline frame should detect the breaking change
    let has_breaking = timeline_frame
        .panel_n
        .items
        .iter()
        .any(|i| matches!(i, PanelItem::Warning(msg) if msg.contains("breaking")));
    assert!(has_breaking);
}

#[test]
fn json_serialization_roundtrip_all_frame_types() {
    // Shape frame
    let shape = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]);
    let f1 = PanllFrame::from_shape("test", &shape);
    let j1 = serde_json::to_string(&f1).unwrap();
    let _: PanllFrame = serde_json::from_str(&j1).unwrap();

    // Morphism frame
    let source = Shape::Atom(AtomKind::I32);
    let target = Shape::Atom(AtomKind::I64);
    let morphism = compare(&source, &target);
    let f2 = PanllFrame::from_morphism("a", "b", &morphism);
    let j2 = serde_json::to_string(&f2).unwrap();
    let _: PanllFrame = serde_json::from_str(&j2).unwrap();

    // Timeline frame
    let mut tl = SchemaTimeline::new("t");
    tl.add_version(SemanticVersion::new(1, 0, 0), Shape::Atom(AtomKind::I32));
    let f3 = PanllFrame::from_timeline(&tl);
    let j3 = serde_json::to_string(&f3).unwrap();
    let _: PanllFrame = serde_json::from_str(&j3).unwrap();

    // Category frame
    let mut cat = ShapeCategory::new();
    cat.add_object("x", Shape::Atom(AtomKind::Bool));
    let f4 = PanllFrame::from_category(&cat);
    let j4 = serde_json::to_string(&f4).unwrap();
    let _: PanllFrame = serde_json::from_str(&j4).unwrap();
}
