// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # PanLL Integration — Three-Panel Data Model for Visual Exploration
//!
//! Maps the shape algebra to PanLL's three-panel architecture:
//!
//! | Panel | Role | Shape IR Mapping |
//! |-------|------|------------------|
//! | **Panel-L** (Constraints) | Structure & bounds | Shape tree, linearity, annotations, information content, transport class limits |
//! | **Panel-N** (Reasoning) | Analysis & strategy | Morphism analysis, pathfinding results, evolution strategy, semver classification |
//! | **Panel-W** (Output) | Generated artifacts | Rendered shapes, DOT graphs, timeline views, adapter suggestions |
//!
//! Each panel produces a [`PanelData`] struct containing structured items
//! that can be rendered by any frontend (TUI, web, PanLL native).
//!
//! ## Usage
//!
//! ```
//! use shape_ir::*;
//! use shape_ir::panll::*;
//!
//! let shape = Shape::struct_from(vec![
//!     ("id", Shape::Atom(AtomKind::I32)),
//!     ("name", Shape::Atom(AtomKind::String)),
//! ]);
//!
//! let frame = PanllFrame::from_shape("User", &shape);
//! assert!(!frame.panel_l.items.is_empty());
//! assert!(frame.panel_w.items.iter().any(|i| matches!(i, PanelItem::ShapeTree(_))));
//! ```

use crate::category::ShapeCategory;
use crate::information::{classify_morphism, information_content, TransportClass};
use crate::morphism::Morphism;
use crate::render;
use crate::shape::Shape;
use crate::temporal::{SchemaTimeline, SemverClassification};
use serde::{Deserialize, Serialize};

/// A single item in a panel's content.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PanelItem {
    /// Key-value display pair.
    KeyValue {
        /// Display key.
        key: String,
        /// Display value.
        value: String,
    },
    /// A labelled section divider.
    Section(String),
    /// A transport class badge with label.
    TransportBadge {
        /// Display label for the badge.
        label: String,
        /// The transport class to display.
        class: TransportClass,
    },
    /// A semver classification badge.
    SemverBadge {
        /// Display label for the badge.
        label: String,
        /// The semver classification to display.
        classification: SemverClassification,
    },
    /// A rendered shape tree (ASCII).
    ShapeTree(String),
    /// A rendered morphism step table (ASCII).
    MorphismTable(String),
    /// A rendered timeline diagram (ASCII).
    TimelineDiagram(String),
    /// A DOT graph source.
    DotGraph(String),
    /// A warning or alert.
    Warning(String),
    /// An informational note.
    Info(String),
    /// A list of items with a label.
    List {
        /// List heading.
        label: String,
        /// List entries.
        items: Vec<String>,
    },
}

/// Data for a single panel.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PanelData {
    /// Panel identifier (L, N, or W).
    pub panel: PanelId,
    /// Panel title.
    pub title: String,
    /// Ordered content items.
    pub items: Vec<PanelItem>,
}

/// Panel identifier matching PanLL's three-panel model.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PanelId {
    /// Panel-L: Constraints and structure.
    L,
    /// Panel-N: Agent reasoning and analysis.
    N,
    /// Panel-W: Results and output.
    W,
}

impl std::fmt::Display for PanelId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PanelId::L => write!(f, "L"),
            PanelId::N => write!(f, "N"),
            PanelId::W => write!(f, "W"),
        }
    }
}

/// A complete three-panel frame for PanLL rendering.
///
/// Contains structured data for all three panels, ready to be consumed
/// by PanLL's TEA framework or rendered as ASCII for terminal output.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PanllFrame {
    /// Panel-L: Constraints, structure, bounds.
    pub panel_l: PanelData,
    /// Panel-N: Reasoning, analysis, strategy.
    pub panel_n: PanelData,
    /// Panel-W: Output, artifacts, visualizations.
    pub panel_w: PanelData,
}

impl PanllFrame {
    /// Create a PanLL frame from a single shape inspection.
    ///
    /// - **L**: Shape structure, field count, information content, annotations
    /// - **N**: (minimal — no morphism to analyze)
    /// - **W**: Rendered shape tree
    pub fn from_shape(name: &str, shape: &Shape) -> Self {
        let info = information_content(shape);
        let fields = shape.field_labels();

        let mut l_items = vec![
            PanelItem::Section("Shape Structure".to_string()),
            PanelItem::KeyValue {
                key: "Name".to_string(),
                value: name.to_string(),
            },
            PanelItem::KeyValue {
                key: "Constructor".to_string(),
                value: constructor_name(shape),
            },
            PanelItem::KeyValue {
                key: "Fields".to_string(),
                value: format!("{}", fields.len()),
            },
            PanelItem::Section("Information Content".to_string()),
            PanelItem::KeyValue {
                key: "Bits".to_string(),
                value: format!("{}", info),
            },
            PanelItem::KeyValue {
                key: "Fixed size".to_string(),
                value: format!("{}", info.is_fixed_size),
            },
        ];

        if let Some(card) = info.cardinality {
            l_items.push(PanelItem::KeyValue {
                key: "Cardinality".to_string(),
                value: format!("{}", card),
            });
        }

        // Field list for L panel
        if !fields.is_empty() {
            l_items.push(PanelItem::List {
                label: "Field labels".to_string(),
                items: fields.iter().map(|l| format!("{}", l)).collect(),
            });
        }

        let n_items = vec![PanelItem::Info(
            "Inspect a morphism or timeline for reasoning analysis.".to_string(),
        )];

        let w_items = vec![
            PanelItem::Section("Shape Tree".to_string()),
            PanelItem::ShapeTree(render::render_shape_tree(shape)),
            PanelItem::Section("Compact Notation".to_string()),
            PanelItem::Info(format!("{}", shape)),
        ];

        PanllFrame {
            panel_l: PanelData {
                panel: PanelId::L,
                title: format!("Constraints: {}", name),
                items: l_items,
            },
            panel_n: PanelData {
                panel: PanelId::N,
                title: "Reasoning".to_string(),
                items: n_items,
            },
            panel_w: PanelData {
                panel: PanelId::W,
                title: format!("Output: {}", name),
                items: w_items,
            },
        }
    }

    /// Create a PanLL frame from a morphism comparison.
    ///
    /// - **L**: Source and target constraints, transport class bounds
    /// - **N**: Morphism metrics, classification reasoning, reversibility
    /// - **W**: Step-by-step morphism table, evolution suggestion
    pub fn from_morphism(source_name: &str, target_name: &str, morphism: &Morphism) -> Self {
        let metrics = classify_morphism(morphism);
        let source_info = information_content(&morphism.source);
        let target_info = information_content(&morphism.target);

        let l_items = vec![
            PanelItem::Section("Source".to_string()),
            PanelItem::KeyValue {
                key: "Name".to_string(),
                value: source_name.to_string(),
            },
            PanelItem::KeyValue {
                key: "Bits".to_string(),
                value: format!("{}", source_info),
            },
            PanelItem::Section("Target".to_string()),
            PanelItem::KeyValue {
                key: "Name".to_string(),
                value: target_name.to_string(),
            },
            PanelItem::KeyValue {
                key: "Bits".to_string(),
                value: format!("{}", target_info),
            },
            PanelItem::Section("Transport Bounds".to_string()),
            PanelItem::TransportBadge {
                label: format!("{} -> {}", source_name, target_name),
                class: morphism.transport_class,
            },
        ];

        let mut n_items = vec![
            PanelItem::Section("Morphism Metrics".to_string()),
            PanelItem::KeyValue {
                key: "Identity ratio".to_string(),
                value: format!("{:.0}%", metrics.identity_ratio * 100.0),
            },
            PanelItem::KeyValue {
                key: "Loss ratio".to_string(),
                value: format!("{:.0}%", metrics.loss_ratio * 100.0),
            },
            PanelItem::KeyValue {
                key: "Padding ratio".to_string(),
                value: format!("{:.0}%", metrics.padding_ratio * 100.0),
            },
            PanelItem::KeyValue {
                key: "Net bits".to_string(),
                value: format!("{:+}", metrics.net_bits),
            },
            PanelItem::KeyValue {
                key: "Reversibility".to_string(),
                value: format!("{:.0}%", metrics.reversibility * 100.0),
            },
            PanelItem::Section("Classification".to_string()),
        ];

        if metrics.is_pure_embedding {
            n_items.push(PanelItem::Info(
                "Pure embedding — all source data preserved, target has extra fields."
                    .to_string(),
            ));
        } else if metrics.is_pure_projection {
            n_items.push(PanelItem::Info(
                "Pure projection — some source data dropped, no new fields."
                    .to_string(),
            ));
        } else if morphism.transport_class == TransportClass::Concorde {
            n_items.push(PanelItem::Info(
                "Isomorphism — shapes carry identical information.".to_string(),
            ));
        } else {
            n_items.push(PanelItem::Info(
                "Mixed transformation — both additions and removals.".to_string(),
            ));
        }

        // Semver suggestion
        let semver = SemverClassification::from_transport_class(morphism.transport_class);
        n_items.push(PanelItem::SemverBadge {
            label: "Suggested version bump".to_string(),
            classification: semver,
        });

        let w_items = vec![
            PanelItem::Section("Morphism Steps".to_string()),
            PanelItem::MorphismTable(render::render_morphism_steps(morphism)),
        ];

        PanllFrame {
            panel_l: PanelData {
                panel: PanelId::L,
                title: format!("Constraints: {} -> {}", source_name, target_name),
                items: l_items,
            },
            panel_n: PanelData {
                panel: PanelId::N,
                title: format!("Reasoning: {} -> {}", source_name, target_name),
                items: n_items,
            },
            panel_w: PanelData {
                panel: PanelId::W,
                title: format!("Output: {} -> {}", source_name, target_name),
                items: w_items,
            },
        }
    }

    /// Create a PanLL frame from a schema timeline.
    ///
    /// - **L**: Version list, compatibility status, constraints
    /// - **N**: Evolution analysis, consistency checks, forecast
    /// - **W**: Rendered timeline diagram
    pub fn from_timeline(timeline: &SchemaTimeline) -> Self {
        let mut l_items = vec![
            PanelItem::Section("Timeline".to_string()),
            PanelItem::KeyValue {
                key: "Schema".to_string(),
                value: timeline.name().to_string(),
            },
            PanelItem::KeyValue {
                key: "Versions".to_string(),
                value: format!("{}", timeline.version_count()),
            },
        ];

        // Version list
        let version_strs: Vec<String> = timeline
            .versions()
            .iter()
            .map(|v| format!("v{}", v.version))
            .collect();
        if !version_strs.is_empty() {
            l_items.push(PanelItem::List {
                label: "Version history".to_string(),
                items: version_strs,
            });
        }

        // Compatibility constraint
        l_items.push(PanelItem::KeyValue {
            key: "Backward compatible".to_string(),
            value: format!("{}", timeline.is_fully_backward_compatible()),
        });

        let mut n_items = vec![PanelItem::Section("Evolution Analysis".to_string())];

        // Analyze each step
        for step in timeline.evolution_steps() {
            n_items.push(PanelItem::SemverBadge {
                label: format!("v{} -> v{}", step.from_version, step.to_version),
                classification: step.classification,
            });

            if !step.version_is_consistent() {
                n_items.push(PanelItem::Warning(format!(
                    "v{} -> v{}: declared bump is inconsistent with actual change",
                    step.from_version, step.to_version
                )));
            }
        }

        // Inconsistency summary
        let inconsistent = timeline.inconsistent_versions();
        if inconsistent.is_empty() {
            n_items.push(PanelItem::Info(
                "All version bumps are consistent with actual changes.".to_string(),
            ));
        } else {
            n_items.push(PanelItem::Warning(format!(
                "{} version bump(s) are inconsistent.",
                inconsistent.len()
            )));
        }

        // Breaking change info
        if let Some(breaking) = timeline.first_breaking_change() {
            n_items.push(PanelItem::Warning(format!(
                "First breaking change: v{} -> v{}",
                breaking.from_version, breaking.to_version
            )));
        }

        let w_items = vec![
            PanelItem::Section("Timeline Diagram".to_string()),
            PanelItem::TimelineDiagram(render::render_timeline(timeline)),
        ];

        PanllFrame {
            panel_l: PanelData {
                panel: PanelId::L,
                title: format!("Constraints: {}", timeline.name()),
                items: l_items,
            },
            panel_n: PanelData {
                panel: PanelId::N,
                title: format!("Reasoning: {}", timeline.name()),
                items: n_items,
            },
            panel_w: PanelData {
                panel: PanelId::W,
                title: format!("Output: {}", timeline.name()),
                items: w_items,
            },
        }
    }

    /// Create a PanLL frame from a shape category.
    ///
    /// - **L**: Object count, arrow count, isomorphic pairs
    /// - **N**: Pathfinding results, lossless reachability analysis
    /// - **W**: DOT graph, ASCII category view
    pub fn from_category(cat: &ShapeCategory) -> Self {
        let iso_pairs = cat.isomorphic_pairs();

        let mut l_items = vec![
            PanelItem::Section("Category Structure".to_string()),
            PanelItem::KeyValue {
                key: "Objects".to_string(),
                value: format!("{}", cat.object_count()),
            },
            PanelItem::KeyValue {
                key: "Arrows".to_string(),
                value: format!("{}", cat.arrow_count()),
            },
            PanelItem::KeyValue {
                key: "Isomorphic pairs".to_string(),
                value: format!("{}", iso_pairs.len()),
            },
        ];

        // Object list
        let object_ids: Vec<String> = cat.object_ids().map(|s| s.to_string()).collect();
        l_items.push(PanelItem::List {
            label: "Objects".to_string(),
            items: object_ids.clone(),
        });

        let mut n_items = vec![PanelItem::Section("Category Analysis".to_string())];

        // Isomorphic pairs
        if !iso_pairs.is_empty() {
            let pair_strs: Vec<String> =
                iso_pairs.iter().map(|(a, b)| format!("{} ≅ {}", a, b)).collect();
            n_items.push(PanelItem::List {
                label: "Isomorphic pairs".to_string(),
                items: pair_strs,
            });
        }

        // Lossless reachability
        for id in &object_ids {
            let mut reachable = cat.lossless_reachable(id);
            reachable.sort();
            if !reachable.is_empty() {
                n_items.push(PanelItem::Info(format!(
                    "{} losslessly reaches: {}",
                    id,
                    reachable.join(", ")
                )));
            }
        }

        let w_items = vec![
            PanelItem::Section("Category Graph".to_string()),
            PanelItem::DotGraph(render::render_category_dot(cat)),
            PanelItem::Section("ASCII View".to_string()),
            PanelItem::Info(render::render_category_ascii(cat)),
        ];

        PanllFrame {
            panel_l: PanelData {
                panel: PanelId::L,
                title: "Constraints: Shape Category".to_string(),
                items: l_items,
            },
            panel_n: PanelData {
                panel: PanelId::N,
                title: "Reasoning: Shape Category".to_string(),
                items: n_items,
            },
            panel_w: PanelData {
                panel: PanelId::W,
                title: "Output: Shape Category".to_string(),
                items: w_items,
            },
        }
    }

    /// Render all three panels as plain text (for terminal output).
    pub fn render_text(&self) -> String {
        let mut output = String::new();

        for panel in [&self.panel_l, &self.panel_n, &self.panel_w] {
            output.push_str(&format!(
                "╔══ Panel-{}: {} ══╗\n",
                panel.panel, panel.title
            ));

            for item in &panel.items {
                match item {
                    PanelItem::KeyValue { key, value } => {
                        output.push_str(&format!("  {}: {}\n", key, value));
                    }
                    PanelItem::Section(title) => {
                        output.push_str(&format!("  ── {} ──\n", title));
                    }
                    PanelItem::TransportBadge { label, class } => {
                        output.push_str(&format!(
                            "  {} {}\n",
                            label,
                            render::render_transport_badge(*class)
                        ));
                    }
                    PanelItem::SemverBadge {
                        label,
                        classification,
                    } => {
                        output.push_str(&format!("  {} [{}]\n", label, classification));
                    }
                    PanelItem::ShapeTree(tree) => {
                        for line in tree.lines() {
                            output.push_str(&format!("  {}\n", line));
                        }
                    }
                    PanelItem::MorphismTable(table) => {
                        for line in table.lines() {
                            output.push_str(&format!("  {}\n", line));
                        }
                    }
                    PanelItem::TimelineDiagram(diagram) => {
                        for line in diagram.lines() {
                            output.push_str(&format!("  {}\n", line));
                        }
                    }
                    PanelItem::DotGraph(dot) => {
                        output.push_str("  (DOT graph — pipe to `dot -Tsvg` for rendering)\n");
                        output.push_str(&format!("  {} lines\n", dot.lines().count()));
                    }
                    PanelItem::Warning(msg) => {
                        output.push_str(&format!("  ⚠ {}\n", msg));
                    }
                    PanelItem::Info(msg) => {
                        output.push_str(&format!("  ℹ {}\n", msg));
                    }
                    PanelItem::List { label, items } => {
                        output.push_str(&format!("  {}:\n", label));
                        for item in items {
                            output.push_str(&format!("    • {}\n", item));
                        }
                    }
                }
            }

            output.push_str(&format!(
                "╚══ End Panel-{} ══╝\n\n",
                panel.panel
            ));
        }

        output
    }
}

/// Get the top-level constructor name for a shape.
fn constructor_name(shape: &Shape) -> String {
    match shape {
        Shape::Unit => "Unit".to_string(),
        Shape::Atom(kind) => format!("Atom({})", kind),
        Shape::Product { .. } => "Product (struct)".to_string(),
        Shape::Sum { .. } => "Sum (enum)".to_string(),
        Shape::Dependent { .. } => "Dependent".to_string(),
        Shape::Recursive { var, .. } => format!("Recursive({})", var),
        Shape::Ref(name) => format!("Ref({})", name),
        Shape::Sequence(_) => "Sequence".to_string(),
        Shape::Optional(_) => "Optional".to_string(),
        Shape::Map { .. } => "Map".to_string(),
        Shape::Annotated { .. } => "Annotated".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::AtomKind;
    use crate::temporal::SemanticVersion;

    #[test]
    fn frame_from_shape() {
        let shape = Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I32)),
            ("name", Shape::Atom(AtomKind::String)),
        ]);

        let frame = PanllFrame::from_shape("User", &shape);

        // L panel has structure info
        assert_eq!(frame.panel_l.panel, PanelId::L);
        assert!(frame
            .panel_l
            .items
            .iter()
            .any(|i| matches!(i, PanelItem::KeyValue { key, .. } if key == "Fields")));

        // W panel has shape tree
        assert!(frame
            .panel_w
            .items
            .iter()
            .any(|i| matches!(i, PanelItem::ShapeTree(_))));
    }

    #[test]
    fn frame_from_morphism() {
        let source = Shape::Atom(AtomKind::I32);
        let target = Shape::Atom(AtomKind::I64);
        let morphism = crate::compare::compare(&source, &target);

        let frame = PanllFrame::from_morphism("i32", "i64", &morphism);

        // N panel has metrics
        assert!(frame
            .panel_n
            .items
            .iter()
            .any(|i| matches!(i, PanelItem::KeyValue { key, .. } if key == "Reversibility")));

        // L panel has transport badge
        assert!(frame
            .panel_l
            .items
            .iter()
            .any(|i| matches!(i, PanelItem::TransportBadge { .. })));
    }

    #[test]
    fn frame_from_timeline() {
        let mut timeline = SchemaTimeline::new("test");
        timeline.add_version(
            SemanticVersion::new(1, 0, 0),
            Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]),
        );
        timeline.add_version(
            SemanticVersion::new(1, 1, 0),
            Shape::struct_from(vec![
                ("id", Shape::Atom(AtomKind::I32)),
                ("name", Shape::Atom(AtomKind::String)),
            ]),
        );

        let frame = PanllFrame::from_timeline(&timeline);

        // L panel has version count
        assert!(frame
            .panel_l
            .items
            .iter()
            .any(|i| matches!(i, PanelItem::KeyValue { key, value } if key == "Versions" && value == "2")));

        // N panel has evolution analysis
        assert!(frame
            .panel_n
            .items
            .iter()
            .any(|i| matches!(i, PanelItem::SemverBadge { .. })));

        // W panel has timeline diagram
        assert!(frame
            .panel_w
            .items
            .iter()
            .any(|i| matches!(i, PanelItem::TimelineDiagram(_))));
    }

    #[test]
    fn frame_from_category() {
        let mut cat = ShapeCategory::new();
        cat.add_object("a", Shape::Atom(AtomKind::I32));
        cat.add_object("b", Shape::Atom(AtomKind::I64));
        cat.compare_all();

        let frame = PanllFrame::from_category(&cat);

        // L panel has object count
        assert!(frame
            .panel_l
            .items
            .iter()
            .any(|i| matches!(i, PanelItem::KeyValue { key, value } if key == "Objects" && value == "2")));

        // W panel has DOT graph
        assert!(frame
            .panel_w
            .items
            .iter()
            .any(|i| matches!(i, PanelItem::DotGraph(_))));
    }

    #[test]
    fn render_text_produces_all_panels() {
        let shape = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]);
        let frame = PanllFrame::from_shape("Test", &shape);
        let text = frame.render_text();

        assert!(text.contains("Panel-L"));
        assert!(text.contains("Panel-N"));
        assert!(text.contains("Panel-W"));
        assert!(text.contains("╔══"));
        assert!(text.contains("╚══"));
    }

    #[test]
    fn panel_id_display() {
        assert_eq!(format!("{}", PanelId::L), "L");
        assert_eq!(format!("{}", PanelId::N), "N");
        assert_eq!(format!("{}", PanelId::W), "W");
    }

    #[test]
    fn constructor_names() {
        assert_eq!(constructor_name(&Shape::Unit), "Unit");
        assert_eq!(constructor_name(&Shape::Atom(AtomKind::I32)), "Atom(i32)");
        assert!(constructor_name(&Shape::struct_from(vec![("a", Shape::Unit)])).contains("Product"));
    }
}
