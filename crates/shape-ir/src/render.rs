// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Visual Rendering — ASCII and DOT output for shapes, morphisms, and timelines
//!
//! Phase 5 of the Universal Data Shape vision: human-readable visual
//! representations of the entire shape algebra.
//!
//! ## Renderers
//!
//! | Function | Output | Purpose |
//! |----------|--------|---------|
//! | [`render_shape_tree`] | ASCII tree | Structural view of a shape |
//! | [`render_morphism_steps`] | ASCII table | Step-by-step morphism visualization |
//! | [`render_timeline`] | ASCII timeline | Schema evolution over versions |
//! | [`render_category_dot`] | Graphviz DOT | Category graph for external tools |
//! | [`render_category_ascii`] | ASCII graph | Category adjacency for terminals |
//! | [`render_transport_badge`] | Colored badge | Transport class indicator |

use crate::category::ShapeCategory;
use crate::information::{classify_morphism, information_content, TransportClass};
use crate::morphism::Morphism;
use crate::shape::Shape;
use crate::temporal::{EvolutionStep, SchemaTimeline, SemverClassification};

/// Render a shape as an indented ASCII tree.
///
/// Each constructor is shown on its own line with structural nesting.
/// Information content is annotated on leaf nodes.
///
/// ```text
/// Product "id"
/// ├── Atom(I32)                    [32 bits, fixed]
/// └── Product "name"
///     ├── Atom(String)             [0+ bits, unbounded]
///     └── Product "email"
///         ├── Optional
///         │   └── Atom(String)     [0+ bits, unbounded]
///         └── Unit
/// ```
pub fn render_shape_tree(shape: &Shape) -> String {
    let mut output = String::new();
    render_shape_node(&mut output, shape, "", true, true);
    output
}

fn render_shape_node(output: &mut String, shape: &Shape, prefix: &str, is_last: bool, is_root: bool) {
    let connector = if is_root {
        ""
    } else if is_last {
        "└── "
    } else {
        "├── "
    };

    let child_prefix = if is_root {
        String::new()
    } else if is_last {
        format!("{}    ", prefix)
    } else {
        format!("{}│   ", prefix)
    };

    match shape {
        Shape::Unit => {
            output.push_str(&format!("{}{}()\n", prefix, connector));
        }
        Shape::Atom(kind) => {
            let info = information_content(shape);
            let info_str = match info.max_bits {
                Some(max) if max == info.min_bits => format!("[{} bits, fixed]", info.min_bits),
                Some(max) => format!("[{}-{} bits]", info.min_bits, max),
                None => format!("[{}+ bits, unbounded]", info.min_bits),
            };
            output.push_str(&format!(
                "{}{}Atom({})  {}\n",
                prefix, connector, kind, info_str
            ));
        }
        Shape::Product { label, left, right } => {
            output.push_str(&format!("{}{}Product \"{}\"\n", prefix, connector, label));
            render_shape_node(output, left, &child_prefix, false, false);
            render_shape_node(output, right, &child_prefix, true, false);
        }
        Shape::Sum { label, left, right } => {
            output.push_str(&format!("{}{}Sum \"{}\"\n", prefix, connector, label));
            render_shape_node(output, left, &child_prefix, false, false);
            render_shape_node(output, right, &child_prefix, true, false);
        }
        Shape::Dependent { binder, body } => {
            output.push_str(&format!("{}{}Dependent\n", prefix, connector));
            render_shape_node(output, binder, &child_prefix, false, false);
            render_shape_node(output, body, &child_prefix, true, false);
        }
        Shape::Recursive { var, body } => {
            output.push_str(&format!("{}{}Recursive (mu {})\n", prefix, connector, var));
            render_shape_node(output, body, &child_prefix, true, false);
        }
        Shape::Ref(name) => {
            output.push_str(&format!("{}{}Ref({})\n", prefix, connector, name));
        }
        Shape::Sequence(inner) => {
            output.push_str(&format!("{}{}Sequence\n", prefix, connector));
            render_shape_node(output, inner, &child_prefix, true, false);
        }
        Shape::Optional(inner) => {
            output.push_str(&format!("{}{}Optional\n", prefix, connector));
            render_shape_node(output, inner, &child_prefix, true, false);
        }
        Shape::Map { key, value } => {
            output.push_str(&format!("{}{}Map\n", prefix, connector));
            render_shape_node(output, key, &child_prefix, false, false);
            render_shape_node(output, value, &child_prefix, true, false);
        }
        Shape::Annotated { shape, annotations } => {
            let constraints: Vec<String> = annotations
                .constraints
                .iter()
                .map(|c| format!("{}", c))
                .collect();
            let ann_str = if constraints.is_empty() {
                String::new()
            } else {
                format!("  @[{}]", constraints.join(", "))
            };
            output.push_str(&format!("{}{}Annotated{}\n", prefix, connector, ann_str));
            render_shape_node(output, shape, &child_prefix, true, false);
        }
    }
}

/// Render morphism steps as an ASCII table.
///
/// ```text
/// Step  Class        Path         Transformation
/// ────  ─────        ────         ──────────────
///  1    ≡ Concorde   .id          identity
///  2    ↑ Business   .name        identity
///  3    ↑ Business   .email       pad(null)
///  4    ↓ Economy    .age         project
/// ```
pub fn render_morphism_steps(morphism: &Morphism) -> String {
    let mut output = String::new();
    let metrics = classify_morphism(morphism);

    // Header
    output.push_str(&format!(
        "Morphism: {} [{} steps]\n",
        render_transport_badge(morphism.transport_class),
        morphism.steps.len()
    ));
    output.push_str(&format!(
        "  identity: {:.0}%  loss: {:.0}%  padding: {:.0}%  net: {:+} bits  reversibility: {:.0}%\n\n",
        metrics.identity_ratio * 100.0,
        metrics.loss_ratio * 100.0,
        metrics.padding_ratio * 100.0,
        metrics.net_bits,
        metrics.reversibility * 100.0,
    ));

    if morphism.steps.is_empty() {
        output.push_str("  (identity — no transformation steps)\n");
        return output;
    }

    // Column headers
    output.push_str("  Step  Class          Transformation\n");
    output.push_str("  ────  ─────          ──────────────\n");

    for (i, step) in morphism.steps.iter().enumerate() {
        let class_icon = match step.transport_class() {
            TransportClass::Concorde => "≡ Concorde  ",
            TransportClass::Business => "↑ Business  ",
            TransportClass::Economy => "↓ Economy   ",
            TransportClass::Wheelbarrow => "✗ Wheelbarrow",
        };

        output.push_str(&format!(
            "  {:>3}   {}  {}\n",
            i + 1,
            class_icon,
            step
        ));
    }

    output
}

/// Render a schema timeline as an ASCII evolution diagram.
///
/// ```text
/// Timeline: users
///
///   v1.0.0  ──[patch]──►  v1.0.1  ──[minor]──►  v1.1.0  ──[MAJOR]──►  v2.0.0
///             ≡ Concorde            ↑ Business              ↓ Economy
///             +0 -0 bits            +33 -0 bits             +0 -32 bits
/// ```
pub fn render_timeline(timeline: &SchemaTimeline) -> String {
    let mut output = String::new();

    output.push_str(&format!(
        "Timeline: {} ({} versions)\n",
        timeline.name(),
        timeline.version_count()
    ));

    if timeline.version_count() == 0 {
        output.push_str("  (empty)\n");
        return output;
    }

    // Backward compatibility summary
    if timeline.is_fully_backward_compatible() {
        output.push_str("  Status: fully backward compatible\n");
    } else if let Some(breaking) = timeline.first_breaking_change() {
        output.push_str(&format!(
            "  Status: breaking change at {} -> {}\n",
            breaking.from_version, breaking.to_version
        ));
    }

    // Inconsistency warnings
    let inconsistent = timeline.inconsistent_versions();
    if !inconsistent.is_empty() {
        output.push_str(&format!(
            "  Warning: {} inconsistent version bump(s)\n",
            inconsistent.len()
        ));
    }

    output.push('\n');

    // Version list with evolution steps
    let versions = timeline.versions();
    let steps = timeline.evolution_steps();

    for (i, vs) in versions.iter().enumerate() {
        let info = information_content(&vs.shape);
        let field_count = vs.shape.field_labels().len();

        output.push_str(&format!(
            "  v{}  ({} fields, {})\n",
            vs.version, field_count, info
        ));

        // Show shape summary
        output.push_str(&format!("    {}\n", vs.shape));

        if i < steps.len() {
            let step = &steps[i];
            render_evolution_arrow(&mut output, step);
        }
    }

    output
}

fn render_evolution_arrow(output: &mut String, step: &EvolutionStep) {
    let class_str = match step.classification {
        SemverClassification::Patch => "≡ patch (isomorphism)",
        SemverClassification::Minor => "↑ minor (additive)",
        SemverClassification::Major => "↓ MAJOR (breaking)",
    };

    let consistency = if step.version_is_consistent() {
        ""
    } else {
        " ⚠ INCONSISTENT BUMP"
    };

    output.push_str(&format!(
        "    │\n    ▼ {}  +{} -{} bits{}\n",
        class_str,
        step.information_cost.bits_added,
        step.information_cost.bits_lost,
        consistency,
    ));

    // Show up to 3 morphism steps
    let max_steps = 3;
    for (i, ms) in step.morphism.steps.iter().enumerate() {
        if i >= max_steps {
            output.push_str(&format!(
                "      ... and {} more steps\n",
                step.morphism.steps.len() - max_steps
            ));
            break;
        }
        output.push_str(&format!("      {}\n", ms));
    }
}

/// Render a transport class as a text badge.
///
/// Returns a compact label like `[≡ Concorde]` or `[↓ Economy]`.
pub fn render_transport_badge(tc: TransportClass) -> String {
    match tc {
        TransportClass::Concorde => "[≡ Concorde]".to_string(),
        TransportClass::Business => "[↑ Business]".to_string(),
        TransportClass::Economy => "[↓ Economy]".to_string(),
        TransportClass::Wheelbarrow => "[✗ Wheelbarrow]".to_string(),
    }
}

/// Render a [`ShapeCategory`] as a Graphviz DOT graph.
///
/// Objects become nodes. Arrows become directed edges colored by transport class:
/// - Concorde: green
/// - Business: blue
/// - Economy: orange
/// - Wheelbarrow: red
pub fn render_category_dot(cat: &ShapeCategory) -> String {
    let mut dot = String::new();

    dot.push_str("digraph ShapeCategory {\n");
    dot.push_str("  rankdir=LR;\n");
    dot.push_str("  node [shape=box, style=rounded, fontname=\"monospace\"];\n");
    dot.push_str("  edge [fontname=\"monospace\", fontsize=10];\n\n");

    // Nodes
    for id in cat.object_ids() {
        let info = cat.object(id).map(information_content);
        let info_label = info
            .map(|i| format!("\\n{}", i))
            .unwrap_or_default();
        dot.push_str(&format!(
            "  \"{}\" [label=\"{}{}\"];\n",
            id, id, info_label
        ));
    }

    dot.push('\n');

    // Edges
    let ids: Vec<String> = cat.object_ids().map(|s| s.to_string()).collect();
    for src in &ids {
        for tgt in &ids {
            if src == tgt {
                continue;
            }
            if let Some(m) = cat.arrow(src, tgt) {
                let (color, label) = match m.transport_class {
                    TransportClass::Concorde => ("green4", "Concorde"),
                    TransportClass::Business => ("blue3", "Business"),
                    TransportClass::Economy => ("orange3", "Economy"),
                    TransportClass::Wheelbarrow => ("red3", "Wheelbarrow"),
                };
                dot.push_str(&format!(
                    "  \"{}\" -> \"{}\" [label=\"{}\", color=\"{}\", fontcolor=\"{}\"];\n",
                    src, tgt, label, color, color
                ));
            }
        }
    }

    dot.push_str("}\n");
    dot
}

/// Render a [`ShapeCategory`] as an ASCII adjacency summary.
///
/// ```text
/// Shape Category: 4 objects, 12 arrows
///
///   protobuf.User ──[≡ Concorde]──► avro.User
///   protobuf.User ──[↑ Business]──► sql.users
///   sql.users     ──[↓ Economy]───► graphql.User
/// ```
pub fn render_category_ascii(cat: &ShapeCategory) -> String {
    let mut output = String::new();

    output.push_str(&format!(
        "Shape Category: {} objects, {} arrows\n\n",
        cat.object_count(),
        cat.arrow_count()
    ));

    // Isomorphic pairs first
    let iso_pairs = cat.isomorphic_pairs();
    if !iso_pairs.is_empty() {
        output.push_str("  Isomorphic pairs:\n");
        for (a, b) in &iso_pairs {
            output.push_str(&format!("    {} ≅ {}\n", a, b));
        }
        output.push('\n');
    }

    // All arrows
    output.push_str("  Arrows:\n");
    let ids: Vec<String> = cat.object_ids().map(|s| s.to_string()).collect();
    let max_id_len = ids.iter().map(|s| s.len()).max().unwrap_or(0);

    for src in &ids {
        for tgt in &ids {
            if src == tgt {
                continue;
            }
            if let Some(m) = cat.arrow(src, tgt) {
                let badge = render_transport_badge(m.transport_class);
                output.push_str(&format!(
                    "    {:width$} ──{}──► {}\n",
                    src,
                    badge,
                    tgt,
                    width = max_id_len
                ));
            }
        }
    }

    // Lossless reachability
    output.push_str("\n  Lossless reachability:\n");
    for id in &ids {
        let mut reachable = cat.lossless_reachable(id);
        reachable.sort();
        if !reachable.is_empty() {
            output.push_str(&format!(
                "    {:width$} -> {}\n",
                id,
                reachable.join(", "),
                width = max_id_len
            ));
        }
    }

    output
}

/// Render an evolution strategy comparison as ASCII.
///
/// Shows the planned evolution from source to target shape with suggested
/// version bump and morphism details.
pub fn render_evolution_strategy(
    source_name: &str,
    target_name: &str,
    source: &Shape,
    target: &Shape,
) -> String {
    let strategy = crate::temporal::plan_evolution(source, target);
    let mut output = String::new();

    output.push_str(&format!(
        "Evolution: {} -> {}\n",
        source_name, target_name
    ));
    output.push_str(&format!(
        "  Suggested bump: {}\n",
        strategy.suggested_version
    ));
    output.push_str(&format!(
        "  Transport: {}\n",
        render_transport_badge(strategy.direct_morphism.transport_class)
    ));
    output.push('\n');

    output.push_str(&render_morphism_steps(&strategy.direct_morphism));

    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::AtomKind;

    #[test]
    fn render_simple_struct_tree() {
        let shape = Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I32)),
            ("name", Shape::Atom(AtomKind::String)),
        ]);

        let tree = render_shape_tree(&shape);
        assert!(tree.contains("Product \"id\""));
        assert!(tree.contains("Atom(i32)"));
        assert!(tree.contains("Atom(string)"));
        assert!(tree.contains("[32 bits, fixed]"));
    }

    #[test]
    fn render_nested_optional_tree() {
        let shape = Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I32)),
            ("email", Shape::optional(Shape::Atom(AtomKind::String))),
        ]);

        let tree = render_shape_tree(&shape);
        assert!(tree.contains("Optional"));
        assert!(tree.contains("Atom(string)"));
    }

    #[test]
    fn render_sum_tree() {
        let shape = Shape::enum_from(vec![
            ("Ok", Shape::Atom(AtomKind::String)),
            ("Err", Shape::Atom(AtomKind::I32)),
        ]);

        let tree = render_shape_tree(&shape);
        assert!(tree.contains("Sum \"Ok\""));
        assert!(tree.contains("Sum \"Err\""));
    }

    #[test]
    fn render_map_tree() {
        let shape = Shape::map(Shape::Atom(AtomKind::String), Shape::Atom(AtomKind::I64));
        let tree = render_shape_tree(&shape);
        assert!(tree.contains("Map"));
        assert!(tree.contains("Atom(string)"));
        assert!(tree.contains("Atom(i64)"));
    }

    #[test]
    fn render_recursive_tree() {
        let shape = Shape::recursive(
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

        let tree = render_shape_tree(&shape);
        assert!(tree.contains("Recursive (mu List)"));
        assert!(tree.contains("Ref(List)"));
    }

    #[test]
    fn render_identity_morphism_steps() {
        let shape = Shape::Atom(AtomKind::I32);
        let morphism = Morphism::identity(shape);
        let rendered = render_morphism_steps(&morphism);
        assert!(rendered.contains("[≡ Concorde]"));
        assert!(rendered.contains("identity — no transformation steps"));
    }

    #[test]
    fn render_transport_badges() {
        assert_eq!(render_transport_badge(TransportClass::Concorde), "[≡ Concorde]");
        assert_eq!(render_transport_badge(TransportClass::Business), "[↑ Business]");
        assert_eq!(render_transport_badge(TransportClass::Economy), "[↓ Economy]");
        assert_eq!(
            render_transport_badge(TransportClass::Wheelbarrow),
            "[✗ Wheelbarrow]"
        );
    }

    #[test]
    fn render_timeline_empty() {
        let timeline = SchemaTimeline::new("empty");
        let rendered = render_timeline(&timeline);
        assert!(rendered.contains("Timeline: empty"));
        assert!(rendered.contains("(empty)"));
    }

    #[test]
    fn render_timeline_with_versions() {
        use crate::temporal::SemanticVersion;

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
        assert!(rendered.contains("Timeline: users (2 versions)"));
        assert!(rendered.contains("v1.0.0"));
        assert!(rendered.contains("v1.1.0"));
        assert!(rendered.contains("minor"));
    }

    #[test]
    fn render_category_dot_output() {
        let mut cat = ShapeCategory::new();
        cat.add_object("a", Shape::Atom(AtomKind::I32));
        cat.add_object("b", Shape::Atom(AtomKind::I64));
        cat.compare_all();

        let dot = render_category_dot(&cat);
        assert!(dot.contains("digraph ShapeCategory"));
        assert!(dot.contains("\"a\""));
        assert!(dot.contains("\"b\""));
        assert!(dot.contains("->"));
    }

    #[test]
    fn render_category_ascii_output() {
        let mut cat = ShapeCategory::new();
        cat.add_object("i32", Shape::Atom(AtomKind::I32));
        cat.add_object("i64", Shape::Atom(AtomKind::I64));
        cat.compare_all();

        let ascii = render_category_ascii(&cat);
        assert!(ascii.contains("Shape Category: 2 objects"));
        assert!(ascii.contains("Arrows:"));
    }

    #[test]
    fn render_evolution_strategy_output() {
        let source = Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I32)),
            ("name", Shape::Atom(AtomKind::String)),
        ]);
        let target = Shape::struct_from(vec![
            ("id", Shape::Atom(AtomKind::I64)),
            ("name", Shape::Atom(AtomKind::String)),
            ("email", Shape::optional(Shape::Atom(AtomKind::String))),
        ]);

        let rendered = render_evolution_strategy("v1", "v2", &source, &target);
        assert!(rendered.contains("Evolution: v1 -> v2"));
        assert!(rendered.contains("Suggested bump:"));
    }
}
