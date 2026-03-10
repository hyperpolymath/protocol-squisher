// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Shape subcommand — extract, graph, compare, render, and visualize data shapes
//!
//! This wires the shape-ir crate into the CLI, enabling users to extract
//! Shape IR representations from any of the 17 supported protocol formats,
//! build shape category graphs with adapter discovery, compare schemas,
//! render visual trees, export DOT graphs, view timelines, and get
//! PanLL three-panel views.

use anyhow::{Context, Result};
use colored::Colorize;
use shape_ir::category::ShapeCategory;
use shape_ir::extract::extract_schema;
use shape_ir::information::{classify_morphism, information_content};
use shape_ir::panll::PanllFrame;
use shape_ir::render;
use shape_ir::temporal::{SchemaTimeline, SemanticVersion};

use crate::formats::ProtocolFormat;
use crate::ShapeCommand;

/// Dispatch shape subcommands.
pub fn run(command: ShapeCommand) -> Result<()> {
    match command {
        ShapeCommand::Extract {
            protocol,
            input,
            format,
        } => {
            let proto = ProtocolFormat::from_str(&protocol)?;
            let ir_schema = proto.analyze_file(&input).with_context(|| {
                format!("Failed to analyze {} as {}", input.display(), protocol)
            })?;

            let extracted = extract_schema(&ir_schema);

            match format.as_str() {
                "json" => {
                    let output: serde_json::Value = extracted
                        .shapes
                        .iter()
                        .map(|(name, shape)| {
                            let info = information_content(shape);
                            (
                                name.clone(),
                                serde_json::json!({
                                    "shape": shape,
                                    "display": format!("{}", shape),
                                    "information": {
                                        "min_bits": info.min_bits,
                                        "max_bits": info.max_bits,
                                        "is_fixed_size": info.is_fixed_size,
                                        "cardinality": info.cardinality.map(|c| c.to_string()),
                                    },
                                }),
                            )
                        })
                        .collect();
                    println!("{}", serde_json::to_string_pretty(&output)?);
                },
                _ => {
                    println!(
                        "{} {} ({} format, {} types)",
                        "Shape extraction:".bright_green().bold(),
                        ir_schema.name,
                        extracted.source_format.bright_cyan(),
                        extracted.shapes.len()
                    );
                    println!();

                    for (name, shape) in &extracted.shapes {
                        let info = information_content(shape);
                        println!("  {} {}", "type".bright_yellow(), name.bold());
                        println!("    {}", shape);
                        println!("    {} {}", "information:".dimmed(), info);
                        println!();
                    }
                },
            }

            Ok(())
        },

        ShapeCommand::Graph {
            protocol,
            inputs,
            from,
            to,
            format,
        } => {
            let proto = ProtocolFormat::from_str(&protocol)?;
            let mut cat = ShapeCategory::new();

            // Extract shapes from all input files and add them as objects
            for input in &inputs {
                let ir_schema = proto
                    .analyze_file(input)
                    .with_context(|| format!("Failed to analyze {}", input.display()))?;
                let extracted = extract_schema(&ir_schema);
                for (name, shape) in extracted.shapes {
                    cat.add_object(name, shape);
                }
            }

            // Compare all pairs to build the morphism graph
            cat.compare_all();

            match format.as_str() {
                "json" => {
                    let mut comparisons = Vec::new();
                    let ids: Vec<String> = cat.object_ids().map(|s| s.to_string()).collect();
                    for src in &ids {
                        for tgt in &ids {
                            if src == tgt {
                                continue;
                            }
                            if let Some(m) = cat.arrow(src, tgt) {
                                comparisons.push(serde_json::json!({
                                    "source": src,
                                    "target": tgt,
                                    "transport_class": format!("{}", m.transport_class),
                                    "is_lossless": m.is_lossless(),
                                }));
                            }
                        }
                    }

                    let mut output = serde_json::json!({
                        "objects": cat.object_count(),
                        "arrows": cat.arrow_count(),
                        "isomorphic_pairs": cat.isomorphic_pairs(),
                        "edges": comparisons,
                    });

                    if let (Some(from_id), Some(to_id)) = (&from, &to) {
                        if let Some(path) = cat.find_path(from_id, to_id) {
                            let composed = cat.compose_path(&path);
                            output["path"] = serde_json::json!({
                                "from": from_id,
                                "to": to_id,
                                "hops": path.len(),
                                "steps": path,
                                "transport_class": composed.as_ref()
                                    .map(|m| format!("{}", m.transport_class)),
                            });
                        }
                    }

                    println!("{}", serde_json::to_string_pretty(&output)?);
                },
                _ => {
                    println!(
                        "{} {} objects, {} arrows",
                        "Shape category:".bright_green().bold(),
                        cat.object_count(),
                        cat.arrow_count(),
                    );
                    println!();

                    // Show isomorphic pairs
                    let iso_pairs = cat.isomorphic_pairs();
                    if !iso_pairs.is_empty() {
                        println!("  {}", "Isomorphic pairs:".bright_cyan());
                        for (a, b) in &iso_pairs {
                            println!("    {} {} {}", a, "≅".bright_green(), b);
                        }
                        println!();
                    }

                    // Show pathfinding result if requested
                    if let (Some(from_id), Some(to_id)) = (&from, &to) {
                        match cat.find_path(from_id, to_id) {
                            Some(path) if path.is_empty() => {
                                println!(
                                    "  {} {} → {} (identity — same shape)",
                                    "Path:".bright_yellow(),
                                    from_id,
                                    to_id,
                                );
                            },
                            Some(path) => {
                                let composed = cat.compose_path(&path);
                                let class_str = composed
                                    .as_ref()
                                    .map(|m| match m.transport_class {
                                        shape_ir::TransportClass::Concorde => {
                                            "Concorde".bright_green()
                                        },
                                        shape_ir::TransportClass::Business => {
                                            "Business".bright_blue()
                                        },
                                        shape_ir::TransportClass::Economy => {
                                            "Economy".bright_yellow()
                                        },
                                        shape_ir::TransportClass::Wheelbarrow => {
                                            "Wheelbarrow".bright_red()
                                        },
                                    })
                                    .unwrap_or_else(|| "unknown".normal());

                                println!(
                                    "  {} {} → {} ({} hops) [{}]",
                                    "Path:".bright_yellow(),
                                    from_id,
                                    to_id,
                                    path.len(),
                                    class_str,
                                );
                                for (i, (src, tgt)) in path.iter().enumerate() {
                                    let arrow = cat.arrow(src, tgt);
                                    let class = arrow
                                        .map(|m| format!("{}", m.transport_class))
                                        .unwrap_or_default();
                                    println!(
                                        "    {}. {} {} {} [{}]",
                                        i + 1,
                                        src,
                                        "→".dimmed(),
                                        tgt,
                                        class,
                                    );
                                }

                                if let Some(m) = composed {
                                    let metrics = classify_morphism(&m);
                                    println!(
                                        "    {} {:.0}% identity, {:.0}% reversible, net {:+} bits",
                                        "metrics:".dimmed(),
                                        metrics.identity_ratio * 100.0,
                                        metrics.reversibility * 100.0,
                                        metrics.net_bits,
                                    );
                                }
                            },
                            None => {
                                println!(
                                    "  {} No path from {} to {}",
                                    "Path:".bright_red(),
                                    from_id,
                                    to_id,
                                );
                            },
                        }
                        println!();
                    }

                    // Show lossless reachability summary
                    let ids: Vec<String> = cat.object_ids().map(|s| s.to_string()).collect();
                    println!("  {}", "Lossless reachability:".bright_cyan());
                    for id in &ids {
                        let mut reachable = cat.lossless_reachable(id);
                        reachable.sort();
                        if !reachable.is_empty() {
                            println!("    {} {} {}", id, "→".dimmed(), reachable.join(", "));
                        }
                    }
                },
            }

            Ok(())
        },

        ShapeCommand::Compare {
            from_format,
            to_format,
            from_path,
            to_path,
            format,
        } => {
            let from_proto = ProtocolFormat::from_str(&from_format)?;
            let to_proto = ProtocolFormat::from_str(&to_format)?;

            let from_ir = from_proto
                .analyze_file(&from_path)
                .with_context(|| format!("Failed to analyze {}", from_path.display()))?;
            let to_ir = to_proto
                .analyze_file(&to_path)
                .with_context(|| format!("Failed to analyze {}", to_path.display()))?;

            let from_shapes = extract_schema(&from_ir);
            let to_shapes = extract_schema(&to_ir);

            // Compare matching type names
            let mut comparisons = Vec::new();
            for (name, source_shape) in &from_shapes.shapes {
                if let Some(target_shape) = to_shapes.shapes.get(name) {
                    let morphism = shape_ir::compare::compare(source_shape, target_shape);
                    comparisons.push((name.clone(), morphism));
                }
            }

            // Also find types only in source or target
            let source_only: Vec<&str> = from_shapes
                .shapes
                .keys()
                .filter(|k| !to_shapes.shapes.contains_key(k.as_str()))
                .map(|k| k.as_str())
                .collect();
            let target_only: Vec<&str> = to_shapes
                .shapes
                .keys()
                .filter(|k| !from_shapes.shapes.contains_key(k.as_str()))
                .map(|k| k.as_str())
                .collect();

            match format.as_str() {
                "json" => {
                    let output = serde_json::json!({
                        "source": {
                            "format": from_format,
                            "file": from_path.display().to_string(),
                            "types": from_shapes.shapes.len(),
                        },
                        "target": {
                            "format": to_format,
                            "file": to_path.display().to_string(),
                            "types": to_shapes.shapes.len(),
                        },
                        "comparisons": comparisons.iter().map(|(name, m)| {
                            let metrics = classify_morphism(m);
                            serde_json::json!({
                                "type": name,
                                "transport_class": format!("{}", m.transport_class),
                                "is_lossless": m.is_lossless(),
                                "steps": m.steps.len(),
                                "cost": {
                                    "bits_added": m.information_cost.bits_added,
                                    "bits_lost": m.information_cost.bits_lost,
                                    "identity_paths": m.information_cost.identity_paths,
                                    "transform_steps": m.information_cost.transform_steps,
                                },
                                "metrics": {
                                    "identity_ratio": metrics.identity_ratio,
                                    "loss_ratio": metrics.loss_ratio,
                                    "padding_ratio": metrics.padding_ratio,
                                    "net_bits": metrics.net_bits,
                                    "is_pure_embedding": metrics.is_pure_embedding,
                                    "is_pure_projection": metrics.is_pure_projection,
                                    "reversibility": metrics.reversibility,
                                },
                            })
                        }).collect::<Vec<_>>(),
                        "source_only": source_only,
                        "target_only": target_only,
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                },
                _ => {
                    println!(
                        "{} {} ({}) vs {} ({})",
                        "Shape comparison:".bright_green().bold(),
                        from_path.display(),
                        from_format.bright_cyan(),
                        to_path.display(),
                        to_format.bright_cyan(),
                    );
                    println!();

                    if comparisons.is_empty() && source_only.is_empty() && target_only.is_empty() {
                        println!("  No types found to compare.");
                        return Ok(());
                    }

                    for (name, morphism) in &comparisons {
                        let metrics = classify_morphism(morphism);
                        let class_color = match morphism.transport_class {
                            shape_ir::TransportClass::Concorde => "Concorde".bright_green(),
                            shape_ir::TransportClass::Business => "Business".bright_blue(),
                            shape_ir::TransportClass::Economy => "Economy".bright_yellow(),
                            shape_ir::TransportClass::Wheelbarrow => "Wheelbarrow".bright_red(),
                        };

                        println!("  {} {} [{}]", name.bold(), "->".dimmed(), class_color,);
                        println!(
                            "    {} +{} bits, -{} bits, {} identity, {} transforms",
                            "cost:".dimmed(),
                            morphism.information_cost.bits_added,
                            morphism.information_cost.bits_lost,
                            morphism.information_cost.identity_paths,
                            morphism.information_cost.transform_steps,
                        );

                        // Metrics summary line
                        let direction = if metrics.is_pure_embedding {
                            "pure embedding".bright_blue()
                        } else if metrics.is_pure_projection {
                            "pure projection".bright_yellow()
                        } else if metrics.transport_class == shape_ir::TransportClass::Concorde {
                            "isomorphism".bright_green()
                        } else {
                            "mixed".normal()
                        };
                        println!(
                            "    {} {} | {:.0}% identity, {:.0}% reversible, net {:+} bits",
                            "metrics:".dimmed(),
                            direction,
                            metrics.identity_ratio * 100.0,
                            metrics.reversibility * 100.0,
                            metrics.net_bits,
                        );

                        // Show first few steps
                        let max_steps = 5;
                        for (i, step) in morphism.steps.iter().enumerate() {
                            if i >= max_steps {
                                println!(
                                    "    {} ... and {} more",
                                    "".dimmed(),
                                    morphism.steps.len() - max_steps
                                );
                                break;
                            }
                            println!("    {} {}", "-".dimmed(), step);
                        }
                        println!();
                    }

                    if !source_only.is_empty() {
                        println!(
                            "  {} {}",
                            "Source only:".bright_yellow(),
                            source_only.join(", ")
                        );
                    }
                    if !target_only.is_empty() {
                        println!(
                            "  {} {}",
                            "Target only:".bright_yellow(),
                            target_only.join(", ")
                        );
                    }
                },
            }

            Ok(())
        },

        ShapeCommand::Render { protocol, input } => {
            let proto = ProtocolFormat::from_str(&protocol)?;
            let ir_schema = proto.analyze_file(&input).with_context(|| {
                format!("Failed to analyze {} as {}", input.display(), protocol)
            })?;

            let extracted = extract_schema(&ir_schema);

            println!(
                "{} {} ({} types)",
                "Shape trees:".bright_green().bold(),
                ir_schema.name,
                extracted.shapes.len()
            );
            println!();

            for (name, shape) in &extracted.shapes {
                println!("  {} {}", "type".bright_yellow(), name.bold());
                print!("{}", render::render_shape_tree(shape));
                println!();
            }

            Ok(())
        },

        ShapeCommand::Dot { protocol, inputs } => {
            let proto = ProtocolFormat::from_str(&protocol)?;
            let mut cat = ShapeCategory::new();

            for input in &inputs {
                let ir_schema = proto
                    .analyze_file(input)
                    .with_context(|| format!("Failed to analyze {}", input.display()))?;
                let extracted = extract_schema(&ir_schema);
                for (name, shape) in extracted.shapes {
                    cat.add_object(name, shape);
                }
            }

            cat.compare_all();
            print!("{}", render::render_category_dot(&cat));

            Ok(())
        },

        ShapeCommand::Timeline {
            protocol,
            inputs,
            name,
        } => {
            let proto = ProtocolFormat::from_str(&protocol)?;
            let mut timeline = SchemaTimeline::new(&name);

            for (i, input) in inputs.iter().enumerate() {
                let ir_schema = proto
                    .analyze_file(input)
                    .with_context(|| format!("Failed to analyze {}", input.display()))?;
                let extracted = extract_schema(&ir_schema);

                // Take the first type from each schema file as the version
                if let Some((_type_name, shape)) = extracted.shapes.into_iter().next() {
                    let version = SemanticVersion::new((i + 1) as u32, 0, 0);
                    timeline.add_version(version, shape);
                }
            }

            print!("{}", render::render_timeline(&timeline));

            Ok(())
        },

        ShapeCommand::Panll {
            protocol,
            inputs,
            format,
        } => {
            let proto = ProtocolFormat::from_str(&protocol)?;

            let frame = if inputs.len() == 1 {
                // Single file — shape inspection
                let ir_schema = proto.analyze_file(&inputs[0]).with_context(|| {
                    format!("Failed to analyze {}", inputs[0].display())
                })?;
                let extracted = extract_schema(&ir_schema);

                if extracted.shapes.len() == 1 {
                    let (name, shape) = extracted.shapes.into_iter().next().unwrap();
                    PanllFrame::from_shape(&name, &shape)
                } else {
                    // Multiple types — build category
                    let mut cat = ShapeCategory::new();
                    for (name, shape) in extracted.shapes {
                        cat.add_object(name, shape);
                    }
                    cat.compare_all();
                    PanllFrame::from_category(&cat)
                }
            } else {
                // Multiple files — build category
                let mut cat = ShapeCategory::new();
                for input in &inputs {
                    let ir_schema = proto
                        .analyze_file(input)
                        .with_context(|| format!("Failed to analyze {}", input.display()))?;
                    let extracted = extract_schema(&ir_schema);
                    for (name, shape) in extracted.shapes {
                        cat.add_object(name, shape);
                    }
                }
                cat.compare_all();
                PanllFrame::from_category(&cat)
            };

            match format.as_str() {
                "json" => {
                    println!("{}", serde_json::to_string_pretty(&frame)?);
                },
                _ => {
                    print!("{}", frame.render_text());
                },
            }

            Ok(())
        },
    }
}
