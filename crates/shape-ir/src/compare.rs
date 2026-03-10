// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Shape Comparison Engine
//!
//! The comparison engine is the core reasoning function: given two shapes,
//! compute the morphism that transforms one into the other. This is how
//! Protocol Squisher answers "how do I convert format A to format B?"
//!
//! The algorithm walks both shapes structurally, identifying:
//! - **Matching fields**: same name and compatible type -> Identity or Widen
//! - **Missing fields**: present in source, absent in target -> Project
//! - **Extra fields**: absent in source, present in target -> Pad
//! - **Type mismatches**: same name, incompatible types -> Narrow or Wheelbarrow
//! - **Renamed fields**: different names, same type (heuristic matching)
//!
//! The resulting morphism carries a transport class that tells you exactly how
//! much information is preserved, and steps that tell you exactly what to do.

use crate::atom::AtomKind;
use crate::information::{InformationCost, TransportClass};
use crate::labels::FieldPath;
use crate::morphism::{DefaultValue, Morphism, MorphismStep};
use crate::shape::Shape;
use std::collections::HashMap;

/// An environment mapping recursion variable names from source shapes to target
/// shapes. This enables alpha-equivalence: `Recursive("List", body)` and
/// `Recursive("L", body)` are considered equivalent if their bodies match after
/// renaming.
type AlphaEnv<'a> = Vec<(&'a str, &'a str)>;

/// Compare two shapes and compute the morphism from `source` to `target`.
///
/// This is the primary entry point for shape analysis. Given any two shapes,
/// it produces a [`Morphism`] that describes exactly how to transform data
/// conforming to `source` into data conforming to `target`.
///
/// # Examples
///
/// ```
/// use shape_ir::{Shape, AtomKind, TransportClass};
/// use shape_ir::compare::compare;
///
/// // Same shape -> Concorde (identity)
/// let s = Shape::Atom(AtomKind::I32);
/// let m = compare(&s, &s);
/// assert_eq!(m.transport_class, TransportClass::Concorde);
///
/// // Widening -> Business
/// let source = Shape::Atom(AtomKind::I32);
/// let target = Shape::Atom(AtomKind::I64);
/// let m = compare(&source, &target);
/// assert_eq!(m.transport_class, TransportClass::Business);
/// ```
pub fn compare(source: &Shape, target: &Shape) -> Morphism {
    let mut steps = Vec::new();
    let mut cost = InformationCost::zero();
    let path = FieldPath::root();
    let env = Vec::new();

    let class = compare_inner(source, target, &path, &mut steps, &mut cost, &env);

    Morphism {
        source: source.clone(),
        target: target.clone(),
        transport_class: class,
        information_cost: cost,
        steps,
    }
}

/// Recursively compare two shapes at a given path, accumulating morphism steps.
///
/// The `env` parameter tracks alpha-renaming for recursion variables: when we
/// enter `Recursive("X", bodyX)` vs `Recursive("Y", bodyY)`, we push
/// `("X", "Y")` so that `Ref("X")` and `Ref("Y")` are recognised as
/// corresponding references rather than falling through to Wheelbarrow.
fn compare_inner(
    source: &Shape,
    target: &Shape,
    path: &FieldPath,
    steps: &mut Vec<MorphismStep>,
    cost: &mut InformationCost,
    env: &AlphaEnv<'_>,
) -> TransportClass {
    // Strip annotations for structural comparison (but they still affect class)
    let source_bare = strip_annotations_shallow(source);
    let target_bare = strip_annotations_shallow(target);

    // Check annotation differences
    let annotation_class = compare_annotations(source, target);

    let structural_class = match (source_bare, target_bare) {
        // Both Unit -> identity
        (Shape::Unit, Shape::Unit) => TransportClass::Concorde,

        // Both atoms
        (Shape::Atom(a), Shape::Atom(b)) => compare_atoms(a, b, path, steps, cost),

        // Both products -> compare field by field
        (
            Shape::Product {
                label: la,
                left: left_a,
                right: right_a,
            },
            Shape::Product {
                label: lb,
                left: left_b,
                right: right_b,
            },
        ) => compare_products(
            la, left_a, right_a, lb, left_b, right_b, path, steps, cost, env,
        ),

        // Both sums -> compare variant by variant
        (
            Shape::Sum {
                label: la,
                left: left_a,
                right: right_a,
            },
            Shape::Sum {
                label: lb,
                left: left_b,
                right: right_b,
            },
        ) => compare_sums(
            la, left_a, right_a, lb, left_b, right_b, path, steps, cost, env,
        ),

        // Both dependent pairs -> compare binder and body
        (
            Shape::Dependent {
                binder: binder_a,
                body: body_a,
            },
            Shape::Dependent {
                binder: binder_b,
                body: body_b,
            },
        ) => {
            let binder_class =
                compare_inner(binder_a, binder_b, &path.join("[binder]"), steps, cost, env);
            let body_class = compare_inner(body_a, body_b, &path.join("[body]"), steps, cost, env);
            TransportClass::compose(binder_class, body_class)
        },

        // Both recursive types -> alpha-equivalent comparison of bodies
        (
            Shape::Recursive {
                var: var_a,
                body: body_a,
            },
            Shape::Recursive {
                var: var_b,
                body: body_b,
            },
        ) => {
            // Extend the alpha-renaming environment: occurrences of Ref(var_a)
            // in body_a correspond to Ref(var_b) in body_b.
            let mut extended_env = env.clone();
            extended_env.push((var_a.as_str(), var_b.as_str()));
            compare_inner(
                body_a,
                body_b,
                &path.join(format!("mu({})", var_a)),
                steps,
                cost,
                &extended_env,
            )
        },

        // Both sequences -> compare element types
        (Shape::Sequence(elem_a), Shape::Sequence(elem_b)) => {
            compare_inner(elem_a, elem_b, &path.join("[*]"), steps, cost, env)
        },

        // Both optionals -> compare inner types
        (Shape::Optional(inner_a), Shape::Optional(inner_b)) => {
            compare_inner(inner_a, inner_b, path, steps, cost, env)
        },

        // Both maps -> compare key and value types
        (Shape::Map { key: ka, value: va }, Shape::Map { key: kb, value: vb }) => {
            let key_class = compare_inner(ka, kb, &path.join("[key]"), steps, cost, env);
            let value_class = compare_inner(va, vb, &path.join("[value]"), steps, cost, env);
            TransportClass::compose(key_class, value_class)
        },

        // Both refs -> check alpha-equivalence first, then direct equality
        (Shape::Ref(a), Shape::Ref(b)) => {
            let alpha_match = env
                .iter()
                .rev()
                .any(|(sa, sb)| *sa == a.as_str() && *sb == b.as_str());
            if alpha_match || a == b {
                TransportClass::Concorde
            } else {
                // Different, unrelated recursion variables — structural mismatch
                steps.push(MorphismStep::Reencode {
                    path: path.clone(),
                    from_encoding: format!("${}", a),
                    to_encoding: format!("${}", b),
                });
                cost.transform_steps += 1;
                TransportClass::Wheelbarrow
            }
        },

        // Optional target wrapping non-optional source -> Business (embedding)
        (_, Shape::Optional(inner_b)) if !matches!(source_bare, Shape::Optional(_)) => {
            let inner_class = compare_inner(source_bare, inner_b, path, steps, cost, env);
            // Wrapping in Optional adds one bit of "always present" padding
            cost.bits_added += 1;
            TransportClass::compose(inner_class, TransportClass::Business)
        },

        // Non-optional target from optional source -> Economy (may lose None)
        (Shape::Optional(inner_a), _) if !matches!(target_bare, Shape::Optional(_)) => {
            let inner_class = compare_inner(inner_a, target_bare, path, steps, cost, env);
            cost.bits_lost += 1;
            TransportClass::compose(inner_class, TransportClass::Economy)
        },

        // Unit source, non-Unit target -> everything is padded
        (Shape::Unit, _) => {
            steps.push(MorphismStep::Pad {
                path: path.clone(),
                shape: target.clone(),
                default: DefaultValue::Null,
            });
            cost.transform_steps += 1;
            TransportClass::Business
        },

        // Non-Unit source, Unit target -> everything is dropped
        (_, Shape::Unit) => {
            steps.push(MorphismStep::Project { path: path.clone() });
            cost.transform_steps += 1;
            TransportClass::Economy
        },

        // All other constructor pairs are structurally incompatible (e.g.,
        // Atom vs Product, Sequence vs Map, Sum vs Dependent). No structural
        // morphism exists — requires full re-encoding through a wheelbarrow path.
        _ => {
            steps.push(MorphismStep::Reencode {
                path: path.clone(),
                from_encoding: format!("{}", source),
                to_encoding: format!("{}", target),
            });
            cost.transform_steps += 1;
            TransportClass::Wheelbarrow
        },
    };

    TransportClass::compose(structural_class, annotation_class)
}

/// Compare two atoms and produce appropriate morphism steps.
fn compare_atoms(
    a: &AtomKind,
    b: &AtomKind,
    path: &FieldPath,
    steps: &mut Vec<MorphismStep>,
    cost: &mut InformationCost,
) -> TransportClass {
    if a == b {
        // Identical atom types -> identity
        steps.push(MorphismStep::Identity { path: path.clone() });
        cost.identity_paths += 1;
        TransportClass::Concorde
    } else if a.can_widen_to(b) {
        // Lossless widening
        let from_bits = a.bit_width().unwrap_or(0);
        let to_bits = b.bit_width().unwrap_or(0);
        cost.bits_added += to_bits.saturating_sub(from_bits);
        cost.transform_steps += 1;
        steps.push(MorphismStep::Widen {
            path: path.clone(),
            from: a.clone(),
            to: b.clone(),
        });
        TransportClass::Business
    } else if b.can_widen_to(a) {
        // Narrowing (reverse of widening)
        let from_bits = a.bit_width().unwrap_or(0);
        let to_bits = b.bit_width().unwrap_or(0);
        cost.bits_lost += from_bits.saturating_sub(to_bits);
        cost.transform_steps += 1;
        steps.push(MorphismStep::Narrow {
            path: path.clone(),
            from: a.clone(),
            to: b.clone(),
        });
        TransportClass::Economy
    } else {
        // Incompatible atom types
        cost.transform_steps += 1;
        steps.push(MorphismStep::Reencode {
            path: path.clone(),
            from_encoding: format!("{}", a),
            to_encoding: format!("{}", b),
        });
        TransportClass::Wheelbarrow
    }
}

/// Compare two product (struct) shapes, matching fields by label name.
#[allow(clippy::too_many_arguments)]
fn compare_products(
    la: &crate::labels::Label,
    left_a: &Shape,
    right_a: &Shape,
    lb: &crate::labels::Label,
    left_b: &Shape,
    right_b: &Shape,
    path: &FieldPath,
    steps: &mut Vec<MorphismStep>,
    cost: &mut InformationCost,
    env: &AlphaEnv<'_>,
) -> TransportClass {
    // Collect fields from both product chains
    let source_fields = collect_product_fields_from(la, left_a, right_a);
    let target_fields = collect_product_fields_from(lb, left_b, right_b);

    let source_map: HashMap<&str, &Shape> = source_fields
        .iter()
        .map(|(name, shape)| (name.as_str(), *shape))
        .collect();
    let target_map: HashMap<&str, &Shape> = target_fields
        .iter()
        .map(|(name, shape)| (name.as_str(), *shape))
        .collect();

    let mut overall_class = TransportClass::Concorde;

    // Match fields present in both
    for (name, source_shape) in &source_fields {
        let field_path = path.join(name.as_str());
        if let Some(target_shape) = target_map.get(name.as_str()) {
            let class = compare_inner(source_shape, target_shape, &field_path, steps, cost, env);
            overall_class = TransportClass::compose(overall_class, class);
        } else {
            // Field in source but not target -> projection (loss)
            steps.push(MorphismStep::Project { path: field_path });
            cost.transform_steps += 1;
            if let Some(bits) = source_shape_bits(source_shape) {
                cost.bits_lost += bits;
            }
            overall_class = TransportClass::compose(overall_class, TransportClass::Economy);
        }
    }

    // Fields in target but not source -> padding
    for (name, target_shape) in &target_fields {
        if !source_map.contains_key(name.as_str()) {
            let field_path = path.join(name.as_str());
            steps.push(MorphismStep::Pad {
                path: field_path,
                shape: (*target_shape).clone(),
                default: default_for_shape(target_shape),
            });
            cost.transform_steps += 1;
            if let Some(bits) = source_shape_bits(target_shape) {
                cost.bits_added += bits;
            }
            overall_class = TransportClass::compose(overall_class, TransportClass::Business);
        }
    }

    overall_class
}

/// Compare two sum (enum/union) shapes, matching variants by label name.
#[allow(clippy::too_many_arguments)]
fn compare_sums(
    la: &crate::labels::Label,
    left_a: &Shape,
    right_a: &Shape,
    lb: &crate::labels::Label,
    left_b: &Shape,
    right_b: &Shape,
    path: &FieldPath,
    steps: &mut Vec<MorphismStep>,
    cost: &mut InformationCost,
    env: &AlphaEnv<'_>,
) -> TransportClass {
    let source_variants = collect_sum_variants_from(la, left_a, right_a);
    let target_variants = collect_sum_variants_from(lb, left_b, right_b);

    let target_map: HashMap<&str, &Shape> = target_variants
        .iter()
        .map(|(name, shape)| (name.as_str(), *shape))
        .collect();

    let mut overall_class = TransportClass::Concorde;

    for (name, source_shape) in &source_variants {
        let variant_path = path.join(name.as_str());
        if let Some(target_shape) = target_map.get(name.as_str()) {
            let class = compare_inner(source_shape, target_shape, &variant_path, steps, cost, env);
            overall_class = TransportClass::compose(overall_class, class);
        } else {
            // Variant in source but not target -> data can't be represented
            steps.push(MorphismStep::Project { path: variant_path });
            cost.transform_steps += 1;
            overall_class = TransportClass::compose(overall_class, TransportClass::Economy);
        }
    }

    // Extra variants in target don't degrade class (they're just unused)
    overall_class
}

/// Collect named fields from a product chain into a flat Vec.
fn collect_product_fields_from<'a>(
    label: &'a crate::labels::Label,
    left: &'a Shape,
    right: &'a Shape,
) -> Vec<(String, &'a Shape)> {
    let mut fields = vec![(label.name.clone(), left)];
    collect_product_tail(right, &mut fields);
    fields
}

/// Recursively collect the tail of a product chain.
fn collect_product_tail<'a>(shape: &'a Shape, fields: &mut Vec<(String, &'a Shape)>) {
    match shape {
        Shape::Product { label, left, right } => {
            fields.push((label.name.clone(), left.as_ref()));
            collect_product_tail(right, fields);
        },
        Shape::Annotated { shape, .. } => collect_product_tail(shape, fields),
        Shape::Unit => {}, // End of chain
        _ => {},           // Unexpected tail — ignore for now
    }
}

/// Collect named variants from a sum chain into a flat Vec.
fn collect_sum_variants_from<'a>(
    label: &'a crate::labels::Label,
    left: &'a Shape,
    right: &'a Shape,
) -> Vec<(String, &'a Shape)> {
    let mut variants = vec![(label.name.clone(), left)];
    collect_sum_tail(right, &mut variants);
    variants
}

/// Recursively collect the tail of a sum chain.
fn collect_sum_tail<'a>(shape: &'a Shape, variants: &mut Vec<(String, &'a Shape)>) {
    match shape {
        Shape::Sum { label, left, right } => {
            variants.push((label.name.clone(), left.as_ref()));
            collect_sum_tail(right, variants);
        },
        Shape::Annotated { shape, .. } => collect_sum_tail(shape, variants),
        Shape::Unit => {},
        _ => {},
    }
}

/// Strip one layer of annotations (shallow, not recursive).
fn strip_annotations_shallow(shape: &Shape) -> &Shape {
    match shape {
        Shape::Annotated { shape, .. } => strip_annotations_shallow(shape),
        other => other,
    }
}

/// Compare annotations between two shapes for transport class impact.
fn compare_annotations(source: &Shape, target: &Shape) -> TransportClass {
    let source_ann = extract_annotations(source);
    let target_ann = extract_annotations(target);

    match (source_ann, target_ann) {
        (None, None) => TransportClass::Concorde,
        (Some(_), None) => TransportClass::Concorde, // Dropping annotations is fine
        (None, Some(_)) => TransportClass::Business, // Adding annotations is padding
        (Some(a), Some(b)) => match a.constraints.len().cmp(&b.constraints.len()) {
            std::cmp::Ordering::Greater => TransportClass::Concorde, // less restrictive target
            std::cmp::Ordering::Less => TransportClass::Economy,     // more restrictive target
            std::cmp::Ordering::Equal => TransportClass::Concorde,
        },
    }
}

/// Extract annotations from a shape if it's annotated.
fn extract_annotations(shape: &Shape) -> Option<&crate::annotations::Annotations> {
    match shape {
        Shape::Annotated { annotations, .. } => Some(annotations),
        _ => None,
    }
}

/// Estimate the bit width of a shape for cost calculation.
fn source_shape_bits(shape: &Shape) -> Option<u64> {
    let info = crate::information::information_content(shape);
    info.max_bits.or(Some(info.min_bits))
}

/// Produce a sensible default value for a shape.
fn default_for_shape(shape: &Shape) -> DefaultValue {
    match shape {
        Shape::Unit => DefaultValue::Null,
        Shape::Atom(kind) => match kind {
            AtomKind::Bool => DefaultValue::Bool(false),
            AtomKind::String => DefaultValue::String(String::new()),
            AtomKind::Bytes => DefaultValue::Bytes(Vec::new()),
            AtomKind::Enum(variants) => {
                if let Some(first) = variants.first() {
                    DefaultValue::String(first.clone())
                } else {
                    DefaultValue::Null
                }
            },
            _ => DefaultValue::Integer(0),
        },
        Shape::Optional(_) => DefaultValue::Null,
        Shape::Sequence(_) => DefaultValue::EmptyCollection,
        Shape::Map { .. } => DefaultValue::EmptyCollection,
        Shape::Annotated { shape, .. } => default_for_shape(shape),
        _ => DefaultValue::Null,
    }
}
