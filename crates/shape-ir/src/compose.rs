// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Morphism Composition
//!
//! Given two morphisms `f: A -> B` and `g: B -> C`, composition produces
//! `g . f: A -> C`. This is the fundamental operation that makes the category
//! of data shapes useful: N formats need only N morphisms to/from the IR,
//! not N^2 morphisms between every pair.
//!
//! Composition respects the algebra:
//! - **Transport class**: The composed class is the worst of the inputs
//! - **Information cost**: Costs are summed (information loss accumulates)
//! - **Steps**: Steps are concatenated (f's steps then g's steps)
//!
//! Associativity holds: `(h . g) . f = h . (g . f)`. This is a consequence
//! of the transport class composition being `max` and cost composition being `+`,
//! both of which are associative.

use crate::information::TransportClass;
use crate::morphism::Morphism;
use thiserror::Error;

/// Errors that can occur during morphism composition.
#[derive(Debug, Error)]
pub enum ComposeError {
    /// The target of `f` does not structurally match the source of `g`.
    /// Composition requires `f.target` and `g.source` to be compatible shapes.
    ///
    /// In Phase 2, this check will become more sophisticated — shapes that are
    /// isomorphic (differ only in annotation or field order) should compose.
    /// For now, we require structural equality.
    #[error(
        "Cannot compose: f's target does not match g's source.\n  f.target = {f_target}\n  g.source = {g_source}"
    )]
    ShapeMismatch {
        /// String representation of f's target shape.
        f_target: String,
        /// String representation of g's source shape.
        g_source: String,
    },
}

/// Compose two morphisms: given `f: A -> B` and `g: B -> C`, produce `g . f: A -> C`.
///
/// # Composition rules
///
/// 1. `f.target` must be structurally compatible with `g.source`
/// 2. The resulting transport class is `max(f.class, g.class)` — the worst of the two
/// 3. The resulting information cost is the sum of both costs
/// 4. The resulting steps are `f.steps ++ g.steps`
///
/// # Errors
///
/// Returns [`ComposeError::ShapeMismatch`] if `f.target` is not compatible
/// with `g.source`.
///
/// # Examples
///
/// ```
/// use shape_ir::{Shape, AtomKind, TransportClass};
/// use shape_ir::compare::compare;
/// use shape_ir::compose::compose;
///
/// let a = Shape::Atom(AtomKind::I32);
/// let b = Shape::Atom(AtomKind::I64);
/// let c = Shape::Atom(AtomKind::I128);
///
/// let f = compare(&a, &b); // i32 -> i64 (Business)
/// let g = compare(&b, &c); // i64 -> i128 (Business)
/// let h = compose(&f, &g).unwrap(); // i32 -> i128 (Business)
///
/// assert_eq!(h.transport_class, TransportClass::Business);
/// assert_eq!(h.steps.len(), f.steps.len() + g.steps.len());
/// ```
pub fn compose(f: &Morphism, g: &Morphism) -> Result<Morphism, ComposeError> {
    // Verify compatibility: f's target should match g's source.
    // We compare stripped shapes for structural compatibility.
    let f_target_stripped = f.target.strip_annotations();
    let g_source_stripped = g.source.strip_annotations();

    if f_target_stripped != g_source_stripped {
        return Err(ComposeError::ShapeMismatch {
            f_target: format!("{}", f.target),
            g_source: format!("{}", g.source),
        });
    }

    // Compose transport class: worst of the two
    let transport_class = TransportClass::compose(f.transport_class, g.transport_class);

    // Compose information cost: sum
    let information_cost = f.information_cost.sum(&g.information_cost);

    // Compose steps: concatenation
    let mut steps = f.steps.clone();
    steps.extend(g.steps.iter().cloned());

    Ok(Morphism {
        source: f.source.clone(),
        target: g.target.clone(),
        transport_class,
        information_cost,
        steps,
    })
}
