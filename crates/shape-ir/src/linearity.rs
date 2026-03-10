// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Linearity — Resource Usage Semantics
//!
//! Not all data is created equal. A JSON string can be copied freely, but a
//! database connection handle must be used exactly once. A unique authentication
//! token can be dropped (revoked) but not duplicated. An audit log entry can be
//! copied (replicated) but must never be silently discarded.
//!
//! Linearity captures these resource semantics as a first-class property of shapes.
//! This is how the Shape IR models:
//! - Rust's ownership and borrowing (Affine)
//! - Linear types in languages like Clean and LinearML
//! - Database connection pools (Linear)
//! - Event sourcing's append-only guarantees (Relevant)
//! - Ordinary copyable data (Unrestricted)
//!
//! When composing morphisms, linearity constrains what transformations are legal.
//! You cannot duplicate a Linear shape, and you cannot silently drop a Relevant one.

use serde::{Deserialize, Serialize};
use std::fmt;

/// Resource usage semantics for a shape.
///
/// The four linearity modes form a lattice:
///
/// ```text
///        Unrestricted (copy + drop)
///          /              \
///       Affine           Relevant
///      (drop only)      (copy only)
///          \              /
///           Linear (neither)
/// ```
///
/// `Unrestricted` is the top (most permissive), `Linear` is the bottom (most
/// restrictive). When combining two shapes, the result's linearity is the meet
/// (greatest lower bound) of the two inputs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Linearity {
    /// Can copy, can drop. Most data lives here — strings, integers, structs
    /// with all-copyable fields. This is the default for shapes without
    /// explicit linearity annotations.
    Unrestricted,

    /// Must use exactly once — cannot copy, cannot drop. File handles, database
    /// connections, unique tokens, one-time-use encryption keys. If a morphism
    /// targets a Linear shape, it must consume the source exactly once.
    Linear,

    /// Can drop but not copy. Owned resources with move semantics — Rust's
    /// default ownership model. A morphism can discard an Affine shape, but
    /// cannot duplicate it.
    Affine,

    /// Can copy but not drop. Audit trails, must-acknowledge messages,
    /// append-only logs. A Relevant shape can be replicated but must eventually
    /// be consumed — it cannot be silently discarded.
    Relevant,
}

impl Linearity {
    /// Returns whether this linearity allows copying (duplication).
    pub fn can_copy(self) -> bool {
        matches!(self, Linearity::Unrestricted | Linearity::Relevant)
    }

    /// Returns whether this linearity allows dropping (discarding).
    pub fn can_drop(self) -> bool {
        matches!(self, Linearity::Unrestricted | Linearity::Affine)
    }

    /// Compute the meet (greatest lower bound) of two linearities.
    ///
    /// When combining shapes (e.g., in a Product), the compound shape's linearity
    /// is the most restrictive of its components. A struct containing one Linear
    /// field and one Unrestricted field is itself Linear.
    ///
    /// ```
    /// use shape_ir::Linearity;
    ///
    /// assert_eq!(Linearity::meet(Linearity::Unrestricted, Linearity::Linear), Linearity::Linear);
    /// assert_eq!(Linearity::meet(Linearity::Affine, Linearity::Relevant), Linearity::Linear);
    /// assert_eq!(Linearity::meet(Linearity::Unrestricted, Linearity::Affine), Linearity::Affine);
    /// ```
    pub fn meet(a: Linearity, b: Linearity) -> Linearity {
        let can_copy = a.can_copy() && b.can_copy();
        let can_drop = a.can_drop() && b.can_drop();
        match (can_copy, can_drop) {
            (true, true) => Linearity::Unrestricted,
            (true, false) => Linearity::Relevant,
            (false, true) => Linearity::Affine,
            (false, false) => Linearity::Linear,
        }
    }

    /// Compute the join (least upper bound) of two linearities.
    ///
    /// The join is the most permissive linearity that is at least as restrictive
    /// as one of the two inputs. Used when choosing between alternatives in a Sum.
    pub fn join(a: Linearity, b: Linearity) -> Linearity {
        let can_copy = a.can_copy() || b.can_copy();
        let can_drop = a.can_drop() || b.can_drop();
        match (can_copy, can_drop) {
            (true, true) => Linearity::Unrestricted,
            (true, false) => Linearity::Relevant,
            (false, true) => Linearity::Affine,
            (false, false) => Linearity::Linear,
        }
    }
}

impl Default for Linearity {
    /// The default linearity is Unrestricted — most data can be freely copied
    /// and dropped.
    fn default() -> Self {
        Linearity::Unrestricted
    }
}

impl fmt::Display for Linearity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Linearity::Unrestricted => write!(f, "unrestricted"),
            Linearity::Linear => write!(f, "linear"),
            Linearity::Affine => write!(f, "affine"),
            Linearity::Relevant => write!(f, "relevant"),
        }
    }
}
