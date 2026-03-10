// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

#![warn(missing_docs)]

//! # Shape IR — Universal Data Shape Intermediate Representation
//!
//! The Shape IR is the foundation of Protocol Squisher's evolution from a format
//! converter into a universal data shape reasoning engine. Every serialization
//! format, database schema, API contract, type system, memory layout, and
//! configuration format can be expressed as a [`Shape`].
//!
//! ## Core concepts
//!
//! - **[`Shape`]**: The universal representation of data shape — 11 constructors
//!   that compose to describe any data structure.
//! - **[`AtomKind`]**: Primitive atomic types — the leaves of the shape tree.
//! - **[`Linearity`]**: Resource usage semantics — can data be copied? dropped?
//! - **[`InformationContent`]**: How many bits a shape needs, computed from structure.
//! - **[`TransportClass`]**: How much information a morphism preserves (Concorde
//!   through Wheelbarrow).
//! - **[`Morphism`]**: A transformation between two shapes — the fundamental arrow
//!   in the category of data shapes.
//!
//! ## Usage
//!
//! ```
//! use shape_ir::*;
//! use shape_ir::compare::compare;
//!
//! // Define two shapes
//! let source = Shape::struct_from(vec![
//!     ("id", Shape::Atom(AtomKind::I32)),
//!     ("name", Shape::Atom(AtomKind::String)),
//! ]);
//! let target = Shape::struct_from(vec![
//!     ("id", Shape::Atom(AtomKind::I64)),
//!     ("name", Shape::Atom(AtomKind::String)),
//!     ("email", Shape::optional(Shape::Atom(AtomKind::String))),
//! ]);
//!
//! // Compare them
//! let morphism = compare(&source, &target);
//! assert_eq!(morphism.transport_class, TransportClass::Business);
//! println!("Steps: {:?}", morphism.steps);
//! ```
//!
//! ## Module structure
//!
//! | Module | Purpose |
//! |--------|---------|
//! | [`shape`] | The core Shape enum and builder methods |
//! | [`atom`] | Primitive atomic types (AtomKind) |
//! | [`linearity`] | Resource usage semantics (Linearity) |
//! | [`information`] | Information content and transport classes |
//! | [`morphism`] | Morphisms and transformation steps |
//! | [`compare`] | Shape comparison engine |
//! | [`compose`] | Morphism composition |
//! | [`category`] | Shape category — adapter discovery and pathfinding |
//! | [`labels`] | Labels and field paths |
//! | [`extract`] | Shape extraction from canonical IR |
//! | [`annotations`] | Annotations and constraints |
//! | [`temporal`] | Temporal algebra — schema evolution, semver, forecasting |
//! | [`render`] | Visual rendering — ASCII trees, DOT graphs, timeline diagrams |
//! | [`panll`] | PanLL integration — three-panel data model (L/N/W) |

pub mod annotations;
pub mod atom;
pub mod category;
pub mod compare;
pub mod compose;
pub mod extract;
pub mod information;
pub mod labels;
pub mod linearity;
pub mod morphism;
pub mod panll;
pub mod render;
pub mod shape;
pub mod temporal;

#[cfg(test)]
mod tests;

// --- Prelude re-exports ---

pub use annotations::{Annotations, Constraint};
pub use atom::{AtomKind, TimePrecision};
pub use category::ShapeCategory;
pub use information::{
    classify_morphism, InformationContent, InformationCost, MorphismMetrics, TransportClass,
};
pub use labels::{FieldPath, Label};
pub use linearity::Linearity;
pub use morphism::{DefaultValue, Morphism, MorphismStep};
pub use shape::Shape;
pub use temporal::{SchemaTimeline, SemanticVersion, SemverClassification};
pub use panll::{PanelId, PanllFrame};
pub use render::{render_shape_tree, render_category_dot, render_timeline};
