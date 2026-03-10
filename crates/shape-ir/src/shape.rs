// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # The Shape Type — Universal Representation of Data Shape
//!
//! This is the core of the entire system. Every serialization format, database
//! schema, API contract, type system, memory layout, and configuration format
//! can be expressed as a [`Shape`].
//!
//! The design is based on a small number of orthogonal constructors that compose
//! to describe any data structure:
//!
//! | Constructor | Models | Examples |
//! |-------------|--------|----------|
//! | [`Shape::Unit`] | Empty / void / null | Protobuf empty message, SQL NULL |
//! | [`Shape::Atom`] | Primitives | int32, string, bool, timestamp |
//! | [`Shape::Product`] | Records / structs | Protobuf messages, SQL rows, JSON objects |
//! | [`Shape::Sum`] | Unions / enums | Protobuf oneofs, Avro unions, Rust enums |
//! | [`Shape::Dependent`] | Conditional types | Tagged unions, JSON Schema if/then |
//! | [`Shape::Recursive`] | Self-referential | Trees, linked lists, JSON any |
//! | [`Shape::Ref`] | Cross-references | Named type references, recursion variables |
//! | [`Shape::Sequence`] | Arrays / lists | Protobuf repeated, SQL ARRAY, JSON array |
//! | [`Shape::Optional`] | Nullable / maybe | Protobuf optional, SQL NULL, JSON null |
//! | [`Shape::Map`] | Dictionaries | Protobuf map, JSON object-as-map |
//! | [`Shape::Annotated`] | Metadata | Constraints, linearity, deprecation |
//!
//! The key insight: these 11 constructors are sufficient to represent the data
//! shape of every format we've encountered. The algebra of composition (Phase 2)
//! will show they form a symmetric monoidal closed category with fixpoints.

use crate::annotations::Annotations;
use crate::atom::AtomKind;
use crate::labels::Label;
use serde::{Deserialize, Serialize};
use std::fmt;

/// The universal representation of data shape.
///
/// Every serialization format, database schema, API contract, type system,
/// memory layout, and configuration format can be expressed as a Shape.
///
/// Shapes form a recursive algebraic data type. Compound shapes (Product, Sum,
/// Sequence, etc.) contain sub-shapes, building up arbitrarily complex
/// structures from the primitive constructors.
///
/// # Design rationale
///
/// **Why Product and Sum use binary constructors (left/right) instead of Vec?**
/// Because binary constructors give us associativity laws for free. A three-field
/// struct `{a, b, c}` is `Product("a", A, Product("b", B, Product("c", C, Unit)))`.
/// This right-nested encoding matches how type theory handles products and makes
/// structural comparison straightforward — no need to handle different orderings
/// of a flat list.
///
/// **Why Dependent?**
/// Many real-world formats have fields whose type depends on another field's value.
/// Protobuf oneofs, Avro unions with type tags, JSON Schema if/then/else, and
/// database CHECK constraints all share this pattern. Without Dependent, we'd need
/// ad-hoc encodings for each case. With it, they all use the same representation.
///
/// **Why Recursive + Ref instead of direct cycles?**
/// Recursive types are modeled using a fixpoint combinator (`Recursive`) and
/// named references (`Ref`). This prevents infinite data structures in memory
/// while still representing infinite types like `List<T> = Nil | Cons(T, List<T>)`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Shape {
    /// Empty / void / unit type. Contains no information.
    ///
    /// Models: Protobuf `google.protobuf.Empty`, JSON `null`, SQL `NULL`,
    /// Rust `()`, the terminal object in the category of shapes.
    Unit,

    /// Primitive atomic type. The leaves of the shape tree.
    ///
    /// Models: every built-in type in every format — integers, floats, strings,
    /// bytes, timestamps, dates, decimals, and flat enumerations.
    Atom(AtomKind),

    /// Product type — a pair of named fields.
    ///
    /// Models: struct, record, row, message, object. A multi-field struct is
    /// encoded as right-nested products terminated by Unit:
    /// `Product("x", X, Product("y", Y, Unit))` represents `{ x: X, y: Y }`.
    ///
    /// The `label` names the left field. The right field carries the rest of
    /// the structure (the "tail").
    Product {
        /// Name of the left (head) field.
        label: Label,
        /// Type of the left (head) field.
        left: Box<Shape>,
        /// The remaining fields (tail). Typically another Product or Unit.
        right: Box<Shape>,
    },

    /// Sum type — a choice between two alternatives.
    ///
    /// Models: union, enum, oneof, variant, tagged union. A multi-variant enum
    /// is encoded as right-nested sums:
    /// `Sum("A", PayloadA, Sum("B", PayloadB, Unit))` represents `A(PayloadA) | B(PayloadB)`.
    ///
    /// The `label` names the left variant.
    Sum {
        /// Name of the left (first) variant.
        label: Label,
        /// Payload type of the left variant. Use Unit for data-less variants.
        left: Box<Shape>,
        /// The remaining variants (tail). Typically another Sum or Unit.
        right: Box<Shape>,
    },

    /// Dependent pair — the type of `body` depends on the value of `binder`.
    ///
    /// This is the most powerful constructor. It models every case where one
    /// field's type is determined by another field's value:
    /// - Protobuf oneofs (the oneof tag determines which field is present)
    /// - Avro unions (the type tag determines the payload schema)
    /// - JSON Schema conditionals (if/then/else)
    /// - Database CHECK constraints (column B's valid range depends on column A)
    /// - Tagged unions in any language
    ///
    /// The `binder` shape describes the discriminant/tag, and the `body` shape
    /// describes the payload whose structure depends on the binder's value.
    Dependent {
        /// The discriminant/tag shape whose runtime value determines the body's type.
        binder: Box<Shape>,
        /// The payload shape, parameterized by the binder's value.
        body: Box<Shape>,
    },

    /// Recursive type via fixpoint. The `var` names the recursion variable,
    /// which can be referenced by [`Shape::Ref`] inside the `body`.
    ///
    /// Models: self-referential types like linked lists, trees, JSON's
    /// unrestricted nesting, and graph structures.
    ///
    /// Example — a linked list of i32:
    /// ```text
    /// Recursive("List", Sum("Cons", Product("head", Atom(I32),
    ///   Product("tail", Ref("List"), Unit)), Sum("Nil", Unit, Unit)))
    /// ```
    Recursive {
        /// Name of the recursion variable (bound within `body`).
        var: String,
        /// The body of the recursive type, which may reference `var` via Ref.
        body: Box<Shape>,
    },

    /// Named reference — refers to a recursion variable bound by [`Shape::Recursive`]
    /// or to a named type in an external schema.
    ///
    /// During shape comparison, Ref nodes are resolved by looking up the
    /// enclosing Recursive binder or the schema's type registry.
    Ref(String),

    /// Sequence / array / repeated field. An ordered collection of elements
    /// sharing the same shape.
    ///
    /// Models: Protobuf `repeated`, JSON arrays, SQL `ARRAY`, Avro arrays.
    /// Information content is unbounded (the sequence can be any length).
    Sequence(Box<Shape>),

    /// Optional / nullable wrapper. The value is either present (with the
    /// inner shape) or absent.
    ///
    /// Models: Protobuf `optional`, SQL nullable columns, JSON Schema
    /// `"type": ["string", "null"]`, Rust `Option<T>`.
    ///
    /// Distinct from annotating a shape as nullable — Optional is a structural
    /// wrapper that adds one bit of "is-present" information.
    Optional(Box<Shape>),

    /// Map / dictionary. An unordered collection of key-value pairs.
    ///
    /// Models: Protobuf `map<K, V>`, JSON objects used as maps, SQL HSTORE,
    /// Redis hashes. Keys must be atoms (typically strings or integers).
    Map {
        /// The shape of map keys. Should be an Atom in most formats.
        key: Box<Shape>,
        /// The shape of map values.
        value: Box<Shape>,
    },

    /// Annotated shape — wraps an inner shape with metadata, constraints,
    /// and linearity information.
    ///
    /// Annotations are semantically transparent for structural comparison:
    /// `Annotated(X, _)` and `X` have the same structure. But annotations
    /// affect morphism transport class because they carry guarantees.
    Annotated {
        /// The underlying shape.
        shape: Box<Shape>,
        /// Metadata and constraints.
        annotations: Annotations,
    },
}

// ---------------------------------------------------------------------------
// Builder methods — ergonomic construction of shapes
// ---------------------------------------------------------------------------

impl Shape {
    /// Create a Product shape (a struct field + rest).
    pub fn product(label: impl Into<Label>, left: Shape, right: Shape) -> Self {
        Shape::Product {
            label: label.into(),
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Create a Sum shape (a variant + rest).
    pub fn sum(label: impl Into<Label>, left: Shape, right: Shape) -> Self {
        Shape::Sum {
            label: label.into(),
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Create a Dependent shape.
    pub fn dependent(binder: Shape, body: Shape) -> Self {
        Shape::Dependent {
            binder: Box::new(binder),
            body: Box::new(body),
        }
    }

    /// Create a Recursive shape.
    pub fn recursive(var: impl Into<String>, body: Shape) -> Self {
        Shape::Recursive {
            var: var.into(),
            body: Box::new(body),
        }
    }

    /// Create a Sequence shape.
    pub fn sequence(element: Shape) -> Self {
        Shape::Sequence(Box::new(element))
    }

    /// Create an Optional shape.
    pub fn optional(inner: Shape) -> Self {
        Shape::Optional(Box::new(inner))
    }

    /// Create a Map shape.
    pub fn map(key: Shape, value: Shape) -> Self {
        Shape::Map {
            key: Box::new(key),
            value: Box::new(value),
        }
    }

    /// Wrap this shape with annotations.
    pub fn annotated(self, annotations: Annotations) -> Self {
        Shape::Annotated {
            shape: Box::new(self),
            annotations,
        }
    }

    /// Convenience: build a multi-field struct from a list of (name, type) pairs.
    ///
    /// Fields are right-nested with Unit as the terminator:
    /// `struct_from([("a", A), ("b", B)])` becomes `Product("a", A, Product("b", B, Unit))`
    pub fn struct_from(fields: Vec<(impl Into<Label>, Shape)>) -> Self {
        let mut result = Shape::Unit;
        for (label, shape) in fields.into_iter().rev() {
            result = Shape::product(label, shape, result);
        }
        result
    }

    /// Convenience: build a multi-variant enum from a list of (name, payload) pairs.
    ///
    /// Variants are right-nested with Unit as the terminator.
    pub fn enum_from(variants: Vec<(impl Into<Label>, Shape)>) -> Self {
        let mut result = Shape::Unit;
        for (label, shape) in variants.into_iter().rev() {
            result = Shape::sum(label, shape, result);
        }
        result
    }

    /// Strip all annotations recursively, returning the bare structural shape.
    pub fn strip_annotations(&self) -> Shape {
        match self {
            Shape::Annotated { shape, .. } => shape.strip_annotations(),
            Shape::Product { label, left, right } => Shape::Product {
                label: label.clone(),
                left: Box::new(left.strip_annotations()),
                right: Box::new(right.strip_annotations()),
            },
            Shape::Sum { label, left, right } => Shape::Sum {
                label: label.clone(),
                left: Box::new(left.strip_annotations()),
                right: Box::new(right.strip_annotations()),
            },
            Shape::Dependent { binder, body } => Shape::Dependent {
                binder: Box::new(binder.strip_annotations()),
                body: Box::new(body.strip_annotations()),
            },
            Shape::Recursive { var, body } => Shape::Recursive {
                var: var.clone(),
                body: Box::new(body.strip_annotations()),
            },
            Shape::Sequence(inner) => Shape::Sequence(Box::new(inner.strip_annotations())),
            Shape::Optional(inner) => Shape::Optional(Box::new(inner.strip_annotations())),
            Shape::Map { key, value } => Shape::Map {
                key: Box::new(key.strip_annotations()),
                value: Box::new(value.strip_annotations()),
            },
            other => other.clone(),
        }
    }

    /// Returns true if this shape contains no information (is Unit or a product
    /// of Units).
    pub fn is_empty(&self) -> bool {
        match self {
            Shape::Unit => true,
            Shape::Annotated { shape, .. } => shape.is_empty(),
            _ => false,
        }
    }

    /// Collect all field labels from a product chain.
    pub fn field_labels(&self) -> Vec<&Label> {
        let mut labels = Vec::new();
        let mut current = self;
        loop {
            match current {
                Shape::Product { label, right, .. } => {
                    labels.push(label);
                    current = right;
                },
                Shape::Annotated { shape, .. } => {
                    current = shape;
                },
                _ => break,
            }
        }
        labels
    }
}

impl fmt::Display for Shape {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Shape::Unit => write!(f, "()"),
            Shape::Atom(kind) => write!(f, "{}", kind),
            Shape::Product { label, left, right } => {
                write!(f, "{{ {}: {}", label, left)?;
                let mut tail = right.as_ref();
                loop {
                    match tail {
                        Shape::Product { label, left, right } => {
                            write!(f, ", {}: {}", label, left)?;
                            tail = right;
                        },
                        Shape::Unit => break,
                        other => {
                            write!(f, ", ..{}", other)?;
                            break;
                        },
                    }
                }
                write!(f, " }}")
            },
            Shape::Sum { label, left, right } => {
                write!(f, "{}", label)?;
                if *left.as_ref() != Shape::Unit {
                    write!(f, "({})", left)?;
                }
                let mut tail = right.as_ref();
                loop {
                    match tail {
                        Shape::Sum { label, left, right } => {
                            write!(f, " | {}", label)?;
                            if *left.as_ref() != Shape::Unit {
                                write!(f, "({})", left)?;
                            }
                            tail = right;
                        },
                        Shape::Unit => break,
                        other => {
                            write!(f, " | {}", other)?;
                            break;
                        },
                    }
                }
                Ok(())
            },
            Shape::Dependent { binder, body } => write!(f, "Sigma({} . {})", binder, body),
            Shape::Recursive { var, body } => write!(f, "mu {}.{}", var, body),
            Shape::Ref(name) => write!(f, "${}", name),
            Shape::Sequence(inner) => write!(f, "[{}]", inner),
            Shape::Optional(inner) => write!(f, "{}?", inner),
            Shape::Map { key, value } => write!(f, "Map<{}, {}>", key, value),
            Shape::Annotated { shape, .. } => write!(f, "{}", shape),
        }
    }
}
