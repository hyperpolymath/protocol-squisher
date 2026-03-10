// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Shape Category — The Algebra of Data Shapes
//!
//! A **category** is a collection of objects (shapes) and arrows (morphisms) with
//! composition and identity. The Shape Category formalizes the relationships
//! between data shapes:
//!
//! - **Objects**: Data shapes (anything expressible as a [`Shape`])
//! - **Arrows**: Morphisms between shapes (produced by [`compare`])
//! - **Composition**: `f: A→B` and `g: B→C` give `g∘f: A→C` (via [`compose`])
//! - **Identity**: For every shape A, there is `id_A: A→A` (Concorde, zero cost)
//!
//! ## Category laws
//!
//! 1. **Left identity**: `id_B ∘ f = f` for any `f: A→B`
//! 2. **Right identity**: `f ∘ id_A = f` for any `f: A→B`
//! 3. **Associativity**: `(h ∘ g) ∘ f = h ∘ (g ∘ f)`
//!
//! ## Adapter discovery
//!
//! Given shapes A and C with no direct morphism, the category can find an
//! indirect path A→B₁→B₂→...→C by composing known morphisms. This is the
//! key practical benefit: N formats need only N morphisms to/from a hub,
//! not N² pairwise morphisms.
//!
//! The [`ShapeCategory::find_path`] method implements Dijkstra's algorithm
//! over the morphism graph, using transport class as the cost metric.
//!
//! [`Shape`]: crate::shape::Shape
//! [`compare`]: crate::compare::compare
//! [`compose`]: crate::compose::compose

use crate::compose::{compose, ComposeError};
use crate::morphism::Morphism;
use crate::shape::Shape;
use serde::{Deserialize, Serialize};
use std::collections::{BinaryHeap, HashMap};
use std::fmt;

/// A unique identifier for a shape within a category.
///
/// Shape IDs are strings that name the object (e.g., "protobuf.User",
/// "sql.users", "rust.UserStruct"). Two shapes with different IDs may
/// still be isomorphic.
pub type ShapeId = String;

/// The category of data shapes.
///
/// Contains a set of named shapes (objects) and morphisms between them
/// (arrows). Supports composition, identity, and adapter discovery.
///
/// # Building a category
///
/// ```
/// use shape_ir::category::ShapeCategory;
/// use shape_ir::{Shape, AtomKind};
/// use shape_ir::compare::compare;
///
/// let mut cat = ShapeCategory::new();
///
/// // Register shapes (objects)
/// cat.add_object("i32", Shape::Atom(AtomKind::I32));
/// cat.add_object("i64", Shape::Atom(AtomKind::I64));
///
/// // Register a morphism (arrow) — computed by comparing the shapes
/// let m = compare(cat.object("i32").unwrap(), cat.object("i64").unwrap());
/// cat.add_arrow("i32", "i64", m);
///
/// // Find a path between shapes
/// let path = cat.find_path("i32", "i64").unwrap();
/// assert_eq!(path.len(), 1);
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ShapeCategory {
    /// Named shapes (the objects of the category).
    objects: HashMap<ShapeId, Shape>,

    /// Morphisms between named shapes (the arrows of the category).
    /// Keyed by (source_id, target_id).
    arrows: HashMap<(ShapeId, ShapeId), Morphism>,
}

impl ShapeCategory {
    /// Create an empty category.
    pub fn new() -> Self {
        Self {
            objects: HashMap::new(),
            arrows: HashMap::new(),
        }
    }

    /// Add a named shape (object) to the category.
    ///
    /// If a shape with this ID already exists, it is replaced.
    pub fn add_object(&mut self, id: impl Into<ShapeId>, shape: Shape) {
        self.objects.insert(id.into(), shape);
    }

    /// Get a shape by ID.
    pub fn object(&self, id: &str) -> Option<&Shape> {
        self.objects.get(id)
    }

    /// Get all object IDs.
    pub fn object_ids(&self) -> impl Iterator<Item = &str> {
        self.objects.keys().map(|s| s.as_str())
    }

    /// Number of objects in the category.
    pub fn object_count(&self) -> usize {
        self.objects.len()
    }

    /// Add a morphism (arrow) between two named shapes.
    ///
    /// Both source and target must already be registered as objects.
    /// If an arrow between this pair already exists, it is replaced only
    /// if the new one has a better (lower) transport class.
    pub fn add_arrow(
        &mut self,
        source: impl Into<ShapeId>,
        target: impl Into<ShapeId>,
        morphism: Morphism,
    ) {
        let key = (source.into(), target.into());
        let replace = match self.arrows.get(&key) {
            Some(existing) => morphism.transport_class < existing.transport_class,
            None => true,
        };
        if replace {
            self.arrows.insert(key, morphism);
        }
    }

    /// Get the direct morphism between two shapes, if one exists.
    pub fn arrow(&self, source: &str, target: &str) -> Option<&Morphism> {
        self.arrows.get(&(source.to_string(), target.to_string()))
    }

    /// Number of arrows in the category.
    pub fn arrow_count(&self) -> usize {
        self.arrows.len()
    }

    /// Get the identity morphism for a shape.
    ///
    /// The identity arrow `id_A: A→A` always exists for any object A and
    /// has transport class Concorde with zero information cost.
    pub fn identity(&self, id: &str) -> Option<Morphism> {
        self.objects
            .get(id)
            .map(|shape| Morphism::identity(shape.clone()))
    }

    /// Compose two arrows: given arrows `source→mid` and `mid→target`,
    /// produce `source→target`.
    ///
    /// Returns `None` if either arrow doesn't exist. Returns an error
    /// if the shapes are incompatible for composition.
    pub fn compose_arrows(
        &self,
        source: &str,
        mid: &str,
        target: &str,
    ) -> Result<Option<Morphism>, ComposeError> {
        let f = match self.arrow(source, mid) {
            Some(m) => m,
            None => return Ok(None),
        };
        let g = match self.arrow(mid, target) {
            Some(m) => m,
            None => return Ok(None),
        };
        compose(f, g).map(Some)
    }

    /// Find the best path between two shapes using Dijkstra's algorithm.
    ///
    /// Returns a sequence of (source_id, target_id) pairs representing
    /// the path, or `None` if no path exists. "Best" means the path whose
    /// composed transport class is minimized (Concorde < Business < Economy
    /// < Wheelbarrow).
    ///
    /// # Algorithm
    ///
    /// Each edge has cost equal to its transport class ordinal (0-3).
    /// Dijkstra finds the path minimizing the maximum edge cost (since
    /// composition takes the max, not the sum).
    pub fn find_path(&self, source: &str, target: &str) -> Option<Vec<(ShapeId, ShapeId)>> {
        if source == target {
            return Some(vec![]);
        }

        if !self.objects.contains_key(source) || !self.objects.contains_key(target) {
            return None;
        }

        // Dijkstra with max-cost metric (minimax path)
        let mut best_cost: HashMap<&str, u8> = HashMap::new();
        let mut prev: HashMap<&str, &str> = HashMap::new();
        let mut heap = BinaryHeap::new();

        best_cost.insert(source, 0);
        heap.push(PathState {
            cost: 0,
            node: source,
        });

        // Build adjacency list
        let mut adj: HashMap<&str, Vec<(&str, u8)>> = HashMap::new();
        for ((src, tgt), morphism) in &self.arrows {
            adj.entry(src.as_str())
                .or_default()
                .push((tgt.as_str(), morphism.transport_class as u8));
        }

        while let Some(PathState { cost, node }) = heap.pop() {
            if node == target {
                // Reconstruct path
                let mut path = Vec::new();
                let mut current = target;
                while let Some(&predecessor) = prev.get(current) {
                    path.push((predecessor.to_string(), current.to_string()));
                    current = predecessor;
                }
                path.reverse();
                return Some(path);
            }

            if cost > *best_cost.get(node).unwrap_or(&u8::MAX) {
                continue;
            }

            if let Some(neighbors) = adj.get(node) {
                for &(next, edge_cost) in neighbors {
                    // Minimax: path cost is max of edge costs
                    let new_cost = cost.max(edge_cost);
                    if new_cost < *best_cost.get(next).unwrap_or(&u8::MAX) {
                        best_cost.insert(next, new_cost);
                        prev.insert(next, node);
                        heap.push(PathState {
                            cost: new_cost,
                            node: next,
                        });
                    }
                }
            }
        }

        None // No path found
    }

    /// Compose the morphisms along a path to produce a single morphism.
    ///
    /// Returns `None` if the path is empty (identity) or if any step fails.
    pub fn compose_path(&self, path: &[(ShapeId, ShapeId)]) -> Option<Morphism> {
        if path.is_empty() {
            return None;
        }

        let first = self.arrow(&path[0].0, &path[0].1)?;
        let mut result = first.clone();

        for step in &path[1..] {
            let next = self.arrow(&step.0, &step.1)?;
            result = compose(&result, next).ok()?;
        }

        Some(result)
    }

    /// Populate the category by comparing all pairs of registered objects.
    ///
    /// For each pair (A, B) where A ≠ B, computes `compare(A, B)` and adds
    /// the resulting morphism as an arrow. This is O(N²) in the number of
    /// objects — use for small categories only.
    pub fn compare_all(&mut self) {
        let ids: Vec<ShapeId> = self.objects.keys().cloned().collect();
        for i in 0..ids.len() {
            for j in 0..ids.len() {
                if i == j {
                    continue;
                }
                let source = &self.objects[&ids[i]];
                let target = &self.objects[&ids[j]];
                let morphism = crate::compare::compare(source, target);
                self.add_arrow(ids[i].clone(), ids[j].clone(), morphism);
            }
        }
    }

    /// Get all outgoing arrows from a shape.
    pub fn outgoing(&self, source: &str) -> Vec<(&str, &Morphism)> {
        self.arrows
            .iter()
            .filter(|((src, _), _)| src == source)
            .map(|((_, tgt), m)| (tgt.as_str(), m))
            .collect()
    }

    /// Get all incoming arrows to a shape.
    pub fn incoming(&self, target: &str) -> Vec<(&str, &Morphism)> {
        self.arrows
            .iter()
            .filter(|((_, tgt), _)| tgt == target)
            .map(|((src, _), m)| (src.as_str(), m))
            .collect()
    }

    /// Check whether a direct arrow from source to target is lossless
    /// (Concorde or Business class).
    pub fn is_lossless(&self, source: &str, target: &str) -> Option<bool> {
        self.arrow(source, target).map(|m| m.is_lossless())
    }

    /// Check the roundtrip property: compose A→B then B→A and check the
    /// resulting transport class.
    ///
    /// For Concorde-class arrows (isomorphisms), the roundtrip should also
    /// be Concorde. For Business-class, the roundtrip is Economy (the
    /// narrowing step loses the padding). For Economy or Wheelbarrow,
    /// the roundtrip is at least Economy.
    ///
    /// Returns `None` if either direction arrow doesn't exist.
    pub fn roundtrip_class(&self, a: &str, b: &str) -> Option<crate::information::TransportClass> {
        let forward = self.arrow(a, b)?;
        let backward = self.arrow(b, a)?;
        compose(forward, backward).ok().map(|m| m.transport_class)
    }

    /// Find all isomorphic pairs (Concorde in both directions).
    ///
    /// Two shapes are isomorphic if A→B is Concorde AND B→A is Concorde.
    /// This is strictly stronger than A→B being Concorde alone (which only
    /// guarantees the forward direction preserves information).
    pub fn isomorphic_pairs(&self) -> Vec<(ShapeId, ShapeId)> {
        let mut pairs = Vec::new();
        let ids: Vec<&str> = self.objects.keys().map(|s| s.as_str()).collect();
        for i in 0..ids.len() {
            for j in (i + 1)..ids.len() {
                let forward = self.arrow(ids[i], ids[j]);
                let backward = self.arrow(ids[j], ids[i]);
                if let (Some(f), Some(b)) = (forward, backward) {
                    if f.transport_class == crate::information::TransportClass::Concorde
                        && b.transport_class == crate::information::TransportClass::Concorde
                    {
                        pairs.push((ids[i].to_string(), ids[j].to_string()));
                    }
                }
            }
        }
        pairs
    }

    /// Compute the product shape of two objects (symmetric monoidal tensor).
    ///
    /// In the symmetric monoidal category, the tensor product A ⊗ B is
    /// `Product("fst", A, Product("snd", B, Unit))` — a pair. The unit
    /// object is `Shape::Unit`.
    ///
    /// This registers the product as a new object and computes arrows
    /// from the components to the product (embedding) and vice versa
    /// (projection).
    pub fn add_product(
        &mut self,
        id: impl Into<ShapeId>,
        a_id: &str,
        b_id: &str,
    ) -> Option<ShapeId> {
        let a = self.objects.get(a_id)?.clone();
        let b = self.objects.get(b_id)?.clone();

        let product =
            crate::shape::Shape::struct_from(vec![("fst", a.clone()), ("snd", b.clone())]);

        let id = id.into();
        self.add_object(id.clone(), product.clone());

        // Add projection arrows: product → a, product → b
        let proj_a = crate::compare::compare(&product, &a);
        let proj_b = crate::compare::compare(&product, &b);
        self.add_arrow(id.clone(), a_id, proj_a);
        self.add_arrow(id.clone(), b_id, proj_b);

        // Add pairing arrows from components
        let embed_a = crate::compare::compare(&a, &product);
        let embed_b = crate::compare::compare(&b, &product);
        self.add_arrow(a_id, id.clone(), embed_a);
        self.add_arrow(b_id, id.clone(), embed_b);

        Some(id)
    }

    /// Compute the coproduct shape of two objects (sum / disjoint union).
    ///
    /// The coproduct A + B is `Sum("left", A, Sum("right", B, Unit))`.
    /// This registers the coproduct and computes injection/projection arrows.
    pub fn add_coproduct(
        &mut self,
        id: impl Into<ShapeId>,
        a_id: &str,
        b_id: &str,
    ) -> Option<ShapeId> {
        let a = self.objects.get(a_id)?.clone();
        let b = self.objects.get(b_id)?.clone();

        let coproduct =
            crate::shape::Shape::enum_from(vec![("left", a.clone()), ("right", b.clone())]);

        let id = id.into();
        self.add_object(id.clone(), coproduct.clone());

        // Add injection arrows: a → coproduct, b → coproduct
        let inj_a = crate::compare::compare(&a, &coproduct);
        let inj_b = crate::compare::compare(&b, &coproduct);
        self.add_arrow(a_id, id.clone(), inj_a);
        self.add_arrow(b_id, id.clone(), inj_b);

        // Add case analysis arrows: coproduct → a, coproduct → b
        let case_a = crate::compare::compare(&coproduct, &a);
        let case_b = crate::compare::compare(&coproduct, &b);
        self.add_arrow(id.clone(), a_id, case_a);
        self.add_arrow(id.clone(), b_id, case_b);

        Some(id)
    }

    /// Find all shapes reachable from a given source via lossless morphisms.
    pub fn lossless_reachable(&self, source: &str) -> Vec<ShapeId> {
        let mut visited = std::collections::HashSet::new();
        let mut queue = std::collections::VecDeque::new();

        visited.insert(source.to_string());
        queue.push_back(source.to_string());

        while let Some(current) = queue.pop_front() {
            for (target, morphism) in self.outgoing(&current) {
                if morphism.is_lossless() && visited.insert(target.to_string()) {
                    queue.push_back(target.to_string());
                }
            }
        }

        visited.remove(source);
        visited.into_iter().collect()
    }
}

impl Default for ShapeCategory {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for ShapeCategory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ShapeCategory({} objects, {} arrows)",
            self.objects.len(),
            self.arrows.len()
        )
    }
}

/// Internal state for Dijkstra's priority queue.
///
/// Uses reverse ordering so that `BinaryHeap` (max-heap) acts as a min-heap.
#[derive(Debug, Clone, Eq, PartialEq)]
struct PathState<'a> {
    /// The minimax cost to reach this node.
    cost: u8,
    /// The node ID.
    node: &'a str,
}

impl Ord for PathState<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Reverse ordering for min-heap behavior
        other
            .cost
            .cmp(&self.cost)
            .then_with(|| self.node.cmp(other.node))
    }
}

impl PartialOrd for PathState<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
