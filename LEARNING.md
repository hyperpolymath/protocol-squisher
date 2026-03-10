<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->

# LEARNING — Insights from Building a Universal Data Shape Reasoning Engine

**Author:** Jonathan D.A. Jewell
**Started:** 2026-03-10
**Status:** Living document — updated throughout the 18-month vision

This file records genuine insights, surprises, and course corrections as they
happen. Not a changelog (that is CHANGELOG.md). Not a plan (that is
VISION-18-MONTHS.md). This is for the things we learn by doing.

---

## 2026-03-10 — Phase 1 begins

The shape-ir crate establishes the foundational types. 84 tests passing
(79 unit + 5 doc). First day of the new direction.

### Key Insight: Binary Product/Sum constructors give associativity laws for free

By defining `Product(label, Shape, Shape)` and `Sum(label, Shape, Shape)` as
binary constructors rather than n-ary lists, we get associativity as a structural
property. A three-field struct `{a, b, c}` is `Product("a", A, Product("b", B, C))`,
which is naturally right-associated. Left association `Product("ab", Product("a", A, B), C)`
is a different shape — and the isomorphism between them is an explicit morphism.

This matters because:
- It forces us to be honest about field ordering (which serialization formats
  care about differently — Protobuf by field number, JSON not at all)
- It gives us a canonical form (right-associated) that we can normalise to
- The associativity isomorphism becomes a concrete, testable morphism rather
  than a hand-waved equivalence
- N-ary products/sums are syntactic sugar over binary ones, which keeps the
  core algebra small

### Key Insight: Transport class as bounded join-semilattice

The transport classes (Concorde < Business < Economy < Wheelbarrow) form a
bounded join-semilattice where composition is `max`. This is not just a metaphor —
it is a precise algebraic structure.

- **Concorde** is the identity element (bottom). Composing with Concorde does
  not degrade quality: `compose(Concorde, x) = x`.
- **Wheelbarrow** is the absorbing element (top). Once you hit Wheelbarrow,
  nothing makes it better: `compose(x, Wheelbarrow) = Wheelbarrow`.
- **Composition is commutative.** The order in which you compose transport
  classes does not matter: `compose(a, b) = compose(b, a)`.
- **Composition is associative.** `compose(compose(a, b), c) = compose(a, compose(b, c))`.

The semilattice structure means that transport class analysis composes for free.
If you know the class of A→B and B→C, you know the class of A→C: it is
`max(class(A→B), class(B→C))`. This is why adapter composition (Phase 2) will
work — transport class is a functor from the category of shapes to the
semilattice of quality levels.

### Key Insight: Linearity as four-point lattice from can_copy × can_drop

Linearity is not a linear ordering — it is a two-dimensional lattice formed
by the Cartesian product of two boolean properties: `can_copy` and `can_drop`.

```
                 Unrestricted (can_copy=true, can_drop=true)
                /            \
         Affine              Relevant
   (copy=false, drop=true)   (copy=true, drop=false)
                \            /
                  Linear (can_copy=false, can_drop=false)
```

- **Unrestricted**: most data (strings, integers, records). Copy and discard freely.
- **Affine**: owned resources (file handles, database connections). Can close/drop
  them, but cannot duplicate them.
- **Relevant**: audit trails, provenance records. Must be consumed (cannot silently
  drop), but can be shared/copied.
- **Linear**: unique tokens, exactly-once delivery receipts. Must use exactly once.

The meet operation (most restrictive combination) gives:
- `meet(Affine, Relevant) = Linear` (cannot copy AND cannot drop)
- `meet(Unrestricted, anything) = anything` (Unrestricted is top)
- `meet(Linear, anything) = Linear` (Linear is bottom)

This lattice structure means that when you compose shapes, linearity annotations
compose correctly by taking the meet. A struct containing one linear field and
one unrestricted field is itself linear (you cannot copy or drop a struct that
contains a non-copyable, non-droppable field).

### Key Insight: InformationContent separating min/max/fixed/cardinality

Rather than a single "size" metric, InformationContent tracks four independent
dimensions:

- **min_bits**: minimum bits needed to represent any value of this shape
- **max_bits**: maximum bits needed for the largest value
- **fixed_size**: whether all values have the same bit width (Option<usize>)
- **cardinality**: number of distinct values (Option<u128>, None if infinite)

This separation enables precise morphism classification:
- **Isomorphism** (Concorde): same cardinality, same bit range
- **Embedding** (Business): target cardinality > source, target bits >= source
- **Projection** (Economy): target cardinality < source, some information lost
- **Best-effort** (Wheelbarrow): below Shannon limit, cannot reconstruct

The "fixed_size implies min_bits == max_bits" invariant is tested and enforced.
This catches a whole class of bugs where someone claims a type is fixed-size
but gives inconsistent bit counts.

---

## 2026-03-10 — Alpha-equivalence, extraction bridge, morphism metrics

Phase 1 expansion: comparison engine now handles all 11 Shape constructors,
shape extraction from existing analyzers works, CLI can extract and compare
shapes, and morphism classification provides quantitative metrics. 116 tests,
criterion benchmarks established.

### Key Insight: Alpha-equivalence for recursive types needs environment threading

Comparing `Recursive("List", body_a)` to `Recursive("L", body_b)` requires
tracking that the variable names `"List"` and `"L"` are bound together, so that
`Ref("List")` in body_a matches `Ref("L")` in body_b. This is standard
alpha-equivalence from lambda calculus, but it was not obvious it would be needed
for a "practical" shape comparison tool.

The implementation threads a `Vec<(&str, &str)>` environment through all
comparison functions. When entering a `Recursive` binder, we push the pair.
When comparing `Ref` nodes, we check the environment in reverse order (inner
bindings shadow outer). This handles nested recursion correctly:

```
Recursive("T", Recursive("U", ... Ref("T") ... Ref("U") ...))
```

Without alpha-equivalence, two structurally identical recursive types with
different variable names would incorrectly classify as Wheelbarrow (incompatible).
With it, they correctly classify as Concorde (isomorphism).

### Key Insight: Shape extraction as a lossy functor from IR to algebra

The `extract_schema` function maps from the existing Canonical IR (`IrSchema`
with `TypeDef` and `IrType`) to the new Shape IR. This is not an isomorphism —
it is deliberately lossy in the **right direction**:

- IR-level details like field numbers, wire formats, encoding hints are dropped
  (they are serialization concerns, not shape concerns)
- IR-level `SpecialType::Any` and `SpecialType::Json` map to a recursive
  6-variant JSON shape (`Null | Bool | Number | String | Array | Object`),
  which captures the structural content
- Self-referential types (detected by `shape_references_name`) are wrapped in
  `Recursive` to make the fixpoint explicit

This is a functor from the category of IR schemas to the category of shapes.
It preserves composition (extracting then comparing gives the same transport
class as comparing in the IR domain). The lossiness is intentional — the shape
algebra operates at a higher level of abstraction.

### Key Insight: Morphism metrics quantify what transport classes only classify

Transport classes are a four-point lattice — useful but coarse. Two Economy
morphisms can be very different: one might lose 1 bit out of 64 (narrowing
I64→I63), the other might lose 63 bits out of 64 (narrowing I64→Bool). Both
are Economy, but the first is nearly reversible and the second is nearly
destructive.

`MorphismMetrics` adds continuous measures:
- **identity_ratio**: what fraction of paths map directly (1.0 for Concorde)
- **loss_ratio**: what fraction of source bits are lost (0.0 for lossless)
- **padding_ratio**: what fraction of target bits are padding (0.0 for exact)
- **reversibility**: estimated roundtrip fidelity (1.0 for isomorphism)
- **net_bits**: signed difference showing growth or shrinkage
- **is_pure_embedding / is_pure_projection**: clean structural characterisation

These metrics will be essential for Phase 2's adapter discovery: when multiple
paths exist between two shapes in the category, the metrics help choose the
best one (highest reversibility, lowest loss).

---

## 2026-03-10 — Category theory meets adapter discovery

Phase 2 core: ShapeCategory implements the category of data shapes with
Dijkstra pathfinding for adapter discovery, symmetric monoidal structure,
and full CLI integration. 165 shape-ir tests, 41 category-specific.

### Key Insight: Minimax pathfinding is the right cost model for morphism chains

Adapter discovery needs to find the "best" morphism chain between two shapes
when no direct morphism exists. The natural first thought is additive cost
(sum of edge weights). But transport class composition takes the **maximum**,
not the sum: a Concorde + Economy chain is Economy, not "double Economy".

This means the optimal pathfinding algorithm is **minimax**: find the path
that minimizes the maximum edge cost. Standard Dijkstra works with a simple
modification — instead of `new_cost = cost + edge_cost`, use
`new_cost = max(cost, edge_cost)`. The priority queue still gives correct
results because max is monotonic.

Practical consequence: a 10-hop path through all-Business edges is strictly
better than a 1-hop Economy shortcut. Length does not matter; only the worst
edge matters. This is deeply satisfying — it means adapter chains degrade
gracefully: adding more hops through good edges never makes things worse.

### Key Insight: Product-with-Unit is not isomorphic to its component

Mathematically, A × 1 ≅ A (the unit object of a monoidal category). But
structurally, `{fst: i32, snd: Unit}` is not the same shape as `i32` — one
is a Product with two fields, the other is an Atom. The comparison engine
correctly identifies this as a structural mismatch (Economy class, because
it is a projection dropping the Unit field).

However, the **information cost** is zero — Unit carries zero bits, so
`bits_lost = 0`. This is the right answer: the shapes are not structurally
identical (different field access patterns), but they carry the same amount
of information. The distinction between structural isomorphism and information
equivalence matters for real adapters: you still need a code transform to
go from `record.fst` to just `value`, even though no data is lost.

### Key Insight: Property tests catch generator bugs, not just code bugs

The `extracted_self_compare_is_concorde` property test was failing — not
because self-comparison was broken, but because the random schema generator
could produce structs with duplicate field names. When a struct has two
fields named "r" (one required, one optional), the comparison engine
correctly treats them as different shapes (Business, not Concorde) because
the duplicate name creates an ambiguous structural mapping.

The fix was making the generator produce indexed field names (`f0`, `f1`, ...)
to guarantee uniqueness. The lesson: property test generators are themselves
a source of subtle invariant violations. The real schemas produced by the
13 analyzers never have duplicate field names — but a random generator
happily creates them unless constrained.

---

<!-- Future entries will be added below as the work progresses. -->
<!-- Format: ## YYYY-MM-DD — Brief topic -->
<!--         Narrative paragraphs + ### Key Insight: subsections -->
