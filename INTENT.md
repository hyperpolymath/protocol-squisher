<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->

# INTENT — Why Protocol Squisher Is Changing Direction

**Author:** Jonathan D.A. Jewell
**Date:** 2026-03-10
**Status:** Active

---

## WHY we are changing direction

Protocol Squisher began as a format converter: give it Protobuf and Avro, get an
adapter. That works. The 13 analyzers work. The transport class scoring works.
The 1100+ tests pass. The v1.1 release is solid.

But in building it, we discovered something larger. The transport class metaphor
(Concorde/Business/Economy/Wheelbarrow) is not really about serialization formats.
It is about **information loss across structural boundaries**. The linearity
annotations we were adding to handle file handles and database connections are not
really about protocol adapters. They are about **resource semantics in data**. The
dependent types we needed for Protobuf oneofs are not a Protobuf-specific feature.
They are about **type-level computation over structure**.

Every serialization format, database schema, API contract, type system, memory
layout, and configuration file is a **data shape**. Converting between them is a
**morphism**. The laws governing those morphisms (information preservation,
roundtrip properties, composition) are **algebra**.

We are not abandoning what we built. We are recognising what it actually is.

---

## WHAT the intellectual lineage is

This work sits at the intersection of several research threads that have not yet
been unified into a single practical tool:

### Bidirectional Transformations (BX)

The BX community has studied the problem of keeping two data sources synchronised
for decades. Lenses, in the programming languages sense, are the core abstraction.

- **Symmetric Lenses** (Hofmann, Pierce, Wagner, 2011) — lenses that work in both
  directions without privileging a "source" and "view". Our transport classes map
  to the information-preservation properties of symmetric lenses: Concorde is an
  isomorphism, Business is an embedding, Economy is a projection.

- **Delta Lenses** (Diskin et al.) — lenses that track the *change* between states,
  not just the states themselves. This is what Phase 4 (temporal dimension) builds
  on: schema evolution is a sequence of deltas.

### Categorical Database Theory

- **Monoidal Categories for Data Migration** (Spivak, 2012) — David Spivak showed
  that database schemas are categories, instances are functors, and migrations are
  natural transformations. Our Phase 3 (database schema reasoning) follows directly
  from this. The category we are building in Phase 2 is the practical instantiation
  of Spivak's abstract framework.

### Information Theory meets Type Theory

- **Information Effects** (James, Sabry, 2012) — information-theoretic reasoning
  about type isomorphisms. Our InformationContent type (min_bits, max_bits,
  fixed_size, cardinality) is the practical encoding of these ideas. Transport
  classes are a coarsening of information-theoretic distance between types.

### Dataflow and Comonadic Computation

- **The Essence of Dataflow Programming** (Uustalu, Vene, 2005) — comonads as a
  model of context-dependent computation. When we reason about how a field's type
  depends on another field's value (Dependent constructor in Shape IR), we are
  building a comonadic structure. Phase 2's category will make this explicit.

### Optics

- **Lenses, Folds, and Traversals** (Kmett) — the Haskell lens library, and the
  profunctor optics framework, showed that lenses, prisms, traversals, and isos
  form a hierarchy of data access patterns. Our Shape constructors (Product, Sum,
  Recursive, Dependent) correspond to different optics (lenses for products, prisms
  for sums, folds for recursion, dependent optics for indexed access).

### Practical Systems

- **Cambria** (Ink & Switch) — a practical lens-based system for evolving data
  schemas in local-first software. Cambria is the closest existing system to what
  we are building, but it focuses on JSON document evolution. We generalise to
  arbitrary data shapes.

- **Apache Arrow** — a columnar in-memory format with a well-defined type system.
  Arrow's schema is a data shape. Our Phase 3 will include an Arrow extractor.

- **buf.build** — Protobuf schema management with breaking change detection. Buf
  does for Protobuf what we want to do for everything.

- **CUE** — a constraint-based configuration language that unifies types and values.
  CUE's lattice-based type system is philosophically aligned with our linearity
  lattice and transport class semilattice.

---

## HOW this connects to the existing work

The existing 13 analyzers (Protobuf, Avro, Cap'n Proto, Thrift, Bebop,
FlatBuffers, GraphQL, TOML, JSON Schema, MessagePack, Python, Rust, ReScript)
do not become obsolete. They become **domain-specific Shape extractors**.

```
BEFORE (v1.x):
  Protobuf parser → Protobuf IR → Canonical IR → Comparison Engine
  Avro parser     → Avro IR     → Canonical IR → Comparison Engine

AFTER (v2.x vision):
  Protobuf parser → Shape extractor → Shape IR → Shape Algebra → Morphism
  Avro parser     → Shape extractor → Shape IR → Shape Algebra → Morphism
  SQL DDL parser  → Shape extractor → Shape IR → Shape Algebra → Morphism
  OpenAPI parser  → Shape extractor → Shape IR → Shape Algebra → Morphism
  Rust AST        → Shape extractor → Shape IR → Shape Algebra → Morphism
  ... anything with structure ...
```

The Canonical IR was already doing this implicitly. The Shape IR makes it explicit,
gives it algebra, and extends it to domains beyond serialization formats.

The existing crates remain:
- `protocol-squisher-ir` — becomes the bridge between format-specific parsers and
  Shape IR (a Shape extractor for the serialization domain)
- `protocol-squisher-compat` — the comparison engine, to be generalised to work
  over Shape IR morphisms
- All 13 analyzer crates — parsers remain, converters adapted to produce Shapes
- `protocol-squisher-cli` — gains new `shape` subcommands alongside existing ones

---

## WHAT we are NOT doing

1. **Not abandoning existing functionality.** The v1.x CLI and library API continue
   to work. Users who depend on `protocol-squisher analyze` do not break.

2. **Not rewriting from scratch.** The shape-ir crate is new, but it builds on the
   concepts proven in the existing IR. The 937 existing tests plus 116 new shape-ir tests all pass.

3. **Not making this theoretical only.** Every phase has a practical deliverable.
   Phase 1 delivers a working crate. Phase 2 delivers adapter composition. Phase 3
   delivers new domain analyzers. The paper (Phase 6) accompanies a tool, not
   replaces one.

4. **Not ignoring the formal methods.** The 5-prover cross-validation (Agda, Coq,
   Lean, Isabelle, Z3) was the right foundation. Phase 2 replaces these scattered
   proofs with a unified algebraic theory that is *more* powerful, not less.

5. **Not doing this alone.** The vision document is public. The shape-ir crate is
   designed for external contribution. Phase 6 explicitly targets a peer-reviewed
   venue.

---

## Key References

1. Hofmann, M., Pierce, B.C., Wagner, D. (2011). *Symmetric Lenses.* POPL.
2. Diskin, Z., Xiong, Y., Czarnecki, K. (2011). *From State- to Delta-Based
   Bidirectional Model Transformations: the Asymmetric Case.* Journal of Object
   Technology.
3. Spivak, D.I. (2012). *Functorial Data Migration.* Information and Computation.
4. James, R.P., Sabry, A. (2012). *Information Effects.* POPL.
5. Uustalu, T., Vene, V. (2005). *The Essence of Dataflow Programming.* CEFP.
6. Kmett, E. *lens: Lenses, Folds, and Traversals.* Hackage.
   https://hackage.haskell.org/package/lens
7. Pickering, M., Gibbons, J., Wu, N. (2017). *Profunctor Optics: Modular Data
   Accessors.* The Art, Science, and Engineering of Programming.
8. Geoffroy, G., Orchard, D. (2024). *Graded Monads and Type-Level Programming
   for Dependence.* ICFP.
