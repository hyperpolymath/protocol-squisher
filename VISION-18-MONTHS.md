<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->

# Protocol Squisher: The 18-Month Vision

**"From format converter to universal data shape reasoning engine"**

**Author:** Jonathan D.A. Jewell
**Date:** 2026-03-10
**Status:** Active — Phase 1 in progress

---

## The Core Insight

Protocol Squisher isn't really about serialization formats. Serialization formats
are just the first place the idea bumps into the world. What we've actually built
is the embryo of **a theory of data shape** — and the next 18 months grow that
embryo into something that doesn't have a name yet.

A field in Protobuf, a column in a database, a key in a JSON document, a struct
member in Rust, a cell in a spreadsheet, an attribute in an XML element, a column
in a CSV — these are all the same thing viewed through different lenses. The tool
we're building is the thing underneath all of them.

---

## Phase 1 — Months 1–3: Strip It Back to the Bone

### Goal
Rewrite ephapax-ir from scratch. Not because it's wrong — because we haven't yet
discovered what it *really* is. The current IR models serialization schemas. The
new IR models **data shape itself**, independent of any format.

### What We Keep
- ephapax-ir (as starting point, to be rewritten)
- The core comparison engine (concepts, not code)
- The transport class metaphor (to be formalized)
- All 13 analyzers (set aside, reconnected later)

### What We Build

#### 1. Dependent Types in the IR
A field's type can depend on another field's value. This is how we model:
- Protobuf oneofs
- Avro unions
- JSON Schema conditionals
- Database CHECK constraints
- Tagged unions across any language

All with a single construct.

```
Shape ::= Unit                         -- empty / void
        | Atom(T)                      -- primitive (bool, int, float, string, bytes)
        | Product(label, Shape, Shape) -- struct / record / row
        | Sum(label, Shape, Shape)     -- union / enum / oneof
        | Dependent(x : Shape, Shape(x)) -- dependent pair (value determines type)
        | Recursive(μ, Shape)          -- fixpoint (trees, lists, graphs)
        | Ref(name)                    -- named reference
        | Annotated(Shape, Metadata)   -- linearity, nullability, constraints
```

#### 2. Linearity as First-Class Property
Some data can be copied (a string), some can't (a file handle, a database
connection, a unique token). Transport classes are already circling this idea —
make it explicit.

```
Linearity ::= Unrestricted  -- can copy, can drop (most data)
            | Linear         -- must use exactly once (handles, tokens)
            | Affine         -- can drop but not copy (owned resources)
            | Relevant       -- can copy but not drop (audit trails)
```

#### 3. Information Content as Measurable Quantity
Every schema has an information-theoretic capacity. When you convert between
formats, information is either preserved, lost, or padded.

- **Concorde** = zero information loss (isomorphism)
- **Business** = lossless but padded (embedding with extra fields)
- **Economy** = lossy but recoverable (projection with known inverse)
- **Wheelbarrow** = lossy, below Shannon limit (fallback, best-effort)

Now we can *prove* which class a conversion falls into, not just estimate.

### Deliverable
A new IR that is the universal representation of data shape, with dependent
types, linearity annotations, and information-theoretic metrics. Smaller than
what we have now. More powerful than anything that exists.

### Implementation Language
Idris2 for the core theory. Rust for the practical engine. Zig for the ABI
boundary (per standard).

---

## Phase 2 — Months 4–6: The Algebra

### Goal
Discover and formalize the algebra of data shapes.

### The Category
Data shapes compose. If you have a shape A and a shape B, you can form:

| Operation | Notation | Meaning | Example |
|-----------|----------|---------|---------|
| Product | A × B | Both together | Struct with fields from A and B |
| Sum | A + B | One or the other | Union / enum / oneof |
| Morphism | A → B | A conversion (adapter) | Protobuf → Avro adapter |
| Tensor | A ⊗ B | Both, but neither copyable | Linear pair (two handles) |
| Fixpoint | μA | Recursive data | Tree, linked list, graph |
| Universal | ∀x.A(x) | Generic / parameterized | `List<T>`, `Option<T>` |

This is a **symmetric monoidal closed category with fixpoints**.

### What This Gives Us

1. **Adapter composition.** A→B and B→C gives A→C for free. N formats need N
   adapters to the IR, not N² adapters between each other.

2. **Correctness proofs.** Roundtrip A→B→A should be identity (for Concorde
   class). This is a coherence condition. Checkable mechanically.

3. **Automatic adapter discovery.** Given a library of known morphisms, find the
   shortest (cheapest) path between any two schemas. Pathfinding in a category.

4. **Information loss quantification.** Every morphism has an
   information-theoretic cost. The cheapest path is the best adapter.

### Deliverable
A formally verified algebra of data shape in Idris2, with composition,
information metrics, and automatic adapter discovery. The 8 Agda theorems
cross-validated in 5 proof systems get replaced by one unified theory that's
more powerful than all of them combined.

---

## Phase 3 — Months 7–9: Eat the World

### Goal
Apply the algebra to everything that has data shape. Not just serialization.

### Database Schemas
A PostgreSQL table is a data shape. A MySQL table is a different data shape.
Schema migration is a morphism.

- Generate migration scripts with proven correctness
- Detect breaking schema changes before they ship
- **Prove that a migration preserves all existing queries** (killer feature)

### API Contracts
An OpenAPI spec is a data shape. API versioning is a family of morphisms.

- Generate backward-compatible API version layers automatically
- Prove that v2 is a superset of v1 (or identify exactly where it isn't)
- Generate client SDKs that work across API versions

### Type Systems
A Rust struct is a data shape. A ReScript record is a data shape. FFI is a
morphism.

- Generate type-safe FFI bindings between any two languages
- Prove that a binding preserves semantics (not just types)
- This is what ephapax was always trying to be

### Memory Layouts
A C struct is a data shape with alignment and padding. A Zig packed struct is a
different shape. ABI compatibility is a morphism.

- Verify ABI compatibility across compiler versions
- Generate zero-copy deserializers with proven safety
- Connects directly to the Idris2 ABI / Zig FFI standard

### Configuration
TOML, YAML, Nickel, environment variables — all data shapes. Migration between
config formats is a morphism.

### Deliverable
A tool that understands data shape across serialization formats, databases, APIs,
type systems, memory layouts, and configuration. Generates adapters, migrations,
bindings, and version layers. Proves they're correct.

This is no longer Protocol Squisher. This is a **universal data shape reasoning
engine**.

---

## Phase 4 — Months 10–12: The Temporal Dimension

### Goal
Add time to the algebra. Schemas evolve. APIs evolve. Everything changes.

### A schema isn't a point — it's a trajectory.

This gives us:

- **Schema archaeology.** Given a database's migration history, reconstruct the
  complete data shape at any point in time. Replay any query against any
  historical schema.

- **Compatibility forecasting.** Given the trajectory of two evolving APIs,
  predict when they'll become incompatible. Weather forecasting for distributed
  systems.

- **Semantic versioning that means something.** A major version bump is a
  morphism that loses information. A minor bump only adds. A patch is an
  isomorphism. Version numbers become provable properties.

- **Evolution strategies.** Given a target schema and a current schema, compute
  the minimum-cost evolution path. A* pathfinding through the space of possible
  schema changes.

### Deliverable
The algebra plus time. Reason about data shape evolution, predict
incompatibilities, generate optimal migration paths.

---

## Phase 5 — Months 13–15: Make It Beautiful

### Goal
Build the interface that makes all of this accessible.

### A Visual Language for Data Shape
Not UML. Not ER diagrams. Something new that represents shape, morphisms,
information flow, and evolution in a single notation. Think of how musical
notation represents both pitch and time — this notation represents both
structure and change.

### PanLL Integration
The three-panel model is perfect:

- **Panel-L:** The constraints. Algebraic laws. Conservation of information.
- **Panel-N:** The reasoning engine. Given two shapes, find the best morphism.
  Given a history, predict the future.
- **Panel-W:** The output. The generated adapter, migration, binding, version
  layer — rendered in whatever target language you need.

### Build Order
1. TUI first (ratatui, three panels, live exploration)
2. Web version (visual notation, drag shapes, draw morphisms, live proofs)

### Deliverable
A beautiful, interactive tool for exploring data shape. Both a research
instrument and a practical tool.

---

## Phase 6 — Months 16–18: The Paper and the Release

### Goal
Write it up and ship it.

### The Paper
Not a blog post — a paper. Genuine computer science:
- The algebra of data shape
- Dependent types, information theory, linearity, temporal evolution
- The proofs
- The implementation
- The applications

Target: POPL or ICFP.

### The Release
Package the practical tool:
- CLI (`shape analyze`, `shape compare`, `shape migrate`, `shape evolve`)
- Server (axum HTTP/JSON API)
- PanLL module
- Library (Rust crate, published to crates.io)

Release both on the same day. The paper gives credibility. The tool gives
utility.

---

## What We Come Out With

Not a format converter. Not a code generator. A **new primitive** in the
programmer's toolkit — the ability to formally reason about data shape across
every boundary in a system, with proofs, with information-theoretic guarantees,
with temporal evolution, and with a beautiful visual language.

---

## Progress Tracking

### Phase 1 (Months 1–3) — IN PROGRESS
- [ ] Design new Shape IR with dependent types
- [ ] Implement linearity annotations
- [ ] Define information-theoretic metrics
- [ ] Port existing analyzer knowledge to new IR
- [ ] Prove basic properties (product/sum associativity, etc.)

### Phase 2 (Months 4–6) — NOT STARTED
- [ ] Formalize the category structure
- [ ] Implement adapter composition
- [ ] Implement automatic adapter discovery (pathfinding)
- [ ] Prove coherence conditions
- [ ] Replace Agda/Coq/Lean/Isabelle/Z3 proofs with unified theory

### Phase 3 (Months 7–9) — NOT STARTED
- [ ] Database schema analyzer
- [ ] API contract analyzer (OpenAPI)
- [ ] Type system analyzer (Rust, ReScript, etc.)
- [ ] Memory layout analyzer (C, Zig structs)
- [ ] Configuration format analyzer

### Phase 4 (Months 10–12) — NOT STARTED
- [ ] Temporal algebra (schema evolution over time)
- [ ] Compatibility forecasting
- [ ] Formal semantic versioning
- [ ] Evolution strategy pathfinder

### Phase 5 (Months 13–15) — NOT STARTED
- [ ] Visual notation design
- [ ] TUI explorer (ratatui)
- [ ] PanLL Panel-L/N/W integration
- [ ] Web interface

### Phase 6 (Months 16–18) — NOT STARTED
- [ ] Paper (POPL/ICFP submission)
- [ ] CLI packaging (`shape` command)
- [ ] crates.io publication
- [ ] Simultaneous paper + tool release
