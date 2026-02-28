# Z3/SMT Proofs for Protocol Squisher

SPDX-License-Identifier: PMPL-1.0-or-later

## Overview

Automated verification of transport class properties using the Z3 SMT solver.
These proofs complement the constructive proofs in Agda, Coq, and Isabelle
with fully automated checking.

## Files

| File | Purpose | Expected Result |
|------|---------|-----------------|
| `types.smt2` | Shared type definitions (PrimitiveType, TransportClass, sizeof, safe_widening) | N/A (library) |
| `transport_exhaustive.smt2` | Verify every type pair maps to exactly one transport class | `unsat` |
| `concorde_constraints.smt2` | Verify Concorde/widening/size constraints (4 checks) | `unsat` (all) |

## Running

Requires Z3 (version 4.8+):

```bash
# Exhaustiveness check
z3 transport_exhaustive.smt2
# Expected output: unsat

# Concorde constraint checks (4 independent checks)
z3 concorde_constraints.smt2
# Expected output: unsat (repeated 4 times)
```

## What "unsat" Means

Each `.smt2` file asserts the **negation** of the property we want to prove.
If Z3 returns `unsat`, it means the negation is unsatisfiable — the property
holds universally.

- `transport_exhaustive.smt2`: "There exists a type pair with no transport class" → unsat (no gaps)
- `concorde_constraints.smt2` check 1: "Concorde assigned to non-identical types" → unsat (only identical)
- `concorde_constraints.smt2` check 2: "Widening to smaller type" → unsat (always larger)
- `concorde_constraints.smt2` check 3: "Type widens to itself" → unsat (irreflexive)
- `concorde_constraints.smt2` check 4: "Widening pair not Business class" → unsat (all Business)
