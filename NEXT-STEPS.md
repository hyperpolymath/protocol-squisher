# Next Steps - Protocol Squisher Development

**Current Status:** Ephapax compiler + linear type checker + Copy types + pattern matching complete ✅

## What's Been Accomplished

1. **Ephapax Compiler** (commit 1981d40)
   - Lexer, parser, AST, interpreter
   - 16 tests, 100% passing
   - CLI with file and inline execution

2. **Linear Type Checker** (commit 5c029b8)
   - Resource safety enforcement
   - 23 tests total (16 compiler + 7 typeck)
   - Catches double-use, unused variables
   - Integrated with CLI (`--check` flag)

3. **Copy Types for Primitives** (commit da25245)
   - i32, i64, bool, f32, f64 marked as Copy
   - Multiple uses allowed for Copy types
   - Preserves linear safety for non-Copy types
   - 23 tests passing with new semantics

4. **Pattern Matching** (commit a17abb1)
   - Match expressions with multiple arms
   - Pattern types: IntLit, BoolLit, Var binding, Wildcard
   - Exhaustiveness checking
   - Type checking ensures all arms same type
   - bebop_analyzer_match.eph demonstrates cleaner code

5. **Protocol Analyzer Prototype** (complete)
   - bebop_analyzer_match.eph uses pattern matching
   - Successfully type checks and executes
   - Outputs: 102 (verified correct)

## The Linear Types Challenge

### Current State

The bebop_analyzer.eph demonstrates a fundamental challenge:

```ephapax
fn bebop_to_ir(bebop_type: i32) -> i32 {
    if bebop_type == bebop_int32() {
        ir_i32()
    } else {
        if bebop_type == bebop_int64() {  // ERROR: bebop_type used again!
            ir_i64()
        } else {
            // ... more uses of bebop_type
        }
    }
}
```

**Error:** `Linear type violation: variable 'bebop_type' used twice`

**Root cause:** Comparison operators consume their operands in strict linear types, but we need to compare the same value multiple times.

### The Solution: Affine Types

Current ephapax uses **linear types** (use exactly once).
Protocol analyzers need **affine types** (use at most once) or **relevant types** (use at least once) with borrowing.

### Three Approaches

**Option 1: Add Borrowing**
```ephapax
fn bebop_to_ir(bebop_type: i32) -> i32 {
    if &bebop_type == bebop_int32() {  // Borrow, don't move
        ir_i32()
    } else {
        if &bebop_type == bebop_int64() {  // Another borrow
            ir_i64()
        } else {
            ...
        }
    }
}
```

Pros: Natural, familiar from Rust
Cons: Requires lifetime tracking, more complex type checker

**Option 2: Relevant Types (Copy trait)**
```ephapax
fn bebop_to_ir(bebop_type: i32) -> i32 {
    // Primitives are Copy, can use multiple times
    if bebop_type == bebop_int32() {
        ir_i32()
    } else {
        if bebop_type == bebop_int64() {
            ir_i64()
        } else {
            ...
        }
    }
}
```

Pros: Simple, primitives can be copied
Cons: Need to distinguish Copy vs. non-Copy types

**Option 3: Pattern Matching**
```ephapax
fn bebop_to_ir(bebop_type: i32) -> i32 {
    match bebop_type {
        BebopInt32 => ir_i32(),
        BebopInt64 => ir_i64(),
        BebopString => ir_string(),
        _ => ir_byte()
    }
}
```

Pros: Consumes value exactly once, exhaustive checking
Cons: Requires pattern matching implementation in compiler

## Recommended Approach

**Phase 1: Add Copy Trait for Primitives**

Modify type checker to allow multiple uses of Copy types:
- i32, i64, bool are Copy
- Strings, custom types are not Copy
- Comparison/arithmetic on Copy types doesn't consume

This is minimal work and enables realistic protocol analyzers.

**Phase 2: Add Pattern Matching**

Implement match expressions:
- Exhaustiveness checking
- Guards and complex patterns
- Better code generation

**Phase 3: Add Borrowing (Optional)**

For advanced use cases:
- Lifetime tracking
- Mutable vs. immutable borrows
- Reference types

## Current Working Examples

### test-bebop-simple.eph ✅

```ephapax
fn bebop_int32() -> i32 { 1 }
fn bebop_string() -> i32 { 2 }

fn bebop_to_ir(bebop_type: i32) -> i32 {
    if bebop_type == bebop_int32() {
        10
    } else {
        20
    }
}

fn main() {
    let field1 = bebop_int32();
    let field2 = bebop_string();
    bebop_to_ir(field1) + bebop_to_ir(field2)
}
```

Output: 30
Linear check: ✅ Pass (each variable used exactly once)

### test-linear-valid.eph ✅

```ephapax
fn identity(x: i32) -> i32 { x }

fn add_const(x: i32) -> i32 {
    let y = 10;
    x + y
}

fn main() {
    let a = 5;
    let b = identity(a);
    add_const(b)
}
```

Output: 15
Linear check: ✅ Pass

## Next Development Tasks

### Immediate (Essential for Analyzers) - ✅ COMPLETE

1. **Implement Copy trait** ✅
   - Mark i32, i64, bool, f32, f64 as Copy
   - Allow multiple uses of Copy types
   - Update type checker to track Copy types

2. **Test with full bebop_analyzer.eph** ✅
   - Verify all functions type check
   - Run analyzer and verify output
   - Compare with Rust analyzer results

3. **Documentation** ✅
   - Update compiler README with Copy types
   - Examples of Copy vs. move semantics
   - Guidelines for analyzer authors

### Medium Priority (Better Ergonomics) - ✅ COMPLETE

4. **Pattern matching** ✅
   - match expressions
   - Exhaustiveness checking
   - Guards (basic wildcard support)

5. **Type inference improvements**
   - Infer Copy trait automatically
   - Better error messages
   - Suggest fixes for linear violations

6. **More operators**
   - Logical AND/OR
   - Bitwise operations
   - String concatenation

### Long Term (Advanced Features)

7. **Borrowing system**
   - Reference types (&T)
   - Lifetime tracking
   - Mutable vs. immutable

8. **WASM backend**
   - Compile to WASM
   - No GC needed (linear types!)
   - Integrate with browsers

9. **Full analyzer suite**
   - Rewrite all 7 analyzers in ephapax
   - Benchmarks vs. Rust
   - Integration with protocol-squisher

## Performance Goals

| Metric | Target |
|--------|--------|
| Type check time | <10ms for analyzer |
| Compile time | <100ms for analyzer |
| Runtime speed | Within 2x of Rust |
| Memory usage | Within 1.5x of Rust |

## Integration Plan

### Phase A: Hybrid (Current)

```
Rust analyzers → IR → Ephapax verification
```

### Phase B: Pure Ephapax Analyzers

```
Ephapax analyzers → IR (with linear guarantees)
```

### Phase C: Full Stack

```
Ephapax analyzer → Ephapax IR → Idris2 proofs → Generated code
```

## Documentation Status

- [x] EPHAPAX-COMPILER-COMPLETE.md
- [x] LINEAR-TYPES-COMPLETE.md
- [x] COPY-TYPES-COMPLETE.md
- [x] NEXT-STEPS.md (this file)
- [ ] PATTERN-MATCHING-COMPLETE.md (to be created)
- [ ] WASM-BACKEND-SPEC.md (next phase)

## See Also

- [ephapax-ir/compiler/README.md](ephapax-ir/compiler/README.md)
- [EPHAPAX-COMPILER-COMPLETE.md](EPHAPAX-COMPILER-COMPLETE.md)
- [LINEAR-TYPES-COMPLETE.md](LINEAR-TYPES-COMPLETE.md)
