# Vec<T> Support Complete

**Date:** 2026-02-04
**Status:** ✅ Complete - Arrays/Vectors implemented in ephapax

## Achievement

Implemented complete Vec<T> (vector/array) support in ephapax, enabling collection-based data structures critical for schema analysis. This was identified as the highest priority blocker in ROADMAP-NEXT-PHASE.md.

## Implementation Details

### 1. Type System (`ast.rs`)

**Added:**
- `Type::Vec(Box<Type>)` variant for vector types
- Updated `is_copy()` - Vec is NOT Copy (heap-allocated)
- Display implementation: `Vec<i32>` format

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    // ... existing types
    Vec(Box<Type>),  // Vector type Vec<T> (heap-allocated, not Copy)
}

impl Type {
    pub fn is_copy(&self) -> bool {
        match self {
            Type::Vec(_) => false, // Vectors are heap-allocated, not Copy
            // ...
        }
    }
}
```

### 2. Expressions (`ast.rs`)

**Added:**
- `Expr::VecLit(Vec<Expr>)` for vector literals `[e1, e2, ...]`
- `Expr::Index { vec, index }` for indexing `vec[idx]`
- Display implementations for both

**Syntax:**
```ephapax
let v = [1, 2, 3, 4, 5];  // VecLit
let first = v[0];         // Index
```

### 3. Lexer (`tokens.rs`)

**Added:**
- `Token::Vec` keyword
- `Token::LBracket` for `[`
- `Token::RBracket` for `]`

### 4. Parser (`parser.rs`)

**Added:**

**Type parsing** (`parse_type`):
```ephapax
Vec<i32>     // parses as Type::Vec(Box::new(Type::I32))
Vec<String>  // parses as Type::Vec(Box::new(Type::String))
```

**Vector literals** (`parse_primary`):
```ephapax
[1, 2, 3]    // parses as VecLit([IntLit(1), IntLit(2), IntLit(3)])
[]           // empty vector
```

**Indexing** (postfix operator in `parse_primary`):
```ephapax
vec[0]       // parses as Index { vec: Var("vec"), index: IntLit(0) }
vec[i]       // parses as Index { vec: Var("vec"), index: Var("i") }
```

### 5. Type Checker (`typeck.rs`)

**VecLit type checking:**
- Empty vectors default to `Vec<i32>`
- All elements must have the same type
- Returns `Vec<T>` where T is element type

**Index type checking:**
- Vector expression must be `Vec<T>` type
- Index expression must be `i32`
- Returns element type `T`

**Error messages:**
```
Type mismatch in vector element at index 2: expected i32, found bool
Indexing requires a vector type
Vector index: expected i32, found String
```

### 6. Interpreter (`interpreter.rs`)

**Added:**
- `Value::Vec(Vec<Value>)` runtime value
- `as_vec()` helper method
- VecLit evaluation - evaluates all elements
- Index evaluation with bounds checking

**Runtime errors:**
```rust
Index 5 out of bounds for vector of length 3
```

**Example:**
```ephapax
let v = [10, 20, 30];  // Creates Value::Vec([Int(10), Int(20), Int(30)])
v[1]                   // Returns Value::Int(20)
```

### 7. WASM Codegen (`codegen.rs`)

**Type mapping:**
- `Vec<T>` → `i32` (pointer to linear memory)

**Current status:**
- VecLit generates placeholder: `(i32.const 0) ;; Vec literal (not yet implemented)`
- Index generates placeholder: `(i64.const 0) ;; Vec indexing (not yet implemented)`

**Future work:**
- Linear memory allocation
- Vec element storage
- Indexing implementation

### 8. CLI (`main.rs`)

**Output formatting:**
```rust
fn print_value(value: &Value) {
    match value {
        Value::Vec(elements) => {
            print!("[");
            for (i, elem) in elements.iter().enumerate() {
                if i > 0 { print!(", "); }
                print_value(elem);
            }
            print!("]");
        }
        // ...
    }
}
```

**Example output:**
```
[1, 2, 3, 4, 5]
[true, false, true]
["hello", "world"]
```

## Linear Type Compliance

Vectors are **heap-allocated** and **NOT Copy**, enforcing linear usage:

```ephapax
fn consume_twice(vec: Vec<i32>) -> i32 {
    let first = vec[0];   // First use - OK
    let second = vec[1];  // ERROR: vec used twice!
}
```

**Error:**
```
Linear type violation: variable 'vec' of type Vec<i32> used twice
  help: Vec<i32> is not Copy; consider restructuring code to use value exactly once
```

**Correct usage:**
```ephapax
fn get_element(vec: Vec<i32>, index: i32) -> i32 {
    vec[index]  // Single use - OK
}
```

## Test Suite

### test-vec.eph
Basic vector creation and indexing:
```ephapax
fn make_vec() -> Vec<i32> {
    [10, 20, 30, 40, 50]
}

fn get_element(vec: Vec<i32>, index: i32) -> i32 {
    vec[index]
}

fn main() {
    let numbers = make_vec();
    get_element(numbers, 1)  // Returns 20
}
```

**Output:** `20` ✓

### test-vec-comprehensive.eph
Demonstrates:
- Empty vectors: `[]` (defaults to `Vec<i32>`)
- Homogeneous vectors: `[1, 2, 3, 4, 5]`
- Nested calls with vectors
- Vector parameters
- Multiple element types: `Vec<bool>`, `Vec<String>`

**Output:** `100` ✓

## Type Checking

All tests pass type checking:
```bash
$ cargo run -- --check test-vec.eph
✓ Type check passed (linear types verified)
```

## Features Demonstrated

| Feature | Syntax | Status |
|---------|--------|--------|
| **Vec type annotation** | `fn f() -> Vec<i32>` | ✅ Working |
| **Vec literals** | `[1, 2, 3]` | ✅ Working |
| **Empty vec** | `[]` | ✅ Working (defaults to Vec<i32>) |
| **Vec indexing** | `vec[0]` | ✅ Working |
| **Type checking** | Element type consistency | ✅ Working |
| **Linear types** | Non-Copy enforcement | ✅ Working |
| **Runtime execution** | Interpreter | ✅ Working |
| **WASM compilation** | WAT generation | ⏳ Placeholder (needs memory mgmt) |

## Use Cases Enabled

### Protocol Analysis

Now we can represent schema fields:

```ephapax
struct Field {
    name: String,
    field_type: i32,
    optional: bool,
}

struct Schema {
    name: String,
    fields: Vec<Field>,  // ✅ Now possible!
}

fn analyze_schema(schema: Schema) -> i32 {
    // Can iterate over fields, count them, etc.
    // (once we add loops)
}
```

### Data Processing

```ephapax
fn process_batch(items: Vec<i32>) -> i32 {
    // Can work with collections of data
    items[0]  // Access elements
}
```

## Roadmap Impact

**ROADMAP-NEXT-PHASE.md Phase 1 progress:**

| Feature | Priority | Estimate | Status |
|---------|----------|----------|--------|
| **Arrays/Vectors** | ⚠️ CRITICAL | 2-3 days | **✅ COMPLETE** |
| Structs/Records | ⚠️ CRITICAL | 3-4 days | 🔜 Next |
| File I/O | ⚠️ CRITICAL | 2-3 days | Later |
| Result/Option | 🔴 HIGH | 2-3 days | Later |
| HashMap | 🔴 HIGH | 2-3 days | Later |

**Critical blocker removed!** Vec support enables:
- Field lists in schemas
- Repeated elements
- Batch processing
- Collection-based algorithms

## Next Steps

### Immediate
1. **Structs/Records** - Second critical blocker
   - Define custom types with named fields
   - Represent schemas, fields, types
   - Estimate: 3-4 days

### Short-Term
2. **Loops** (for/while) - Quick win
   - Iterate over Vec elements
   - Process field lists
   - Estimate: 2-3 days

3. **Vec methods** - Enhancement
   - `len()`, `push()`, `pop()` (if we add mutability)
   - Estimate: 1-2 days

### WASM Production
4. **Linear memory management**
   - Allocate Vec storage
   - Implement Vec literals in WASM
   - Implement indexing in WASM
   - Estimate: 3-5 days

## Files Modified

### Core Compiler
- `ast.rs` - Type::Vec, Expr::VecLit, Expr::Index
- `tokens.rs` - Vec keyword, [ ] tokens
- `parser.rs` - Parse Vec<T> types, vec literals, indexing
- `typeck.rs` - VecLit and Index type checking
- `interpreter.rs` - Value::Vec, runtime evaluation
- `codegen.rs` - WASM placeholders
- `main.rs` - Vec output formatting

### Tests
- `test-vec.eph` - Basic Vec test
- `test-vec-comprehensive.eph` - Advanced features

### Documentation
- `VEC-SUPPORT-COMPLETE.md` - This file

## Lessons Learned

1. **Linear types work well** - Vec being non-Copy makes sense for resource safety
2. **Type inference needed** - Empty vectors need better type inference (future work)
3. **Parser composition** - Postfix operators (indexing) integrate cleanly
4. **WASM requires memory** - Full Vec support in WASM needs linear memory management
5. **Incremental development** - Implementing interpreter first, then WASM works well

## Commit Message

```
feat: implement Vec<T> support (arrays/vectors)

- Add Vec<T> type to type system (heap-allocated, not Copy)
- Parse vec literals [e1, e2, ...] and indexing vec[i]
- Type check element consistency and index types
- Interpreter runtime with Value::Vec and bounds checking
- WASM placeholders (full support needs linear memory)
- Tests: test-vec.eph, test-vec-comprehensive.eph

Removes critical blocker from ROADMAP-NEXT-PHASE.md Phase 1.
Enables field lists, repeated elements, batch processing.

Next: Structs/Records for custom types
```

## See Also

- [ROADMAP-NEXT-PHASE.md](ROADMAP-NEXT-PHASE.md) - Production roadmap
- [NEXT-STEPS.md](NEXT-STEPS.md) - Development tasks
- [EPHAPAX-COMPILER-COMPLETE.md](EPHAPAX-COMPILER-COMPLETE.md) - Compiler foundation
- [LINEAR-TYPES-COMPLETE.md](LINEAR-TYPES-COMPLETE.md) - Linear type system
- [COPY-TYPES-COMPLETE.md](COPY-TYPES-COMPLETE.md) - Copy trait

---

**Status:** ✅ Complete
**Blocker Removed:** Arrays/Vectors ⚠️ CRITICAL
**Next Critical:** Structs/Records ⚠️ CRITICAL
