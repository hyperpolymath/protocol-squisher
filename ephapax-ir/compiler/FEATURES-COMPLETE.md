# Ephapax Compiler - Phase 1+ Features Complete

## Summary

The Ephapax compiler now has a complete set of features beyond the original Phase 1 MVP, including:

### Core Language Features
- ✅ Linear type system with move semantics
- ✅ Borrow tracking (variables can be borrowed multiple times)
- ✅ Pattern matching (Option, Result, exhaustive checking)
- ✅ Unary operators (NOT `!`, NEG `-`)
- ✅ Block expressions with proper scoping
- ✅ Let bindings with correct scoping (restructure_lets)

### Data Structures

**HashMap**
- ✅ HashMap literals: `{"key": "value", ...}`
- ✅ `hashmap_new()` - create empty HashMap
- ✅ `hashmap_insert(map, key, value)` - add key-value pair
- ✅ `hashmap_get(&map, key)` - get value (returns Option)
- ✅ `hashmap_remove(map, key)` - remove key (returns new HashMap)
- ✅ `hashmap_contains_key(&map, key)` - check if key exists

**Vec**
- ✅ `vec_new()` - create empty vector
- ✅ `vec_push(vec, elem)` - append element
- ✅ `vec_pop(vec)` - remove last element (returns Option<T>)
- ✅ `vec_length(&vec)` - get length (accepts Vec or &Vec)
- ✅ `vec_get(&vec, index)` - get element at index (returns Option)

### Standard Library Functions

**String Operations**
- ✅ `string_length(&str)` - get string length
- ✅ `string_to_upper(&str)` - convert to uppercase
- ✅ `string_to_lower(&str)` - convert to lowercase
- ✅ `string_substring(&str, start, len)` - extract substring

**Math Operations**
- ✅ `abs(n)` - absolute value
- ✅ `min(a, b)` - minimum of two values
- ✅ `max(a, b)` - maximum of two values
- ✅ `pow(base, exp)` - exponentiation

### Type System Features

**Borrow Semantics**
- Variables can be borrowed multiple times without consumption
- Borrows satisfy "must use" requirement for linear types
- Separate tracking for borrowed vs consumed variables
- References (&T) accepted by built-in functions where appropriate

**Linear Types**
- Non-Copy types (Vec, HashMap, String) must be used exactly once
- Borrowing counts as using the variable for linear type checking
- Clear error messages for linear type violations

### Parser Improvements

**Disambiguation**
- HashMap literals `{"k": v}` vs blocks `{ expr }`
- Struct literals `S { f: v }` vs control flow blocks
- Proper precedence for if/while condition parsing

**Scoping**
- Let bindings scope to all remaining expressions in block
- restructure_lets ensures correct variable visibility

## Test Files

- `test-vec-clean.eph` - Vec operations test
- `test-stdlib.eph` - String and math operations
- `test-hashmap-literal.eph` - HashMap literal syntax
- `demo-mvp-complete.eph` - Comprehensive demo of all features

## Known Limitations

1. **Variable Shadowing**: Using the same variable name with `let v = f(v)` causes type checker issues. Workaround: use distinct names (v1, v2, v3).

2. **Print Statements**: Must be inside block expressions to execute properly. Top-level prints in function body don't output.

3. **Tuple Patterns**: Pattern matching doesn't support tuple destructuring yet (e.g., `(a, b) => ...`).

## Build and Run

```bash
cargo build --quiet
cargo run -- demo-mvp-complete.eph
```

## Next Steps (Future Phases)

- Mutable variables (`let mut`)
- For/while loops with mutation
- Tuple type and tuple patterns
- Schema parsers (.bop, .fbs, .proto)
- WASM codegen improvements
- More standard library functions
