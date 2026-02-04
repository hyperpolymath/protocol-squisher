# Ephapax Roadmap - Next Phase

**Current Status:** Core language complete, basic analyzers working
**Goal:** Production-ready protocol analyzer suite

## Critical Path to Production

### Phase 1: Essential Language Features (Highest Priority)

These are **blockers** for real schema parsing and analysis:

#### 1.1 Arrays/Vectors ⚠️ CRITICAL
**Why:** Schema files have lists of fields, repeated elements, etc.
**Example Use:**
```ephapax
// Current: Can't represent this
// Needed:
fn analyze_fields(fields: Vec<Field>) -> i32 {
    // Iterate over schema fields
}
```
**Estimate:** 2-3 days
**Files:** ast.rs, parser.rs, typeck.rs, interpreter.rs, codegen.rs

#### 1.2 Structs/Records ⚠️ CRITICAL
**Why:** Need to represent schemas, fields, types as data structures
**Example Use:**
```ephapax
struct Field {
    name: String,
    field_type: i32,
    optional: bool,
}

struct Schema {
    name: String,
    fields: Vec<Field>,
}
```
**Estimate:** 3-4 days
**Files:** ast.rs, parser.rs, typeck.rs, interpreter.rs, codegen.rs

#### 1.3 File I/O ⚠️ CRITICAL
**Why:** Need to read .bop, .fbs, .proto, etc. files
**Example Use:**
```ephapax
fn parse_bebop_file(path: String) -> Result<Schema> {
    let content = read_file(path)?;
    parse_bebop_schema(content)
}
```
**Estimate:** 2-3 days
**Requires:** Result type, String operations, FFI or built-in functions

#### 1.4 Result/Option Types 🔴 HIGH
**Why:** Proper error handling for parsing, validation
**Example Use:**
```ephapax
fn parse_field(line: String) -> Result<Field, ParseError> {
    match extract_type(line) {
        Some(t) => Ok(Field { ... }),
        None => Err(ParseError::InvalidSyntax),
    }
}
```
**Estimate:** 2-3 days
**Files:** ast.rs, parser.rs, typeck.rs, interpreter.rs

#### 1.5 HashMap/Map Types 🔴 HIGH
**Why:** Schema name lookups, type mappings
**Example Use:**
```ephapax
fn build_type_map(schema: Schema) -> Map<String, Type> {
    // Map field names to types
}
```
**Estimate:** 2-3 days

**Phase 1 Total:** ~15-20 days of development

### Phase 2: WASM Production Readiness

#### 2.1 Memory Management for WASM
**Current Issue:** Strings map to null pointers in WASM
**Need:**
- Linear memory allocation
- String table for string literals
- Heap allocator for dynamic strings
- Garbage collection or manual memory management

**Example:**
```wat
(memory 1)  ;; 1 page = 64KB
(data (i32.const 0) "Hello, World!")  ;; String table
```
**Estimate:** 5-7 days

#### 2.2 WASM Binary Compilation
**Current:** Generate WAT text format
**Need:** Compile WAT → WASM binary
**Tools:** `wat2wasm` or `wasmtime` integration
**Estimate:** 1-2 days

#### 2.3 WASM Runtime Integration
**Need:**
- Import/export functions
- Host function bindings (for file I/O)
- WASI support for system calls
**Estimate:** 3-5 days

**Phase 2 Total:** ~10-15 days

### Phase 3: Parser Implementation

#### 3.1 Bebop Parser
**Parse:** `.bop` schema files
**Example:**
```bebop
struct User {
    int32 id;
    string name;
    float64 score;
}
```
**Need:** String parsing, regex, or parser combinators
**Estimate:** 3-4 days

#### 3.2 FlatBuffers Parser
**Parse:** `.fbs` schema files
**Estimate:** 3-4 days

#### 3.3 Protocol Buffers Parser
**Parse:** `.proto` files (proto2/proto3)
**Estimate:** 4-5 days

#### 3.4 Other Protocol Parsers
- MessagePack (JSON-like, easier)
- Avro (JSON schema)
- Thrift (.thrift files)
- Cap'n Proto (.capnp files)
**Estimate:** 10-15 days total

**Phase 3 Total:** ~25-35 days

### Phase 4: Integration & Deployment

#### 4.1 Rust FFI Integration
**Need:** Call ephapax analyzers from Rust
**Approach:**
```rust
// In protocol-squisher Rust code
use ephapax_runtime::analyze_bebop;

let analysis = analyze_bebop("schema.bop")?;
```
**Estimate:** 3-5 days

#### 4.2 CLI Integration
**Need:** `protocol-squisher analyze schema.bop`
**Estimate:** 2-3 days

#### 4.3 Benchmarking
**Need:** Compare ephapax vs Rust analyzers
**Metrics:**
- Parse time
- Analysis time
- Memory usage
- Accuracy
**Estimate:** 3-5 days

#### 4.4 Optimization
**Need:**
- Constant folding
- Dead code elimination
- Inlining
- Loop optimization (when loops added)
**Estimate:** 5-10 days

**Phase 4 Total:** ~15-25 days

## Quick Wins (High Impact, Low Effort)

### 1. Loops (for/while) - 2-3 days
**Why:** Iterate over fields, elements
**Impact:** 🔴 HIGH

### 2. Mutable Variables - 1-2 days
**Why:** Build up schemas, accumulate results
**Impact:** 🟡 MEDIUM

### 3. Comments in Code - 1 day
**Why:** Better code documentation
**Impact:** 🟢 LOW (already have // comments in lexer)

### 4. Better Error Messages - 2-3 days
**Why:** Developer experience
**Impact:** 🟡 MEDIUM

### 5. Standard Library - 3-5 days
**Why:** Common utilities (string ops, math, etc.)
**Impact:** 🔴 HIGH

## What's NOT Needed (Lower Priority)

### Can Skip for Now:
- ❌ Generics - Can hardcode types initially
- ❌ Traits - Not essential for analyzers
- ❌ Macros - Not needed yet
- ❌ Async/await - Analyzers are sync
- ❌ FFI to other languages - WASM is enough
- ❌ Package manager - Single project for now
- ❌ IDE integration - VSCode extension later
- ❌ Debugger - Print debugging works
- ❌ Profiler - Optimize later

## Minimum Viable Analyzer (MVA)

To get ONE working end-to-end analyzer:

**Must Have:**
1. ✅ String type (done)
2. ⚠️ Arrays/Vec
3. ⚠️ Structs
4. ⚠️ File I/O
5. ⚠️ Result/Option
6. 🔴 Loops
7. 🔴 String methods (split, trim, etc.)

**Estimate to MVA:** ~25-30 days

**Then we can:**
```bash
ephapax analyze schema.bop --output analysis.json
```

## Alternative: Hybrid Approach

**What if we DON'T wait for full ephapax features?**

### Option A: Rust Parser + Ephapax Analysis
```
Rust parses schema → IR → Ephapax WASM analyzer → Results
```
**Pros:**
- Can use existing Rust parsers
- Focus ephapax on analysis logic only
- WASM deployment works immediately

**Cons:**
- Not "pure ephapax"
- Still need Rust dependencies

**Time to Working:** ~5-10 days

### Option B: Transpile Approach
```
Ephapax + macros → Generate Rust code → Compile
```
**Pros:**
- Leverage Rust ecosystem
- Easy integration

**Cons:**
- Not true WASM compilation
- Defeats purpose of ephapax

### Option C: JSON Schema Input
```
Convert schema to JSON → Ephapax reads JSON → Analyze
```
**Pros:**
- Simple input format
- No schema parsing needed in ephapax

**Cons:**
- Extra conversion step
- Loses schema structure

## Recommended Path Forward

### Sprint 1 (Week 1-2): Core Language Extensions
1. Arrays/Vec - 3 days
2. Structs - 4 days
3. Result/Option - 3 days
**Deliverable:** Can represent schemas as data

### Sprint 2 (Week 3): I/O & Loops
1. File I/O - 3 days
2. Loops (for) - 2 days
**Deliverable:** Can read files and iterate

### Sprint 3 (Week 4-5): First Parser
1. Bebop parser - 4 days
2. String utilities - 2 days
3. Testing - 2 days
**Deliverable:** Parse .bop files

### Sprint 4 (Week 6-7): WASM Production
1. Memory management - 5 days
2. Binary compilation - 2 days
3. Runtime integration - 3 days
**Deliverable:** Deployable WASM module

### Sprint 5 (Week 8-9): Integration
1. Rust FFI - 3 days
2. CLI integration - 2 days
3. Benchmarking - 3 days
**Deliverable:** Production analyzer

**Total Timeline:** ~9 weeks to production

## Immediate Next Steps (This Week)

1. **Add Vec<T> type** - Most critical blocker
2. **Add struct definitions** - Second most critical
3. **Add for loops** - Quick win for iteration
4. **Test with realistic schema** - Validate approach

## Questions to Answer

1. **Do we need pure ephapax parsers, or can Rust parsers feed ephapax analyzers?**
   - Pure: 25-35 days
   - Hybrid: 5-10 days

2. **WASM deployment critical, or interpreter OK initially?**
   - WASM: +10-15 days
   - Interpreter: Ready now

3. **Which protocol should we prioritize?**
   - Bebop (simplest)
   - Protobuf (most popular)
   - FlatBuffers (best performance)

4. **How important is matching Rust performance?**
   - Critical: Need heavy optimization
   - OK if close: Current approach fine

## Success Metrics

**MVP Success:**
- [ ] Parse at least 1 protocol schema format
- [ ] Analyze 10+ real-world schemas
- [ ] Match Rust analyzer accuracy (100%)
- [ ] Within 2x Rust performance
- [ ] Compile to WASM
- [ ] Integrate with protocol-squisher CLI

**Production Success:**
- [ ] All 7 protocols supported
- [ ] 1000+ schemas analyzed
- [ ] Within 1.5x Rust performance
- [ ] < 100KB WASM binary
- [ ] < 10ms analysis time per schema
- [ ] Browser deployment working

## Resources Needed

**Development Time:**
- Minimum: 25-30 days (MVA)
- Realistic: 45-60 days (production)
- Ideal: 90 days (polished, optimized)

**Current Assets:**
- ✅ Working compiler
- ✅ Type checker
- ✅ WASM codegen
- ✅ Basic analyzers
- ✅ Documentation

**Missing Assets:**
- ⚠️ Arrays, structs, I/O
- ⚠️ Parser implementations
- ⚠️ WASM memory management
- ⚠️ Standard library

## Conclusion

**Minimum to be useful:** Arrays + Structs + File I/O + Loops = ~15 days

**Recommended start:** Implement Vec<T> this week, then structs next week.

**Decision point:** Pure ephapax vs hybrid approach determines timeline (9 weeks vs 2 weeks).

Want me to start on Vec<T> type implementation now?
