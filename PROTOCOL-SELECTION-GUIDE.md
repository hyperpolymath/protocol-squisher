# Protocol Selection Guide

**Quick decision tree for choosing the right serialization protocol.**

## Start Here: What's Your Priority?

```
                         YOUR PRIORITY
                              │
                              │
        ┌─────────────────────┼─────────────────────┐
        │                     │                     │
        ▼                     ▼                     ▼
    PERFORMANCE          FLEXIBILITY          OPTIMIZATION
    (speed/latency)    (rapid development)   (find improvements)
        │                     │                     │
        │                     │                     │
        ▼                     ▼                     ▼
    See Flow 1            See Flow 2            See Flow 3
```

---

## Flow 1: Performance Priority

**You need:** Microsecond latency, zero-copy access, maximum throughput

```
START: Performance is critical
    │
    ├─ Real-time system? (games, audio, trading)
    │   YES → Cap'n Proto (0.18 squishability - theoretical optimum)
    │
    ├─ Embedded/IoT? (limited memory)
    │   YES → FlatBuffers (0.25 squishability - zero-copy structs)
    │
    ├─ Rust-to-Rust only?
    │   YES → Rust serde (0.75 squishability - borrow checker wins)
    │
    └─ Cross-language with good perf?
        YES → Bebop (0.62) or Protobuf (0.68) - modern balanced
```

**Key Insight:** Zero-copy protocols (Cap'n Proto, FlatBuffers) have LOW squishability because they're already optimal. This is a FEATURE.

---

## Flow 2: Flexibility Priority

**You need:** Rapid iteration, schema changes, no compile step

```
START: Flexibility is critical
    │
    ├─ Schema completely unknown?
    │   YES → JSON Schema (0.35 squishability - universal baseline)
    │
    ├─ Need better performance than JSON?
    │   YES → MessagePack (0.45 squishability - binary type tags)
    │
    ├─ Frontend ↔ Backend (web)?
    │   YES → JSON Schema (human-readable, debugging)
    │
    ├─ Python ecosystem?
    │   YES → Pydantic (0.42 squishability - runtime validation)
    │
    └─ JavaScript/TypeScript?
        YES → ReScript (0.58 squishability - OCaml types, JS target)
```

**Key Insight:** Dynamic protocols sacrifice performance for flexibility. MessagePack is the sweet spot (binary + dynamic).

---

## Flow 3: Optimization Priority

**You need:** Protocol-squisher to find improvements, reduce bandwidth

```
START: Want to find optimizations
    │
    ├─ Long-lived data storage?
    │   YES → Avro (0.85 squishability - HIGHEST, union types + evolution)
    │
    ├─ Multiple schema versions in production?
    │   YES → Avro (0.85) or Thrift (0.82) - backward compat creates bloat
    │
    ├─ Legacy system with deprecated fields?
    │   YES → Avro (0.85) or Thrift (0.82) - perfect for finding waste
    │
    ├─ Analytics/data warehouse?
    │   YES → Avro (0.85) - schema evolution built-in
    │
    └─ RPC-focused microservices?
        YES → Thrift (0.82 squishability - RPC metadata overhead)
```

**Key Insight:** Schema evolution protocols have HIGHEST squishability (0.8+) because backward compatibility creates optimization opportunities.

---

## Decision Matrix

| Criterion | Top Choice | Runner-Up | Avoid |
|-----------|------------|-----------|-------|
| **Latency < 1ms** | Cap'n Proto | FlatBuffers | JSON |
| **Cross-language** | Protobuf | Bebop | Rust serde |
| **Schema evolution** | Avro | Thrift | Cap'n Proto |
| **Rapid prototyping** | JSON | MessagePack | Cap'n Proto |
| **Bandwidth optimization** | Avro/Thrift | Protobuf | JSON |
| **Zero build step** | JSON | MessagePack | Any schema-based |
| **Type safety** | Rust serde | Protobuf | JSON |
| **Debugging ease** | JSON | Protobuf (text format) | Cap'n Proto |

---

## Common Use Cases

### Web API (Public-Facing)
**Recommendation:** JSON Schema (0.35)
- Human-readable
- Universal compatibility
- Easy debugging
- Accept lower performance for accessibility

---

### Microservices (Internal)
**Recommendation:** Protobuf (0.68) or Bebop (0.62)
- Type safety
- Good performance
- Moderate squishability
- Active tooling ecosystems

**Why not Cap'n Proto?** Over-optimized for most microservices. Protobuf is "good enough" with better tooling.

---

### Data Warehouse / Analytics
**Recommendation:** Avro (0.85)
- Schema evolution built-in
- Reader/writer schema separation
- Highest squishability (find bloat)
- Hadoop/Spark ecosystem

---

### Real-Time Systems (Trading, Robotics)
**Recommendation:** Cap'n Proto (0.18)
- Theoretical performance limit
- Zero-copy everything
- Predictable latency
- Low squishability expected (already optimal)

---

### Mobile Apps
**Recommendation:** Protobuf (0.68) or Bebop (0.62)
- Bandwidth efficiency (cellular)
- Battery efficiency (less CPU)
- Small binary size
- Good cross-platform support

---

### Game Engines
**Recommendation:** FlatBuffers (0.25)
- Zero-copy structs (Vec3, Matrix)
- Mmap support (large assets)
- Predictable memory layout
- Low squishability (already optimized)

---

### IoT / Embedded
**Recommendation:** FlatBuffers (0.25) or Bebop (0.62)
- Limited memory
- No heap allocation (FlatBuffers structs)
- Simple parsing (Bebop fixed-width)
- Low power consumption

---

### Configuration Files
**Recommendation:** JSON Schema (0.35) or TOML
- Human-readable
- Version control friendly
- No binary tooling needed
- Not performance-critical

---

## Squishability Interpretation

### High Squishability (0.7-0.9) - Avro, Thrift
**Meaning:** Protocol-squisher will find MANY optimization opportunities

**Why?**
- Backward compatibility bloat (deprecated fields)
- Union types for null handling
- Over-specified types (int32 when int8 sufficient)
- Optional fields that are always present

**Use When:**
- You WANT to find improvements
- Schema evolves frequently
- Multiple teams/versions
- Long-term data storage

---

### Medium Squishability (0.5-0.7) - Protobuf, Bebop, Rust serde
**Meaning:** Some optimization opportunities, balanced design

**Why?**
- Modern design with less bloat
- Some optional fields
- Safe widening opportunities (int32→int64)
- Type precision choices (f32 vs f64)

**Use When:**
- Standard backend services
- Microservices communication
- Mobile apps
- Good performance with some optimization potential

---

### Low Squishability (0.2-0.4) - Cap'n Proto, FlatBuffers, JSON
**Meaning:** Few optimization opportunities

**Why (Zero-Copy):**
- Cap'n Proto: Already at theoretical optimum
- FlatBuffers: Zero-copy structs, manual optimization
- These are FEATURES (already fast)

**Why (Baseline):**
- JSON: String-based, no binary optimization
- Low performance but that's expected

**Use When:**
- Performance-critical (zero-copy protocols)
- Universal compatibility (JSON)
- Already optimized systems

---

## Protocol Compatibility Guide

### Best Cross-Protocol Pairs (Business Class Transport)

**Schema-Based ↔ Schema-Based:**
- ✅ Protobuf ↔ Avro (field mapping)
- ✅ Protobuf ↔ Thrift (nearly identical)
- ✅ Bebop ↔ Protobuf (compatible types)

**Evolution ↔ Dynamic:**
- ✅ Avro ↔ MessagePack (union types map well)

**Within Ecosystem:**
- ✅ Rust serde ↔ Rust serde (zero-copy)
- ✅ Python ↔ Python (native objects)

---

### Problematic Cross-Protocol Pairs (Wheelbarrow Class)

**Static ↔ Dynamic:**
- ⚠️ Protobuf ↔ JSON (binary ↔ string conversion)
- ⚠️ Cap'n Proto ↔ JSON (zero-copy ↔ heap-everything)

**Language Ownership Mismatch:**
- ⚠️ Rust ↔ Python (ownership vs GC)
- ⚠️ Rust ↔ JavaScript (lifetimes vs dynamic)

**Zero-Copy ↔ Others:**
- ⚠️ Cap'n Proto ↔ Avro (layout mismatch)
- ⚠️ FlatBuffers ↔ Thrift (memory model incompatibility)

---

## Anti-Patterns to Avoid

### ❌ Using Cap'n Proto for Microservices
**Why Wrong:** Over-optimized. Protobuf is easier with good-enough performance.
**Use Instead:** Protobuf (0.68) or Bebop (0.62)

---

### ❌ Using JSON for High-Volume Logs
**Why Wrong:** String-based, high bandwidth, slow parsing
**Use Instead:** MessagePack (0.45) or Protobuf (0.68)

---

### ❌ Using Avro for Real-Time Systems
**Why Wrong:** Schema evolution overhead, union type tags
**Use Instead:** Cap'n Proto (0.18) or FlatBuffers (0.25)

---

### ❌ Using FlatBuffers for Frequently-Changing Schemas
**Why Wrong:** Fixed layouts, hard to evolve
**Use Instead:** Avro (0.85) or Thrift (0.82)

---

### ❌ Using Protobuf for Configuration Files
**Why Wrong:** Binary format, not human-readable, needs tooling
**Use Instead:** JSON (0.35) or TOML

---

## Quick Reference Chart

```
Performance ◄────────────────────────────────────► Flexibility
            (low squishability)              (high squishability)

Cap'n Proto    FlatBuffers    Bebop      Avro        JSON
   0.18           0.25         0.62       0.85        0.35
    │              │            │          │           │
    │              │            │          │           └─ Baseline fallback
    │              │            │          └─ Schema evolution (most squishable)
    │              │            └─ Modern balanced
    │              └─ Zero-copy structs
    └─ Theoretical optimum (least squishable)
```

---

## When Protocol-Squisher Helps Most

### ✅ High Value (Use Protocol-Squisher)

1. **Schema Evolution Analysis** (Avro, Thrift)
   - Find deprecated fields (52% of evolved schemas)
   - Identify unnecessary optionals (68% always present)
   - Detect type over-specification (int32→int64 widening)

2. **Legacy System Optimization** (Any protocol with history)
   - Backward compatibility bloat
   - Accumulated technical debt
   - Multiple schema versions in production

3. **Cross-Protocol Translation**
   - Protobuf ↔ Avro (Business class achievable)
   - Thrift ↔ Bebop (safe migration path)
   - Any ↔ JSON (universal fallback)

---

### ⚠️ Limited Value (Already Optimal)

1. **Zero-Copy Protocols** (Cap'n Proto, FlatBuffers)
   - Low squishability by design (0.18-0.25)
   - Already at theoretical optimum
   - Manual optimization already done

2. **Fresh Schemas** (New projects)
   - No backward compatibility bloat yet
   - Minimal optimization opportunities
   - Consider using for initial design validation

3. **Single-Protocol Systems** (No cross-protocol needs)
   - Cap'n Proto ↔ Cap'n Proto (Concorde class, no squishing)
   - Rust serde ↔ Rust serde (zero-copy, already optimal)

---

## Summary Recommendations

### Starting a New Project?
→ **Bebop (0.62)** or **Protobuf (0.68)** for balanced performance + tooling

### Inheriting Legacy System?
→ **Run protocol-squisher on Avro/Thrift** to find optimization opportunities (0.8+ squishability)

### Need Maximum Performance?
→ **Cap'n Proto (0.18)** for theoretical limit (don't expect squishing opportunities)

### Need Maximum Flexibility?
→ **JSON (0.35)** or **MessagePack (0.45)** for schema-less development

### Building for Long-Term?
→ **Avro (0.85)** for schema evolution + protocol-squisher analysis

---

**See also:**
- [DIVERSITY-ANALYSIS.md](DIVERSITY-ANALYSIS.md) - Complete 11-protocol analysis
- [DIVERSITY-SUMMARY.txt](DIVERSITY-SUMMARY.txt) - Visual rankings and charts
- [PROTOCOL-COMPARISON.txt](PROTOCOL-COMPARISON.txt) - Quick reference tables
