# Benchmark Results Interpretation Guide

This document explains how to interpret protocol-squisher benchmark results and validate performance claims.

## Quick Reference: Expected Performance

| Transport Class | Target Range | What It Means | Example Operations |
|-----------------|--------------|---------------|-------------------|
| **Concorde** | 1-2ns | Sub-pointer-dereference | i64 identity, str borrow |
| **Business Class** | 10-20ns | Single arithmetic op | i32→i64 widening |
| **Economy** | 50-100ns | Small allocation | String clone, Vec<10> |
| **Wheelbarrow** | 100-1000ns | JSON serialization | Full roundtrip |

## Understanding Criterion Output

### Terminal Output

```
Concorde/i64_identity
                        time:   [1.2345 ns 1.2678 ns 1.3012 ns]
                        change: [-5.1234% -2.3456% +0.8901%] (p = 0.42 > 0.05)
                        No change in performance detected.
```

**Fields:**
- **time**: `[lower_bound mean upper_bound]` - 95% confidence interval
  - **lower_bound**: Fastest observed performance
  - **mean**: Average across all samples
  - **upper_bound**: Slowest observed performance

- **change**: Percentage difference vs previous baseline
  - Negative = improvement (faster)
  - Positive = regression (slower)

- **p-value**: Statistical significance
  - `p < 0.05`: Change is statistically significant
  - `p > 0.05`: Change may be noise

- **Status message**:
  - "No change detected": Within noise threshold
  - "Performance has improved": Statistically significant speedup
  - "Performance has regressed": Statistically significant slowdown

### HTML Reports

Navigate to `target/criterion/report/index.html` for interactive visualizations:

1. **Violin Plots**: Show distribution of measurements
   - Wide = high variance
   - Narrow = consistent performance

2. **Line Charts**: Performance over time (if multiple runs)
   - Upward trend = regression
   - Downward trend = improvement

3. **PDF Estimates**: Probability density function
   - Sharp peak = consistent
   - Flat/wide = variable

4. **Comparison Tables**: Side-by-side baseline comparison

## Validating Transport Class Claims

### Concorde (1-2ns target)

**What to check:**

```bash
cargo bench --bench transport_classes Concorde
```

**Expected results:**
- `i64_identity`: 0.5-2ns (may be optimized to near-zero)
- `str_borrow`: 1-2ns (reference passing)
- `f64_identity`: 0.5-2ns (register operation)

**If higher than expected:**
- Check for debug mode (should be release)
- Ensure inlining is working (`#[inline(always)]`)
- Verify `black_box` isn't preventing optimization

**Interpretation:**
- Times <1ns are effectively zero-cost
- Times 1-2ns are single CPU instructions
- Concorde should be indistinguishable from raw Rust

### Business Class (10-20ns target)

**What to check:**

```bash
cargo bench --bench transport_classes BusinessClass
```

**Expected results:**
- `i32_to_i64`: 5-15ns (safe widening cast)
- `f32_to_f64`: 5-15ns (safe widening cast)
- `struct_widen`: 10-25ns (multiple field operations)

**If higher than expected:**
- Check if bounds checking is being inserted
- Verify struct layout (padding affects copy speed)
- Look for unnecessary clones

**Interpretation:**
- Business Class = few CPU cycles overhead
- Safe conversions with zero data loss
- Should be close to raw casts

### Economy (50-100ns target)

**What to check:**

```bash
cargo bench --bench transport_classes Economy
```

**Expected results:**
- `vec_i32_to_i64/10`: 50-100ns (small allocation)
- `vec_i32_to_i64/100`: 200-500ns (larger allocation)
- `string_clone`: 20-50ns (depends on string length)
- `option_some`: 5-10ns (no allocation)
- `option_none`: 5-10ns (no allocation)

**If higher than expected:**
- Check allocator performance (`jemalloc` vs system)
- Verify iterator is being optimized
- Look for unnecessary intermediate allocations

**Interpretation:**
- Economy = dominated by allocation cost
- Scales with data size
- Option operations should be cheap (no alloc)
- Vec operations scale linearly with size

### Wheelbarrow (100-1000ns target)

**What to check:**

```bash
cargo bench --bench transport_classes Wheelbarrow
```

**Expected results:**
- `manual_lossy`: 100-300ns (field-by-field conversion)
- `json_roundtrip`: 500-2000ns (full serialization)

**If higher than expected:**
- This is expected for JSON fallback
- Check if `serde_json` is in release mode
- Verify data size isn't excessive

**Interpretation:**
- Wheelbarrow = last resort fallback
- JSON roundtrip is expensive but correct
- Manual conversion is faster but lossy
- Times <1µs are acceptable for fallback path

## Container Operation Patterns

### Vec Operations

```bash
cargo bench --bench container_operations Vec
```

**Scaling expectations:**
- **10 elements**: ~50-100ns
- **100 elements**: ~200-500ns
- **1000 elements**: ~2-5µs
- **10000 elements**: ~20-50µs

**Linear scaling**: Time should be proportional to element count.

**Complexity:**
- `direct_access`: O(1) - constant time
- `element_widen`: O(n) - linear in size
- `complex_clone`: O(n) - linear in size
- `nested_flatten`: O(n*m) - quadratic

### Option Operations

```bash
cargo bench --bench container_operations Option
```

**All should be <10ns:**
- `map_identity_some`: 0-5ns (should optimize to no-op)
- `map_identity_none`: 0-5ns (branch prediction)
- `map_widen_some`: 5-10ns (single cast)
- `unwrap_or_default`: 5-20ns (depends on default cost)

**If >20ns:**
- Check if Option::map is being inlined
- Verify branch prediction is working
- Look for unnecessary clones

### HashMap Operations

```bash
cargo bench --bench container_operations HashMap
```

**Expected:**
- `lookup_present`: 10-30ns (hash + probe)
- `lookup_absent`: 10-30ns (hash + probe + not found)
- `value_widen_100`: 1-3µs (rebuild entire map)
- `to_vec_100`: 2-5µs (allocation + iteration)

**Scaling:**
- Lookups: O(1) average, O(n) worst case
- Conversions: O(n) linear in map size

### Nested Containers

```bash
cargo bench --bench container_operations Nested
```

**Complexity multiplies:**
- `vec_option_filter_100`: 200-500ns (filter + collect)
- `map_option_compact_100`: 1-3µs (filter map + rebuild)
- `vec_map_merge_10x10`: 2-5µs (nested iteration)

**Interpretation:**
- Each nesting level adds overhead
- Filter operations scale with data size
- Nested structures are Economy/Wheelbarrow

## Generated vs Handwritten Comparison

```bash
cargo bench --bench generated_vs_handwritten
```

### Expected Ratios

| Operation | Raw (baseline) | Handwritten | Generated | Target Ratio |
|-----------|----------------|-------------|-----------|--------------|
| Point create | 1-2ns | 3-5ns | 5-10ns | <5x raw |
| Point get_x | 0-1ns | 1-2ns | 2-5ns | <5x raw |
| User create | 20-40ns | 50-100ns | 80-150ns | <4x raw |
| Vec sum (100) | 50-100ns | 60-120ns | 80-150ns | <2x raw |
| JSON roundtrip | 200-500ns | 500-1000ns | 1000-2000ns | <4x raw |

**Interpretation:**
- **Raw**: Theoretical maximum (no safety)
- **Handwritten**: Manual PyO3 FFI (baseline)
- **Generated**: What protocol-squisher produces

**Success criteria:**
- Generated should be ≤2x handwritten
- Generated adds validation overhead
- JSON fallback is 2-4x slower than manual

### Validation Overhead

Generated code includes:
- Null pointer checks
- Range validation
- String validation (email format, etc.)
- Default value handling

**This overhead is intentional** - it provides correctness guarantees.

**If >5x raw:**
- Check if validation can be optimized
- Verify assertions aren't in hot loop
- Look for unnecessary string allocations

## Performance Regression Detection

### Establishing Baselines

```bash
# Save current performance as baseline
./scripts/run-benchmarks.sh --all --baseline main

# After changes, compare
./scripts/run-benchmarks.sh --all --compare main
```

### Acceptable Variance

Due to system noise, allow for:
- **±5%**: Normal variance (ignore)
- **±10%**: Investigate if consistent
- **>20%**: Definite regression/improvement

### Investigating Regressions

If benchmarks show >10% slowdown:

1. **Verify release mode**: `cargo bench` uses release, but check `Cargo.toml`
2. **Check for debug symbols**: `strip = true` in profile
3. **System load**: Close background apps, rerun
4. **CPU throttling**: Check `cpufreq` settings
5. **Allocator**: Try `jemalloc` if using system allocator

### Statistical Significance

Criterion uses Student's t-test:
- **p < 0.05**: Change is real (95% confidence)
- **p > 0.05**: Change may be noise

**Always check p-value** before investigating regressions.

## Real-World Context

### Nanosecond Scale

| Time | What Happens |
|------|--------------|
| 1ns | Single CPU cycle (3GHz CPU) |
| 10ns | L1 cache access |
| 100ns | L2 cache access |
| 1µs | L3 cache access / mutex lock |
| 10µs | System call |
| 100µs | Network round-trip (localhost) |

**Interpretation:**
- <10ns = essentially free
- 10-100ns = cache-level overhead
- 100-1000ns = acceptable for conversion
- >1µs = consider optimization

### Python Context

Python function call overhead: ~100-300ns

**Meaning:**
- Concorde/Business: Faster than Python function call
- Economy: Comparable to Python function call
- Wheelbarrow: 3-10x Python function call

**This is why generated code matters** - it avoids multiple Python→Rust→Python transitions.

## Troubleshooting

### "Times are all near zero"

**Cause**: Optimizer eliminated the benchmark

**Fix:**
- Ensure `black_box()` wraps inputs and outputs
- Check that function isn't `const`
- Verify work is actually being done

### "High variance (>20%)"

**Cause**: System noise or cache effects

**Fix:**
- Close background applications
- Disable CPU frequency scaling
- Increase sample size: `--sample-size 1000`
- Run multiple times and average

### "Results differ from expectations"

**Check:**
1. Release mode enabled (`cargo bench`, not `cargo test`)
2. CPU not throttled (`cpufreq-info`)
3. Allocator choice (jemalloc vs system)
4. Data size matches test case
5. Branch prediction (depends on workload)

### "Outliers detected"

Criterion classifies outliers:
- **Mild**: 1.5 IQR from median (expected, ignore)
- **Severe**: 3.0 IQR from median (investigate)

**Causes:**
- Background processes
- GC pauses (not Rust, but system)
- CPU frequency changes
- Cache effects

**Action:**
- Review HTML report for outlier distribution
- If >10% severe outliers, rerun in isolated environment

## Continuous Monitoring

### Setting Up CI Benchmarks

```yaml
# .github/workflows/benchmarks.yml
name: Performance
on: [push, pull_request]
jobs:
  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Run benchmarks
        run: cargo bench
      - name: Upload results
        uses: actions/upload-artifact@v4
        with:
          name: benchmarks
          path: target/criterion/
```

### Tracking Trends

Use criterion's HTML reports to track performance over time:
- Green = improvement
- Red = regression
- Gray = no significant change

## Summary Checklist

Before releasing, verify:

- [ ] Concorde: All <2ns
- [ ] Business Class: All <20ns
- [ ] Economy: <100ns for small data
- [ ] Wheelbarrow: <1µs for typical cases
- [ ] Generated code ≤2x handwritten
- [ ] No >20% regressions vs baseline
- [ ] p-values >0.05 for "no change" results
- [ ] Outliers <10% of samples
- [ ] HTML reports generated successfully

## Further Reading

- [Criterion User Guide](https://bheisler.github.io/criterion.rs/book/)
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [Benchmarking Best Practices](https://www.youtube.com/watch?v=6_Zvv0nZCZQ)
- [Protocol Squisher Design](./DESIGN.md)
