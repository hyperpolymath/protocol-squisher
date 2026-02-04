# Protocol Squisher Benchmarks

Comprehensive performance benchmarking suite to validate transport class overhead claims and compare generated code against baselines.

## Benchmark Suites

### 1. Transport Classes (`transport_classes.rs`)

Validates the performance claims for all four transport classes:

- **Concorde** (1-2ns target): Zero-copy operations
  - i64 identity
  - String borrowing (no allocation)
  - f64 pass-through

- **Business Class** (10-20ns target): Safe widening conversions
  - i32 → i64 (safe widening)
  - f32 → f64 (safe widening)
  - u32 → u64 (safe widening)
  - Struct field widening

- **Economy** (50-100ns target): Moderate overhead with allocation
  - Vec<i32> → Vec<i64> conversion
  - Option<T> unwrapping
  - String cloning
  - Flattening optional fields

- **Wheelbarrow** (100-1000ns target): JSON serialization fallback
  - Manual lossy conversions
  - Full JSON roundtrip (serialize + deserialize)

### 2. Container Operations (`container_operations.rs`)

Tests realistic container patterns across transport classes:

**Vec Operations:**
- Direct element access (Concorde baseline)
- Element type widening at various sizes (10, 100, 1K, 10K)
- Complex struct cloning
- Nested Vec flattening

**Option Operations:**
- Map identity (should optimize to zero-cost)
- Map with conversion
- Unwrap with default
- Option → Result conversion
- Nested Option flattening

**HashMap Operations:**
- Direct lookups (present/absent)
- Value type widening
- HashMap → Vec conversion (ordering loss)
- Complex value cloning

**Nested Containers:**
- Vec<Option<T>> filtering
- Option<Vec<T>> unwrapping
- HashMap<K, Option<V>> compaction
- Vec<HashMap<K, V>> merging

### 3. Generated vs Handwritten (`generated_vs_handwritten.rs`)

Compares three implementation approaches:

- **Raw Rust**: Theoretical maximum (inline, no overhead)
- **Handwritten FFI**: PyO3 baseline (manual FFI code)
- **Generated Code**: What protocol-squisher produces

**Test Cases:**
- Point struct (create, field access)
- User struct (create with validation, field access)
- Vec operations (sum with different sizes)
- Complex API response serialization

This validates that generated code is competitive with hand-written FFI while adding safety checks.

### 4. Optimizer Bench (`optimizer_bench.rs`)

Original benchmarks comparing optimized conversions vs JSON fallback (already present).

## Running Benchmarks

### Run All Benchmarks

```bash
cargo bench
```

This generates HTML reports in `target/criterion/`.

### Run Specific Suite

```bash
# Transport classes only
cargo bench --bench transport_classes

# Container operations only
cargo bench --bench container_operations

# Generated vs handwritten comparison
cargo bench --bench generated_vs_handwritten

# Original optimizer benchmarks
cargo bench --bench optimizer_bench
```

### Run Specific Test

```bash
# Run only Concorde benchmarks
cargo bench --bench transport_classes Concorde

# Run only Vec operations
cargo bench --bench container_operations Vec

# Run only Point operations
cargo bench --bench generated_vs_handwritten Point
```

### View HTML Reports

After running benchmarks, open the HTML reports:

```bash
# Open the main criterion report index
firefox target/criterion/report/index.html

# Or specific benchmark group
firefox target/criterion/Concorde/report/index.html
```

## Performance Targets

Based on theoretical overhead analysis:

| Transport Class | Target Latency | Typical Use Case |
|-----------------|----------------|------------------|
| **Concorde** | 1-2ns | Identical types, zero-copy |
| **Business Class** | 10-20ns | Safe widening (i32→i64, f32→f64) |
| **Economy** | 50-100ns | Allocation required (Vec, String) |
| **Wheelbarrow** | 100-1000ns | JSON serialization fallback |

**Note:** Actual performance depends on:
- Data size (Vec/HashMap element count)
- String lengths
- Memory allocator efficiency
- CPU cache effects

## Interpreting Results

### Criterion Output

Criterion provides detailed statistics:

```
Concorde/i64_identity  time:   [1.2345 ns 1.2678 ns 1.3012 ns]
                       change: [-5.1234% -2.3456% +0.8901%] (p = 0.42 > 0.05)
                       No change in performance detected.
```

- **time**: [lower_bound mean upper_bound] in nanoseconds
- **change**: Percentage change vs previous run
- **p-value**: Statistical significance (< 0.05 = significant change)

### HTML Reports

The HTML reports include:
- **Violin plots**: Distribution of measurement samples
- **Line charts**: Performance over time (if multiple runs)
- **PDF estimates**: Probability density of the measurement
- **Comparison**: Side-by-side comparison between runs

### Expected Results

**Concorde** should show:
- Sub-nanosecond for i64 identity (may be optimized away)
- 1-2ns for str borrowing
- Similar for f64 pass-through

**Business Class** should show:
- 5-10ns for scalar widening (i32→i64, f32→f64)
- 10-20ns for struct field widening

**Economy** should show:
- 50-100ns for small Vec conversions (10 elements)
- 500-1000ns for larger Vec conversions (1000 elements)
- 20-50ns for String clone
- 10-20ns for Option operations

**Wheelbarrow** should show:
- 500-1000ns for manual lossy conversions
- 1000-5000ns for JSON roundtrip (depends on data size)

### Performance Regression

If benchmarks show significant regression:

1. **Check for debug builds**: Benchmarks should run in release mode
2. **System load**: Close other applications
3. **CPU throttling**: Check `cpufreq` settings
4. **Outliers**: Criterion automatically detects and reports outliers

## CI Integration

Benchmarks can be integrated into CI for regression detection:

```yaml
# .github/workflows/benchmarks.yml
name: Benchmarks
on:
  push:
    branches: [main]
  pull_request:
jobs:
  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - name: Run benchmarks
        run: cargo bench --no-fail-fast
      - name: Upload results
        uses: actions/upload-artifact@v4
        with:
          name: benchmark-results
          path: target/criterion/
```

## Benchmark Development

### Adding New Benchmarks

1. Create new `.rs` file in `benches/`
2. Add `[[bench]]` entry in `Cargo.toml`
3. Follow criterion patterns:

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn my_benchmark(c: &mut Criterion) {
    c.bench_function("my_test", |b| {
        b.iter(|| {
            let result = my_function(black_box(input));
            black_box(result)
        })
    });
}

criterion_group!(benches, my_benchmark);
criterion_main!(benches);
```

### Using `black_box`

Always wrap inputs and outputs with `black_box()` to prevent compiler optimizations:

```rust
// WRONG: Compiler may optimize away the entire computation
b.iter(|| my_function(42));

// CORRECT: Forces the computation to actually run
b.iter(|| {
    let result = my_function(black_box(42));
    black_box(result)
});
```

### Parameterized Benchmarks

Use `BenchmarkId` for size/parameter variations:

```rust
use criterion::BenchmarkId;

let mut group = c.benchmark_group("vec_conversion");
for size in [10, 100, 1000].iter() {
    let vec: Vec<i32> = (0..*size).collect();
    group.bench_with_input(
        BenchmarkId::new("conversion", size),
        &vec,
        |b, vec| {
            b.iter(|| convert(black_box(vec)))
        },
    );
}
group.finish();
```

## Advanced Options

### Criterion Configuration

Customize in `Cargo.toml`:

```toml
[dev-dependencies]
criterion = {
    version = "0.5",
    features = [
        "html_reports",  # Enable HTML report generation
        "csv_output",    # Export to CSV
    ]
}
```

### Sampling Configuration

Control measurement precision:

```rust
use criterion::{Criterion, SamplingMode};

fn my_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("my_group");
    group.sampling_mode(SamplingMode::Flat); // Linear sampling
    group.sample_size(1000); // Number of samples
    group.measurement_time(std::time::Duration::from_secs(10));
    // ... benchmarks
    group.finish();
}
```

### Throughput Measurement

Measure operations per second:

```rust
use criterion::Throughput;

group.throughput(Throughput::Elements(vec.len() as u64));
```

## Troubleshooting

### "Benchmark took too long"

Increase timeout:

```rust
group.measurement_time(std::time::Duration::from_secs(60));
```

### High Variance

Reduce system noise:
- Close background applications
- Disable CPU frequency scaling
- Run multiple times and average

### Outliers

Criterion automatically detects outliers. Check HTML reports for:
- **Mild outliers**: May indicate background interference
- **Severe outliers**: Check for bugs or system issues

## References

- [Criterion.rs Documentation](https://bheisler.github.io/criterion.rs/book/)
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [Protocol Squisher Design Doc](../docs/DESIGN.md)
