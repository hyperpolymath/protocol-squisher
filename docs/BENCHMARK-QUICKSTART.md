# Benchmark Quick Start Guide

Get up and running with protocol-squisher benchmarks in 5 minutes.

## TL;DR

```bash
# Run all benchmarks
cargo bench

# View HTML reports
firefox target/criterion/report/index.html

# Or use the convenience script
./scripts/run-benchmarks.sh --all --view
```

## First Time Setup

### Prerequisites

- Rust 1.83+ (for criterion 0.5 features)
- 5-10 minutes for initial compilation
- ~500MB disk space for benchmark artifacts

### Install & Build

```bash
cd protocol-squisher

# Build benchmarks (release mode, ~3 minutes)
cargo bench --no-run

# Run a quick test
cargo bench --bench transport_classes Concorde/i64_identity
```

Expected output:
```
Concorde/i64_identity   time:   [1.2345 ns 1.2678 ns 1.3012 ns]
```

## Running Benchmarks

### Quick Development Check

Run a single fast benchmark to verify changes:

```bash
# Just Concorde (fastest, ~30 seconds)
cargo bench --bench transport_classes Concorde

# Just point operations (fast, ~1 minute)
cargo bench --bench generated_vs_handwritten Point
```

### Full Benchmark Suite

```bash
# All benchmarks (~10-15 minutes)
cargo bench

# Or use the script with options
./scripts/run-benchmarks.sh --all

# Quick mode (faster but less precise)
./scripts/run-benchmarks.sh --all --quick
```

### Individual Suites

```bash
# Transport classes only (~3 minutes)
cargo bench --bench transport_classes

# Container operations (~4 minutes)
cargo bench --bench container_operations

# Generated vs handwritten (~3 minutes)
cargo bench --bench generated_vs_handwritten

# Optimizer comparisons (~2 minutes)
cargo bench --bench optimizer_bench
```

## Viewing Results

### Terminal Output

Criterion prints results after each benchmark:

```
Concorde/i64_identity
                        time:   [1.2345 ns 1.2678 ns 1.3012 ns]
                        Found 3 outliers among 100 measurements (3.00%)
                          2 (2.00%) high mild
                          1 (1.00%) high severe
```

**Key info:**
- **Mean time**: 1.2678 ns (middle value)
- **Range**: 1.2345 to 1.3012 ns (95% confidence)
- **Outliers**: 3% outliers (acceptable if <10%)

### HTML Reports

Much better for analysis:

```bash
# Open main report
firefox target/criterion/report/index.html

# Or specific benchmark
firefox target/criterion/Concorde/report/index.html
```

**HTML reports include:**
- Interactive violin plots
- Statistical analysis
- Outlier detection
- Historical comparison (if multiple runs)

### Script Output

The convenience script provides a summary:

```bash
./scripts/run-benchmarks.sh --all --summary

# Creates: benchmark-reports/summary-TIMESTAMP.txt
```

## Interpreting Results

### Are My Results Good?

Compare against these targets:

| Benchmark Group | Target Time | Your Result | Status |
|-----------------|-------------|-------------|--------|
| Concorde | 1-2ns | ? | ✓/✗ |
| Business Class | 10-20ns | ? | ✓/✗ |
| Economy | 50-100ns | ? | ✓/✗ |
| Wheelbarrow | 100-1000ns | ? | ✓/✗ |

**Quick check:**
```bash
# Grep for Concorde results
cargo bench --bench transport_classes Concorde 2>&1 | grep "time:"

# Compare against 2ns target
```

### Common Results

**Concorde** (zero-copy):
```
i64_identity:  1.2 ns ✓ EXCELLENT
str_borrow:    1.5 ns ✓ EXCELLENT
f64_identity:  0.9 ns ✓ EXCELLENT (may be optimized away)
```

**Business Class** (safe widening):
```
i32_to_i64:    8.7 ns ✓ EXCELLENT
f32_to_f64:    9.2 ns ✓ EXCELLENT
struct_widen: 15.3 ns ✓ GOOD
```

**Economy** (allocation):
```
vec_i32_to_i64/10:   67 ns ✓ GOOD
string_clone:        42 ns ✓ GOOD
option_some:          7 ns ✓ EXCELLENT
```

**Wheelbarrow** (JSON):
```
manual_lossy:    234 ns ✓ GOOD
json_roundtrip: 1543 ns ✓ ACCEPTABLE
```

### When Results Are Unexpected

**If times are 10x higher:**
1. Check for debug mode: `cargo bench` (not `cargo test`)
2. Verify optimizer is running: `cat Cargo.toml | grep opt-level`
3. Close background apps and rerun

**If times are inconsistent:**
1. Check for high variance in output (>20%)
2. Disable CPU frequency scaling: `sudo cpupower frequency-set -g performance`
3. Run on idle system

**If comparisons show regression:**
1. Look for "Performance has regressed" in output
2. Check p-value (p < 0.05 = significant)
3. Compare against baseline (see below)

## Establishing Baselines

Track performance over time:

```bash
# Before making changes
./scripts/run-benchmarks.sh --all --baseline before

# After making changes
./scripts/run-benchmarks.sh --all --compare before
```

Criterion will show comparisons:
```
Concorde/i64_identity
                        time:   [1.2345 ns 1.2678 ns 1.3012 ns]
                        change: [-5.12% -2.35% +0.89%] (p = 0.42 > 0.05)
                        No change in performance detected.
```

**Change interpretation:**
- `-5.12%` to `+0.89%`: Range of change (lower bound to upper bound)
- `-2.35%`: Mean change (negative = improvement)
- `p = 0.42`: Not statistically significant (would need p < 0.05)

## Continuous Integration

### Basic CI Setup

Add to `.github/workflows/benchmarks.yml`:

```yaml
name: Benchmarks
on: [push, pull_request]
jobs:
  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - run: cargo bench --no-fail-fast
      - uses: actions/upload-artifact@v4
        with:
          name: benchmark-results
          path: target/criterion/
```

### PR Comments

For automated PR feedback, use [criterion-compare-action](https://github.com/boa-dev/criterion-compare-action).

## Troubleshooting

### "Benchmarks take too long"

Use quick mode:
```bash
./scripts/run-benchmarks.sh --quick --transport
```

Or reduce sample size:
```bash
cargo bench -- --sample-size 10
```

### "Cannot find firefox"

Manually open reports:
```bash
ls target/criterion/*/report/index.html
```

Or use your browser:
```bash
chromium target/criterion/report/index.html
```

### "Results are noisy"

1. Close background applications
2. Disable CPU frequency scaling
3. Increase sample size: `--sample-size 1000`
4. Run multiple times and average

### "Build fails"

Check Rust version:
```bash
rustc --version  # Should be 1.83+
```

Update if needed:
```bash
rustup update stable
```

## Next Steps

- **Full guide**: See [benches/README.md](../benches/README.md)
- **Interpretation**: See [BENCHMARK-RESULTS.md](./BENCHMARK-RESULTS.md)
- **Adding benchmarks**: See [benches/README.md#benchmark-development](../benches/README.md#benchmark-development)

## Cheat Sheet

```bash
# Quick test (30 seconds)
cargo bench --bench transport_classes Concorde

# Full run (10-15 minutes)
cargo bench

# With baseline comparison
./scripts/run-benchmarks.sh --all --baseline main
./scripts/run-benchmarks.sh --all --compare main

# View results
firefox target/criterion/report/index.html

# Check specific result
cargo bench --bench transport_classes Concorde/i64_identity 2>&1 | grep time
```

## Common Issues

| Problem | Solution |
|---------|----------|
| "Too slow" | Use `--quick` flag |
| "Build error" | Update Rust: `rustup update` |
| "Can't find reports" | Check `target/criterion/report/` |
| "High variance" | Close apps, disable freq scaling |
| "Regression detected" | Check p-value, rerun to confirm |

## Support

For issues:
1. Check [BENCHMARK-RESULTS.md](./BENCHMARK-RESULTS.md) for detailed interpretation
2. Review [benches/README.md](../benches/README.md) for development guide
3. Open an issue with benchmark output

---

**Ready to benchmark? Start with:**
```bash
cargo bench --bench transport_classes Concorde
```
