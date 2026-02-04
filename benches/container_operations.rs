// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>

//! Benchmark container operations across transport classes
//!
//! Tests realistic patterns:
//! - Vec<T> conversions at various sizes
//! - Option<T> handling patterns
//! - HashMap lookups and conversions
//! - Nested containers (Vec<Option<T>>, etc.)

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use std::collections::HashMap;

// ============================================================================
// Vec Operations
// ============================================================================

/// Direct Vec access (Concorde baseline)
fn vec_direct_access(vec: &Vec<i64>, index: usize) -> i64 {
    vec[index]
}

/// Vec element conversion (Business Class)
fn vec_element_widen(vec: &Vec<i32>) -> Vec<i64> {
    vec.iter().map(|&x| x as i64).collect()
}

/// Vec with complex type (Economy)
#[derive(Clone)]
#[allow(dead_code)]
struct ComplexItem {
    id: i64,
    value: String,
}

fn vec_complex_clone(vec: &Vec<ComplexItem>) -> Vec<ComplexItem> {
    vec.clone()
}

/// Nested Vec (Economy to Wheelbarrow boundary)
fn vec_nested_flatten(vec: &Vec<Vec<i32>>) -> Vec<i32> {
    vec.iter().flat_map(|inner| inner.iter()).copied().collect()
}

// ============================================================================
// Option Operations
// ============================================================================

/// Option::map (zero-cost if optimized)
fn option_map_identity(opt: Option<i64>) -> Option<i64> {
    opt.map(|x| x)
}

/// Option::map with conversion (Business Class)
fn option_map_widen(opt: Option<i32>) -> Option<i64> {
    opt.map(|x| x as i64)
}

/// Option unwrap with default (Economy)
fn option_unwrap_or_default(opt: Option<String>) -> String {
    opt.unwrap_or_default()
}

/// Option to Result (Economy)
fn option_to_result(opt: Option<i64>) -> Result<i64, &'static str> {
    opt.ok_or("value not present")
}

/// Nested Option (Economy)
fn option_nested_flatten(opt: Option<Option<i64>>) -> Option<i64> {
    opt.flatten()
}

// ============================================================================
// HashMap Operations
// ============================================================================

/// Direct HashMap lookup (Concorde)
fn map_lookup(map: &HashMap<String, i64>, key: &str) -> Option<i64> {
    map.get(key).copied()
}

/// HashMap value conversion (Business Class)
fn map_value_widen(map: &HashMap<String, i32>) -> HashMap<String, i64> {
    map.iter().map(|(k, &v)| (k.clone(), v as i64)).collect()
}

/// HashMap to Vec (Economy - ordering lost)
fn map_to_vec(map: &HashMap<String, i64>) -> Vec<(String, i64)> {
    map.iter().map(|(k, v)| (k.clone(), *v)).collect()
}

/// HashMap with complex values (Economy)
fn map_complex_clone(map: &HashMap<String, ComplexItem>) -> HashMap<String, ComplexItem> {
    map.clone()
}

// ============================================================================
// Nested Container Operations
// ============================================================================

/// Vec<Option<T>> - common pattern
fn vec_option_filter_map(vec: &Vec<Option<i64>>) -> Vec<i64> {
    vec.iter().filter_map(|&x| x).collect()
}

/// Option<Vec<T>> - flatten
fn option_vec_unwrap(opt: Option<Vec<i64>>) -> Vec<i64> {
    opt.unwrap_or_default()
}

/// HashMap<String, Option<T>> - compact
fn map_option_compact(map: &HashMap<String, Option<i64>>) -> HashMap<String, i64> {
    map.iter()
        .filter_map(|(k, &v)| v.map(|val| (k.clone(), val)))
        .collect()
}

/// Vec<HashMap<String, T>> - complex nesting
fn vec_map_merge(vec: &Vec<HashMap<String, i64>>) -> HashMap<String, i64> {
    let mut result = HashMap::new();
    for map in vec {
        result.extend(map.iter().map(|(k, v)| (k.clone(), *v)));
    }
    result
}

// ============================================================================
// Benchmarks
// ============================================================================

fn bench_vec_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("Vec");

    // Direct access
    let vec: Vec<i64> = (0..1000).collect();
    group.bench_function("direct_access", |b| {
        b.iter(|| {
            let result = vec_direct_access(black_box(&vec), black_box(500));
            black_box(result)
        })
    });

    // Element widening at different sizes
    for size in [10, 100, 1000, 10000].iter() {
        let vec: Vec<i32> = (0..*size).collect();
        group.bench_with_input(BenchmarkId::new("element_widen", size), &vec, |b, vec| {
            b.iter(|| {
                let result = vec_element_widen(black_box(vec));
                black_box(result)
            })
        });
    }

    // Complex type clone
    let complex_vec: Vec<ComplexItem> = (0..100)
        .map(|i| ComplexItem {
            id: i,
            value: format!("item_{}", i),
        })
        .collect();
    group.bench_function("complex_clone_100", |b| {
        b.iter(|| {
            let result = vec_complex_clone(black_box(&complex_vec));
            black_box(result)
        })
    });

    // Nested Vec flatten
    let nested: Vec<Vec<i32>> = (0..10).map(|_| (0..10).collect()).collect();
    group.bench_function("nested_flatten", |b| {
        b.iter(|| {
            let result = vec_nested_flatten(black_box(&nested));
            black_box(result)
        })
    });

    group.finish();
}

fn bench_option_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("Option");

    // Map identity
    group.bench_function("map_identity_some", |b| {
        b.iter(|| {
            let result = option_map_identity(black_box(Some(42)));
            black_box(result)
        })
    });

    group.bench_function("map_identity_none", |b| {
        b.iter(|| {
            let result = option_map_identity(black_box(None));
            black_box(result)
        })
    });

    // Map with conversion
    group.bench_function("map_widen_some", |b| {
        b.iter(|| {
            let result = option_map_widen(black_box(Some(42)));
            black_box(result)
        })
    });

    // Unwrap with default
    group.bench_function("unwrap_or_default_some", |b| {
        b.iter(|| {
            let result = option_unwrap_or_default(black_box(Some(String::from("test"))));
            black_box(result)
        })
    });

    group.bench_function("unwrap_or_default_none", |b| {
        b.iter(|| {
            let result = option_unwrap_or_default(black_box(None));
            black_box(result)
        })
    });

    // To Result
    group.bench_function("to_result_some", |b| {
        b.iter(|| {
            let result = option_to_result(black_box(Some(42)));
            black_box(result)
        })
    });

    // Nested flatten
    group.bench_function("nested_flatten_some_some", |b| {
        b.iter(|| {
            let result = option_nested_flatten(black_box(Some(Some(42))));
            black_box(result)
        })
    });

    group.finish();
}

fn bench_hashmap_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("HashMap");

    // Setup test data
    let mut map_i64: HashMap<String, i64> = HashMap::new();
    let mut map_i32: HashMap<String, i32> = HashMap::new();
    for i in 0..100 {
        let key = format!("key_{}", i);
        map_i64.insert(key.clone(), i);
        map_i32.insert(key, i as i32);
    }

    // Direct lookup
    group.bench_function("lookup_present", |b| {
        b.iter(|| {
            let result = map_lookup(black_box(&map_i64), black_box("key_50"));
            black_box(result)
        })
    });

    group.bench_function("lookup_absent", |b| {
        b.iter(|| {
            let result = map_lookup(black_box(&map_i64), black_box("key_missing"));
            black_box(result)
        })
    });

    // Value widening
    group.bench_function("value_widen_100", |b| {
        b.iter(|| {
            let result = map_value_widen(black_box(&map_i32));
            black_box(result)
        })
    });

    // To Vec
    group.bench_function("to_vec_100", |b| {
        b.iter(|| {
            let result = map_to_vec(black_box(&map_i64));
            black_box(result)
        })
    });

    // Complex values
    let mut map_complex: HashMap<String, ComplexItem> = HashMap::new();
    for i in 0..100 {
        map_complex.insert(
            format!("key_{}", i),
            ComplexItem {
                id: i,
                value: format!("value_{}", i),
            },
        );
    }
    group.bench_function("complex_clone_100", |b| {
        b.iter(|| {
            let result = map_complex_clone(black_box(&map_complex));
            black_box(result)
        })
    });

    group.finish();
}

fn bench_nested_containers(c: &mut Criterion) {
    let mut group = c.benchmark_group("Nested");

    // Vec<Option<T>>
    let vec_opt: Vec<Option<i64>> = (0..100)
        .map(|i| if i % 2 == 0 { Some(i) } else { None })
        .collect();
    group.bench_function("vec_option_filter_100", |b| {
        b.iter(|| {
            let result = vec_option_filter_map(black_box(&vec_opt));
            black_box(result)
        })
    });

    // Option<Vec<T>>
    let opt_vec = Some((0..100).collect::<Vec<i64>>());
    group.bench_function("option_vec_unwrap_some", |b| {
        b.iter(|| {
            let result = option_vec_unwrap(black_box(opt_vec.clone()));
            black_box(result)
        })
    });

    // HashMap<String, Option<T>>
    let mut map_opt: HashMap<String, Option<i64>> = HashMap::new();
    for i in 0..100 {
        map_opt.insert(
            format!("key_{}", i),
            if i % 2 == 0 { Some(i) } else { None },
        );
    }
    group.bench_function("map_option_compact_100", |b| {
        b.iter(|| {
            let result = map_option_compact(black_box(&map_opt));
            black_box(result)
        })
    });

    // Vec<HashMap<String, T>>
    let vec_map: Vec<HashMap<String, i64>> = (0..10)
        .map(|i| {
            let mut m = HashMap::new();
            for j in 0..10 {
                m.insert(format!("key_{}_{}", i, j), j);
            }
            m
        })
        .collect();
    group.bench_function("vec_map_merge_10x10", |b| {
        b.iter(|| {
            let result = vec_map_merge(black_box(&vec_map));
            black_box(result)
        })
    });

    group.finish();
}

criterion_group!(
    container_benches,
    bench_vec_operations,
    bench_option_operations,
    bench_hashmap_operations,
    bench_nested_containers
);

criterion_main!(container_benches);
