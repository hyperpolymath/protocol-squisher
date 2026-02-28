// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>

//! Benchmark all four transport classes to validate overhead claims
//!
//! Expected performance targets:
//! - Concorde: 1-2ns (zero-copy, pointer passing)
//! - Business: 10-20ns (safe widening, no allocation)
//! - Economy: 50-100ns (allocation, safe conversion)
//! - Wheelbarrow: 100-1000ns (JSON serialization fallback)

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use serde::{Deserialize, Serialize};
use std::hint::black_box;

// ============================================================================
// Concorde: Zero-copy, full fidelity
// ============================================================================

/// Identical types - pointer passing only
#[derive(Clone, Copy)]
#[allow(dead_code)]
struct ConcordeI64 {
    value: i64,
}

#[inline(always)]
fn concorde_i64_identity(input: &ConcordeI64) -> ConcordeI64 {
    *input // Just copy the value
}

/// String reference - true zero-copy via borrowing
#[inline(always)]
fn concorde_str_borrow(input: &str) -> &str {
    input // No allocation, just reference
}

/// f64 identity - native type
#[inline(always)]
fn concorde_f64_identity(input: f64) -> f64 {
    input
}

// ============================================================================
// Business Class: Minor overhead, safe widening
// ============================================================================

/// Safe widening conversions - no data loss possible
#[inline]
fn business_i32_to_i64(input: i32) -> i64 {
    input as i64 // Safe widening
}

#[inline]
fn business_f32_to_f64(input: f32) -> f64 {
    input as f64 // Safe widening
}

#[inline]
fn business_u32_to_u64(input: u32) -> u64 {
    input as u64
}

/// Struct with field widening
#[derive(Clone)]
struct BusinessSource {
    id: i32,
    value: f32,
}

#[derive(Clone)]
#[allow(dead_code)]
struct BusinessTarget {
    id: i64,
    value: f64,
}

#[inline]
fn business_struct_widen(input: &BusinessSource) -> BusinessTarget {
    BusinessTarget {
        id: input.id as i64,
        value: input.value as f64,
    }
}

// ============================================================================
// Economy: Moderate overhead, documented losses
// ============================================================================

/// Vec conversion with allocation
fn economy_vec_i32_to_i64(input: &[i32]) -> Vec<i64> {
    input.iter().map(|&x| x as i64).collect()
}

/// Option handling
fn economy_option_unwrap(input: Option<i64>, default: i64) -> i64 {
    input.unwrap_or(default)
}

/// String cloning (allocation required)
fn economy_string_clone(input: &str) -> String {
    input.to_owned()
}

/// Struct with optional fields
#[derive(Clone)]
#[allow(dead_code)]
struct EconomySource {
    required: i64,
    optional: Option<String>,
}

#[derive(Clone)]
#[allow(dead_code)]
struct EconomyTarget {
    required: i64,
    optional: String,
}

fn economy_flatten_optional(input: &EconomySource) -> EconomyTarget {
    EconomyTarget {
        required: input.required,
        optional: input.optional.clone().unwrap_or_default(),
    }
}

// ============================================================================
// Wheelbarrow: High overhead, JSON fallback
// ============================================================================

#[derive(Serialize, Deserialize, Clone)]
struct WheelbarrowSource {
    id: i64,
    name: String,
    tags: Vec<String>,
}

#[derive(Serialize, Deserialize, Clone)]
struct WheelbarrowTarget {
    id: String, // Type coercion
    name: String,
    tag_count: usize, // Lossy conversion
}

fn wheelbarrow_json_convert(input: &WheelbarrowSource) -> WheelbarrowTarget {
    // Manual lossy conversion (what JSON fallback would do)
    WheelbarrowTarget {
        id: input.id.to_string(),
        name: input.name.clone(),
        tag_count: input.tags.len(),
    }
}

fn wheelbarrow_json_serialize_deserialize(input: &WheelbarrowSource) -> WheelbarrowSource {
    let json = serde_json::to_string(input).unwrap();
    serde_json::from_str(&json).unwrap()
}

// ============================================================================
// Benchmarks
// ============================================================================

fn bench_concorde(c: &mut Criterion) {
    let mut group = c.benchmark_group("Concorde");

    // i64 identity
    let value = ConcordeI64 { value: 42 };
    group.bench_function("i64_identity", |b| {
        b.iter(|| {
            let result = concorde_i64_identity(black_box(&value));
            black_box(result)
        })
    });

    // str borrow
    let s = "hello world";
    group.bench_function("str_borrow", |b| {
        b.iter(|| {
            let result = concorde_str_borrow(black_box(s));
            black_box(result)
        })
    });

    // f64 identity
    group.bench_function("f64_identity", |b| {
        b.iter(|| {
            let result = concorde_f64_identity(black_box(std::f64::consts::PI));
            black_box(result)
        })
    });

    group.finish();
}

fn bench_business_class(c: &mut Criterion) {
    let mut group = c.benchmark_group("BusinessClass");

    // Safe widening conversions
    group.bench_function("i32_to_i64", |b| {
        b.iter(|| {
            let result = business_i32_to_i64(black_box(12345));
            black_box(result)
        })
    });

    group.bench_function("f32_to_f64", |b| {
        b.iter(|| {
            let result = business_f32_to_f64(black_box(std::f32::consts::PI));
            black_box(result)
        })
    });

    group.bench_function("u32_to_u64", |b| {
        b.iter(|| {
            let result = business_u32_to_u64(black_box(99999));
            black_box(result)
        })
    });

    // Struct widening
    let source = BusinessSource {
        id: 42,
        value: std::f32::consts::PI,
    };
    group.bench_function("struct_widen", |b| {
        b.iter(|| {
            let result = business_struct_widen(black_box(&source));
            black_box(result)
        })
    });

    group.finish();
}

fn bench_economy(c: &mut Criterion) {
    let mut group = c.benchmark_group("Economy");

    // Vec conversion at different sizes
    for size in [10, 100, 1000].iter() {
        let vec: Vec<i32> = (0..*size).collect();
        group.bench_with_input(BenchmarkId::new("vec_i32_to_i64", size), &vec, |b, vec| {
            b.iter(|| {
                let result = economy_vec_i32_to_i64(black_box(vec));
                black_box(result)
            })
        });
    }

    // Option handling
    group.bench_function("option_some", |b| {
        b.iter(|| {
            let result = economy_option_unwrap(black_box(Some(42)), 0);
            black_box(result)
        })
    });

    group.bench_function("option_none", |b| {
        b.iter(|| {
            let result = economy_option_unwrap(black_box(None), 99);
            black_box(result)
        })
    });

    // String cloning
    let s = String::from("hello world");
    group.bench_function("string_clone", |b| {
        b.iter(|| {
            let result = economy_string_clone(black_box(&s));
            black_box(result)
        })
    });

    // Flatten optional
    let source = EconomySource {
        required: 42,
        optional: Some(String::from("test")),
    };
    group.bench_function("flatten_optional_some", |b| {
        b.iter(|| {
            let result = economy_flatten_optional(black_box(&source));
            black_box(result)
        })
    });

    let source_none = EconomySource {
        required: 42,
        optional: None,
    };
    group.bench_function("flatten_optional_none", |b| {
        b.iter(|| {
            let result = economy_flatten_optional(black_box(&source_none));
            black_box(result)
        })
    });

    group.finish();
}

fn bench_wheelbarrow(c: &mut Criterion) {
    let mut group = c.benchmark_group("Wheelbarrow");

    let source = WheelbarrowSource {
        id: 123456789,
        name: String::from("test_object"),
        tags: vec![
            String::from("tag1"),
            String::from("tag2"),
            String::from("tag3"),
        ],
    };

    // Manual lossy conversion
    group.bench_function("manual_lossy", |b| {
        b.iter(|| {
            let result = wheelbarrow_json_convert(black_box(&source));
            black_box(result)
        })
    });

    // Full JSON roundtrip (actual fallback path)
    group.bench_function("json_roundtrip", |b| {
        b.iter(|| {
            let result = wheelbarrow_json_serialize_deserialize(black_box(&source));
            black_box(result)
        })
    });

    group.finish();
}

criterion_group!(
    transport_benches,
    bench_concorde,
    bench_business_class,
    bench_economy,
    bench_wheelbarrow
);

criterion_main!(transport_benches);
