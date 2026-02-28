// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Criterion benchmarks comparing optimized conversions vs JSON fallback
//!
//! Run with: cargo bench

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use serde::{Deserialize, Serialize};
use std::hint::black_box;

// === Sample Types ===

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct PointI32 {
    x: i32,
    y: i32,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct PointI64 {
    x: i64,
    y: i64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct UserV1 {
    id: u64,
    name: String,
    email: String,
    age: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct UserV2 {
    id: u64,
    name: String,
    email: String,
    age: u64,
    active: Option<bool>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct LargeStruct {
    field1: String,
    field2: String,
    field3: i64,
    field4: i64,
    field5: f64,
    field6: Vec<i32>,
    field7: Option<String>,
    field8: bool,
}

// === Conversion Functions ===

fn json_convert<S: Serialize, T: for<'de> Deserialize<'de>>(source: &S) -> T {
    let json = serde_json::to_string(source).unwrap();
    serde_json::from_str(&json).unwrap()
}

#[inline]
fn optimized_point_i32_to_i64(source: &PointI32) -> PointI64 {
    PointI64 {
        x: source.x as i64,
        y: source.y as i64,
    }
}

#[inline]
fn optimized_user_v1_to_v2(source: &UserV1) -> UserV2 {
    UserV2 {
        id: source.id,
        name: source.name.clone(),
        email: source.email.clone(),
        age: source.age as u64,
        active: None,
    }
}

// === Benchmarks ===

fn point_conversion(c: &mut Criterion) {
    let point = PointI32 { x: 100, y: 200 };

    let mut group = c.benchmark_group("point_i32_to_i64");

    group.bench_function("json_fallback", |b| {
        b.iter(|| {
            let result: PointI64 = json_convert(black_box(&point));
            black_box(result)
        })
    });

    group.bench_function("optimized", |b| {
        b.iter(|| {
            let result = optimized_point_i32_to_i64(black_box(&point));
            black_box(result)
        })
    });

    group.finish();
}

fn user_conversion(c: &mut Criterion) {
    let user = UserV1 {
        id: 12345,
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
        age: 30,
    };

    let mut group = c.benchmark_group("user_v1_to_v2");

    group.bench_function("json_fallback", |b| {
        b.iter(|| {
            let result: UserV2 = json_convert(black_box(&user));
            black_box(result)
        })
    });

    group.bench_function("optimized", |b| {
        b.iter(|| {
            let result = optimized_user_v1_to_v2(black_box(&user));
            black_box(result)
        })
    });

    group.finish();
}

fn large_struct_conversion(c: &mut Criterion) {
    let large = LargeStruct {
        field1: "hello world".to_string(),
        field2: "foo bar baz".to_string(),
        field3: 1234567890,
        field4: 9876543210,
        field5: std::f64::consts::PI,
        field6: vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        field7: Some("optional value".to_string()),
        field8: true,
    };

    let mut group = c.benchmark_group("large_struct_identity");

    group.bench_function("json_roundtrip", |b| {
        b.iter(|| {
            let result: LargeStruct = json_convert(black_box(&large));
            black_box(result)
        })
    });

    group.bench_function("clone", |b| {
        b.iter(|| {
            let result = black_box(&large).clone();
            black_box(result)
        })
    });

    group.finish();
}

fn vec_conversion(c: &mut Criterion) {
    let mut group = c.benchmark_group("vec_conversion");

    for size in [10, 100, 1000, 10000].iter() {
        let vec: Vec<i32> = (0..*size).collect();

        group.bench_with_input(BenchmarkId::new("json_i32_to_i64", size), &vec, |b, vec| {
            b.iter(|| {
                let result: Vec<i64> = json_convert(black_box(vec));
                black_box(result)
            })
        });

        group.bench_with_input(
            BenchmarkId::new("optimized_i32_to_i64", size),
            &vec,
            |b, vec| {
                b.iter(|| {
                    let result: Vec<i64> = black_box(vec).iter().map(|&x| x as i64).collect();
                    black_box(result)
                })
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    point_conversion,
    user_conversion,
    large_struct_conversion,
    vec_conversion,
);

criterion_main!(benches);
