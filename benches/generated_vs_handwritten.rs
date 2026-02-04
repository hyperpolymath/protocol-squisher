// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>

//! Compare generated code performance vs hand-written FFI
//!
//! This benchmark simulates:
//! - Generated adapter code (what protocol-squisher produces)
//! - Hand-written PyO3 FFI code (baseline)
//! - Raw Rust functions (theoretical maximum)

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use serde::{Deserialize, Serialize};

// ============================================================================
// Test Structures
// ============================================================================

#[derive(Clone, Debug)]
#[allow(dead_code)]
struct Point {
    x: i64,
    y: i64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct User {
    id: u64,
    name: String,
    email: String,
    age: u32,
    active: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct ApiResponse {
    status: u32,
    message: String,
    data: Vec<User>,
    timestamp: i64,
}

// ============================================================================
// Raw Rust (theoretical maximum)
// ============================================================================

#[inline]
fn raw_point_create(x: i64, y: i64) -> Point {
    Point { x, y }
}

#[inline]
fn raw_point_get_x(p: &Point) -> i64 {
    p.x
}

fn raw_user_create(id: u64, name: String, email: String, age: u32, active: bool) -> User {
    User {
        id,
        name,
        email,
        age,
        active,
    }
}

fn raw_user_get_name(u: &User) -> &str {
    &u.name
}

// ============================================================================
// Hand-written FFI (baseline for comparison)
// ============================================================================

/// Simulates PyO3 conversion overhead
fn handwritten_point_create(x: i64, y: i64) -> Point {
    // Simulate argument extraction overhead
    let _arg_check = (x, y);
    Point { x, y }
}

fn handwritten_point_get_x(p: &Point) -> i64 {
    // Simulate Python object creation overhead
    let result = p.x;
    // In real PyO3: py.eval(), GIL acquisition, etc.
    result
}

fn handwritten_user_create(
    id: u64,
    name: String,
    email: String,
    age: u32,
    active: bool,
) -> User {
    // Simulate string conversion overhead
    let _name_check = name.len();
    let _email_check = email.len();
    User {
        id,
        name,
        email,
        age,
        active,
    }
}

fn handwritten_user_get_name(u: &User) -> String {
    // Simulate PyString creation
    u.name.clone()
}

// ============================================================================
// Generated Code (what protocol-squisher produces)
// ============================================================================

/// Generated adapter with type checking
fn generated_point_create(x: i64, y: i64) -> Point {
    // Runtime type validation (what generated code adds)
    assert!(x.abs() < i64::MAX);
    assert!(y.abs() < i64::MAX);
    Point { x, y }
}

fn generated_point_get_x(p: &Point) -> i64 {
    // Generated adapters include bounds checks
    assert!(!std::ptr::eq(p, std::ptr::null()));
    p.x
}

fn generated_user_create(
    id: u64,
    name: String,
    email: String,
    age: u32,
    active: bool,
) -> User {
    // Generated code includes validation
    assert!(!name.is_empty(), "name must not be empty");
    assert!(email.contains('@'), "email must be valid");
    assert!(age < 150, "age must be realistic");

    User {
        id,
        name,
        email,
        age,
        active,
    }
}

fn generated_user_get_name(u: &User) -> String {
    // Generated code adds defensive cloning
    u.name.clone()
}

// ============================================================================
// Complex Type Operations
// ============================================================================

/// Raw: Direct Vec access
fn raw_vec_sum(vec: &Vec<i64>) -> i64 {
    vec.iter().sum()
}

/// Handwritten: With iterator overhead
fn handwritten_vec_sum(vec: &Vec<i64>) -> i64 {
    let mut sum = 0;
    for &item in vec.iter() {
        sum += item;
    }
    sum
}

/// Generated: With validation
fn generated_vec_sum(vec: &Vec<i64>) -> i64 {
    assert!(!vec.is_empty(), "vec must not be empty");
    vec.iter().sum()
}

/// Serialize/deserialize comparison
fn raw_serialize_deserialize(response: &ApiResponse) -> ApiResponse {
    // Simulates in-memory conversion (no serialization)
    response.clone()
}

fn handwritten_serialize_deserialize(response: &ApiResponse) -> ApiResponse {
    // Simulates manual field-by-field conversion
    ApiResponse {
        status: response.status,
        message: response.message.clone(),
        data: response.data.clone(),
        timestamp: response.timestamp,
    }
}

fn generated_serialize_deserialize(response: &ApiResponse) -> ApiResponse {
    // What protocol-squisher generates: JSON fallback
    let json = serde_json::to_string(response).unwrap();
    serde_json::from_str(&json).unwrap()
}

// ============================================================================
// Benchmarks
// ============================================================================

fn bench_point_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("Point");

    // Creation
    group.bench_function("raw_create", |b| {
        b.iter(|| {
            let p = raw_point_create(black_box(10), black_box(20));
            black_box(p)
        })
    });

    group.bench_function("handwritten_create", |b| {
        b.iter(|| {
            let p = handwritten_point_create(black_box(10), black_box(20));
            black_box(p)
        })
    });

    group.bench_function("generated_create", |b| {
        b.iter(|| {
            let p = generated_point_create(black_box(10), black_box(20));
            black_box(p)
        })
    });

    // Field access
    let point = Point { x: 42, y: 99 };

    group.bench_function("raw_get_x", |b| {
        b.iter(|| {
            let x = raw_point_get_x(black_box(&point));
            black_box(x)
        })
    });

    group.bench_function("handwritten_get_x", |b| {
        b.iter(|| {
            let x = handwritten_point_get_x(black_box(&point));
            black_box(x)
        })
    });

    group.bench_function("generated_get_x", |b| {
        b.iter(|| {
            let x = generated_point_get_x(black_box(&point));
            black_box(x)
        })
    });

    group.finish();
}

fn bench_user_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("User");

    let name = String::from("Alice");
    let email = String::from("alice@example.com");

    // Creation
    group.bench_function("raw_create", |b| {
        b.iter(|| {
            let u = raw_user_create(
                black_box(1),
                black_box(name.clone()),
                black_box(email.clone()),
                black_box(30),
                black_box(true),
            );
            black_box(u)
        })
    });

    group.bench_function("handwritten_create", |b| {
        b.iter(|| {
            let u = handwritten_user_create(
                black_box(1),
                black_box(name.clone()),
                black_box(email.clone()),
                black_box(30),
                black_box(true),
            );
            black_box(u)
        })
    });

    group.bench_function("generated_create", |b| {
        b.iter(|| {
            let u = generated_user_create(
                black_box(1),
                black_box(name.clone()),
                black_box(email.clone()),
                black_box(30),
                black_box(true),
            );
            black_box(u)
        })
    });

    // Field access
    let user = User {
        id: 1,
        name: String::from("Alice"),
        email: String::from("alice@example.com"),
        age: 30,
        active: true,
    };

    group.bench_function("raw_get_name", |b| {
        b.iter(|| {
            let name = raw_user_get_name(black_box(&user));
            black_box(name)
        })
    });

    group.bench_function("handwritten_get_name", |b| {
        b.iter(|| {
            let name = handwritten_user_get_name(black_box(&user));
            black_box(name)
        })
    });

    group.bench_function("generated_get_name", |b| {
        b.iter(|| {
            let name = generated_user_get_name(black_box(&user));
            black_box(name)
        })
    });

    group.finish();
}

fn bench_vec_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("Vec");

    for size in [10, 100, 1000].iter() {
        let vec: Vec<i64> = (0..*size).collect();

        group.bench_with_input(BenchmarkId::new("raw_sum", size), &vec, |b, vec| {
            b.iter(|| {
                let sum = raw_vec_sum(black_box(vec));
                black_box(sum)
            })
        });

        group.bench_with_input(
            BenchmarkId::new("handwritten_sum", size),
            &vec,
            |b, vec| {
                b.iter(|| {
                    let sum = handwritten_vec_sum(black_box(vec));
                    black_box(sum)
                })
            },
        );

        group.bench_with_input(BenchmarkId::new("generated_sum", size), &vec, |b, vec| {
            b.iter(|| {
                let sum = generated_vec_sum(black_box(vec));
                black_box(sum)
            })
        });
    }

    group.finish();
}

fn bench_complex_serialization(c: &mut Criterion) {
    let mut group = c.benchmark_group("ApiResponse");

    let response = ApiResponse {
        status: 200,
        message: String::from("Success"),
        data: vec![
            User {
                id: 1,
                name: String::from("Alice"),
                email: String::from("alice@example.com"),
                age: 30,
                active: true,
            },
            User {
                id: 2,
                name: String::from("Bob"),
                email: String::from("bob@example.com"),
                age: 25,
                active: false,
            },
        ],
        timestamp: 1234567890,
    };

    group.bench_function("raw_clone", |b| {
        b.iter(|| {
            let result = raw_serialize_deserialize(black_box(&response));
            black_box(result)
        })
    });

    group.bench_function("handwritten_convert", |b| {
        b.iter(|| {
            let result = handwritten_serialize_deserialize(black_box(&response));
            black_box(result)
        })
    });

    group.bench_function("generated_json_fallback", |b| {
        b.iter(|| {
            let result = generated_serialize_deserialize(black_box(&response));
            black_box(result)
        })
    });

    group.finish();
}

criterion_group!(
    comparison_benches,
    bench_point_operations,
    bench_user_operations,
    bench_vec_operations,
    bench_complex_serialization
);

criterion_main!(comparison_benches);
