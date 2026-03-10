// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Criterion benchmarks for the Shape IR comparison engine, information content
//! computation, and morphism classification.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use shape_ir::compare::compare;
use shape_ir::compose::compose;
use shape_ir::information::{classify_morphism, information_content};
use shape_ir::*;

// ---------------------------------------------------------------------------
// Shape construction helpers
// ---------------------------------------------------------------------------

/// A simple 3-field struct: { id: i32, name: String, active: Bool }.
fn simple_struct() -> Shape {
    Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
        ("active", Shape::Atom(AtomKind::Bool)),
    ])
}

/// A wider version: { id: i64, name: String, active: Bool, email: Optional<String> }.
fn wide_struct() -> Shape {
    Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I64)),
        ("name", Shape::Atom(AtomKind::String)),
        ("active", Shape::Atom(AtomKind::Bool)),
        ("email", Shape::optional(Shape::Atom(AtomKind::String))),
    ])
}

/// A 3-variant enum: A(i32) | B(String) | C(Bool).
fn simple_enum() -> Shape {
    Shape::enum_from(vec![
        ("A", Shape::Atom(AtomKind::I32)),
        ("B", Shape::Atom(AtomKind::String)),
        ("C", Shape::Atom(AtomKind::Bool)),
    ])
}

/// A deeply nested struct (10 fields).
fn deep_struct() -> Shape {
    Shape::struct_from(vec![
        ("f0", Shape::Atom(AtomKind::I32)),
        ("f1", Shape::Atom(AtomKind::I64)),
        ("f2", Shape::Atom(AtomKind::F32)),
        ("f3", Shape::Atom(AtomKind::F64)),
        ("f4", Shape::Atom(AtomKind::Bool)),
        ("f5", Shape::Atom(AtomKind::String)),
        ("f6", Shape::Atom(AtomKind::U8)),
        ("f7", Shape::Atom(AtomKind::U16)),
        ("f8", Shape::Atom(AtomKind::U32)),
        ("f9", Shape::Atom(AtomKind::U64)),
    ])
}

/// A recursive list shape: List = Cons(i32, List) | Nil.
fn recursive_list() -> Shape {
    Shape::recursive(
        "List",
        Shape::sum(
            "Cons",
            Shape::product(
                "head",
                Shape::Atom(AtomKind::I32),
                Shape::Ref("List".into()),
            ),
            Shape::Unit,
        ),
    )
}

// ---------------------------------------------------------------------------
// Benchmarks
// ---------------------------------------------------------------------------

fn bench_compare(c: &mut Criterion) {
    let mut group = c.benchmark_group("compare");

    // Identity comparisons (fast path)
    let atom = Shape::Atom(AtomKind::I32);
    group.bench_function("atom_identity", |b| {
        b.iter(|| compare(black_box(&atom), black_box(&atom)))
    });

    let s = simple_struct();
    group.bench_function("struct_3_identity", |b| {
        b.iter(|| compare(black_box(&s), black_box(&s)))
    });

    let ds = deep_struct();
    group.bench_function("struct_10_identity", |b| {
        b.iter(|| compare(black_box(&ds), black_box(&ds)))
    });

    // Widening
    let i32_shape = Shape::Atom(AtomKind::I32);
    let i64_shape = Shape::Atom(AtomKind::I64);
    group.bench_function("atom_widen_i32_i64", |b| {
        b.iter(|| compare(black_box(&i32_shape), black_box(&i64_shape)))
    });

    // Struct with field differences
    let ss = simple_struct();
    let ws = wide_struct();
    group.bench_function("struct_widen_3_to_4", |b| {
        b.iter(|| compare(black_box(&ss), black_box(&ws)))
    });

    // Enum comparison
    let e = simple_enum();
    group.bench_function("enum_3_identity", |b| {
        b.iter(|| compare(black_box(&e), black_box(&e)))
    });

    // Recursive shape
    let rl = recursive_list();
    group.bench_function("recursive_list_identity", |b| {
        b.iter(|| compare(black_box(&rl), black_box(&rl)))
    });

    group.finish();
}

fn bench_information_content(c: &mut Criterion) {
    let mut group = c.benchmark_group("information_content");

    let atom = Shape::Atom(AtomKind::I32);
    group.bench_function("atom_i32", |b| {
        b.iter(|| information_content(black_box(&atom)))
    });

    let s = simple_struct();
    group.bench_function("struct_3", |b| {
        b.iter(|| information_content(black_box(&s)))
    });

    let ds = deep_struct();
    group.bench_function("struct_10", |b| {
        b.iter(|| information_content(black_box(&ds)))
    });

    let e = simple_enum();
    group.bench_function("enum_3", |b| b.iter(|| information_content(black_box(&e))));

    let opt = Shape::optional(Shape::Atom(AtomKind::I64));
    group.bench_function("optional_i64", |b| {
        b.iter(|| information_content(black_box(&opt)))
    });

    let rl = recursive_list();
    group.bench_function("recursive_list", |b| {
        b.iter(|| information_content(black_box(&rl)))
    });

    group.finish();
}

fn bench_classify_morphism(c: &mut Criterion) {
    let mut group = c.benchmark_group("classify_morphism");

    // Pre-compute morphisms
    let i32_shape = Shape::Atom(AtomKind::I32);
    let identity_m = compare(&i32_shape, &i32_shape);
    group.bench_function("identity", |b| {
        b.iter(|| classify_morphism(black_box(&identity_m)))
    });

    let i64_shape = Shape::Atom(AtomKind::I64);
    let widen_m = compare(&i32_shape, &i64_shape);
    group.bench_function("widening", |b| {
        b.iter(|| classify_morphism(black_box(&widen_m)))
    });

    let ss = simple_struct();
    let ws = wide_struct();
    let struct_m = compare(&ss, &ws);
    group.bench_function("struct_widen", |b| {
        b.iter(|| classify_morphism(black_box(&struct_m)))
    });

    group.finish();
}

fn bench_compose(c: &mut Criterion) {
    let mut group = c.benchmark_group("compose");

    let i32_shape = Shape::Atom(AtomKind::I32);
    let i64_shape = Shape::Atom(AtomKind::I64);
    let i128_shape = Shape::Atom(AtomKind::I128);

    let f = compare(&i32_shape, &i64_shape);
    let g = compare(&i64_shape, &i128_shape);
    group.bench_function("atom_chain_i32_i64_i128", |b| {
        b.iter(|| compose(black_box(&f), black_box(&g)))
    });

    group.finish();
}

fn bench_category(c: &mut Criterion) {
    let mut group = c.benchmark_group("category");

    // Build a 4-node category
    let mut cat = shape_ir::category::ShapeCategory::new();
    cat.add_object("i8", Shape::Atom(AtomKind::I8));
    cat.add_object("i16", Shape::Atom(AtomKind::I16));
    cat.add_object("i32", Shape::Atom(AtomKind::I32));
    cat.add_object("i64", Shape::Atom(AtomKind::I64));
    cat.compare_all();

    group.bench_function("find_path_4_nodes", |b| {
        b.iter(|| cat.find_path(black_box("i8"), black_box("i64")))
    });

    group.bench_function("compose_path_3_hops", |b| {
        let path = cat.find_path("i8", "i64").unwrap();
        b.iter(|| cat.compose_path(black_box(&path)))
    });

    group.bench_function("lossless_reachable", |b| {
        b.iter(|| cat.lossless_reachable(black_box("i8")))
    });

    // Larger category: 8 types
    let mut big_cat = shape_ir::category::ShapeCategory::new();
    big_cat.add_object("bool", Shape::Atom(AtomKind::Bool));
    big_cat.add_object("u8", Shape::Atom(AtomKind::U8));
    big_cat.add_object("u16", Shape::Atom(AtomKind::U16));
    big_cat.add_object("u32", Shape::Atom(AtomKind::U32));
    big_cat.add_object("u64", Shape::Atom(AtomKind::U64));
    big_cat.add_object("i32", Shape::Atom(AtomKind::I32));
    big_cat.add_object("i64", Shape::Atom(AtomKind::I64));
    big_cat.add_object("str", Shape::Atom(AtomKind::String));
    big_cat.compare_all();

    group.bench_function("compare_all_8_types", |b| {
        let mut cat = shape_ir::category::ShapeCategory::new();
        cat.add_object("bool", Shape::Atom(AtomKind::Bool));
        cat.add_object("u8", Shape::Atom(AtomKind::U8));
        cat.add_object("u16", Shape::Atom(AtomKind::U16));
        cat.add_object("u32", Shape::Atom(AtomKind::U32));
        cat.add_object("u64", Shape::Atom(AtomKind::U64));
        cat.add_object("i32", Shape::Atom(AtomKind::I32));
        cat.add_object("i64", Shape::Atom(AtomKind::I64));
        cat.add_object("str", Shape::Atom(AtomKind::String));
        b.iter(|| {
            let mut c = cat.clone();
            c.compare_all();
            black_box(c)
        })
    });

    group.bench_function("find_path_8_nodes", |b| {
        b.iter(|| big_cat.find_path(black_box("bool"), black_box("str")))
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_compare,
    bench_information_content,
    bench_classify_morphism,
    bench_compose,
    bench_category,
);
criterion_main!(benches);
