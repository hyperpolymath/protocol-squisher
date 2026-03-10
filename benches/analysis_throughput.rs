// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Benchmark: schema analysis and comparison throughput
//!
//! Measures:
//! - Schema analysis throughput (schemas/sec) via IR construction
//! - Comparison throughput (pairs/sec) via compatibility engine
//! - Large schema handling (1000+ fields)
//!
//! Run with: `just bench` or `cargo bench --bench analysis_throughput`

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use protocol_squisher_compat::{bidirectional_compare, compare_schemas};
use protocol_squisher_ir::*;
use std::hint::black_box;

/// Build a schema with `n` fields of the given type.
fn make_schema_with_fields(name: &str, field_count: usize, field_type: PrimitiveType) -> IrSchema {
    let mut schema = IrSchema::new(name, "bench");
    let fields: Vec<FieldDef> = (0..field_count)
        .map(|i| FieldDef {
            name: format!("field_{i}"),
            ty: IrType::Primitive(field_type),
            optional: i % 3 == 0,
            constraints: if i % 5 == 0 {
                vec![Constraint::NonNegative]
            } else {
                vec![]
            },
            metadata: FieldMetadata::default(),
        })
        .collect();
    schema.add_type(
        "Record".to_string(),
        TypeDef::Struct(StructDef {
            name: "Record".to_string(),
            fields,
            metadata: TypeMetadata::default(),
        }),
    );
    schema.add_root("Record".to_string());
    schema
}

/// Build a schema with multiple types, each having `fields_per_type` fields.
fn make_multi_type_schema(name: &str, type_count: usize, fields_per_type: usize) -> IrSchema {
    let mut schema = IrSchema::new(name, "bench");
    for t in 0..type_count {
        let fields: Vec<FieldDef> = (0..fields_per_type)
            .map(|i| FieldDef {
                name: format!("field_{i}"),
                ty: IrType::Primitive(if i % 2 == 0 {
                    PrimitiveType::I64
                } else {
                    PrimitiveType::String
                }),
                optional: i % 4 == 0,
                constraints: vec![],
                metadata: FieldMetadata::default(),
            })
            .collect();
        let type_name = format!("Type_{t}");
        schema.add_type(
            type_name.clone(),
            TypeDef::Struct(StructDef {
                name: type_name.clone(),
                fields,
                metadata: TypeMetadata::default(),
            }),
        );
        if t == 0 {
            schema.add_root(type_name);
        }
    }
    schema
}

// ─── Benchmarks ─────────────────────────────────────────────────────────────

fn bench_schema_construction(c: &mut Criterion) {
    let mut group = c.benchmark_group("schema_construction");

    for field_count in [10, 100, 500, 1000, 5000] {
        group.bench_with_input(
            BenchmarkId::new("fields", field_count),
            &field_count,
            |b, &n| {
                b.iter(|| {
                    let schema = make_schema_with_fields("bench", n, PrimitiveType::I64);
                    black_box(schema)
                })
            },
        );
    }

    group.finish();
}

fn bench_schema_json_roundtrip(c: &mut Criterion) {
    let mut group = c.benchmark_group("schema_json_roundtrip");

    for field_count in [10, 100, 1000] {
        let schema = make_schema_with_fields("bench", field_count, PrimitiveType::I64);
        let json = schema.to_json().unwrap();

        group.bench_with_input(
            BenchmarkId::new("serialize", field_count),
            &schema,
            |b, schema| {
                b.iter(|| {
                    let j = black_box(schema).to_json().unwrap();
                    black_box(j)
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("deserialize", field_count),
            &json,
            |b, json| {
                b.iter(|| {
                    let s = IrSchema::from_json(black_box(json)).unwrap();
                    black_box(s)
                })
            },
        );
    }

    group.finish();
}

fn bench_comparison_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("comparison_throughput");

    for field_count in [10, 100, 500, 1000] {
        let source = make_schema_with_fields("source", field_count, PrimitiveType::I32);
        let target = make_schema_with_fields("target", field_count, PrimitiveType::I64);

        group.bench_with_input(
            BenchmarkId::new("compare_schemas", field_count),
            &(source.clone(), target.clone()),
            |b, (src, tgt)| {
                b.iter(|| {
                    let result = compare_schemas(black_box(src), black_box(tgt));
                    black_box(result)
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("bidirectional_compare", field_count),
            &(source.clone(), target.clone()),
            |b, (src, tgt)| {
                b.iter(|| {
                    let result = bidirectional_compare(black_box(src), black_box(tgt));
                    black_box(result)
                })
            },
        );
    }

    group.finish();
}

fn bench_large_schema_handling(c: &mut Criterion) {
    let mut group = c.benchmark_group("large_schema");

    // 1000+ fields, single type
    let large = make_schema_with_fields("large", 2000, PrimitiveType::I64);
    group.bench_function("validate_2000_fields", |b| {
        b.iter(|| {
            let result = protocol_squisher_ir::validate_schema(black_box(&large));
            black_box(result)
        })
    });

    // 50 types x 20 fields = 1000 fields across types
    let multi = make_multi_type_schema("multi", 50, 20);
    let multi_target = make_multi_type_schema("multi_target", 50, 20);
    group.bench_function("compare_50_types_x_20_fields", |b| {
        b.iter(|| {
            let result = compare_schemas(black_box(&multi), black_box(&multi_target));
            black_box(result)
        })
    });

    group.finish();
}

criterion_group!(
    analysis_benches,
    bench_schema_construction,
    bench_schema_json_roundtrip,
    bench_comparison_throughput,
    bench_large_schema_handling,
);

criterion_main!(analysis_benches);
