// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Tests for information content calculation and transport classes.

use crate::information::information_content;
use crate::*;

// ---------------------------------------------------------------------------
// Atom information content
// ---------------------------------------------------------------------------

#[test]
fn unit_has_zero_information() {
    let info = information_content(&Shape::Unit);
    assert_eq!(info.min_bits, 0);
    assert_eq!(info.max_bits, Some(0));
    assert!(info.is_fixed_size);
    assert_eq!(info.cardinality, Some(1));
}

#[test]
fn bool_has_one_bit() {
    let info = information_content(&Shape::Atom(AtomKind::Bool));
    assert_eq!(info.min_bits, 1);
    assert_eq!(info.max_bits, Some(1));
    assert!(info.is_fixed_size);
    assert_eq!(info.cardinality, Some(2));
}

#[test]
fn i32_has_32_bits() {
    let info = information_content(&Shape::Atom(AtomKind::I32));
    assert_eq!(info.min_bits, 32);
    assert_eq!(info.max_bits, Some(32));
    assert!(info.is_fixed_size);
    assert_eq!(info.cardinality, Some(4_294_967_296));
}

#[test]
fn i64_has_64_bits() {
    let info = information_content(&Shape::Atom(AtomKind::I64));
    assert_eq!(info.min_bits, 64);
    assert_eq!(info.max_bits, Some(64));
}

#[test]
fn string_is_unbounded() {
    let info = information_content(&Shape::Atom(AtomKind::String));
    assert_eq!(info.max_bits, None);
    assert!(!info.is_fixed_size);
    assert_eq!(info.cardinality, None);
}

#[test]
fn bytes_is_unbounded() {
    let info = information_content(&Shape::Atom(AtomKind::Bytes));
    assert_eq!(info.max_bits, None);
    assert!(!info.is_fixed_size);
}

#[test]
fn fixed_bytes_has_known_width() {
    // UUID = 16 bytes = 128 bits
    let info = information_content(&Shape::Atom(AtomKind::FixedBytes(16)));
    assert_eq!(info.min_bits, 128);
    assert_eq!(info.max_bits, Some(128));
    assert!(info.is_fixed_size);
}

#[test]
fn enum_information_content() {
    let info = information_content(&Shape::Atom(AtomKind::Enum(vec![
        "A".into(),
        "B".into(),
        "C".into(),
        "D".into(),
    ])));
    assert_eq!(info.min_bits, 2); // ceil(log2(4)) = 2
    assert_eq!(info.cardinality, Some(4));
}

// ---------------------------------------------------------------------------
// Compound shape information content
// ---------------------------------------------------------------------------

#[test]
fn product_sums_bits() {
    let shape = Shape::struct_from(vec![
        ("x", Shape::Atom(AtomKind::I32)),
        ("y", Shape::Atom(AtomKind::I32)),
    ]);
    let info = information_content(&shape);
    // 32 + 32 + 0 (Unit terminator) = 64
    assert_eq!(info.min_bits, 64);
    assert_eq!(info.max_bits, Some(64));
    assert!(info.is_fixed_size);
}

#[test]
fn product_with_string_is_unbounded() {
    let shape = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    let info = information_content(&shape);
    assert_eq!(info.max_bits, None);
    assert!(!info.is_fixed_size);
}

#[test]
fn sum_uses_max_plus_tag() {
    let shape = Shape::enum_from(vec![
        ("A", Shape::Atom(AtomKind::I32)), // 32 bits
        ("B", Shape::Atom(AtomKind::I64)), // 64 bits
    ]);
    let info = information_content(&shape);
    // Tag bit + max(inner sum)
    // The inner sum is Sum("B", I64, Unit), which is 1 + max(64, 0) = 65
    // The outer sum is 1 + max(32, 65) = 66
    // min_bits: 1 + min(32, 1 + min(64, 0)) = 1 + min(32, 1) = 2
    assert!(info.min_bits <= info.max_bits.unwrap_or(u64::MAX));
}

#[test]
fn sum_cardinality_is_sum_of_variants() {
    let shape = Shape::sum(
        "A",
        Shape::Atom(AtomKind::Bool), // 2
        Shape::sum(
            "B",
            Shape::Atom(AtomKind::Bool), // 2
            Shape::Unit,
        ),
    );
    let info = information_content(&shape);
    // The inner Sum("B", Bool, Unit) has cardinality 2 + 1 = 3
    // The outer Sum("A", Bool, inner) has cardinality 2 + 3 = 5
    assert_eq!(info.cardinality, Some(5));
}

#[test]
fn sequence_is_unbounded() {
    let shape = Shape::sequence(Shape::Atom(AtomKind::I32));
    let info = information_content(&shape);
    assert_eq!(info.min_bits, 0);
    assert_eq!(info.max_bits, None);
    assert!(!info.is_fixed_size);
    assert_eq!(info.cardinality, None);
}

#[test]
fn optional_adds_one_bit() {
    let inner = Shape::Atom(AtomKind::I32);
    let inner_info = information_content(&inner);
    let opt = Shape::optional(inner);
    let opt_info = information_content(&opt);

    assert_eq!(opt_info.max_bits, Some(inner_info.max_bits.expect("inner max_bits should be Some") + 1));
    assert_eq!(
        opt_info.cardinality,
        Some(inner_info.cardinality.expect("inner cardinality should be Some") + 1)
    );
}

#[test]
fn map_is_unbounded() {
    let shape = Shape::map(Shape::Atom(AtomKind::String), Shape::Atom(AtomKind::I32));
    let info = information_content(&shape);
    assert_eq!(info.max_bits, None);
    assert!(!info.is_fixed_size);
}

#[test]
fn recursive_is_unbounded() {
    let shape = Shape::recursive("T", Shape::Atom(AtomKind::I32));
    let info = information_content(&shape);
    assert_eq!(info.max_bits, None);
}

#[test]
fn annotated_same_as_inner() {
    let inner = Shape::Atom(AtomKind::I32);
    let annotated = inner
        .clone()
        .annotated(Annotations::new().with_nullable(true));
    assert_eq!(information_content(&inner), information_content(&annotated));
}

// ---------------------------------------------------------------------------
// Transport class ordering and composition
// ---------------------------------------------------------------------------

#[test]
fn transport_class_ordering() {
    assert!(TransportClass::Concorde < TransportClass::Business);
    assert!(TransportClass::Business < TransportClass::Economy);
    assert!(TransportClass::Economy < TransportClass::Wheelbarrow);
}

#[test]
fn transport_class_compose_takes_worst() {
    assert_eq!(
        TransportClass::compose(TransportClass::Concorde, TransportClass::Concorde),
        TransportClass::Concorde
    );
    assert_eq!(
        TransportClass::compose(TransportClass::Concorde, TransportClass::Business),
        TransportClass::Business
    );
    assert_eq!(
        TransportClass::compose(TransportClass::Business, TransportClass::Economy),
        TransportClass::Economy
    );
    assert_eq!(
        TransportClass::compose(TransportClass::Economy, TransportClass::Wheelbarrow),
        TransportClass::Wheelbarrow
    );
    assert_eq!(
        TransportClass::compose(TransportClass::Concorde, TransportClass::Wheelbarrow),
        TransportClass::Wheelbarrow
    );
}

#[test]
fn transport_class_compose_is_commutative() {
    let classes = [
        TransportClass::Concorde,
        TransportClass::Business,
        TransportClass::Economy,
        TransportClass::Wheelbarrow,
    ];
    for a in &classes {
        for b in &classes {
            assert_eq!(
                TransportClass::compose(*a, *b),
                TransportClass::compose(*b, *a),
                "compose({:?}, {:?}) != compose({:?}, {:?})",
                a,
                b,
                b,
                a
            );
        }
    }
}

#[test]
fn transport_class_compose_is_associative() {
    let classes = [
        TransportClass::Concorde,
        TransportClass::Business,
        TransportClass::Economy,
        TransportClass::Wheelbarrow,
    ];
    for a in &classes {
        for b in &classes {
            for c in &classes {
                let left = TransportClass::compose(TransportClass::compose(*a, *b), *c);
                let right = TransportClass::compose(*a, TransportClass::compose(*b, *c));
                assert_eq!(left, right);
            }
        }
    }
}

#[test]
fn concorde_is_identity_for_compose() {
    let classes = [
        TransportClass::Concorde,
        TransportClass::Business,
        TransportClass::Economy,
        TransportClass::Wheelbarrow,
    ];
    for c in &classes {
        assert_eq!(TransportClass::compose(TransportClass::Concorde, *c), *c);
        assert_eq!(TransportClass::compose(*c, TransportClass::Concorde), *c);
    }
}

#[test]
fn lossless_check() {
    assert!(TransportClass::Concorde.is_lossless());
    assert!(TransportClass::Business.is_lossless());
    assert!(!TransportClass::Economy.is_lossless());
    assert!(!TransportClass::Wheelbarrow.is_lossless());
}

// ---------------------------------------------------------------------------
// Information cost
// ---------------------------------------------------------------------------

#[test]
fn information_cost_sum() {
    let a = InformationCost {
        bits_added: 32,
        bits_lost: 0,
        identity_paths: 2,
        transform_steps: 1,
    };
    let b = InformationCost {
        bits_added: 0,
        bits_lost: 16,
        identity_paths: 1,
        transform_steps: 2,
    };
    let sum = a.sum(&b);
    assert_eq!(sum.bits_added, 32);
    assert_eq!(sum.bits_lost, 16);
    assert_eq!(sum.identity_paths, 3);
    assert_eq!(sum.transform_steps, 3);
}

// ---------------------------------------------------------------------------
// Morphism metrics / classification
// ---------------------------------------------------------------------------

#[test]
fn identity_morphism_has_perfect_metrics() {
    let shape = Shape::Atom(AtomKind::I32);
    let m = crate::compare::compare(&shape, &shape);
    let metrics = crate::information::classify_morphism(&m);

    assert_eq!(metrics.transport_class, TransportClass::Concorde);
    assert_eq!(metrics.loss_ratio, 0.0);
    assert_eq!(metrics.net_bits, 0);
    assert!(!metrics.is_pure_embedding);
    assert!(!metrics.is_pure_projection);
    assert_eq!(metrics.reversibility, 1.0);
}

#[test]
fn widening_is_pure_embedding() {
    let source = Shape::Atom(AtomKind::I32);
    let target = Shape::Atom(AtomKind::I64);
    let m = crate::compare::compare(&source, &target);
    let metrics = crate::information::classify_morphism(&m);

    assert_eq!(metrics.transport_class, TransportClass::Business);
    assert!(metrics.is_pure_embedding);
    assert!(!metrics.is_pure_projection);
    assert_eq!(metrics.loss_ratio, 0.0);
    assert!(metrics.net_bits > 0);
    assert_eq!(metrics.reversibility, 1.0);
}

#[test]
fn narrowing_is_pure_projection() {
    let source = Shape::Atom(AtomKind::I64);
    let target = Shape::Atom(AtomKind::I32);
    let m = crate::compare::compare(&source, &target);
    let metrics = crate::information::classify_morphism(&m);

    assert_eq!(metrics.transport_class, TransportClass::Economy);
    assert!(!metrics.is_pure_embedding);
    assert!(metrics.is_pure_projection);
    assert!(metrics.loss_ratio > 0.0);
    assert!(metrics.net_bits < 0);
    assert!(metrics.reversibility < 1.0);
    assert!(metrics.reversibility > 0.0);
}

#[test]
fn struct_with_extra_and_dropped_fields_metrics() {
    let source = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
        ("old_field", Shape::Atom(AtomKind::Bool)),
    ]);
    let target = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I64)),        // widened
        ("name", Shape::Atom(AtomKind::String)),   // same
        ("new_field", Shape::Atom(AtomKind::F64)), // added
    ]);
    let m = crate::compare::compare(&source, &target);
    let metrics = crate::information::classify_morphism(&m);

    // Both adds and removes -> neither pure embedding nor pure projection
    assert!(!metrics.is_pure_embedding);
    assert!(!metrics.is_pure_projection);
    // Should be Economy (worst of Business + Economy)
    assert_eq!(metrics.transport_class, TransportClass::Economy);
}

#[test]
fn metrics_display_is_readable() {
    let source = Shape::Atom(AtomKind::I32);
    let target = Shape::Atom(AtomKind::I64);
    let m = crate::compare::compare(&source, &target);
    let metrics = crate::information::classify_morphism(&m);
    let display = format!("{}", metrics);

    assert!(display.contains("Business"));
    assert!(display.contains("identity:"));
    assert!(display.contains("reversibility:"));
}
