// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Tests for the temporal algebra — schema evolution, semver classification,
//! compatibility forecasting, and evolution strategies.

use crate::temporal::*;
use crate::*;

// ---------------------------------------------------------------------------
// SemanticVersion
// ---------------------------------------------------------------------------

#[test]
fn semver_ordering() {
    let v1 = SemanticVersion::new(1, 0, 0);
    let v1_1 = SemanticVersion::new(1, 1, 0);
    let v2 = SemanticVersion::new(2, 0, 0);

    assert!(v1 < v1_1);
    assert!(v1_1 < v2);
    assert!(v1 < v2);
}

#[test]
fn semver_compatibility() {
    let v1_0 = SemanticVersion::new(1, 0, 0);
    let v1_5 = SemanticVersion::new(1, 5, 3);
    let v2_0 = SemanticVersion::new(2, 0, 0);

    assert!(v1_0.is_compatible_with(&v1_5));
    assert!(!v1_0.is_compatible_with(&v2_0));
}

#[test]
fn semver_display() {
    let v = SemanticVersion::new(1, 2, 3);
    assert_eq!(v.to_string(), "1.2.3");
}

// ---------------------------------------------------------------------------
// SemverClassification
// ---------------------------------------------------------------------------

#[test]
fn classification_from_transport_class() {
    assert_eq!(
        SemverClassification::from_transport_class(TransportClass::Concorde),
        SemverClassification::Patch
    );
    assert_eq!(
        SemverClassification::from_transport_class(TransportClass::Business),
        SemverClassification::Minor
    );
    assert_eq!(
        SemverClassification::from_transport_class(TransportClass::Economy),
        SemverClassification::Major
    );
    assert_eq!(
        SemverClassification::from_transport_class(TransportClass::Wheelbarrow),
        SemverClassification::Major
    );
}

#[test]
fn classification_predicates() {
    assert!(!SemverClassification::Patch.is_breaking());
    assert!(!SemverClassification::Minor.is_breaking());
    assert!(SemverClassification::Major.is_breaking());

    assert!(SemverClassification::Patch.is_backward_compatible());
    assert!(SemverClassification::Minor.is_backward_compatible());
    assert!(!SemverClassification::Major.is_backward_compatible());
}

// ---------------------------------------------------------------------------
// SchemaTimeline — basic operations
// ---------------------------------------------------------------------------

#[test]
fn empty_timeline() {
    let t = SchemaTimeline::new("test");
    assert_eq!(t.name(), "test");
    assert_eq!(t.version_count(), 0);
    assert!(t.current().is_none());
    assert!(t.evolution_steps().is_empty());
}

#[test]
fn single_version_timeline() {
    let mut t = SchemaTimeline::new("users");
    let v1 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    t.add_version(SemanticVersion::new(1, 0, 0), v1);

    assert_eq!(t.version_count(), 1);
    assert!(t.current().is_some());
    assert_eq!(t.current().unwrap().version, SemanticVersion::new(1, 0, 0));
    assert!(t.evolution_steps().is_empty()); // No predecessor → no step
}

#[test]
fn additive_evolution_is_minor() {
    let mut t = SchemaTimeline::new("users");

    let v1 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    t.add_version(SemanticVersion::new(1, 0, 0), v1);

    // Add an optional field — non-breaking, minor
    let v2 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
        ("email", Shape::optional(Shape::Atom(AtomKind::String))),
    ]);
    t.add_version(SemanticVersion::new(1, 1, 0), v2);

    assert_eq!(t.evolution_steps().len(), 1);
    let step = &t.evolution_steps()[0];
    assert_eq!(step.classification, SemverClassification::Minor);
    assert!(step.version_is_consistent());
}

#[test]
fn identical_evolution_is_patch() {
    let mut t = SchemaTimeline::new("config");

    let shape = Shape::struct_from(vec![("host", Shape::Atom(AtomKind::String))]);
    t.add_version(SemanticVersion::new(1, 0, 0), shape.clone());
    t.add_version(SemanticVersion::new(1, 0, 1), shape);

    let step = &t.evolution_steps()[0];
    assert_eq!(step.classification, SemverClassification::Patch);
    assert!(step.version_is_consistent());
}

#[test]
fn widening_evolution_is_minor() {
    let mut t = SchemaTimeline::new("metrics");

    let v1 = Shape::struct_from(vec![("count", Shape::Atom(AtomKind::I32))]);
    t.add_version(SemanticVersion::new(1, 0, 0), v1);

    // Widen I32 → I64
    let v2 = Shape::struct_from(vec![("count", Shape::Atom(AtomKind::I64))]);
    t.add_version(SemanticVersion::new(1, 1, 0), v2);

    let step = &t.evolution_steps()[0];
    assert_eq!(step.classification, SemverClassification::Minor);
}

#[test]
fn narrowing_evolution_is_major() {
    let mut t = SchemaTimeline::new("metrics");

    let v1 = Shape::struct_from(vec![("count", Shape::Atom(AtomKind::I64))]);
    t.add_version(SemanticVersion::new(1, 0, 0), v1);

    // Narrow I64 → I32 — BREAKING
    let v2 = Shape::struct_from(vec![("count", Shape::Atom(AtomKind::I32))]);
    t.add_version(SemanticVersion::new(2, 0, 0), v2);

    let step = &t.evolution_steps()[0];
    assert_eq!(step.classification, SemverClassification::Major);
    assert!(step.version_is_consistent()); // Declared as major bump
}

#[test]
fn type_change_is_major() {
    let mut t = SchemaTimeline::new("config");

    let v1 = Shape::struct_from(vec![("port", Shape::Atom(AtomKind::I32))]);
    t.add_version(SemanticVersion::new(1, 0, 0), v1);

    // Change I32 → String — BREAKING
    let v2 = Shape::struct_from(vec![("port", Shape::Atom(AtomKind::String))]);
    t.add_version(SemanticVersion::new(2, 0, 0), v2);

    let step = &t.evolution_steps()[0];
    assert_eq!(step.classification, SemverClassification::Major);
}

// ---------------------------------------------------------------------------
// Version consistency checks
// ---------------------------------------------------------------------------

#[test]
fn inconsistent_version_detected() {
    let mut t = SchemaTimeline::new("api");

    let v1 = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I64))]);
    t.add_version(SemanticVersion::new(1, 0, 0), v1);

    // Narrowing I64 → I32 is a breaking change, but declared as patch
    let v2 = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]);
    t.add_version(SemanticVersion::new(1, 0, 1), v2); // WRONG: should be 2.0.0

    let inconsistent = t.inconsistent_versions();
    assert_eq!(inconsistent.len(), 1);
    assert_eq!(inconsistent[0], 0);
}

#[test]
fn consistent_timeline_passes() {
    let mut t = SchemaTimeline::new("api");

    let v1 = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]);
    t.add_version(SemanticVersion::new(1, 0, 0), v1);

    let v2 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    t.add_version(SemanticVersion::new(1, 1, 0), v2);

    assert!(t.inconsistent_versions().is_empty());
}

// ---------------------------------------------------------------------------
// Timeline queries
// ---------------------------------------------------------------------------

#[test]
fn backward_compatible_timeline() {
    let mut t = SchemaTimeline::new("api");

    let v1 = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]);
    t.add_version(SemanticVersion::new(1, 0, 0), v1);

    let v2 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    t.add_version(SemanticVersion::new(1, 1, 0), v2);

    assert!(t.is_fully_backward_compatible());
    assert!(t.first_breaking_change().is_none());
}

#[test]
fn breaking_timeline() {
    let mut t = SchemaTimeline::new("api");

    let v1 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    t.add_version(SemanticVersion::new(1, 0, 0), v1);

    // Remove name field — BREAKING
    let v2 = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I64))]);
    t.add_version(SemanticVersion::new(2, 0, 0), v2);

    assert!(!t.is_fully_backward_compatible());
    let breaking = t.first_breaking_change().unwrap();
    assert_eq!(breaking.from_version, SemanticVersion::new(1, 0, 0));
}

#[test]
fn at_version_lookup() {
    let mut t = SchemaTimeline::new("api");

    let v1 = Shape::struct_from(vec![("x", Shape::Atom(AtomKind::I32))]);
    t.add_version(SemanticVersion::new(1, 0, 0), v1);

    let v2 = Shape::struct_from(vec![("x", Shape::Atom(AtomKind::I64))]);
    t.add_version(SemanticVersion::new(1, 1, 0), v2);

    assert!(t.at_version(&SemanticVersion::new(1, 0, 0)).is_some());
    assert!(t.at_version(&SemanticVersion::new(1, 1, 0)).is_some());
    assert!(t.at_version(&SemanticVersion::new(9, 9, 9)).is_none());
}

#[test]
fn morphism_to_current() {
    let mut t = SchemaTimeline::new("api");

    let v1 = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]);
    t.add_version(SemanticVersion::new(1, 0, 0), v1);

    let v2 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    t.add_version(SemanticVersion::new(1, 1, 0), v2);

    let v3 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I64)),
        ("name", Shape::Atom(AtomKind::String)),
        ("email", Shape::optional(Shape::Atom(AtomKind::String))),
    ]);
    t.add_version(SemanticVersion::new(1, 2, 0), v3);

    // v1 → current (v3): added fields + widened id
    let m = t.morphism_to_current(&SemanticVersion::new(1, 0, 0)).unwrap();
    assert_eq!(m.transport_class, TransportClass::Business);

    // v3 → current (same): identity
    let m_self = t.morphism_to_current(&SemanticVersion::new(1, 2, 0)).unwrap();
    assert_eq!(m_self.transport_class, TransportClass::Concorde);
}

// ---------------------------------------------------------------------------
// Multi-step timeline
// ---------------------------------------------------------------------------

#[test]
fn three_version_timeline() {
    let mut t = SchemaTimeline::new("users");

    let v1 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    t.add_version(SemanticVersion::new(1, 0, 0), v1);

    let v2 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
        ("email", Shape::optional(Shape::Atom(AtomKind::String))),
    ]);
    t.add_version(SemanticVersion::new(1, 1, 0), v2);

    let v3 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I64)),
        ("name", Shape::Atom(AtomKind::String)),
        ("email", Shape::optional(Shape::Atom(AtomKind::String))),
        ("active", Shape::Atom(AtomKind::Bool)),
    ]);
    t.add_version(SemanticVersion::new(1, 2, 0), v3);

    assert_eq!(t.version_count(), 3);
    assert_eq!(t.evolution_steps().len(), 2);

    // v1→v2: added optional email = Minor
    assert_eq!(
        t.evolution_steps()[0].classification,
        SemverClassification::Minor
    );
    // v2→v3: widened id + added active = Minor (Business)
    assert_eq!(
        t.evolution_steps()[1].classification,
        SemverClassification::Minor
    );

    assert!(t.is_fully_backward_compatible());
}

// ---------------------------------------------------------------------------
// Compatibility forecast
// ---------------------------------------------------------------------------

#[test]
fn compatible_timelines_stay_compatible() {
    let mut ta = SchemaTimeline::new("service_a");
    let mut tb = SchemaTimeline::new("service_b");

    // Both start with the same shape
    let base = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    ta.add_version(SemanticVersion::new(1, 0, 0), base.clone());
    tb.add_version(SemanticVersion::new(1, 0, 0), base);

    // A adds email
    let a_v2 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
        ("email", Shape::optional(Shape::Atom(AtomKind::String))),
    ]);
    ta.add_version(SemanticVersion::new(1, 1, 0), a_v2);

    // B adds phone
    let b_v2 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
        ("phone", Shape::optional(Shape::Atom(AtomKind::String))),
    ]);
    tb.add_version(SemanticVersion::new(1, 1, 0), b_v2);

    let forecast = forecast_compatibility(&ta, &tb);
    assert_eq!(forecast.timeline_a, "service_a");
    assert_eq!(forecast.timeline_b, "service_b");
    assert!(!forecast.compatibility_matrix.is_empty());
    // v1↔v1 is safe
    assert!(forecast.last_safe_pair.is_some());
}

#[test]
fn diverging_timelines_detected() {
    let mut ta = SchemaTimeline::new("api_a");
    let mut tb = SchemaTimeline::new("api_b");

    let base = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]);
    ta.add_version(SemanticVersion::new(1, 0, 0), base.clone());
    tb.add_version(SemanticVersion::new(1, 0, 0), base);

    // A changes type of id to String — incompatible with B's I32
    let a_v2 = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::String))]);
    ta.add_version(SemanticVersion::new(2, 0, 0), a_v2);

    let forecast = forecast_compatibility(&ta, &tb);
    // a_v2 vs b_v1: String vs I32 → Wheelbarrow
    assert!(forecast.first_unsafe_pair.is_some());
}

// ---------------------------------------------------------------------------
// Evolution strategy
// ---------------------------------------------------------------------------

#[test]
fn plan_additive_evolution() {
    let source = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]);
    let target = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);

    let strategy = plan_evolution(&source, &target);
    assert_eq!(strategy.overall_classification, SemverClassification::Minor);
    assert_eq!(strategy.suggested_version, SemverClassification::Minor);
}

#[test]
fn plan_breaking_evolution() {
    let source = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I64)),
        ("name", Shape::Atom(AtomKind::String)),
    ]);
    let target = Shape::struct_from(vec![("id", Shape::Atom(AtomKind::I32))]);

    let strategy = plan_evolution(&source, &target);
    assert_eq!(strategy.overall_classification, SemverClassification::Major);
}

#[test]
fn plan_identical_evolution() {
    let shape = Shape::struct_from(vec![("x", Shape::Atom(AtomKind::I32))]);
    let strategy = plan_evolution(&shape, &shape);
    assert_eq!(strategy.overall_classification, SemverClassification::Patch);
}

// ---------------------------------------------------------------------------
// next_version
// ---------------------------------------------------------------------------

#[test]
fn next_version_major() {
    let v = SemanticVersion::new(1, 5, 3);
    assert_eq!(
        next_version(&v, SemverClassification::Major),
        SemanticVersion::new(2, 0, 0)
    );
}

#[test]
fn next_version_minor() {
    let v = SemanticVersion::new(1, 5, 3);
    assert_eq!(
        next_version(&v, SemverClassification::Minor),
        SemanticVersion::new(1, 6, 0)
    );
}

#[test]
fn next_version_patch() {
    let v = SemanticVersion::new(1, 5, 3);
    assert_eq!(
        next_version(&v, SemverClassification::Patch),
        SemanticVersion::new(1, 5, 4)
    );
}

// ---------------------------------------------------------------------------
// Real-world scenario: database migration history
// ---------------------------------------------------------------------------

#[test]
fn database_migration_scenario() {
    let mut t = SchemaTimeline::new("orders");

    // v1.0.0: initial table
    let v1 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("customer_id", Shape::Atom(AtomKind::I32)),
        ("total", Shape::Atom(AtomKind::F32)),
    ]);
    t.add_version(SemanticVersion::new(1, 0, 0), v1);

    // v1.1.0: add created_at and status
    let v2 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("customer_id", Shape::Atom(AtomKind::I32)),
        ("total", Shape::Atom(AtomKind::F32)),
        ("created_at", Shape::Atom(AtomKind::Timestamp(TimePrecision::Microseconds))),
        ("status", Shape::optional(Shape::Atom(AtomKind::String))),
    ]);
    t.add_version(SemanticVersion::new(1, 1, 0), v2);

    // v1.2.0: widen total to F64 for precision
    let v3 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I32)),
        ("customer_id", Shape::Atom(AtomKind::I32)),
        ("total", Shape::Atom(AtomKind::F64)),
        ("created_at", Shape::Atom(AtomKind::Timestamp(TimePrecision::Microseconds))),
        ("status", Shape::optional(Shape::Atom(AtomKind::String))),
    ]);
    t.add_version(SemanticVersion::new(1, 2, 0), v3);

    // v2.0.0: change id to I64, remove status (breaking!)
    let v4 = Shape::struct_from(vec![
        ("id", Shape::Atom(AtomKind::I64)),
        ("customer_id", Shape::Atom(AtomKind::I64)),
        ("total", Shape::Atom(AtomKind::F64)),
        ("created_at", Shape::Atom(AtomKind::Timestamp(TimePrecision::Microseconds))),
    ]);
    t.add_version(SemanticVersion::new(2, 0, 0), v4);

    assert_eq!(t.version_count(), 4);
    assert_eq!(t.evolution_steps().len(), 3);

    // v1→v2: additive = Minor ✓
    assert_eq!(
        t.evolution_steps()[0].classification,
        SemverClassification::Minor
    );
    // v2→v3: widening = Minor ✓
    assert_eq!(
        t.evolution_steps()[1].classification,
        SemverClassification::Minor
    );
    // v3→v4: breaking (removed field) = Major ✓
    assert_eq!(
        t.evolution_steps()[2].classification,
        SemverClassification::Major
    );

    // All version bumps are consistent
    assert!(t.inconsistent_versions().is_empty());

    // First breaking change is v3→v4
    let breaking = t.first_breaking_change().unwrap();
    assert_eq!(breaking.from_version, SemanticVersion::new(1, 2, 0));
    assert_eq!(breaking.to_version, SemanticVersion::new(2, 0, 0));

    // v1 → current requires handling the breaking change
    let m = t.morphism_to_current(&SemanticVersion::new(1, 0, 0)).unwrap();
    assert!(
        m.transport_class == TransportClass::Economy
            || m.transport_class == TransportClass::Business,
        "v1→v4 should be Economy or Business, got {:?}",
        m.transport_class
    );
}
