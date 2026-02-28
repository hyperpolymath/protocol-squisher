// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Advanced optimization tests covering complex scenarios

use protocol_squisher_compat::EphapaxCompatibilityEngine;
use protocol_squisher_ir::*;
use protocol_squisher_optimizer::*;
use protocol_squisher_transport_primitives::TransportClass;
use std::collections::BTreeMap;

/// Helper to create a field
fn field(name: &str, ty: IrType, optional: bool) -> FieldDef {
    FieldDef {
        name: name.to_string(),
        ty,
        optional,
        constraints: vec![],
        metadata: FieldMetadata::default(),
    }
}

/// Helper to create a struct
fn make_struct(name: &str, fields: Vec<FieldDef>) -> TypeDef {
    TypeDef::Struct(StructDef {
        name: name.to_string(),
        fields,
        metadata: TypeMetadata::default(),
    })
}

/// Helper to create a schema
fn make_schema(name: &str, types: BTreeMap<String, TypeDef>, roots: Vec<String>) -> IrSchema {
    IrSchema {
        name: name.to_string(),
        version: "1.0.0".to_string(),
        source_format: "test".to_string(),
        types,
        roots,
        metadata: Default::default(),
    }
}

#[test]
fn test_nested_struct_optimization() {
    // Source: nested struct with i64 fields
    // Target: nested struct with i32 fields (needs widening)
    let mut source_types = BTreeMap::new();
    source_types.insert(
        "Inner".to_string(),
        make_struct(
            "Inner",
            vec![field("value", IrType::Primitive(PrimitiveType::I64), false)],
        ),
    );
    source_types.insert(
        "Outer".to_string(),
        make_struct(
            "Outer",
            vec![
                field("id", IrType::Primitive(PrimitiveType::I64), false),
                field("inner", IrType::Reference("Inner".to_string()), false),
            ],
        ),
    );

    let mut target_types = BTreeMap::new();
    target_types.insert(
        "Inner".to_string(),
        make_struct(
            "Inner",
            vec![field("value", IrType::Primitive(PrimitiveType::I32), false)],
        ),
    );
    target_types.insert(
        "Outer".to_string(),
        make_struct(
            "Outer",
            vec![
                field("id", IrType::Primitive(PrimitiveType::I32), false),
                field("inner", IrType::Reference("Inner".to_string()), false),
            ],
        ),
    );

    let source = make_schema("source", source_types, vec!["Outer".to_string()]);
    let target = make_schema("target", target_types, vec!["Outer".to_string()]);

    let engine = EphapaxCompatibilityEngine::new();
    let optimizer = EphapaxOptimizer::new(engine);

    let result = optimizer.analyze_and_suggest(&source, &target);

    // Should suggest widening for Outer.id
    // Note: Inner.value won't be suggested because optimizer currently only
    // analyzes root-level types, not nested type references
    assert!(
        !result.suggestions.is_empty(),
        "Should have optimization suggestions"
    );

    let outer_id_suggestion = result
        .suggestions
        .iter()
        .find(|s| s.target.contains("Outer.id"));
    assert!(
        outer_id_suggestion.is_some(),
        "Should suggest widening Outer.id"
    );
}

#[test]
fn test_vec_element_narrowing_optimization() {
    // Source: Vec<i64>
    // Target: Vec<i32> - element narrowing
    let mut source_types = BTreeMap::new();
    source_types.insert(
        "Data".to_string(),
        make_struct(
            "Data",
            vec![field(
                "values",
                IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
                    PrimitiveType::I64,
                )))),
                false,
            )],
        ),
    );

    let mut target_types = BTreeMap::new();
    target_types.insert(
        "Data".to_string(),
        make_struct(
            "Data",
            vec![field(
                "values",
                IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
                    PrimitiveType::I32,
                )))),
                false,
            )],
        ),
    );

    let source = make_schema("source", source_types, vec!["Data".to_string()]);
    let target = make_schema("target", target_types, vec!["Data".to_string()]);

    let engine = EphapaxCompatibilityEngine::new();
    let optimizer = EphapaxOptimizer::new(engine);

    let result = optimizer.analyze_and_suggest(&source, &target);

    // Current compatibility should show Wheelbarrow for values field
    assert_eq!(
        result.current.overall_class,
        TransportClass::Wheelbarrow,
        "Vec with narrowing element should be Wheelbarrow"
    );

    // Should suggest widening the element type
    let vec_suggestion = result
        .suggestions
        .iter()
        .find(|s| s.target.contains("values"));
    assert!(
        vec_suggestion.is_some(),
        "Should suggest widening Vec element type"
    );

    if let Some(suggestion) = vec_suggestion {
        assert_eq!(
            suggestion.current_class,
            TransportClass::Wheelbarrow,
            "Current class should be Wheelbarrow"
        );
        // Note: Widening Vec<i32> → Vec<i64> results in ContainerMatch (Business),
        // not ZeroCopy (Concorde), because containers always have overhead
        assert_eq!(
            suggestion.improved_class,
            TransportClass::Business,
            "Improved class should be Business (ContainerMatch) after widening Vec element"
        );
    }
}

#[test]
fn test_option_narrowing_optimization() {
    // Source: Option<i64>
    // Target: Option<i32> - inner narrowing
    let mut source_types = BTreeMap::new();
    source_types.insert(
        "Optional".to_string(),
        make_struct(
            "Optional",
            vec![field(
                "maybe_value",
                IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
                    PrimitiveType::I64,
                )))),
                false,
            )],
        ),
    );

    let mut target_types = BTreeMap::new();
    target_types.insert(
        "Optional".to_string(),
        make_struct(
            "Optional",
            vec![field(
                "maybe_value",
                IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
                    PrimitiveType::I32,
                )))),
                false,
            )],
        ),
    );

    let source = make_schema("source", source_types, vec!["Optional".to_string()]);
    let target = make_schema("target", target_types, vec!["Optional".to_string()]);

    let engine = EphapaxCompatibilityEngine::new();
    let optimizer = EphapaxOptimizer::new(engine);

    let result = optimizer.analyze_and_suggest(&source, &target);

    // Should suggest widening Option<i32> → Option<i64>
    assert!(
        !result.suggestions.is_empty(),
        "Should have optimization suggestions"
    );

    let opt_suggestion = result
        .suggestions
        .iter()
        .find(|s| s.target.contains("maybe_value"));
    assert!(
        opt_suggestion.is_some(),
        "Should suggest widening Option inner type"
    );
}

#[test]
fn test_map_key_value_narrowing() {
    // Source: Map<String, i64>
    // Target: Map<String, i32> - value narrowing
    let mut source_types = BTreeMap::new();
    source_types.insert(
        "Mapping".to_string(),
        make_struct(
            "Mapping",
            vec![field(
                "data",
                IrType::Container(ContainerType::Map(
                    Box::new(IrType::Primitive(PrimitiveType::String)),
                    Box::new(IrType::Primitive(PrimitiveType::I64)),
                )),
                false,
            )],
        ),
    );

    let mut target_types = BTreeMap::new();
    target_types.insert(
        "Mapping".to_string(),
        make_struct(
            "Mapping",
            vec![field(
                "data",
                IrType::Container(ContainerType::Map(
                    Box::new(IrType::Primitive(PrimitiveType::String)),
                    Box::new(IrType::Primitive(PrimitiveType::I32)),
                )),
                false,
            )],
        ),
    );

    let source = make_schema("source", source_types, vec!["Mapping".to_string()]);
    let target = make_schema("target", target_types, vec!["Mapping".to_string()]);

    let engine = EphapaxCompatibilityEngine::new();
    let optimizer = EphapaxOptimizer::new(engine);

    let result = optimizer.analyze_and_suggest(&source, &target);

    // Should be Wheelbarrow due to value narrowing
    assert_eq!(
        result.current.overall_class,
        TransportClass::Wheelbarrow,
        "Map with narrowing value should be Wheelbarrow"
    );

    // Should suggest widening the value type
    let map_suggestion = result
        .suggestions
        .iter()
        .find(|s| s.target.contains("data"));
    assert!(
        map_suggestion.is_some(),
        "Should suggest widening Map value type"
    );
}

#[test]
fn test_tuple_narrowing_optimization() {
    // Source: (i64, f64, String)
    // Target: (i32, f32, String) - first two narrowing
    let mut source_types = BTreeMap::new();
    source_types.insert(
        "Triple".to_string(),
        make_struct(
            "Triple",
            vec![field(
                "tuple",
                IrType::Container(ContainerType::Tuple(vec![
                    IrType::Primitive(PrimitiveType::I64),
                    IrType::Primitive(PrimitiveType::F64),
                    IrType::Primitive(PrimitiveType::String),
                ])),
                false,
            )],
        ),
    );

    let mut target_types = BTreeMap::new();
    target_types.insert(
        "Triple".to_string(),
        make_struct(
            "Triple",
            vec![field(
                "tuple",
                IrType::Container(ContainerType::Tuple(vec![
                    IrType::Primitive(PrimitiveType::I32),
                    IrType::Primitive(PrimitiveType::F32),
                    IrType::Primitive(PrimitiveType::String),
                ])),
                false,
            )],
        ),
    );

    let source = make_schema("source", source_types, vec!["Triple".to_string()]);
    let target = make_schema("target", target_types, vec!["Triple".to_string()]);

    let engine = EphapaxCompatibilityEngine::new();
    let optimizer = EphapaxOptimizer::new(engine);

    let result = optimizer.analyze_and_suggest(&source, &target);

    // Should be Wheelbarrow due to tuple element narrowing
    assert_eq!(
        result.current.overall_class,
        TransportClass::Wheelbarrow,
        "Tuple with narrowing elements should be Wheelbarrow"
    );
}

#[test]
fn test_mixed_transport_class_optimization() {
    // Schema with mixture of Concorde, Business, and Wheelbarrow fields
    let mut source_types = BTreeMap::new();
    source_types.insert(
        "Mixed".to_string(),
        make_struct(
            "Mixed",
            vec![
                field("perfect", IrType::Primitive(PrimitiveType::I64), false), // Concorde
                field("widening", IrType::Primitive(PrimitiveType::I32), false), // Business (if target is i64)
                field("narrowing", IrType::Primitive(PrimitiveType::I64), false), // Wheelbarrow (if target is i32)
                field("string", IrType::Primitive(PrimitiveType::String), false), // Concorde
            ],
        ),
    );

    let mut target_types = BTreeMap::new();
    target_types.insert(
        "Mixed".to_string(),
        make_struct(
            "Mixed",
            vec![
                field("perfect", IrType::Primitive(PrimitiveType::I64), false), // Match
                field("widening", IrType::Primitive(PrimitiveType::I64), false), // Widening
                field("narrowing", IrType::Primitive(PrimitiveType::I32), false), // Narrowing
                field("string", IrType::Primitive(PrimitiveType::String), false), // Match
            ],
        ),
    );

    let source = make_schema("source", source_types, vec!["Mixed".to_string()]);
    let target = make_schema("target", target_types, vec!["Mixed".to_string()]);

    let engine = EphapaxCompatibilityEngine::new();
    let optimizer = EphapaxOptimizer::new(engine);

    let result = optimizer.analyze_and_suggest(&source, &target);

    // Should suggest widening the narrowing field
    let narrowing_suggestion = result
        .suggestions
        .iter()
        .find(|s| s.target.contains("narrowing"));
    assert!(
        narrowing_suggestion.is_some(),
        "Should suggest widening narrowing field"
    );

    // Should NOT suggest anything for perfect or string fields (already Concorde)
    assert!(
        !result
            .suggestions
            .iter()
            .any(|s| s.target.contains("perfect")),
        "Should not suggest changes for perfect match field"
    );
    assert!(
        !result
            .suggestions
            .iter()
            .any(|s| s.target.contains("string")),
        "Should not suggest changes for perfect match string field"
    );

    // Calculate expected zero-copy percentage
    // Current: 2/4 fields are Concorde (perfect + string)
    // After optimization: 3/4 or 4/4 depending on widening field
    assert!(
        result.potential_zero_copy_percentage > 50.0,
        "Potential zero-copy should improve from current 50%"
    );
}

#[test]
fn test_empty_struct_optimization() {
    // Edge case: empty struct
    let mut source_types = BTreeMap::new();
    source_types.insert("Empty".to_string(), make_struct("Empty", vec![]));

    let mut target_types = BTreeMap::new();
    target_types.insert("Empty".to_string(), make_struct("Empty", vec![]));

    let source = make_schema("source", source_types, vec!["Empty".to_string()]);
    let target = make_schema("target", target_types, vec!["Empty".to_string()]);

    let engine = EphapaxCompatibilityEngine::new();
    let optimizer = EphapaxOptimizer::new(engine);

    let result = optimizer.analyze_and_suggest(&source, &target);

    // Empty struct should be Concorde (trivially compatible)
    // No suggestions needed
    assert!(
        result.suggestions.is_empty(),
        "Empty struct should need no optimization"
    );
}

#[test]
fn test_single_field_struct_optimization() {
    // Edge case: single-field struct
    let mut source_types = BTreeMap::new();
    source_types.insert(
        "Single".to_string(),
        make_struct(
            "Single",
            vec![field("value", IrType::Primitive(PrimitiveType::I64), false)],
        ),
    );

    let mut target_types = BTreeMap::new();
    target_types.insert(
        "Single".to_string(),
        make_struct(
            "Single",
            vec![field("value", IrType::Primitive(PrimitiveType::I32), false)],
        ),
    );

    let source = make_schema("source", source_types, vec!["Single".to_string()]);
    let target = make_schema("target", target_types, vec!["Single".to_string()]);

    let engine = EphapaxCompatibilityEngine::new();
    let optimizer = EphapaxOptimizer::new(engine);

    let result = optimizer.analyze_and_suggest(&source, &target);

    // Should suggest widening the single field (and possibly making it optional)
    // Optimizer generates both "widen type" and "make optional" suggestions
    assert!(
        !result.suggestions.is_empty(),
        "Should have optimization suggestions"
    );

    // Find the widening suggestion (should be first due to higher impact)
    let widen_suggestion = result
        .suggestions
        .iter()
        .find(|s| matches!(s.kind, SuggestionKind::WidenType { .. }));

    assert!(widen_suggestion.is_some(), "Should suggest widening");

    if let Some(suggestion) = widen_suggestion {
        assert_eq!(suggestion.current_class, TransportClass::Wheelbarrow);
        assert_eq!(suggestion.improved_class, TransportClass::Concorde);
        assert_eq!(
            suggestion.impact, 100.0,
            "Single field should have 100% impact"
        );
    }
}

#[test]
fn test_large_struct_impact_calculation() {
    // Large struct with many fields
    let fields: Vec<FieldDef> = (0..20)
        .map(|i| {
            field(
                &format!("field{}", i),
                IrType::Primitive(PrimitiveType::I64),
                false,
            )
        })
        .collect();

    let mut source_types = BTreeMap::new();
    source_types.insert("Large".to_string(), make_struct("Large", fields.clone()));

    // Target has one field with narrowing
    let mut target_fields = fields.clone();
    target_fields[0].ty = IrType::Primitive(PrimitiveType::I32); // Narrowing on first field

    let mut target_types = BTreeMap::new();
    target_types.insert("Large".to_string(), make_struct("Large", target_fields));

    let source = make_schema("source", source_types, vec!["Large".to_string()]);
    let target = make_schema("target", target_types, vec!["Large".to_string()]);

    let engine = EphapaxCompatibilityEngine::new();
    let optimizer = EphapaxOptimizer::new(engine);

    let result = optimizer.analyze_and_suggest(&source, &target);

    // Should suggest widening field0
    let field0_suggestion = result
        .suggestions
        .iter()
        .find(|s| s.target.contains("field0"));
    assert!(
        field0_suggestion.is_some(),
        "Should suggest widening field0"
    );

    if let Some(suggestion) = field0_suggestion {
        // Impact should be 1/20 = 5%
        assert!(
            (suggestion.impact - 5.0).abs() < 0.1,
            "Impact should be ~5% (1/20 fields)"
        );
    }

    // Potential improvement: from 19/20 (95%) to 20/20 (100%)
    assert!(
        (result.potential_zero_copy_percentage - 100.0).abs() < 0.1,
        "Should be 100% after optimization"
    );
}

#[test]
fn test_no_suggestions_for_perfect_schema() {
    // Schema that's already 100% Concorde
    let mut source_types = BTreeMap::new();
    source_types.insert(
        "Perfect".to_string(),
        make_struct(
            "Perfect",
            vec![
                field("id", IrType::Primitive(PrimitiveType::I64), false),
                field("name", IrType::Primitive(PrimitiveType::String), false),
                field("score", IrType::Primitive(PrimitiveType::F64), false),
                field("active", IrType::Primitive(PrimitiveType::Bool), false),
            ],
        ),
    );

    let target_types = source_types.clone();

    let source = make_schema("source", source_types, vec!["Perfect".to_string()]);
    let target = make_schema("target", target_types, vec!["Perfect".to_string()]);

    let engine = EphapaxCompatibilityEngine::new();
    let optimizer = EphapaxOptimizer::new(engine);

    let result = optimizer.analyze_and_suggest(&source, &target);

    // No suggestions needed - already perfect
    assert!(
        result.suggestions.is_empty(),
        "Perfect schema should need no optimization"
    );
    assert_eq!(result.current.overall_class, TransportClass::Concorde);
    assert!(result.would_be_production_ready);
}

#[test]
fn test_deeply_nested_container_optimization() {
    // Vec<Option<Vec<i64>>> vs Vec<Option<Vec<i32>>>
    let inner_source = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
        PrimitiveType::I64,
    ))));
    let mid_source = IrType::Container(ContainerType::Option(Box::new(inner_source)));
    let outer_source = IrType::Container(ContainerType::Vec(Box::new(mid_source)));

    let inner_target = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
        PrimitiveType::I32,
    ))));
    let mid_target = IrType::Container(ContainerType::Option(Box::new(inner_target)));
    let outer_target = IrType::Container(ContainerType::Vec(Box::new(mid_target)));

    let mut source_types = BTreeMap::new();
    source_types.insert(
        "Nested".to_string(),
        make_struct("Nested", vec![field("data", outer_source, false)]),
    );

    let mut target_types = BTreeMap::new();
    target_types.insert(
        "Nested".to_string(),
        make_struct("Nested", vec![field("data", outer_target, false)]),
    );

    let source = make_schema("source", source_types, vec!["Nested".to_string()]);
    let target = make_schema("target", target_types, vec!["Nested".to_string()]);

    let engine = EphapaxCompatibilityEngine::new();
    let optimizer = EphapaxOptimizer::new(engine);

    let result = optimizer.analyze_and_suggest(&source, &target);

    // Should detect narrowing in deeply nested container
    assert_eq!(
        result.current.overall_class,
        TransportClass::Wheelbarrow,
        "Deeply nested narrowing should be Wheelbarrow"
    );

    // Should suggest widening
    assert!(
        !result.suggestions.is_empty(),
        "Should have suggestions for nested narrowing"
    );
}

#[test]
fn test_suggestion_impact_sorting() {
    // Schema with multiple fields needing optimization
    let mut source_types = BTreeMap::new();
    source_types.insert(
        "Multi".to_string(),
        make_struct(
            "Multi",
            vec![
                field("a", IrType::Primitive(PrimitiveType::I64), false),
                field("b", IrType::Primitive(PrimitiveType::I64), false),
                field("c", IrType::Primitive(PrimitiveType::I64), false),
                field("d", IrType::Primitive(PrimitiveType::I64), false),
            ],
        ),
    );

    let mut target_types = BTreeMap::new();
    target_types.insert(
        "Multi".to_string(),
        make_struct(
            "Multi",
            vec![
                field("a", IrType::Primitive(PrimitiveType::I32), false),
                field("b", IrType::Primitive(PrimitiveType::I32), false),
                field("c", IrType::Primitive(PrimitiveType::I32), false),
                field("d", IrType::Primitive(PrimitiveType::I64), false), // Match
            ],
        ),
    );

    let source = make_schema("source", source_types, vec!["Multi".to_string()]);
    let target = make_schema("target", target_types, vec!["Multi".to_string()]);

    let engine = EphapaxCompatibilityEngine::new();
    let optimizer = EphapaxOptimizer::new(engine);

    let result = optimizer.analyze_and_suggest(&source, &target);

    // Should suggest widening for a, b, c (optimizer also generates "make optional" suggestions)
    // Total: 3 widen + 3 make-optional = 6 suggestions
    assert!(
        result.suggestions.len() >= 3,
        "Should have at least 3 suggestions"
    );

    // Filter for widening suggestions only
    let widen_suggestions: Vec<_> = result
        .suggestions
        .iter()
        .filter(|s| matches!(s.kind, SuggestionKind::WidenType { .. }))
        .collect();

    assert_eq!(
        widen_suggestions.len(),
        3,
        "Should suggest widening 3 fields"
    );

    // All widening suggestions should have equal impact (25% each for 4-field struct)
    for suggestion in &widen_suggestions {
        assert!(
            (suggestion.impact - 25.0).abs() < 0.1,
            "Each field should have 25% impact"
        );
    }

    // Verify sorting (all suggestions, not just widening)
    for i in 1..result.suggestions.len() {
        assert!(
            result.suggestions[i - 1].impact >= result.suggestions[i].impact,
            "Suggestions should be sorted by impact (descending)"
        );
    }
}
