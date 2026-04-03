// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Property-based tests for the Shape IR.
//!
//! These tests verify algebraic properties that must hold for all shapes,
//! not just specific examples. They use proptest to generate random shapes
//! and check that invariants are maintained.

use crate::compare::compare;
use crate::compose::compose;
use crate::information::information_content;
use crate::*;
use proptest::prelude::*;

// ---------------------------------------------------------------------------
// Shape generators
// ---------------------------------------------------------------------------

/// Generate a random AtomKind (excluding Enum for simplicity).
fn arb_atom_kind() -> impl Strategy<Value = AtomKind> {
    prop_oneof![
        Just(AtomKind::Bool),
        Just(AtomKind::U8),
        Just(AtomKind::U16),
        Just(AtomKind::U32),
        Just(AtomKind::U64),
        Just(AtomKind::I8),
        Just(AtomKind::I16),
        Just(AtomKind::I32),
        Just(AtomKind::I64),
        Just(AtomKind::F32),
        Just(AtomKind::F64),
        Just(AtomKind::String),
    ]
}

/// Generate a random leaf shape (atom or unit).
fn arb_leaf_shape() -> impl Strategy<Value = Shape> {
    prop_oneof![Just(Shape::Unit), arb_atom_kind().prop_map(Shape::Atom),]
}

/// Generate a random shape up to a given depth.
fn arb_shape(depth: u32) -> impl Strategy<Value = Shape> {
    if depth == 0 {
        arb_leaf_shape().boxed()
    } else {
        prop_oneof![
            arb_leaf_shape(),
            (arb_shape(depth - 1)).prop_map(Shape::optional),
            (arb_shape(depth - 1)).prop_map(Shape::sequence),
            ("[a-z]{1,8}", arb_shape(depth - 1), arb_shape(depth - 1),)
                .prop_map(|(name, left, right)| Shape::product(name.as_str(), left, right)),
        ]
        .boxed()
    }
}

// ---------------------------------------------------------------------------
// Property tests
// ---------------------------------------------------------------------------

proptest! {
    /// Comparing a shape to itself always yields Concorde.
    #[test]
    fn self_comparison_is_concorde(shape in arb_shape(2)) {
        let m = compare(&shape, &shape);
        prop_assert_eq!(m.transport_class, TransportClass::Concorde);
    }

    /// Information content min_bits <= max_bits (when max_bits is bounded).
    #[test]
    fn min_bits_leq_max_bits(shape in arb_shape(2)) {
        let info = information_content(&shape);
        if let Some(max) = info.max_bits {
            prop_assert!(info.min_bits <= max, "min {} > max {}", info.min_bits, max);
        }
    }

    /// Fixed-size shapes have min_bits == max_bits.
    #[test]
    fn fixed_size_implies_equal_bounds(shape in arb_shape(2)) {
        let info = information_content(&shape);
        if info.is_fixed_size {
            prop_assert_eq!(info.min_bits, info.max_bits.unwrap_or(0));
        }
    }

    /// Composing a morphism with its reverse gives Economy or worse
    /// (because narrowing after widening loses info about the padding).
    #[test]
    fn roundtrip_compose_class(
        a_kind in prop_oneof![Just(AtomKind::I32), Just(AtomKind::I64)],
        b_kind in prop_oneof![Just(AtomKind::I64), Just(AtomKind::I128)],
    ) {
        let a = Shape::Atom(a_kind.clone());
        let b = Shape::Atom(b_kind.clone());
        let f = compare(&a, &b);
        let g = compare(&b, &a);

        if let Ok(h) = compose(&f, &g) {
            // Roundtrip class should be worst of forward and backward
            let expected_worst = TransportClass::compose(f.transport_class, g.transport_class);
            prop_assert_eq!(h.transport_class, expected_worst);
        }
    }

    /// Transport class composition is commutative.
    #[test]
    fn transport_compose_commutative(
        a in prop_oneof![
            Just(TransportClass::Concorde),
            Just(TransportClass::Business),
            Just(TransportClass::Economy),
            Just(TransportClass::Wheelbarrow),
        ],
        b in prop_oneof![
            Just(TransportClass::Concorde),
            Just(TransportClass::Business),
            Just(TransportClass::Economy),
            Just(TransportClass::Wheelbarrow),
        ],
    ) {
        prop_assert_eq!(
            TransportClass::compose(a, b),
            TransportClass::compose(b, a)
        );
    }

    /// Linearity meet is commutative.
    #[test]
    fn linearity_meet_commutative(
        a in prop_oneof![
            Just(Linearity::Unrestricted),
            Just(Linearity::Linear),
            Just(Linearity::Affine),
            Just(Linearity::Relevant),
        ],
        b in prop_oneof![
            Just(Linearity::Unrestricted),
            Just(Linearity::Linear),
            Just(Linearity::Affine),
            Just(Linearity::Relevant),
        ],
    ) {
        prop_assert_eq!(Linearity::meet(a, b), Linearity::meet(b, a));
    }

    /// Linearity meet is associative.
    #[test]
    fn linearity_meet_associative(
        a in prop_oneof![
            Just(Linearity::Unrestricted),
            Just(Linearity::Linear),
            Just(Linearity::Affine),
            Just(Linearity::Relevant),
        ],
        b in prop_oneof![
            Just(Linearity::Unrestricted),
            Just(Linearity::Linear),
            Just(Linearity::Affine),
            Just(Linearity::Relevant),
        ],
        c in prop_oneof![
            Just(Linearity::Unrestricted),
            Just(Linearity::Linear),
            Just(Linearity::Affine),
            Just(Linearity::Relevant),
        ],
    ) {
        let left = Linearity::meet(Linearity::meet(a, b), c);
        let right = Linearity::meet(a, Linearity::meet(b, c));
        prop_assert_eq!(left, right);
    }

    /// Unrestricted is the identity for linearity meet.
    #[test]
    fn unrestricted_is_meet_identity(
        a in prop_oneof![
            Just(Linearity::Unrestricted),
            Just(Linearity::Linear),
            Just(Linearity::Affine),
            Just(Linearity::Relevant),
        ],
    ) {
        prop_assert_eq!(Linearity::meet(Linearity::Unrestricted, a), a);
        prop_assert_eq!(Linearity::meet(a, Linearity::Unrestricted), a);
    }

    // -----------------------------------------------------------------------
    // Transport class semilattice laws
    // -----------------------------------------------------------------------

    /// Transport class composition is associative: (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c).
    #[test]
    fn transport_compose_associative(
        a in arb_transport_class(),
        b in arb_transport_class(),
        c in arb_transport_class(),
    ) {
        let left = TransportClass::compose(TransportClass::compose(a, b), c);
        let right = TransportClass::compose(a, TransportClass::compose(b, c));
        prop_assert_eq!(left, right);
    }

    /// Transport class composition is idempotent: a ⊔ a = a.
    #[test]
    fn transport_compose_idempotent(a in arb_transport_class()) {
        prop_assert_eq!(TransportClass::compose(a, a), a);
    }

    /// Concorde is the identity element: Concorde ⊔ a = a.
    #[test]
    fn concorde_is_compose_identity(a in arb_transport_class()) {
        prop_assert_eq!(TransportClass::compose(TransportClass::Concorde, a), a);
        prop_assert_eq!(TransportClass::compose(a, TransportClass::Concorde), a);
    }

    /// Wheelbarrow is the absorbing element: Wheelbarrow ⊔ a = Wheelbarrow.
    #[test]
    fn wheelbarrow_is_absorbing(a in arb_transport_class()) {
        prop_assert_eq!(
            TransportClass::compose(TransportClass::Wheelbarrow, a),
            TransportClass::Wheelbarrow
        );
    }

    // -----------------------------------------------------------------------
    // Product (struct) associativity
    // -----------------------------------------------------------------------

    /// Product is associative up to isomorphism: comparing
    /// {a, {b, c}} to {a, b, c} (built via struct_from) yields Concorde
    /// because struct_from already right-nests to the canonical form.
    #[test]
    fn struct_from_is_canonical(
        a_kind in arb_atom_kind(),
        b_kind in arb_atom_kind(),
        c_kind in arb_atom_kind(),
    ) {
        // struct_from always produces the same right-nested canonical form
        let s = Shape::struct_from(vec![
            ("a", Shape::Atom(a_kind.clone())),
            ("b", Shape::Atom(b_kind.clone())),
            ("c", Shape::Atom(c_kind.clone())),
        ]);

        // Manual construction should match
        let manual = Shape::product(
            "a",
            Shape::Atom(a_kind),
            Shape::product(
                "b",
                Shape::Atom(b_kind),
                Shape::product("c", Shape::Atom(c_kind), Shape::Unit),
            ),
        );

        prop_assert_eq!(&s, &manual);
    }

    /// Comparing two structs with the same fields in the same order is Concorde.
    #[test]
    fn same_struct_different_construction_is_concorde(
        a_kind in arb_atom_kind(),
        b_kind in arb_atom_kind(),
    ) {
        let s1 = Shape::struct_from(vec![
            ("x", Shape::Atom(a_kind.clone())),
            ("y", Shape::Atom(b_kind.clone())),
        ]);
        let s2 = Shape::struct_from(vec![
            ("x", Shape::Atom(a_kind)),
            ("y", Shape::Atom(b_kind)),
        ]);
        let m = compare(&s1, &s2);
        prop_assert_eq!(m.transport_class, TransportClass::Concorde);
    }

    // -----------------------------------------------------------------------
    // Sum (enum) associativity
    // -----------------------------------------------------------------------

    /// enum_from produces canonical right-nested form.
    #[test]
    fn enum_from_is_canonical(
        a_kind in arb_atom_kind(),
        b_kind in arb_atom_kind(),
    ) {
        let e = Shape::enum_from(vec![
            ("A", Shape::Atom(a_kind.clone())),
            ("B", Shape::Atom(b_kind.clone())),
        ]);

        let manual = Shape::sum(
            "A",
            Shape::Atom(a_kind),
            Shape::sum("B", Shape::Atom(b_kind), Shape::Unit),
        );

        prop_assert_eq!(&e, &manual);
    }

    /// Comparing two enums with the same variants in the same order is Concorde.
    #[test]
    fn same_enum_is_concorde(
        a_kind in arb_atom_kind(),
        b_kind in arb_atom_kind(),
    ) {
        let e1 = Shape::enum_from(vec![
            ("A", Shape::Atom(a_kind.clone())),
            ("B", Shape::Atom(b_kind.clone())),
        ]);
        let e2 = Shape::enum_from(vec![
            ("A", Shape::Atom(a_kind)),
            ("B", Shape::Atom(b_kind)),
        ]);
        let m = compare(&e1, &e2);
        prop_assert_eq!(m.transport_class, TransportClass::Concorde);
    }

    // -----------------------------------------------------------------------
    // Morphism composition associativity
    // -----------------------------------------------------------------------

    /// Morphism composition is associative: (h ∘ g) ∘ f = h ∘ (g ∘ f).
    /// We test with a chain of atom widenings: i32 -> i64 -> i128.
    #[test]
    fn morphism_compose_associative(
        chain in prop_oneof![
            Just((AtomKind::I8, AtomKind::I16, AtomKind::I32, AtomKind::I64)),
            Just((AtomKind::U8, AtomKind::U16, AtomKind::U32, AtomKind::U64)),
            Just((AtomKind::I16, AtomKind::I32, AtomKind::I64, AtomKind::I128)),
        ],
    ) {
        let (a, b, c, d) = chain;
        let f = compare(&Shape::Atom(a), &Shape::Atom(b.clone()));
        let g = compare(&Shape::Atom(b), &Shape::Atom(c.clone()));
        let h = compare(&Shape::Atom(c), &Shape::Atom(d));

        let gf = compose(&f, &g).expect("composing f then g should succeed in associativity test");
        let hg = compose(&g, &h).expect("composing g then h should succeed in associativity test");

        let left = compose(&gf, &h).expect("composing (g∘f) then h should succeed");   // (g ∘ f) ∘ h  -- note: our compose is f then g
        let right = compose(&f, &hg).expect("composing f then (h∘g) should succeed");  // f ∘ (h ∘ g)

        prop_assert_eq!(left.transport_class, right.transport_class);
        prop_assert_eq!(left.source, right.source);
        prop_assert_eq!(left.target, right.target);
    }

    // -----------------------------------------------------------------------
    // Information content properties
    // -----------------------------------------------------------------------

    /// Product information content is additive: info(A × B) ≥ info(A) + info(B).
    #[test]
    fn product_info_is_additive(
        a_kind in arb_atom_kind(),
        b_kind in arb_atom_kind(),
    ) {
        let a = Shape::Atom(a_kind);
        let b = Shape::Atom(b_kind);
        let product = Shape::struct_from(vec![
            ("a", a.clone()),
            ("b", b.clone()),
        ]);

        let info_a = information_content(&a);
        let info_b = information_content(&b);
        let info_prod = information_content(&product);

        // min_bits of product >= sum of component min_bits
        prop_assert!(
            info_prod.min_bits >= info_a.min_bits + info_b.min_bits,
            "product min_bits {} < {} + {}",
            info_prod.min_bits, info_a.min_bits, info_b.min_bits
        );
    }

    /// Optional adds exactly 1 bit to the min_bits.
    #[test]
    fn optional_adds_one_bit(shape in arb_leaf_shape()) {
        let inner_info = information_content(&shape);
        let opt_info = information_content(&Shape::optional(shape));
        prop_assert_eq!(opt_info.min_bits, 1); // Minimum is just the presence bit
        if let (Some(inner_max), Some(opt_max)) = (inner_info.max_bits, opt_info.max_bits) {
            prop_assert_eq!(opt_max, inner_max + 1);
        }
    }

    /// Sequence is always unbounded.
    #[test]
    fn sequence_is_unbounded(shape in arb_leaf_shape()) {
        let info = information_content(&Shape::sequence(shape));
        prop_assert!(info.max_bits.is_none(), "Sequence should be unbounded");
    }
}

// ---------------------------------------------------------------------------
// Strategy helpers (outside proptest! macro for reuse)
// ---------------------------------------------------------------------------

fn arb_transport_class() -> impl Strategy<Value = TransportClass> {
    prop_oneof![
        Just(TransportClass::Concorde),
        Just(TransportClass::Business),
        Just(TransportClass::Economy),
        Just(TransportClass::Wheelbarrow),
    ]
}

// ---------------------------------------------------------------------------
// IR type generators for extraction tests
// ---------------------------------------------------------------------------

use protocol_squisher_ir::*;

/// Generate a random PrimitiveType.
fn arb_primitive_type() -> impl Strategy<Value = PrimitiveType> {
    prop_oneof![
        Just(PrimitiveType::Bool),
        Just(PrimitiveType::I8),
        Just(PrimitiveType::I16),
        Just(PrimitiveType::I32),
        Just(PrimitiveType::I64),
        Just(PrimitiveType::U8),
        Just(PrimitiveType::U16),
        Just(PrimitiveType::U32),
        Just(PrimitiveType::U64),
        Just(PrimitiveType::F32),
        Just(PrimitiveType::F64),
        Just(PrimitiveType::String),
        Just(PrimitiveType::Bytes),
        Just(PrimitiveType::Uuid),
    ]
}

/// Generate a random IrType (leaf or simple container).
fn arb_ir_type(depth: u32) -> impl Strategy<Value = IrType> {
    if depth == 0 {
        prop_oneof![
            arb_primitive_type().prop_map(IrType::Primitive),
            Just(IrType::Special(SpecialType::Unit)),
        ]
        .boxed()
    } else {
        prop_oneof![
            arb_primitive_type().prop_map(IrType::Primitive),
            arb_ir_type(depth - 1)
                .prop_map(|t| IrType::Container(ContainerType::Option(Box::new(t)))),
            arb_ir_type(depth - 1).prop_map(|t| IrType::Container(ContainerType::Vec(Box::new(t)))),
            (arb_ir_type(depth - 1), arb_ir_type(depth - 1)).prop_map(|(k, v)| {
                IrType::Container(ContainerType::Map(Box::new(k), Box::new(v)))
            }),
        ]
        .boxed()
    }
}

/// Generate a random struct schema with 1-5 fields (unique names via index).
fn arb_struct_schema(
    num_fields: std::ops::RangeInclusive<usize>,
) -> impl Strategy<Value = IrSchema> {
    proptest::collection::vec(arb_ir_type(1), num_fields).prop_map(|types| {
        let fields: Vec<FieldDef> = types
            .into_iter()
            .enumerate()
            .map(|(i, ty)| FieldDef {
                name: format!("f{}", i),
                ty,
                optional: false,
                constraints: vec![],
                metadata: FieldMetadata::default(),
            })
            .collect();
        let mut schema = IrSchema::new("test", "test-format");
        schema.add_type(
            "T".into(),
            TypeDef::Struct(StructDef {
                name: "T".into(),
                fields,
                metadata: TypeMetadata::default(),
            }),
        );
        schema.add_root("T".into());
        schema
    })
}

// ---------------------------------------------------------------------------
// Extraction property tests
// ---------------------------------------------------------------------------

proptest! {
    /// Extracted shapes always have valid information content (min <= max).
    #[test]
    fn extracted_info_min_leq_max(schema in arb_struct_schema(1..=5)) {
        let extracted = crate::extract::extract_schema(&schema);
        for shape in extracted.shapes.values() {
            let info = information_content(shape);
            if let Some(max) = info.max_bits {
                prop_assert!(info.min_bits <= max, "min {} > max {}", info.min_bits, max);
            }
        }
    }

    /// Extracting the same schema twice yields identical shapes.
    #[test]
    fn extraction_is_deterministic(schema in arb_struct_schema(1..=4)) {
        let a = crate::extract::extract_schema(&schema);
        let b = crate::extract::extract_schema(&schema);
        for (name, shape_a) in &a.shapes {
            let shape_b = &b.shapes[name];
            prop_assert_eq!(shape_a, shape_b);
        }
    }

    /// Self-comparison of extracted shapes always yields Concorde.
    #[test]
    fn extracted_self_compare_is_concorde(schema in arb_struct_schema(1..=4)) {
        let extracted = crate::extract::extract_schema(&schema);
        for shape in extracted.shapes.values() {
            let m = compare(shape, shape);
            prop_assert_eq!(
                m.transport_class,
                TransportClass::Concorde,
                "Self-comparison of extracted shape should be Concorde"
            );
        }
    }

    /// Extraction preserves the number of non-skipped fields as product labels.
    #[test]
    fn extraction_preserves_field_count(
        types in proptest::collection::vec(arb_ir_type(0), 1..=6)
    ) {
        let fields: Vec<FieldDef> = types.into_iter().enumerate().map(|(i, ty)| FieldDef {
            name: format!("f{}", i),
            ty,
            optional: false,
            constraints: vec![],
            metadata: FieldMetadata::default(),
        }).collect();
        let expected_count = fields.len();

        let mut schema = IrSchema::new("test", "test");
        schema.add_type("S".into(), TypeDef::Struct(StructDef {
            name: "S".into(),
            fields,
            metadata: TypeMetadata::default(),
        }));
        schema.add_root("S".into());

        let extracted = crate::extract::extract_schema(&schema);
        let shape = &extracted.shapes["S"];
        let labels = shape.field_labels();
        prop_assert_eq!(
            labels.len(), expected_count,
            "Expected {} labels, got {}",
            expected_count, labels.len()
        );
    }

    /// Optional IR fields produce Optional shapes.
    #[test]
    fn optional_ir_fields_become_optional_shapes(prim in arb_primitive_type()) {
        let mut schema = IrSchema::new("test", "test");
        schema.add_type("O".into(), TypeDef::Struct(StructDef {
            name: "O".into(),
            fields: vec![FieldDef {
                name: "f".into(),
                ty: IrType::Primitive(prim),
                optional: true,
                constraints: vec![],
                metadata: FieldMetadata::default(),
            }],
            metadata: TypeMetadata::default(),
        }));
        schema.add_root("O".into());

        let extracted = crate::extract::extract_schema(&schema);
        let shape = &extracted.shapes["O"];

        // The field should be Optional
        match shape {
            Shape::Product { left, .. } => {
                prop_assert!(
                    matches!(left.as_ref(), Shape::Optional(_)),
                    "Optional IR field should produce Optional shape, got {:?}",
                    left
                );
            }
            other => prop_assert!(false, "Expected Product, got {:?}", other),
        }
    }

    /// Comparing extracted shapes from two schemas with widened fields yields Business.
    #[test]
    fn widened_extraction_is_business(
        prim in prop_oneof![
            Just((PrimitiveType::I32, PrimitiveType::I64)),
            Just((PrimitiveType::U16, PrimitiveType::U32)),
            Just((PrimitiveType::F32, PrimitiveType::F64)),
            Just((PrimitiveType::I8, PrimitiveType::I16)),
        ]
    ) {
        let (narrow, wide) = prim;
        let make_schema = |p: PrimitiveType| {
            let mut schema = IrSchema::new("test", "test");
            schema.add_type("W".into(), TypeDef::Struct(StructDef {
                name: "W".into(),
                fields: vec![FieldDef {
                    name: "v".into(),
                    ty: IrType::Primitive(p),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
                metadata: TypeMetadata::default(),
            }));
            schema.add_root("W".into());
            schema
        };

        let a = crate::extract::extract_schema(&make_schema(narrow));
        let b = crate::extract::extract_schema(&make_schema(wide));

        let m = compare(&a.shapes["W"], &b.shapes["W"]);
        prop_assert_eq!(
            m.transport_class,
            TransportClass::Business,
            "Widening should be Business"
        );
    }

    /// Vec<T> in IR extracts to Sequence(T) which is unbounded.
    #[test]
    fn vec_extracts_to_unbounded_sequence(prim in arb_primitive_type()) {
        let mut schema = IrSchema::new("test", "test");
        schema.add_type("V".into(), TypeDef::Struct(StructDef {
            name: "V".into(),
            fields: vec![FieldDef {
                name: "items".into(),
                ty: IrType::Container(ContainerType::Vec(Box::new(
                    IrType::Primitive(prim),
                ))),
                optional: false,
                constraints: vec![],
                metadata: FieldMetadata::default(),
            }],
            metadata: TypeMetadata::default(),
        }));
        schema.add_root("V".into());

        let extracted = crate::extract::extract_schema(&schema);
        let shape = &extracted.shapes["V"];
        let info = information_content(shape);
        prop_assert!(
            info.max_bits.is_none(),
            "Struct containing Vec should be unbounded"
        );
    }

    // -----------------------------------------------------------------------
    // Category laws (property-based)
    // -----------------------------------------------------------------------

    /// Identity morphism composes as left identity: id_B ∘ f has same class as f.
    #[test]
    fn category_left_identity(
        a_kind in arb_atom_kind(),
        b_kind in arb_atom_kind(),
    ) {
        let a = Shape::Atom(a_kind);
        let b = Shape::Atom(b_kind);
        let f = compare(&a, &b);
        let id_b = crate::morphism::Morphism::identity(b);

        if let Ok(composed) = crate::compose::compose(&f, &id_b) {
            prop_assert_eq!(composed.transport_class, f.transport_class);
        }
    }

    /// Identity morphism composes as right identity: f ∘ id_A has same class as f.
    #[test]
    fn category_right_identity(
        a_kind in arb_atom_kind(),
        b_kind in arb_atom_kind(),
    ) {
        let a = Shape::Atom(a_kind);
        let b = Shape::Atom(b_kind);
        let f = compare(&a, &b);
        let id_a = crate::morphism::Morphism::identity(a);

        if let Ok(composed) = crate::compose::compose(&id_a, &f) {
            prop_assert_eq!(composed.transport_class, f.transport_class);
        }
    }

    /// Map<K,V> in IR extracts to Map shape which is unbounded.
    #[test]
    fn map_extracts_to_unbounded(
        key_prim in arb_primitive_type(),
        val_prim in arb_primitive_type(),
    ) {
        let mut schema = IrSchema::new("test", "test");
        schema.add_type("M".into(), TypeDef::Struct(StructDef {
            name: "M".into(),
            fields: vec![FieldDef {
                name: "data".into(),
                ty: IrType::Container(ContainerType::Map(
                    Box::new(IrType::Primitive(key_prim)),
                    Box::new(IrType::Primitive(val_prim)),
                )),
                optional: false,
                constraints: vec![],
                metadata: FieldMetadata::default(),
            }],
            metadata: TypeMetadata::default(),
        }));
        schema.add_root("M".into());

        let extracted = crate::extract::extract_schema(&schema);
        let shape = &extracted.shapes["M"];
        let info = information_content(shape);
        prop_assert!(
            info.max_bits.is_none(),
            "Struct containing Map should be unbounded"
        );
    }

    // -----------------------------------------------------------------------
    // Pathfinding property tests
    // -----------------------------------------------------------------------

    /// Pathfinding: find_path(a, a) always returns empty path (identity).
    #[test]
    fn pathfinding_self_is_empty(kind in arb_atom_kind()) {
        let mut cat = crate::category::ShapeCategory::new();
        cat.add_object("x", Shape::Atom(kind));
        let path = cat.find_path("x", "x").expect("self-path should always be found");
        prop_assert!(path.is_empty(), "Self-path should be empty, got {:?}", path);
    }

    /// Pathfinding: a direct edge always yields a 1-hop path.
    #[test]
    fn pathfinding_direct_is_one_hop(
        a_kind in arb_atom_kind(),
        b_kind in arb_atom_kind(),
    ) {
        let a = Shape::Atom(a_kind);
        let b = Shape::Atom(b_kind);
        let mut cat = crate::category::ShapeCategory::new();
        cat.add_object("a", a.clone());
        cat.add_object("b", b.clone());
        cat.add_arrow("a", "b", compare(&a, &b));

        let path = cat.find_path("a", "b").expect("direct path a->b should be found");
        prop_assert_eq!(path.len(), 1, "Direct edge should give 1-hop path");
        prop_assert_eq!(&path[0].0, "a");
        prop_assert_eq!(&path[0].1, "b");
    }

    /// Pathfinding: the composed transport class of a path is never better
    /// than the worst individual edge in the path.
    #[test]
    fn pathfinding_composed_class_is_worst_edge(
        chain in prop_oneof![
            Just((AtomKind::I8, AtomKind::I16, AtomKind::I32)),
            Just((AtomKind::U8, AtomKind::U16, AtomKind::U32)),
            Just((AtomKind::I16, AtomKind::I32, AtomKind::I64)),
        ],
    ) {
        let (a, b, c) = chain;
        let sa = Shape::Atom(a);
        let sb = Shape::Atom(b);
        let sc = Shape::Atom(c);

        let mut cat = crate::category::ShapeCategory::new();
        cat.add_object("a", sa.clone());
        cat.add_object("b", sb.clone());
        cat.add_object("c", sc.clone());

        let m_ab = compare(&sa, &sb);
        let m_bc = compare(&sb, &sc);
        cat.add_arrow("a", "b", m_ab.clone());
        cat.add_arrow("b", "c", m_bc.clone());

        let path = cat.find_path("a", "c").expect("path a->c should be found via b");
        let composed = cat.compose_path(&path).expect("composing path a->c should produce a valid morphism");

        // Composed class should be the worst of the two edges
        let expected = crate::TransportClass::compose(
            m_ab.transport_class,
            m_bc.transport_class,
        );
        prop_assert_eq!(
            composed.transport_class, expected,
            "Composed class should be max of edge classes"
        );
    }

    /// compare_all creates exactly N*(N-1) arrows for N objects.
    #[test]
    fn compare_all_arrow_count(
        kinds in proptest::collection::vec(arb_atom_kind(), 2..=5),
    ) {
        let mut cat = crate::category::ShapeCategory::new();
        for (i, kind) in kinds.iter().enumerate() {
            cat.add_object(format!("s{}", i), Shape::Atom(kind.clone()));
        }
        cat.compare_all();

        let n = kinds.len();
        prop_assert_eq!(
            cat.arrow_count(), n * (n - 1),
            "Expected {} arrows for {} objects, got {}",
            n * (n - 1), n, cat.arrow_count()
        );
    }

    /// Isomorphic pairs are symmetric: if (a,b) is listed, both a→b and b→a
    /// are Concorde.
    #[test]
    fn isomorphic_pairs_are_symmetric(kind in arb_atom_kind()) {
        let s = Shape::Atom(kind);
        let mut cat = crate::category::ShapeCategory::new();
        cat.add_object("x", s.clone());
        cat.add_object("y", s.clone());
        cat.compare_all();

        let pairs = cat.isomorphic_pairs();
        for (a, b) in &pairs {
            let forward = cat.arrow(a, b).expect("forward arrow should exist for isomorphic pair");
            let backward = cat.arrow(b, a).expect("backward arrow should exist for isomorphic pair");
            prop_assert_eq!(forward.transport_class, crate::TransportClass::Concorde);
            prop_assert_eq!(backward.transport_class, crate::TransportClass::Concorde);
        }
    }

    /// Lossless reachability: every reachable target has a lossless arrow
    /// on the path.
    #[test]
    fn lossless_reachable_targets_are_lossless(
        chain in prop_oneof![
            Just((AtomKind::I8, AtomKind::I16, AtomKind::I32)),
            Just((AtomKind::U8, AtomKind::U16, AtomKind::U32)),
        ],
    ) {
        let (a, b, c) = chain;
        let sa = Shape::Atom(a);
        let sb = Shape::Atom(b);
        let sc = Shape::Atom(c);

        let mut cat = crate::category::ShapeCategory::new();
        cat.add_object("a", sa.clone());
        cat.add_object("b", sb.clone());
        cat.add_object("c", sc.clone());

        // Widening chain a→b→c is Business (lossless)
        cat.add_arrow("a", "b", compare(&sa, &sb));
        cat.add_arrow("b", "c", compare(&sb, &sc));

        let reachable = cat.lossless_reachable("a");
        for target in &reachable {
            // Every reachable target should have a direct arrow that is lossless
            // (since we only added direct arrows, not transitive ones)
            let path = cat.find_path("a", target).expect("path from 'a' to reachable target should exist");
            for (src, tgt) in &path {
                let arrow = cat.arrow(src, tgt).expect("arrow on path should exist");
                prop_assert!(
                    arrow.is_lossless(),
                    "Arrow {}→{} on lossless path should be lossless, got {:?}",
                    src, tgt, arrow.transport_class
                );
            }
        }
    }

    /// Transport class ordering: Concorde < Business < Economy < Wheelbarrow.
    #[test]
    fn transport_class_total_order(
        a in arb_transport_class(),
        b in arb_transport_class(),
    ) {
        // The ordering is a total order: exactly one of <, =, > holds
        let cmp = a.partial_cmp(&b);
        prop_assert!(cmp.is_some(), "Transport classes should be totally ordered");
    }
}
