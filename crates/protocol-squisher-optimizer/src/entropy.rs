// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <jonathan.jewell@open.ac.uk>

//! Information-theoretic analysis for protocol optimization.
//!
//! Applies Shannon entropy and rate-distortion theory to quantify how much
//! optimization potential exists in a schema. Key metrics:
//!
//! - **Field entropy**: bits of information a field actually carries
//! - **Allocated bits**: bits the wire format allocates for the field
//! - **Waste ratio**: (allocated - entropy) / allocated
//! - **Squishability**: aggregate waste across a schema
//!
//! ## Theory
//!
//! Shannon's source coding theorem says you can't compress below entropy H(X).
//! For protocol fields, we can estimate H(X) from type constraints:
//!
//! - A `bool` has H = 1 bit, but most formats allocate 8 bits (7 bits wasted)
//! - A `u8` with range [0, 3] has H = 2 bits but uses 8 bits (6 bits wasted)
//! - A `String` with known set of values has H = log2(|set|) bits
//!
//! The gap between entropy and allocated bits is the optimization opportunity.

use protocol_squisher_ir::{
    Constraint, ContainerType, FieldDef, IrSchema, IrType, PrimitiveType, StructDef, TypeDef,
};

/// Entropy analysis for a single field.
#[derive(Debug, Clone)]
pub struct FieldEntropy {
    /// Field name
    pub field_name: String,
    /// Estimated Shannon entropy in bits
    pub entropy_bits: f64,
    /// Bits allocated by the wire format
    pub allocated_bits: f64,
    /// Wasted bits (allocated - entropy), always >= 0
    pub wasted_bits: f64,
    /// Waste ratio (0.0 = perfectly efficient, 1.0 = all waste)
    pub waste_ratio: f64,
    /// Explanation of how entropy was estimated
    pub reasoning: String,
}

/// Entropy analysis for a complete schema.
#[derive(Debug, Clone)]
pub struct SchemaEntropy {
    /// Schema name
    pub schema_name: String,
    /// Per-field entropy analysis
    pub fields: Vec<FieldEntropy>,
    /// Total entropy across all fields (bits)
    pub total_entropy_bits: f64,
    /// Total allocated bits across all fields
    pub total_allocated_bits: f64,
    /// Overall waste ratio
    pub overall_waste_ratio: f64,
    /// Theoretical compression ratio (allocated / entropy)
    pub theoretical_compression_ratio: f64,
    /// Most wasteful fields (sorted by wasted_bits descending)
    pub optimization_targets: Vec<String>,
}

/// Analyze the entropy of a schema.
pub fn analyze_schema_entropy(schema: &IrSchema) -> SchemaEntropy {
    let mut all_fields = Vec::new();

    for type_def in schema.types.values() {
        if let TypeDef::Struct(s) = type_def {
            let mut fields = analyze_struct_entropy(s);
            all_fields.append(&mut fields);
        }
    }

    let total_entropy: f64 = all_fields.iter().map(|f| f.entropy_bits).sum();
    let total_allocated: f64 = all_fields.iter().map(|f| f.allocated_bits).sum();

    let overall_waste_ratio = if total_allocated > 0.0 {
        (total_allocated - total_entropy) / total_allocated
    } else {
        0.0
    };

    let theoretical_compression_ratio = if total_entropy > 0.0 {
        total_allocated / total_entropy
    } else {
        1.0
    };

    // Find top optimization targets
    let mut sorted = all_fields.clone();
    sorted.sort_by(|a, b| b.wasted_bits.total_cmp(&a.wasted_bits));
    let optimization_targets: Vec<String> = sorted
        .iter()
        .filter(|f| f.wasted_bits > 0.0)
        .take(5)
        .map(|f| format!("{} ({:.1} bits wasted)", f.field_name, f.wasted_bits))
        .collect();

    SchemaEntropy {
        schema_name: schema.name.clone(),
        fields: all_fields,
        total_entropy_bits: total_entropy,
        total_allocated_bits: total_allocated,
        overall_waste_ratio,
        theoretical_compression_ratio,
        optimization_targets,
    }
}

/// Analyze entropy for all fields in a struct.
fn analyze_struct_entropy(s: &StructDef) -> Vec<FieldEntropy> {
    s.fields.iter().map(analyze_field_entropy).collect()
}

/// Analyze entropy for a single field.
fn analyze_field_entropy(field: &FieldDef) -> FieldEntropy {
    let (entropy_bits, allocated_bits, reasoning) =
        estimate_type_entropy(&field.ty, &field.constraints);

    // Optional fields have additional entropy: 1 bit for presence/absence
    let (entropy_bits, allocated_bits, reasoning) = if field.optional {
        (
            entropy_bits + 1.0,
            allocated_bits + 8.0, // Most formats use at least a byte for optionality
            format!(
                "{} + 1 bit optionality (8 bits allocated for presence tag)",
                reasoning
            ),
        )
    } else {
        (entropy_bits, allocated_bits, reasoning)
    };

    let wasted_bits = (allocated_bits - entropy_bits).max(0.0);
    let waste_ratio = if allocated_bits > 0.0 {
        wasted_bits / allocated_bits
    } else {
        0.0
    };

    FieldEntropy {
        field_name: field.name.clone(),
        entropy_bits,
        allocated_bits,
        wasted_bits,
        waste_ratio,
        reasoning,
    }
}

/// Estimate entropy and allocation for an IR type.
///
/// Returns (entropy_bits, allocated_bits, reasoning).
fn estimate_type_entropy(ty: &IrType, constraints: &[Constraint]) -> (f64, f64, String) {
    match ty {
        IrType::Primitive(p) => estimate_primitive_entropy(p, constraints),
        IrType::Container(c) => estimate_container_entropy(c, constraints),
        IrType::Reference(_) => (64.0, 64.0, "reference type (estimated)".to_string()),
        IrType::Special(_) => (0.0, 0.0, "special type".to_string()),
    }
}

/// Estimate entropy for primitive types.
fn estimate_primitive_entropy(p: &PrimitiveType, constraints: &[Constraint]) -> (f64, f64, String) {
    // Check for range constraints that reduce entropy
    let range_constraint = constraints.iter().find_map(|c| {
        if let Constraint::Range { min, max } = c {
            Some((min.as_f64(), max.as_f64()))
        } else {
            None
        }
    });

    match p {
        PrimitiveType::Bool => (
            1.0,
            8.0,
            "bool: 1 bit entropy, 8 bits allocated".to_string(),
        ),

        PrimitiveType::I8 | PrimitiveType::U8 => {
            if let Some((min, max)) = range_constraint {
                let range = (max - min + 1.0).max(1.0);
                let entropy = range.log2();
                (
                    entropy,
                    8.0,
                    format!(
                        "u8 with range [{}, {}]: {:.1} bits entropy",
                        min, max, entropy
                    ),
                )
            } else {
                (8.0, 8.0, "u8/i8: full 8-bit range".to_string())
            }
        },

        PrimitiveType::I16 | PrimitiveType::U16 => {
            if let Some((min, max)) = range_constraint {
                let range = (max - min + 1.0).max(1.0);
                let entropy = range.log2();
                (
                    entropy,
                    16.0,
                    format!(
                        "u16 with range [{}, {}]: {:.1} bits entropy",
                        min, max, entropy
                    ),
                )
            } else {
                (16.0, 16.0, "u16/i16: full 16-bit range".to_string())
            }
        },

        PrimitiveType::I32 | PrimitiveType::U32 => {
            if let Some((min, max)) = range_constraint {
                let range = (max - min + 1.0).max(1.0);
                let entropy = range.log2();
                (
                    entropy,
                    32.0,
                    format!(
                        "u32 with range [{}, {}]: {:.1} bits entropy",
                        min, max, entropy
                    ),
                )
            } else {
                (32.0, 32.0, "u32/i32: full 32-bit range".to_string())
            }
        },

        PrimitiveType::I64 | PrimitiveType::U64 => {
            if let Some((min, max)) = range_constraint {
                let range = (max - min + 1.0).max(1.0);
                let entropy = range.log2();
                (
                    entropy,
                    64.0,
                    format!(
                        "u64 with range [{}, {}]: {:.1} bits entropy",
                        min, max, entropy
                    ),
                )
            } else {
                (64.0, 64.0, "u64/i64: full 64-bit range".to_string())
            }
        },

        PrimitiveType::I128 | PrimitiveType::U128 => {
            (128.0, 128.0, "i128/u128: full 128-bit range".to_string())
        },

        PrimitiveType::F32 => (32.0, 32.0, "f32: IEEE 754 single precision".to_string()),
        PrimitiveType::F64 => (64.0, 64.0, "f64: IEEE 754 double precision".to_string()),

        PrimitiveType::String => {
            // Check for max length constraint
            let max_len = constraints.iter().find_map(|c| {
                if let Constraint::MaxLength(n) = c {
                    Some(*n)
                } else {
                    None
                }
            });
            match max_len {
                Some(n) if n <= 255 => {
                    let bits = (n as f64) * 8.0;
                    (
                        bits * 0.6,
                        bits + 16.0,
                        format!(
                            "string(max {}): ~{:.0} bits entropy (English text ~4.7 bits/char)",
                            n,
                            bits * 0.6
                        ),
                    )
                },
                _ => (
                    80.0,
                    128.0,
                    "string: ~80 bits entropy estimate (10 char avg)".to_string(),
                ),
            }
        },

        PrimitiveType::Bytes => (64.0, 128.0, "bytes: variable length".to_string()),
        PrimitiveType::Char => (
            8.0,
            16.0,
            "char: ~8 bits entropy in 16-bit allocation".to_string(),
        ),
        PrimitiveType::DateTime => (
            40.0,
            64.0,
            "datetime: ~40 bits entropy (reasonable range)".to_string(),
        ),
        PrimitiveType::Date => (
            16.0,
            32.0,
            "date: ~16 bits entropy (year range)".to_string(),
        ),
        PrimitiveType::Time => (17.0, 32.0, "time: ~17 bits (86400 seconds)".to_string()),
        PrimitiveType::Duration => (32.0, 64.0, "duration: wide range".to_string()),
        PrimitiveType::Uuid => (
            122.0,
            128.0,
            "uuid: 122 random bits in 128-bit allocation".to_string(),
        ),
        PrimitiveType::Decimal => (64.0, 128.0, "decimal: variable precision".to_string()),
        PrimitiveType::BigInt => (64.0, 128.0, "bigint: variable size".to_string()),
    }
}

/// Estimate entropy for container types.
fn estimate_container_entropy(c: &ContainerType, constraints: &[Constraint]) -> (f64, f64, String) {
    match c {
        ContainerType::Option(inner) => {
            let (inner_entropy, inner_alloc, _) = estimate_type_entropy(inner, constraints);
            // 1 bit for Some/None, plus inner entropy weighted by expected presence
            let entropy = 1.0 + inner_entropy * 0.7; // assume 70% present
            let allocated = 8.0 + inner_alloc; // tag byte + inner
            (
                entropy,
                allocated,
                format!("Option: 1 bit presence + {:.0} bits inner", inner_entropy),
            )
        },
        ContainerType::Vec(inner) => {
            let (inner_entropy, inner_alloc, _) = estimate_type_entropy(inner, constraints);
            // Estimate 10 elements by default
            let count = 10.0;
            let entropy = 4.0 + inner_entropy * count; // ~4 bits for length
            let allocated = 32.0 + inner_alloc * count; // length prefix + elements
            (
                entropy,
                allocated,
                format!("Vec: ~{:.0} elements x {:.0} bits", count, inner_entropy),
            )
        },
        ContainerType::Array(inner, size) => {
            let (inner_entropy, inner_alloc, _) = estimate_type_entropy(inner, constraints);
            let n = *size as f64;
            (
                inner_entropy * n,
                inner_alloc * n,
                format!("Array[{}]: {} x {:.0} bits", size, size, inner_entropy),
            )
        },
        ContainerType::Set(inner) => {
            let (inner_entropy, inner_alloc, _) = estimate_type_entropy(inner, constraints);
            let count = 8.0;
            (
                inner_entropy * count,
                inner_alloc * count + 32.0,
                format!("Set: ~{:.0} unique elements", count),
            )
        },
        ContainerType::Map(key, val) => {
            let (key_entropy, key_alloc, _) = estimate_type_entropy(key, constraints);
            let (val_entropy, val_alloc, _) = estimate_type_entropy(val, constraints);
            let count = 8.0;
            let entropy = count * (key_entropy + val_entropy);
            let allocated = 32.0 + count * (key_alloc + val_alloc);
            (entropy, allocated, format!("Map: ~{:.0} entries", count))
        },
        ContainerType::Tuple(types) => {
            let mut total_entropy = 0.0;
            let mut total_alloc = 0.0;
            for t in types {
                let (e, a, _) = estimate_type_entropy(t, constraints);
                total_entropy += e;
                total_alloc += a;
            }
            (
                total_entropy,
                total_alloc,
                format!("Tuple of {} elements", types.len()),
            )
        },
        ContainerType::Result(ok, err) => {
            let (ok_entropy, ok_alloc, _) = estimate_type_entropy(ok, constraints);
            let (err_entropy, err_alloc, _) = estimate_type_entropy(err, constraints);
            // 1 bit for Ok/Err, weighted average of payloads (assume 90% Ok)
            let entropy = 1.0 + ok_entropy * 0.9 + err_entropy * 0.1;
            let allocated = 8.0 + ok_alloc.max(err_alloc);
            (
                entropy,
                allocated,
                "Result: 1 bit discriminant + payload".to_string(),
            )
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{constraints::NumberValue, *};

    fn make_field(name: &str, ty: IrType, constraints: Vec<Constraint>) -> FieldDef {
        FieldDef {
            name: name.to_string(),
            ty,
            optional: false,
            constraints,
            metadata: FieldMetadata::default(),
        }
    }

    #[test]
    fn test_bool_entropy() {
        let field = make_field("flag", IrType::Primitive(PrimitiveType::Bool), vec![]);
        let result = analyze_field_entropy(&field);
        assert_eq!(result.entropy_bits, 1.0);
        assert_eq!(result.allocated_bits, 8.0);
        assert_eq!(result.wasted_bits, 7.0);
    }

    #[test]
    fn test_constrained_u32_entropy() {
        let field = make_field(
            "status",
            IrType::Primitive(PrimitiveType::U32),
            vec![Constraint::Range {
                min: NumberValue::Integer(0),
                max: NumberValue::Integer(3),
            }],
        );
        let result = analyze_field_entropy(&field);
        assert!(result.entropy_bits < 3.0); // log2(4) = 2
        assert_eq!(result.allocated_bits, 32.0);
        assert!(result.wasted_bits > 29.0); // 32 - 2 = 30
    }

    #[test]
    fn test_full_range_no_waste() {
        let field = make_field("data", IrType::Primitive(PrimitiveType::U64), vec![]);
        let result = analyze_field_entropy(&field);
        assert_eq!(result.entropy_bits, 64.0);
        assert_eq!(result.allocated_bits, 64.0);
        assert_eq!(result.wasted_bits, 0.0);
        assert_eq!(result.waste_ratio, 0.0);
    }

    #[test]
    fn test_uuid_efficiency() {
        let field = make_field("id", IrType::Primitive(PrimitiveType::Uuid), vec![]);
        let result = analyze_field_entropy(&field);
        assert_eq!(result.entropy_bits, 122.0); // 6 bits are version/variant
        assert_eq!(result.allocated_bits, 128.0);
        assert_eq!(result.wasted_bits, 6.0);
    }

    #[test]
    fn test_optional_field_adds_presence_bit() {
        let mut field = make_field("email", IrType::Primitive(PrimitiveType::String), vec![]);
        let required = analyze_field_entropy(&field);

        field.optional = true;
        let optional = analyze_field_entropy(&field);

        assert!(optional.entropy_bits > required.entropy_bits);
        assert!(optional.allocated_bits > required.allocated_bits);
    }

    #[test]
    fn test_schema_entropy() {
        let mut schema = IrSchema::new("test", "test");
        schema.add_type(
            "Record".to_string(),
            TypeDef::Struct(StructDef {
                name: "Record".to_string(),
                fields: vec![
                    make_field("flag", IrType::Primitive(PrimitiveType::Bool), vec![]),
                    make_field("id", IrType::Primitive(PrimitiveType::U64), vec![]),
                    make_field(
                        "status",
                        IrType::Primitive(PrimitiveType::U8),
                        vec![Constraint::Range {
                            min: NumberValue::Integer(0),
                            max: NumberValue::Integer(7),
                        }],
                    ),
                ],
                metadata: TypeMetadata::default(),
            }),
        );

        let result = analyze_schema_entropy(&schema);
        assert_eq!(result.fields.len(), 3);
        assert!(result.total_entropy_bits < result.total_allocated_bits);
        assert!(result.overall_waste_ratio > 0.0);
        assert!(result.theoretical_compression_ratio > 1.0);
        assert!(!result.optimization_targets.is_empty());
    }

    #[test]
    fn test_waste_ratio_bounds() {
        let field = make_field("x", IrType::Primitive(PrimitiveType::Bool), vec![]);
        let result = analyze_field_entropy(&field);
        assert!(result.waste_ratio >= 0.0);
        assert!(result.waste_ratio <= 1.0);
    }

    #[test]
    fn test_vec_entropy_scales_with_elements() {
        let inner = IrType::Primitive(PrimitiveType::I32);
        let vec_type = IrType::Container(ContainerType::Vec(Box::new(inner)));
        let field = make_field("values", vec_type, vec![]);
        let result = analyze_field_entropy(&field);
        // Vec of i32 should have significant entropy
        assert!(result.entropy_bits > 100.0);
    }
}
