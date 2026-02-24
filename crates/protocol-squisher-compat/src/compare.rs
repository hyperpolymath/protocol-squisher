// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Type comparison and compatibility analysis
//!
//! Compares IR types to determine compatibility and conversion requirements.

use crate::transport::{ConversionLoss, LossKind, LossSeverity, TransportClass};
use protocol_squisher_ir::{ContainerType, IrType, PrimitiveType, SpecialType};

/// Result of comparing two types
#[derive(Debug, Clone)]
pub struct TypeComparison {
    /// The transport class for this conversion
    pub class: TransportClass,
    /// Any losses that would occur
    pub losses: Vec<ConversionLoss>,
    /// Path context for nested comparisons
    pub path: String,
}

impl TypeComparison {
    /// Create a new comparison result
    pub fn new(class: TransportClass, path: impl Into<String>) -> Self {
        Self {
            class,
            losses: Vec::new(),
            path: path.into(),
        }
    }

    /// Add a loss to this comparison
    pub fn with_loss(mut self, loss: ConversionLoss) -> Self {
        // Update class based on loss severity
        self.class = self.class.combine(loss.severity.to_transport_class());
        self.losses.push(loss);
        self
    }

    /// Combine with another comparison (nested types)
    pub fn combine(mut self, other: TypeComparison) -> Self {
        self.class = self.class.combine(other.class);
        self.losses.extend(other.losses);
        self
    }
}

/// Compare two IR types for compatibility
pub fn compare_types(source: &IrType, target: &IrType, path: &str) -> TypeComparison {
    match (source, target) {
        // Identical types
        (a, b) if a == b => TypeComparison::new(TransportClass::Concorde, path),

        // Primitive comparisons
        (IrType::Primitive(src), IrType::Primitive(tgt)) => compare_primitives(src, tgt, path),

        // Container comparisons
        (IrType::Container(src), IrType::Container(tgt)) => compare_containers(src, tgt, path),

        // Special type comparisons
        (IrType::Special(src), IrType::Special(tgt)) => compare_specials(src, tgt, path),

        // Reference comparisons (by name)
        (IrType::Reference(src), IrType::Reference(tgt)) => {
            if src == tgt {
                TypeComparison::new(TransportClass::Concorde, path)
            } else {
                // Different type names - needs resolution
                TypeComparison::new(TransportClass::BusinessClass, path).with_loss(ConversionLoss {
                    kind: LossKind::TypeCoercion,
                    path: path.to_string(),
                    description: format!("Type reference changed: {src} -> {tgt}"),
                    severity: LossSeverity::Minor,
                })
            }
        },

        // Primitive to container (wrapping)
        (IrType::Primitive(_), IrType::Container(ContainerType::Option(inner))) => {
            let inner_cmp = compare_types(source, inner, &format!("{path}.inner"));
            inner_cmp.combine(
                TypeComparison::new(TransportClass::BusinessClass, path).with_loss(
                    ConversionLoss {
                        kind: LossKind::NullabilityChanged,
                        path: path.to_string(),
                        description: "Value wrapped in Option".to_string(),
                        severity: LossSeverity::Info,
                    },
                ),
            )
        },

        // Container to primitive (unwrapping)
        (IrType::Container(ContainerType::Option(inner)), IrType::Primitive(_)) => {
            let inner_cmp = compare_types(inner, target, &format!("{path}.inner"));
            inner_cmp.combine(
                TypeComparison::new(TransportClass::Economy, path).with_loss(ConversionLoss {
                    kind: LossKind::NullabilityChanged,
                    path: path.to_string(),
                    description: "Option unwrapped (null values will fail)".to_string(),
                    severity: LossSeverity::Moderate,
                }),
            )
        },

        // Special JSON to anything (dynamic typing)
        (IrType::Special(SpecialType::Json), _) => {
            TypeComparison::new(TransportClass::Economy, path).with_loss(ConversionLoss {
                kind: LossKind::ValidationChanged,
                path: path.to_string(),
                description: "Dynamic JSON converted to typed value".to_string(),
                severity: LossSeverity::Minor,
            })
        },

        // Anything to JSON (loss of type info)
        (_, IrType::Special(SpecialType::Json)) => {
            TypeComparison::new(TransportClass::Economy, path).with_loss(ConversionLoss {
                kind: LossKind::ValidationChanged,
                path: path.to_string(),
                description: "Typed value converted to dynamic JSON".to_string(),
                severity: LossSeverity::Minor,
            })
        },

        // Incompatible types
        _ => TypeComparison::new(TransportClass::Incompatible, path).with_loss(ConversionLoss {
            kind: LossKind::TypeCoercion,
            path: path.to_string(),
            description: format!("Incompatible types: {:?} -> {:?}", source, target),
            severity: LossSeverity::Critical,
        }),
    }
}

/// Compare primitive types
fn compare_primitives(
    source: &PrimitiveType,
    target: &PrimitiveType,
    path: &str,
) -> TypeComparison {
    use PrimitiveType::*;

    // Identical primitives
    if source == target {
        return TypeComparison::new(TransportClass::Concorde, path);
    }

    match (source, target) {
        // Integer widening (lossless)
        (I8, I16 | I32 | I64 | I128)
        | (I16, I32 | I64 | I128)
        | (I32, I64 | I128)
        | (I64, I128)
        | (U8, U16 | U32 | U64 | U128 | I16 | I32 | I64 | I128)
        | (U16, U32 | U64 | U128 | I32 | I64 | I128)
        | (U32, U64 | U128 | I64 | I128)
        | (U64, U128 | I128) => TypeComparison::new(TransportClass::Concorde, path),

        // Integer narrowing (potential range loss)
        (I128, I64 | I32 | I16 | I8)
        | (I64, I32 | I16 | I8)
        | (I32, I16 | I8)
        | (I16, I8)
        | (U128, U64 | U32 | U16 | U8)
        | (U64, U32 | U16 | U8)
        | (U32, U16 | U8)
        | (U16, U8) => {
            TypeComparison::new(TransportClass::Economy, path).with_loss(ConversionLoss {
                kind: LossKind::RangeLoss,
                path: path.to_string(),
                description: format!("{source:?} narrowed to {target:?}"),
                severity: LossSeverity::Moderate,
            })
        },

        // Signed to unsigned (potential range loss)
        (I8 | I16 | I32 | I64 | I128, U8 | U16 | U32 | U64 | U128) => {
            TypeComparison::new(TransportClass::Economy, path).with_loss(ConversionLoss {
                kind: LossKind::RangeLoss,
                path: path.to_string(),
                description: "Signed to unsigned conversion (negatives will fail)".to_string(),
                severity: LossSeverity::Moderate,
            })
        },

        // Unsigned to signed narrowing
        (U128, I64 | I32 | I16 | I8) | (U64, I32 | I16 | I8) | (U32, I16 | I8) | (U16, I8) => {
            TypeComparison::new(TransportClass::Economy, path).with_loss(ConversionLoss {
                kind: LossKind::RangeLoss,
                path: path.to_string(),
                description: format!("{source:?} narrowed to {target:?}"),
                severity: LossSeverity::Moderate,
            })
        },

        // Float widening (lossless)
        (F32, F64) => TypeComparison::new(TransportClass::Concorde, path),

        // Float narrowing (precision loss)
        (F64, F32) => {
            TypeComparison::new(TransportClass::Economy, path).with_loss(ConversionLoss {
                kind: LossKind::PrecisionLoss,
                path: path.to_string(),
                description: "f64 narrowed to f32".to_string(),
                severity: LossSeverity::Minor,
            })
        },

        // Integer to float (potential precision loss for large integers)
        (I64 | I128 | U64 | U128, F32 | F64) => TypeComparison::new(TransportClass::Economy, path)
            .with_loss(ConversionLoss {
                kind: LossKind::PrecisionLoss,
                path: path.to_string(),
                description: "Large integer to float (precision loss possible)".to_string(),
                severity: LossSeverity::Minor,
            }),

        // Small integer to float (lossless)
        (I8 | I16 | I32 | U8 | U16 | U32, F64) => {
            TypeComparison::new(TransportClass::Concorde, path)
        },

        (I8 | I16 | U8 | U16, F32) => TypeComparison::new(TransportClass::Concorde, path),

        // Float to integer (truncation)
        (F32 | F64, I8 | I16 | I32 | I64 | I128 | U8 | U16 | U32 | U64 | U128) => {
            TypeComparison::new(TransportClass::Wheelbarrow, path).with_loss(ConversionLoss {
                kind: LossKind::PrecisionLoss,
                path: path.to_string(),
                description: "Float truncated to integer".to_string(),
                severity: LossSeverity::Major,
            })
        },

        // String to other string-like (generally compatible)
        (String, Char) => {
            TypeComparison::new(TransportClass::Economy, path).with_loss(ConversionLoss {
                kind: LossKind::RangeLoss,
                path: path.to_string(),
                description: "String truncated to single char".to_string(),
                severity: LossSeverity::Major,
            })
        },

        (Char, String) => TypeComparison::new(TransportClass::Concorde, path),

        // DateTime conversions
        (DateTime, Date) => {
            TypeComparison::new(TransportClass::Economy, path).with_loss(ConversionLoss {
                kind: LossKind::PrecisionLoss,
                path: path.to_string(),
                description: "DateTime truncated to Date (time lost)".to_string(),
                severity: LossSeverity::Moderate,
            })
        },

        (DateTime, Time) => {
            TypeComparison::new(TransportClass::Economy, path).with_loss(ConversionLoss {
                kind: LossKind::PrecisionLoss,
                path: path.to_string(),
                description: "DateTime truncated to Time (date lost)".to_string(),
                severity: LossSeverity::Moderate,
            })
        },

        (Date, DateTime) | (Time, DateTime) => {
            TypeComparison::new(TransportClass::BusinessClass, path).with_loss(ConversionLoss {
                kind: LossKind::DefaultLost,
                path: path.to_string(),
                description: "Missing component filled with default".to_string(),
                severity: LossSeverity::Minor,
            })
        },

        // Decimal/BigInt conversions
        (Decimal, F64) => {
            TypeComparison::new(TransportClass::Economy, path).with_loss(ConversionLoss {
                kind: LossKind::PrecisionLoss,
                path: path.to_string(),
                description: "Decimal to f64 (precision loss)".to_string(),
                severity: LossSeverity::Moderate,
            })
        },

        (BigInt, I64) => {
            TypeComparison::new(TransportClass::Economy, path).with_loss(ConversionLoss {
                kind: LossKind::RangeLoss,
                path: path.to_string(),
                description: "BigInt to i64 (range loss)".to_string(),
                severity: LossSeverity::Moderate,
            })
        },

        // Incompatible primitives
        _ => TypeComparison::new(TransportClass::Incompatible, path).with_loss(ConversionLoss {
            kind: LossKind::TypeCoercion,
            path: path.to_string(),
            description: format!("Incompatible primitives: {source:?} -> {target:?}"),
            severity: LossSeverity::Critical,
        }),
    }
}

/// Compare container types
fn compare_containers(
    source: &ContainerType,
    target: &ContainerType,
    path: &str,
) -> TypeComparison {
    match (source, target) {
        // Option comparisons
        (ContainerType::Option(src), ContainerType::Option(tgt)) => {
            compare_types(src, tgt, &format!("{path}.inner"))
        },

        // Vec comparisons
        (ContainerType::Vec(src), ContainerType::Vec(tgt)) => {
            compare_types(src, tgt, &format!("{path}[]"))
        },

        // Array to Vec (lossless)
        (ContainerType::Array(src, _), ContainerType::Vec(tgt)) => {
            compare_types(src, tgt, &format!("{path}[]"))
        },

        // Vec to Array (potential truncation)
        (ContainerType::Vec(src), ContainerType::Array(tgt, len)) => {
            let inner = compare_types(src, tgt, &format!("{path}[]"));
            inner.combine(
                TypeComparison::new(TransportClass::Economy, path).with_loss(ConversionLoss {
                    kind: LossKind::RangeLoss,
                    path: path.to_string(),
                    description: format!("Vec truncated to array of length {len}"),
                    severity: LossSeverity::Moderate,
                }),
            )
        },

        // Set comparisons
        (ContainerType::Set(src), ContainerType::Set(tgt)) => {
            compare_types(src, tgt, &format!("{path}{{}}"))
        },

        // Set to Vec (ordering added)
        (ContainerType::Set(src), ContainerType::Vec(tgt)) => {
            let inner = compare_types(src, tgt, &format!("{path}[]"));
            inner.combine(
                TypeComparison::new(TransportClass::BusinessClass, path).with_loss(
                    ConversionLoss {
                        kind: LossKind::OrderingLost,
                        path: path.to_string(),
                        description: "Set converted to Vec (arbitrary ordering)".to_string(),
                        severity: LossSeverity::Info,
                    },
                ),
            )
        },

        // Vec to Set (duplicates removed)
        (ContainerType::Vec(src), ContainerType::Set(tgt)) => {
            let inner = compare_types(src, tgt, &format!("{path}{{}}"));
            inner.combine(
                TypeComparison::new(TransportClass::Economy, path).with_loss(ConversionLoss {
                    kind: LossKind::CollectionTypeChanged,
                    path: path.to_string(),
                    description: "Vec to Set (duplicates removed)".to_string(),
                    severity: LossSeverity::Moderate,
                }),
            )
        },

        // Map comparisons
        (ContainerType::Map(sk, sv), ContainerType::Map(tk, tv)) => {
            let key_cmp = compare_types(sk, tk, &format!("{path}.key"));
            let val_cmp = compare_types(sv, tv, &format!("{path}.value"));
            key_cmp.combine(val_cmp)
        },

        // Tuple comparisons
        (ContainerType::Tuple(src), ContainerType::Tuple(tgt)) => {
            if src.len() != tgt.len() {
                return TypeComparison::new(TransportClass::Incompatible, path).with_loss(
                    ConversionLoss {
                        kind: LossKind::TypeCoercion,
                        path: path.to_string(),
                        description: format!(
                            "Tuple length mismatch: {} vs {}",
                            src.len(),
                            tgt.len()
                        ),
                        severity: LossSeverity::Critical,
                    },
                );
            }

            let mut result = TypeComparison::new(TransportClass::Concorde, path);
            for (i, (s, t)) in src.iter().zip(tgt.iter()).enumerate() {
                result = result.combine(compare_types(s, t, &format!("{path}.{i}")));
            }
            result
        },

        // Result comparisons
        (ContainerType::Result(sok, serr), ContainerType::Result(tok, terr)) => {
            let ok_cmp = compare_types(sok, tok, &format!("{path}.ok"));
            let err_cmp = compare_types(serr, terr, &format!("{path}.err"));
            ok_cmp.combine(err_cmp)
        },

        // Incompatible containers
        _ => TypeComparison::new(TransportClass::Incompatible, path).with_loss(ConversionLoss {
            kind: LossKind::TypeCoercion,
            path: path.to_string(),
            description: format!("Incompatible containers: {:?} -> {:?}", source, target),
            severity: LossSeverity::Critical,
        }),
    }
}

/// Compare special types
fn compare_specials(source: &SpecialType, target: &SpecialType, path: &str) -> TypeComparison {
    if source == target {
        return TypeComparison::new(TransportClass::Concorde, path);
    }

    match (source, target) {
        (SpecialType::Unit, SpecialType::Never) | (SpecialType::Never, SpecialType::Unit) => {
            TypeComparison::new(TransportClass::BusinessClass, path)
        },

        _ => TypeComparison::new(TransportClass::Incompatible, path).with_loss(ConversionLoss {
            kind: LossKind::TypeCoercion,
            path: path.to_string(),
            description: format!("Incompatible special types: {:?} -> {:?}", source, target),
            severity: LossSeverity::Critical,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identical_types() {
        let ty = IrType::Primitive(PrimitiveType::I32);
        let cmp = compare_types(&ty, &ty, "test");
        assert_eq!(cmp.class, TransportClass::Concorde);
        assert!(cmp.losses.is_empty());
    }

    #[test]
    fn test_integer_widening() {
        let src = IrType::Primitive(PrimitiveType::I32);
        let tgt = IrType::Primitive(PrimitiveType::I64);
        let cmp = compare_types(&src, &tgt, "test");
        assert_eq!(cmp.class, TransportClass::Concorde);
    }

    #[test]
    fn test_integer_narrowing() {
        let src = IrType::Primitive(PrimitiveType::I64);
        let tgt = IrType::Primitive(PrimitiveType::I32);
        let cmp = compare_types(&src, &tgt, "test");
        assert_eq!(cmp.class, TransportClass::Economy);
        assert!(!cmp.losses.is_empty());
    }

    #[test]
    fn test_float_precision_loss() {
        let src = IrType::Primitive(PrimitiveType::F64);
        let tgt = IrType::Primitive(PrimitiveType::F32);
        let cmp = compare_types(&src, &tgt, "test");
        assert_eq!(cmp.class, TransportClass::Economy);
    }

    #[test]
    fn test_option_inner() {
        let src = IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
            PrimitiveType::I32,
        ))));
        let tgt = IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
            PrimitiveType::I64,
        ))));
        let cmp = compare_types(&src, &tgt, "test");
        assert_eq!(cmp.class, TransportClass::Concorde);
    }

    #[test]
    fn test_vec_to_set() {
        let src = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
            PrimitiveType::String,
        ))));
        let tgt = IrType::Container(ContainerType::Set(Box::new(IrType::Primitive(
            PrimitiveType::String,
        ))));
        let cmp = compare_types(&src, &tgt, "test");
        assert_eq!(cmp.class, TransportClass::Economy);
    }

    #[test]
    fn test_incompatible() {
        let src = IrType::Primitive(PrimitiveType::String);
        let tgt = IrType::Primitive(PrimitiveType::Bool);
        let cmp = compare_types(&src, &tgt, "test");
        assert_eq!(cmp.class, TransportClass::Incompatible);
    }
}
