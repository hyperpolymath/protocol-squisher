// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Protocol Squisher Constraint Evaluation Engine
//!
//! Evaluates declarative constraints from the IR against schemas and live
//! data values. Designed for Pane-L (symbolic) integration in PanLL, where
//! constraints must be checked interactively against actual data.
//!
//! ## Overview
//!
//! The IR already defines 30+ [`Constraint`] variants (numeric, string,
//! collection, relational, conditional, composite). This crate adds:
//!
//! - **Schema-level constraint evaluation** — check whether a schema
//!   satisfies a set of constraints (type compatibility, field presence,
//!   version range, cardinality, nullability).
//! - **Value-level constraint evaluation** — check whether a concrete
//!   JSON value satisfies a constraint.
//! - **Constraint reports** — per-constraint pass/fail with severity.
//!
//! ## Usage
//!
//! ```rust,ignore
//! use protocol_squisher_constraints::*;
//! use protocol_squisher_ir::IrSchema;
//!
//! let mut set = ConstraintSet::new();
//! set.add(SchemaConstraint::FieldPresence {
//!     type_name: "User".into(),
//!     field_name: "email".into(),
//!     required: true,
//! });
//!
//! let report = evaluate(&schema, &set);
//! assert!(report.passed());
//! ```

use protocol_squisher_ir::{
    Constraint, FieldDef, IrSchema, IrType, PrimitiveType, StructDef, TypeDef,
};
use serde::{Deserialize, Serialize};

// ─── Schema-Level Constraints ───────────────────────────────────────────────

/// A schema-level constraint that can be evaluated against an [`IrSchema`].
///
/// These go beyond the field-level [`Constraint`] variants in the IR by
/// expressing structural requirements on the schema itself.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SchemaConstraint {
    /// A field of a specific type must be compatible with an expected type.
    TypeCompatibility {
        /// Name of the type in the schema.
        type_name: String,
        /// Name of the field to check.
        field_name: String,
        /// Expected primitive type.
        expected_type: PrimitiveType,
    },

    /// A field must (or must not) be present in a type.
    FieldPresence {
        /// Name of the type in the schema.
        type_name: String,
        /// Name of the field.
        field_name: String,
        /// Whether the field is required to be present (`true`) or absent (`false`).
        required: bool,
    },

    /// The schema version must fall within a semver range.
    VersionRange {
        /// Minimum version (inclusive). Empty string means no lower bound.
        min_version: String,
        /// Maximum version (inclusive). Empty string means no upper bound.
        max_version: String,
    },

    /// A collection field must have a cardinality within bounds.
    Cardinality {
        /// Name of the type in the schema.
        type_name: String,
        /// Name of the field.
        field_name: String,
        /// Minimum number of items (inclusive).
        min: Option<usize>,
        /// Maximum number of items (inclusive).
        max: Option<usize>,
    },

    /// A field must (or must not) be nullable/optional.
    Nullability {
        /// Name of the type in the schema.
        type_name: String,
        /// Name of the field.
        field_name: String,
        /// `true` means the field must be nullable; `false` means it must not be.
        must_be_nullable: bool,
    },
}

// ─── Constraint Set ─────────────────────────────────────────────────────────

/// A collection of schema constraints to evaluate together.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ConstraintSet {
    /// The constraints in this set.
    pub constraints: Vec<SchemaConstraint>,
}

impl ConstraintSet {
    /// Create an empty constraint set.
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
        }
    }

    /// Add a constraint to the set.
    pub fn add(&mut self, constraint: SchemaConstraint) {
        self.constraints.push(constraint);
    }

    /// Number of constraints in the set.
    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }
}

// ─── Evaluation Results ─────────────────────────────────────────────────────

/// Severity of a constraint violation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ConstraintSeverity {
    /// Informational — not a real problem.
    Info,
    /// Warning — should be addressed but not blocking.
    Warning,
    /// Error — constraint is violated and must be fixed.
    Error,
}

/// Describes a single constraint violation.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ConstraintViolation {
    /// The constraint that was violated.
    pub constraint: SchemaConstraint,
    /// Human-readable description of the violation.
    pub message: String,
    /// Severity of this violation.
    pub severity: ConstraintSeverity,
}

/// Result of evaluating a single constraint.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ConstraintResult {
    /// The constraint that was evaluated.
    pub constraint: SchemaConstraint,
    /// Whether the constraint passed.
    pub passed: bool,
    /// Violation details (present only if `passed` is `false`).
    pub violation: Option<ConstraintViolation>,
}

/// Report from evaluating a [`ConstraintSet`] against an [`IrSchema`].
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstraintReport {
    /// Per-constraint results.
    pub results: Vec<ConstraintResult>,
    /// Overall verdict: `true` if all constraints pass.
    pub all_passed: bool,
    /// Number of errors.
    pub error_count: usize,
    /// Number of warnings.
    pub warning_count: usize,
    /// Number of informational notices.
    pub info_count: usize,
}

impl ConstraintReport {
    /// Whether all constraints passed.
    pub fn passed(&self) -> bool {
        self.all_passed
    }

    /// Number of violations at or above the given severity.
    pub fn violations_at_least(&self, severity: ConstraintSeverity) -> usize {
        self.results
            .iter()
            .filter(|r| {
                if let Some(v) = &r.violation {
                    v.severity >= severity
                } else {
                    false
                }
            })
            .count()
    }
}

// ─── Evaluation Logic ───────────────────────────────────────────────────────

/// Evaluate a set of constraints against a schema.
///
/// Returns a [`ConstraintReport`] with per-constraint pass/fail results
/// and an overall verdict.
pub fn evaluate(schema: &IrSchema, constraints: &ConstraintSet) -> ConstraintReport {
    let mut results = Vec::with_capacity(constraints.len());
    let mut error_count = 0usize;
    let mut warning_count = 0usize;
    let mut info_count = 0usize;

    for constraint in &constraints.constraints {
        let result = evaluate_one(schema, constraint);
        if let Some(ref v) = result.violation {
            match v.severity {
                ConstraintSeverity::Error => error_count += 1,
                ConstraintSeverity::Warning => warning_count += 1,
                ConstraintSeverity::Info => info_count += 1,
            }
        }
        results.push(result);
    }

    let all_passed = error_count == 0;

    ConstraintReport {
        results,
        all_passed,
        error_count,
        warning_count,
        info_count,
    }
}

/// Evaluate a single schema constraint.
fn evaluate_one(schema: &IrSchema, constraint: &SchemaConstraint) -> ConstraintResult {
    match constraint {
        SchemaConstraint::TypeCompatibility {
            type_name,
            field_name,
            expected_type,
        } => evaluate_type_compatibility(schema, type_name, field_name, *expected_type, constraint),

        SchemaConstraint::FieldPresence {
            type_name,
            field_name,
            required,
        } => evaluate_field_presence(schema, type_name, field_name, *required, constraint),

        SchemaConstraint::VersionRange {
            min_version,
            max_version,
        } => evaluate_version_range(schema, min_version, max_version, constraint),

        SchemaConstraint::Cardinality {
            type_name,
            field_name,
            min,
            max,
        } => evaluate_cardinality(schema, type_name, field_name, *min, *max, constraint),

        SchemaConstraint::Nullability {
            type_name,
            field_name,
            must_be_nullable,
        } => evaluate_nullability(schema, type_name, field_name, *must_be_nullable, constraint),
    }
}

/// Look up a field in a schema type. Returns `None` if the type or field
/// does not exist.
fn find_field<'a>(schema: &'a IrSchema, type_name: &str, field_name: &str) -> Option<&'a FieldDef> {
    let type_def = schema.types.get(type_name)?;
    match type_def {
        TypeDef::Struct(StructDef { fields, .. }) => fields.iter().find(|f| f.name == field_name),
        _ => None,
    }
}

/// Check whether `actual` is compatible with (can satisfy) `expected`.
///
/// Widening (e.g. I32 assigned where I64 is expected) is compatible.
fn primitive_compatible(actual: PrimitiveType, expected: PrimitiveType) -> bool {
    if actual == expected {
        return true;
    }
    // Safe widening paths
    matches!(
        (actual, expected),
        (PrimitiveType::I8, PrimitiveType::I16)
            | (PrimitiveType::I8, PrimitiveType::I32)
            | (PrimitiveType::I8, PrimitiveType::I64)
            | (PrimitiveType::I8, PrimitiveType::I128)
            | (PrimitiveType::I16, PrimitiveType::I32)
            | (PrimitiveType::I16, PrimitiveType::I64)
            | (PrimitiveType::I16, PrimitiveType::I128)
            | (PrimitiveType::I32, PrimitiveType::I64)
            | (PrimitiveType::I32, PrimitiveType::I128)
            | (PrimitiveType::I64, PrimitiveType::I128)
            | (PrimitiveType::U8, PrimitiveType::U16)
            | (PrimitiveType::U8, PrimitiveType::U32)
            | (PrimitiveType::U8, PrimitiveType::U64)
            | (PrimitiveType::U8, PrimitiveType::U128)
            | (PrimitiveType::U16, PrimitiveType::U32)
            | (PrimitiveType::U16, PrimitiveType::U64)
            | (PrimitiveType::U16, PrimitiveType::U128)
            | (PrimitiveType::U32, PrimitiveType::U64)
            | (PrimitiveType::U32, PrimitiveType::U128)
            | (PrimitiveType::U64, PrimitiveType::U128)
            | (PrimitiveType::F32, PrimitiveType::F64)
    )
}

fn evaluate_type_compatibility(
    schema: &IrSchema,
    type_name: &str,
    field_name: &str,
    expected: PrimitiveType,
    constraint: &SchemaConstraint,
) -> ConstraintResult {
    let Some(field) = find_field(schema, type_name, field_name) else {
        return ConstraintResult {
            constraint: constraint.clone(),
            passed: false,
            violation: Some(ConstraintViolation {
                constraint: constraint.clone(),
                message: format!("Type '{type_name}' or field '{field_name}' not found in schema"),
                severity: ConstraintSeverity::Error,
            }),
        };
    };

    let actual_primitive = match &field.ty {
        IrType::Primitive(p) => Some(*p),
        _ => None,
    };

    match actual_primitive {
        Some(actual) if primitive_compatible(actual, expected) => ConstraintResult {
            constraint: constraint.clone(),
            passed: true,
            violation: None,
        },
        Some(actual) => ConstraintResult {
            constraint: constraint.clone(),
            passed: false,
            violation: Some(ConstraintViolation {
                constraint: constraint.clone(),
                message: format!(
                    "Field '{type_name}.{field_name}' has type {actual:?}, expected {expected:?}"
                ),
                severity: ConstraintSeverity::Error,
            }),
        },
        None => ConstraintResult {
            constraint: constraint.clone(),
            passed: false,
            violation: Some(ConstraintViolation {
                constraint: constraint.clone(),
                message: format!("Field '{type_name}.{field_name}' is not a primitive type"),
                severity: ConstraintSeverity::Error,
            }),
        },
    }
}

fn evaluate_field_presence(
    schema: &IrSchema,
    type_name: &str,
    field_name: &str,
    required: bool,
    constraint: &SchemaConstraint,
) -> ConstraintResult {
    let type_def = schema.types.get(type_name);
    let field_exists = type_def
        .map(|td| match td {
            TypeDef::Struct(s) => s.fields.iter().any(|f| f.name == field_name),
            _ => false,
        })
        .unwrap_or(false);

    if required && !field_exists {
        ConstraintResult {
            constraint: constraint.clone(),
            passed: false,
            violation: Some(ConstraintViolation {
                constraint: constraint.clone(),
                message: format!("Required field '{type_name}.{field_name}' is missing"),
                severity: ConstraintSeverity::Error,
            }),
        }
    } else if !required && field_exists {
        ConstraintResult {
            constraint: constraint.clone(),
            passed: false,
            violation: Some(ConstraintViolation {
                constraint: constraint.clone(),
                message: format!("Field '{type_name}.{field_name}' should not be present"),
                severity: ConstraintSeverity::Warning,
            }),
        }
    } else {
        ConstraintResult {
            constraint: constraint.clone(),
            passed: true,
            violation: None,
        }
    }
}

fn evaluate_version_range(
    schema: &IrSchema,
    min_version: &str,
    max_version: &str,
    constraint: &SchemaConstraint,
) -> ConstraintResult {
    let version = &schema.version;

    let min_ok = min_version.is_empty() || version.as_str() >= min_version;
    let max_ok = max_version.is_empty() || version.as_str() <= max_version;

    if min_ok && max_ok {
        ConstraintResult {
            constraint: constraint.clone(),
            passed: true,
            violation: None,
        }
    } else {
        let range_desc = match (min_version.is_empty(), max_version.is_empty()) {
            (false, false) => format!("[{min_version}, {max_version}]"),
            (true, false) => format!("[*, {max_version}]"),
            (false, true) => format!("[{min_version}, *]"),
            (true, true) => "[*, *]".to_string(),
        };
        ConstraintResult {
            constraint: constraint.clone(),
            passed: false,
            violation: Some(ConstraintViolation {
                constraint: constraint.clone(),
                message: format!("Schema version '{version}' is outside range {range_desc}"),
                severity: ConstraintSeverity::Error,
            }),
        }
    }
}

fn evaluate_cardinality(
    schema: &IrSchema,
    type_name: &str,
    field_name: &str,
    min: Option<usize>,
    max: Option<usize>,
    constraint: &SchemaConstraint,
) -> ConstraintResult {
    let Some(field) = find_field(schema, type_name, field_name) else {
        return ConstraintResult {
            constraint: constraint.clone(),
            passed: false,
            violation: Some(ConstraintViolation {
                constraint: constraint.clone(),
                message: format!("Type '{type_name}' or field '{field_name}' not found in schema"),
                severity: ConstraintSeverity::Error,
            }),
        };
    };

    // Check that the field is a collection type
    let is_collection = matches!(
        &field.ty,
        IrType::Container(
            protocol_squisher_ir::ContainerType::Vec(_)
                | protocol_squisher_ir::ContainerType::Set(_)
                | protocol_squisher_ir::ContainerType::Array(_, _)
                | protocol_squisher_ir::ContainerType::Map(_, _)
        )
    );

    if !is_collection {
        return ConstraintResult {
            constraint: constraint.clone(),
            passed: false,
            violation: Some(ConstraintViolation {
                constraint: constraint.clone(),
                message: format!("Field '{type_name}.{field_name}' is not a collection type"),
                severity: ConstraintSeverity::Error,
            }),
        };
    }

    // For Array(_, size) we can statically check cardinality
    if let IrType::Container(protocol_squisher_ir::ContainerType::Array(_, size)) = &field.ty {
        let min_ok = min.map_or(true, |m| *size >= m);
        let max_ok = max.map_or(true, |m| *size <= m);

        if !min_ok || !max_ok {
            return ConstraintResult {
                constraint: constraint.clone(),
                passed: false,
                violation: Some(ConstraintViolation {
                    constraint: constraint.clone(),
                    message: format!(
                        "Array '{type_name}.{field_name}' has fixed size {size}, \
                         outside cardinality bounds [{}, {}]",
                        min.map_or("*".to_string(), |m| m.to_string()),
                        max.map_or("*".to_string(), |m| m.to_string()),
                    ),
                    severity: ConstraintSeverity::Error,
                }),
            };
        }
    }

    // For dynamic collections, check field-level constraints for
    // MinItems/MaxItems that might conflict with the requested bounds.
    let mut violations = Vec::new();
    for c in &field.constraints {
        match c {
            Constraint::MinItems(field_min) => {
                if let Some(req_max) = max {
                    if *field_min > req_max {
                        violations.push(format!(
                            "Field MinItems({field_min}) exceeds requested max({req_max})"
                        ));
                    }
                }
            },
            Constraint::MaxItems(field_max) => {
                if let Some(req_min) = min {
                    if *field_max < req_min {
                        violations.push(format!(
                            "Field MaxItems({field_max}) is below requested min({req_min})"
                        ));
                    }
                }
            },
            _ => {},
        }
    }

    if violations.is_empty() {
        ConstraintResult {
            constraint: constraint.clone(),
            passed: true,
            violation: None,
        }
    } else {
        ConstraintResult {
            constraint: constraint.clone(),
            passed: false,
            violation: Some(ConstraintViolation {
                constraint: constraint.clone(),
                message: violations.join("; "),
                severity: ConstraintSeverity::Error,
            }),
        }
    }
}

fn evaluate_nullability(
    schema: &IrSchema,
    type_name: &str,
    field_name: &str,
    must_be_nullable: bool,
    constraint: &SchemaConstraint,
) -> ConstraintResult {
    let Some(field) = find_field(schema, type_name, field_name) else {
        return ConstraintResult {
            constraint: constraint.clone(),
            passed: false,
            violation: Some(ConstraintViolation {
                constraint: constraint.clone(),
                message: format!("Type '{type_name}' or field '{field_name}' not found in schema"),
                severity: ConstraintSeverity::Error,
            }),
        };
    };

    let is_nullable = field.optional || field.ty.is_optional();

    if must_be_nullable && !is_nullable {
        ConstraintResult {
            constraint: constraint.clone(),
            passed: false,
            violation: Some(ConstraintViolation {
                constraint: constraint.clone(),
                message: format!("Field '{type_name}.{field_name}' must be nullable but is not"),
                severity: ConstraintSeverity::Error,
            }),
        }
    } else if !must_be_nullable && is_nullable {
        ConstraintResult {
            constraint: constraint.clone(),
            passed: false,
            violation: Some(ConstraintViolation {
                constraint: constraint.clone(),
                message: format!("Field '{type_name}.{field_name}' must not be nullable but is"),
                severity: ConstraintSeverity::Error,
            }),
        }
    } else {
        ConstraintResult {
            constraint: constraint.clone(),
            passed: true,
            violation: None,
        }
    }
}

// ─── Value-Level Evaluation ─────────────────────────────────────────────────

/// Evaluate a single IR [`Constraint`] against a concrete JSON value.
///
/// This is the function Pane-L calls for interactive constraint checking
/// in the Protocol Playground.
pub fn evaluate_value(
    constraint: &Constraint,
    value: &serde_json::Value,
) -> Result<bool, EvalError> {
    match constraint {
        // ── Numeric ──────────────────────────────────────────────────
        Constraint::Min(nv) => {
            let n = value_as_f64(value)?;
            Ok(n >= nv.as_f64())
        },
        Constraint::Max(nv) => {
            let n = value_as_f64(value)?;
            Ok(n <= nv.as_f64())
        },
        Constraint::Range { min, max } => {
            let n = value_as_f64(value)?;
            Ok(n >= min.as_f64() && n <= max.as_f64())
        },
        Constraint::MultipleOf(nv) => {
            let n = value_as_f64(value)?;
            let d = nv.as_f64();
            if d == 0.0 {
                return Err(EvalError::DivisionByZero);
            }
            Ok((n % d).abs() < f64::EPSILON)
        },
        Constraint::Positive => {
            let n = value_as_f64(value)?;
            Ok(n > 0.0)
        },
        Constraint::Negative => {
            let n = value_as_f64(value)?;
            Ok(n < 0.0)
        },
        Constraint::NonNegative => {
            let n = value_as_f64(value)?;
            Ok(n >= 0.0)
        },

        // ── String ──────────────────────────────────────────────────
        Constraint::MinLength(len) => {
            let s = value_as_str(value)?;
            Ok(s.len() >= *len)
        },
        Constraint::MaxLength(len) => {
            let s = value_as_str(value)?;
            Ok(s.len() <= *len)
        },
        Constraint::ExactLength(len) => {
            let s = value_as_str(value)?;
            Ok(s.len() == *len)
        },
        Constraint::NonEmpty => {
            let s = value_as_str(value)?;
            Ok(!s.is_empty())
        },
        // Pattern matching not supported without a regex engine; return
        // an error so the caller can fall back to a regex crate.
        Constraint::Pattern(_) => Err(EvalError::UnsupportedConstraint(
            "Pattern matching requires a regex engine".into(),
        )),
        Constraint::Format(_) => Err(EvalError::UnsupportedConstraint(
            "Format validation requires a dedicated validator".into(),
        )),

        // ── Collection ──────────────────────────────────────────────
        Constraint::MinItems(n) => {
            let arr = value_as_array(value)?;
            Ok(arr.len() >= *n)
        },
        Constraint::MaxItems(n) => {
            let arr = value_as_array(value)?;
            Ok(arr.len() <= *n)
        },
        Constraint::UniqueItems => {
            let arr = value_as_array(value)?;
            let mut seen = Vec::with_capacity(arr.len());
            for item in arr {
                let s = serde_json::to_string(item).unwrap_or_default();
                if seen.contains(&s) {
                    return Ok(false);
                }
                seen.push(s);
            }
            Ok(true)
        },
        Constraint::Contains(expected) => {
            let arr = value_as_array(value)?;
            Ok(arr.contains(expected))
        },

        // ── Enum/choice ─────────────────────────────────────────────
        Constraint::OneOf(allowed) => Ok(allowed.contains(value)),
        Constraint::NotOneOf(disallowed) => Ok(!disallowed.contains(value)),

        // ── Composite ───────────────────────────────────────────────
        Constraint::AllOf(cs) => {
            for c in cs {
                if !evaluate_value(c, value)? {
                    return Ok(false);
                }
            }
            Ok(true)
        },
        Constraint::AnyOf(cs) => {
            for c in cs {
                if evaluate_value(c, value)? {
                    return Ok(true);
                }
            }
            Ok(false)
        },
        Constraint::OneOfConstraints(cs) => {
            let mut count = 0;
            for c in cs {
                if evaluate_value(c, value)? {
                    count += 1;
                }
            }
            Ok(count == 1)
        },
        Constraint::Not(c) => {
            let inner = evaluate_value(c, value)?;
            Ok(!inner)
        },

        // ── Relational and Conditional ──────────────────────────────
        // These require context (sibling field values) which is not
        // available in single-value evaluation.
        Constraint::EqualTo(_)
        | Constraint::NotEqualTo(_)
        | Constraint::LessThan(_)
        | Constraint::GreaterThan(_)
        | Constraint::ConditionalOn { .. } => Err(EvalError::UnsupportedConstraint(
            "Relational/conditional constraints require sibling field context".into(),
        )),

        // ── Custom ──────────────────────────────────────────────────
        Constraint::Custom { name, .. } => Err(EvalError::UnsupportedConstraint(format!(
            "Custom constraint '{name}' has no built-in evaluator"
        ))),
    }
}

/// Errors from value-level constraint evaluation.
#[derive(Debug, Clone, PartialEq)]
pub enum EvalError {
    /// The value is not the expected JSON type for this constraint.
    TypeMismatch(String),
    /// Division by zero in a MultipleOf constraint.
    DivisionByZero,
    /// Constraint type not supported for value-level evaluation.
    UnsupportedConstraint(String),
}

impl std::fmt::Display for EvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EvalError::TypeMismatch(msg) => write!(f, "Type mismatch: {msg}"),
            EvalError::DivisionByZero => write!(f, "Division by zero in MultipleOf"),
            EvalError::UnsupportedConstraint(msg) => {
                write!(f, "Unsupported constraint: {msg}")
            },
        }
    }
}

impl std::error::Error for EvalError {}

// ─── Helpers ────────────────────────────────────────────────────────────────

fn value_as_f64(value: &serde_json::Value) -> Result<f64, EvalError> {
    value
        .as_f64()
        .or_else(|| value.as_i64().map(|i| i as f64))
        .or_else(|| value.as_u64().map(|u| u as f64))
        .ok_or_else(|| EvalError::TypeMismatch("expected a number".into()))
}

fn value_as_str(value: &serde_json::Value) -> Result<&str, EvalError> {
    value
        .as_str()
        .ok_or_else(|| EvalError::TypeMismatch("expected a string".into()))
}

fn value_as_array(value: &serde_json::Value) -> Result<&Vec<serde_json::Value>, EvalError> {
    value
        .as_array()
        .ok_or_else(|| EvalError::TypeMismatch("expected an array".into()))
}

// ─── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{
        ContainerType, FieldDef, FieldMetadata, IrType, NumberValue, PrimitiveType, StructDef,
        TypeDef, TypeMetadata,
    };

    /// Helper: build a schema with one struct type containing the given fields.
    fn schema_with_struct(
        type_name: &str,
        fields: Vec<(&str, IrType, bool, Vec<Constraint>)>,
    ) -> IrSchema {
        let mut schema = IrSchema::new("test-schema", "test");
        schema.version = "1.0.0".to_string();
        schema.add_type(
            type_name.to_string(),
            TypeDef::Struct(StructDef {
                name: type_name.to_string(),
                fields: fields
                    .into_iter()
                    .map(|(name, ty, optional, constraints)| FieldDef {
                        name: name.to_string(),
                        ty,
                        optional,
                        constraints,
                        metadata: FieldMetadata::default(),
                    })
                    .collect(),
                metadata: TypeMetadata::default(),
            }),
        );
        schema
    }

    // ── Schema-level: TypeCompatibility ─────────────────────────────

    #[test]
    fn type_compatibility_exact_match() {
        let schema = schema_with_struct(
            "User",
            vec![("id", IrType::Primitive(PrimitiveType::I64), false, vec![])],
        );
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::TypeCompatibility {
            type_name: "User".into(),
            field_name: "id".into(),
            expected_type: PrimitiveType::I64,
        });
        let report = evaluate(&schema, &set);
        assert!(report.passed());
        assert_eq!(report.error_count, 0);
    }

    #[test]
    fn type_compatibility_widening_allowed() {
        let schema = schema_with_struct(
            "User",
            vec![("id", IrType::Primitive(PrimitiveType::I32), false, vec![])],
        );
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::TypeCompatibility {
            type_name: "User".into(),
            field_name: "id".into(),
            expected_type: PrimitiveType::I64,
        });
        let report = evaluate(&schema, &set);
        assert!(report.passed());
    }

    #[test]
    fn type_compatibility_narrowing_fails() {
        let schema = schema_with_struct(
            "User",
            vec![("id", IrType::Primitive(PrimitiveType::I64), false, vec![])],
        );
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::TypeCompatibility {
            type_name: "User".into(),
            field_name: "id".into(),
            expected_type: PrimitiveType::I32,
        });
        let report = evaluate(&schema, &set);
        assert!(!report.passed());
        assert_eq!(report.error_count, 1);
    }

    #[test]
    fn type_compatibility_missing_field() {
        let schema = schema_with_struct("User", vec![]);
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::TypeCompatibility {
            type_name: "User".into(),
            field_name: "id".into(),
            expected_type: PrimitiveType::I64,
        });
        let report = evaluate(&schema, &set);
        assert!(!report.passed());
    }

    // ── Schema-level: FieldPresence ─────────────────────────────────

    #[test]
    fn field_presence_required_present() {
        let schema = schema_with_struct(
            "User",
            vec![(
                "email",
                IrType::Primitive(PrimitiveType::String),
                false,
                vec![],
            )],
        );
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::FieldPresence {
            type_name: "User".into(),
            field_name: "email".into(),
            required: true,
        });
        let report = evaluate(&schema, &set);
        assert!(report.passed());
    }

    #[test]
    fn field_presence_required_missing() {
        let schema = schema_with_struct("User", vec![]);
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::FieldPresence {
            type_name: "User".into(),
            field_name: "email".into(),
            required: true,
        });
        let report = evaluate(&schema, &set);
        assert!(!report.passed());
    }

    #[test]
    fn field_presence_forbidden_present() {
        let schema = schema_with_struct(
            "User",
            vec![(
                "ssn",
                IrType::Primitive(PrimitiveType::String),
                false,
                vec![],
            )],
        );
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::FieldPresence {
            type_name: "User".into(),
            field_name: "ssn".into(),
            required: false,
        });
        let report = evaluate(&schema, &set);
        // Forbidden field present is a warning, not error
        assert!(report.passed()); // warnings don't fail
        assert_eq!(report.warning_count, 1);
    }

    // ── Schema-level: VersionRange ──────────────────────────────────

    #[test]
    fn version_range_within() {
        let schema = {
            let mut s = IrSchema::new("test", "test");
            s.version = "1.0.0".to_string();
            s
        };
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::VersionRange {
            min_version: "0.9.0".into(),
            max_version: "2.0.0".into(),
        });
        let report = evaluate(&schema, &set);
        assert!(report.passed());
    }

    #[test]
    fn version_range_below_min() {
        let schema = {
            let mut s = IrSchema::new("test", "test");
            s.version = "0.5.0".to_string();
            s
        };
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::VersionRange {
            min_version: "1.0.0".into(),
            max_version: "".into(),
        });
        let report = evaluate(&schema, &set);
        assert!(!report.passed());
    }

    // ── Schema-level: Cardinality ───────────────────────────────────

    #[test]
    fn cardinality_on_vec_passes() {
        let schema = schema_with_struct(
            "Order",
            vec![(
                "items",
                IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
                    PrimitiveType::String,
                )))),
                false,
                vec![],
            )],
        );
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::Cardinality {
            type_name: "Order".into(),
            field_name: "items".into(),
            min: Some(1),
            max: Some(100),
        });
        let report = evaluate(&schema, &set);
        assert!(report.passed());
    }

    #[test]
    fn cardinality_on_non_collection_fails() {
        let schema = schema_with_struct(
            "User",
            vec![(
                "name",
                IrType::Primitive(PrimitiveType::String),
                false,
                vec![],
            )],
        );
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::Cardinality {
            type_name: "User".into(),
            field_name: "name".into(),
            min: Some(1),
            max: None,
        });
        let report = evaluate(&schema, &set);
        assert!(!report.passed());
    }

    #[test]
    fn cardinality_array_static_check() {
        let schema = schema_with_struct(
            "Matrix",
            vec![(
                "row",
                IrType::Container(ContainerType::Array(
                    Box::new(IrType::Primitive(PrimitiveType::F64)),
                    3,
                )),
                false,
                vec![],
            )],
        );
        // min=5 but array is size 3 → fail
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::Cardinality {
            type_name: "Matrix".into(),
            field_name: "row".into(),
            min: Some(5),
            max: None,
        });
        let report = evaluate(&schema, &set);
        assert!(!report.passed());
    }

    // ── Schema-level: Nullability ───────────────────────────────────

    #[test]
    fn nullability_optional_field_must_be_nullable() {
        let schema = schema_with_struct(
            "User",
            vec![(
                "nickname",
                IrType::Primitive(PrimitiveType::String),
                true,
                vec![],
            )],
        );
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::Nullability {
            type_name: "User".into(),
            field_name: "nickname".into(),
            must_be_nullable: true,
        });
        let report = evaluate(&schema, &set);
        assert!(report.passed());
    }

    #[test]
    fn nullability_required_field_must_not_be_nullable() {
        let schema = schema_with_struct(
            "User",
            vec![("id", IrType::Primitive(PrimitiveType::I64), false, vec![])],
        );
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::Nullability {
            type_name: "User".into(),
            field_name: "id".into(),
            must_be_nullable: false,
        });
        let report = evaluate(&schema, &set);
        assert!(report.passed());
    }

    #[test]
    fn nullability_violation() {
        let schema = schema_with_struct(
            "User",
            vec![("id", IrType::Primitive(PrimitiveType::I64), false, vec![])],
        );
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::Nullability {
            type_name: "User".into(),
            field_name: "id".into(),
            must_be_nullable: true,
        });
        let report = evaluate(&schema, &set);
        assert!(!report.passed());
    }

    // ── Multiple constraints ────────────────────────────────────────

    #[test]
    fn multiple_constraints_all_pass() {
        let schema = schema_with_struct(
            "User",
            vec![
                ("id", IrType::Primitive(PrimitiveType::I64), false, vec![]),
                (
                    "name",
                    IrType::Primitive(PrimitiveType::String),
                    false,
                    vec![],
                ),
                (
                    "email",
                    IrType::Primitive(PrimitiveType::String),
                    true,
                    vec![],
                ),
            ],
        );
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::FieldPresence {
            type_name: "User".into(),
            field_name: "id".into(),
            required: true,
        });
        set.add(SchemaConstraint::TypeCompatibility {
            type_name: "User".into(),
            field_name: "id".into(),
            expected_type: PrimitiveType::I64,
        });
        set.add(SchemaConstraint::Nullability {
            type_name: "User".into(),
            field_name: "email".into(),
            must_be_nullable: true,
        });
        let report = evaluate(&schema, &set);
        assert!(report.passed());
        assert_eq!(report.results.len(), 3);
    }

    #[test]
    fn multiple_constraints_partial_failure() {
        let schema = schema_with_struct(
            "User",
            vec![("id", IrType::Primitive(PrimitiveType::I32), false, vec![])],
        );
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::FieldPresence {
            type_name: "User".into(),
            field_name: "id".into(),
            required: true,
        });
        // This one will fail (narrowing)
        set.add(SchemaConstraint::TypeCompatibility {
            type_name: "User".into(),
            field_name: "id".into(),
            expected_type: PrimitiveType::I16,
        });
        let report = evaluate(&schema, &set);
        assert!(!report.passed());
        assert_eq!(report.error_count, 1);
        // First constraint passed
        assert!(report.results[0].passed);
        // Second constraint failed
        assert!(!report.results[1].passed);
    }

    // ── Value-level evaluation ──────────────────────────────────────

    #[test]
    fn value_min_passes() {
        let c = Constraint::Min(NumberValue::Integer(5));
        assert!(evaluate_value(&c, &serde_json::json!(10)).unwrap());
    }

    #[test]
    fn value_min_fails() {
        let c = Constraint::Min(NumberValue::Integer(5));
        assert!(!evaluate_value(&c, &serde_json::json!(3)).unwrap());
    }

    #[test]
    fn value_range() {
        let c = Constraint::Range {
            min: NumberValue::Integer(0),
            max: NumberValue::Integer(100),
        };
        assert!(evaluate_value(&c, &serde_json::json!(50)).unwrap());
        assert!(!evaluate_value(&c, &serde_json::json!(101)).unwrap());
    }

    #[test]
    fn value_min_length() {
        let c = Constraint::MinLength(3);
        assert!(evaluate_value(&c, &serde_json::json!("hello")).unwrap());
        assert!(!evaluate_value(&c, &serde_json::json!("hi")).unwrap());
    }

    #[test]
    fn value_non_empty() {
        let c = Constraint::NonEmpty;
        assert!(evaluate_value(&c, &serde_json::json!("x")).unwrap());
        assert!(!evaluate_value(&c, &serde_json::json!("")).unwrap());
    }

    #[test]
    fn value_min_items() {
        let c = Constraint::MinItems(2);
        assert!(evaluate_value(&c, &serde_json::json!([1, 2, 3])).unwrap());
        assert!(!evaluate_value(&c, &serde_json::json!([1])).unwrap());
    }

    #[test]
    fn value_unique_items() {
        let c = Constraint::UniqueItems;
        assert!(evaluate_value(&c, &serde_json::json!([1, 2, 3])).unwrap());
        assert!(!evaluate_value(&c, &serde_json::json!([1, 2, 1])).unwrap());
    }

    #[test]
    fn value_one_of() {
        let c = Constraint::OneOf(vec![
            serde_json::json!("red"),
            serde_json::json!("green"),
            serde_json::json!("blue"),
        ]);
        assert!(evaluate_value(&c, &serde_json::json!("red")).unwrap());
        assert!(!evaluate_value(&c, &serde_json::json!("yellow")).unwrap());
    }

    #[test]
    fn value_all_of_composite() {
        let c = Constraint::AllOf(vec![
            Constraint::Min(NumberValue::Integer(0)),
            Constraint::Max(NumberValue::Integer(100)),
        ]);
        assert!(evaluate_value(&c, &serde_json::json!(50)).unwrap());
        assert!(!evaluate_value(&c, &serde_json::json!(150)).unwrap());
    }

    #[test]
    fn value_not_constraint() {
        let c = Constraint::Not(Box::new(Constraint::Negative));
        assert!(evaluate_value(&c, &serde_json::json!(5)).unwrap());
        assert!(!evaluate_value(&c, &serde_json::json!(-3)).unwrap());
    }

    #[test]
    fn value_type_mismatch_error() {
        let c = Constraint::Min(NumberValue::Integer(0));
        let result = evaluate_value(&c, &serde_json::json!("not a number"));
        assert!(result.is_err());
        assert!(matches!(result, Err(EvalError::TypeMismatch(_))));
    }

    #[test]
    fn value_positive_negative() {
        assert!(evaluate_value(&Constraint::Positive, &serde_json::json!(1)).unwrap());
        assert!(!evaluate_value(&Constraint::Positive, &serde_json::json!(-1)).unwrap());
        assert!(evaluate_value(&Constraint::Negative, &serde_json::json!(-1)).unwrap());
        assert!(evaluate_value(&Constraint::NonNegative, &serde_json::json!(0)).unwrap());
    }

    #[test]
    fn violations_at_least_counting() {
        let schema = schema_with_struct("User", vec![]);
        let mut set = ConstraintSet::new();
        set.add(SchemaConstraint::FieldPresence {
            type_name: "User".into(),
            field_name: "a".into(),
            required: true,
        });
        set.add(SchemaConstraint::FieldPresence {
            type_name: "User".into(),
            field_name: "b".into(),
            required: true,
        });
        let report = evaluate(&schema, &set);
        assert_eq!(report.violations_at_least(ConstraintSeverity::Error), 2);
        assert_eq!(report.violations_at_least(ConstraintSeverity::Warning), 2);
    }
}
