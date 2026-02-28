// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Generates formal proof goals from IR type pairs and transport class claims.
//!
//! The `ProofGoalGenerator` translates protocol-squisher's type analysis
//! results into theorem statements that ECHIDNA's prover backends can attempt
//! to verify. Each prover uses different syntax, so the generator formats
//! goals appropriately for Agda, Coq, Lean4, Z3, etc.

use crate::types::ProverKind;
use protocol_squisher_ir::PrimitiveType;

/// Generates formal proof goals for ECHIDNA from IR type analysis.
///
/// Takes `(source, target)` primitive type pairs and transport class claims,
/// and produces prover-specific theorem strings that can be submitted to
/// ECHIDNA for verification.
pub struct ProofGoalGenerator;

impl ProofGoalGenerator {
    /// Generate a goal asserting that widening from `source` to `target` is
    /// lossless (no information is lost in the conversion).
    ///
    /// This is the core proof obligation for Business-class transport:
    /// every value of the source type must be exactly representable in the
    /// target type.
    pub fn widening_is_lossless(
        source: &PrimitiveType,
        target: &PrimitiveType,
        prover: ProverKind,
    ) -> String {
        let source_name = primitive_type_name(source);
        let target_name = primitive_type_name(target);

        match prover {
            ProverKind::Agda => format!(
                "widening-lossless : (x : {source_name}) → \
                 fromTarget (toTarget x) ≡ x"
            ),
            ProverKind::Coq => format!(
                "Theorem widening_lossless : forall (x : {source_name}), \
                 from_target (to_target x) = x."
            ),
            ProverKind::Lean4 => format!(
                "theorem widening_lossless (x : {source_name}) : \
                 fromTarget (toTarget x) = x := by sorry"
            ),
            ProverKind::Z3 => format!(
                "(assert (forall ((x {source_name})) \
                 (= (from_target (to_target x)) x)))\n(check-sat)"
            ),
            ProverKind::Idris2 => format!(
                "wideningLossless : (x : {source_name}) -> \
                 fromTarget (toTarget x) === x"
            ),
            ProverKind::Isabelle | ProverKind::Isabelle2024 => format!(
                "lemma widening_lossless: \
                 \"\\<forall>x::{source_name}. from_target (to_target x) = x\""
            ),
            _ => format!(
                "-- [{prover:?}] Prove: widening {source_name} → {target_name} is lossless\n\
                 -- forall x : {source_name}, roundtrip(x) = x"
            ),
        }
    }

    /// Generate a goal asserting that narrowing from `source` to `target`
    /// preserves values within the target's representable range.
    ///
    /// For narrowing conversions, we can only guarantee losslessness for
    /// values that fit in the target type. This generates a conditional
    /// proof obligation.
    pub fn narrowing_is_checked(
        source: &PrimitiveType,
        target: &PrimitiveType,
        prover: ProverKind,
    ) -> String {
        let source_name = primitive_type_name(source);
        let target_name = primitive_type_name(target);
        let (lo, hi) = target_range_bounds(target);

        match prover {
            ProverKind::Coq => format!(
                "Theorem narrowing_checked : forall (x : {source_name}), \
                 {lo} <= x <= {hi} -> \
                 from_target (to_target x) = x."
            ),
            ProverKind::Z3 => format!(
                "(assert (forall ((x {source_name})) \
                 (=> (and (>= x {lo}) (<= x {hi})) \
                 (= (from_target (to_target x)) x))))\n(check-sat)"
            ),
            ProverKind::Lean4 => format!(
                "theorem narrowing_checked (x : {source_name}) \
                 (h : {lo} ≤ x ∧ x ≤ {hi}) : \
                 fromTarget (toTarget x) = x := by sorry"
            ),
            _ => format!(
                "-- [{prover:?}] Prove: narrowing {source_name} → {target_name} \
                 is safe for values in [{lo}, {hi}]"
            ),
        }
    }

    /// Generate a goal asserting that a transport class assignment is correct.
    ///
    /// Encodes the claim "the conversion from `source_type` to `target_type`
    /// has fidelity ≥ `fidelity_percent`%" as a formal statement.
    pub fn transport_class_correct(
        source: &PrimitiveType,
        target: &PrimitiveType,
        fidelity_percent: u8,
        prover: ProverKind,
    ) -> String {
        let source_name = primitive_type_name(source);
        let target_name = primitive_type_name(target);

        match prover {
            ProverKind::Coq => format!(
                "Theorem transport_class_correct : \
                 fidelity (convert {source_name} {target_name}) >= {fidelity_percent}."
            ),
            ProverKind::Z3 => format!(
                "(assert (>= (fidelity (convert {source_name} {target_name})) {fidelity_percent}))\n\
                 (check-sat)"
            ),
            _ => format!(
                "-- [{prover:?}] Prove: transport {source_name} → {target_name} \
                 has fidelity >= {fidelity_percent}%"
            ),
        }
    }
}

/// Map a `PrimitiveType` to a human-readable type name used in proof goals.
fn primitive_type_name(ty: &PrimitiveType) -> &'static str {
    match ty {
        PrimitiveType::Bool => "Bool",
        PrimitiveType::I8 => "Int8",
        PrimitiveType::I16 => "Int16",
        PrimitiveType::I32 => "Int32",
        PrimitiveType::I64 => "Int64",
        PrimitiveType::I128 => "Int128",
        PrimitiveType::U8 => "UInt8",
        PrimitiveType::U16 => "UInt16",
        PrimitiveType::U32 => "UInt32",
        PrimitiveType::U64 => "UInt64",
        PrimitiveType::U128 => "UInt128",
        PrimitiveType::F32 => "Float32",
        PrimitiveType::F64 => "Float64",
        PrimitiveType::String => "String",
        PrimitiveType::Char => "Char",
        PrimitiveType::Bytes => "Bytes",
        PrimitiveType::DateTime => "DateTime",
        PrimitiveType::Date => "Date",
        PrimitiveType::Time => "Time",
        PrimitiveType::Duration => "Duration",
        PrimitiveType::Uuid => "UUID",
        PrimitiveType::Decimal => "Decimal",
        PrimitiveType::BigInt => "BigInt",
    }
}

/// Return the (min, max) representable integer bounds for a target type.
///
/// Used in narrowing proofs to constrain the domain of the proof obligation.
fn target_range_bounds(ty: &PrimitiveType) -> (i128, i128) {
    match ty {
        PrimitiveType::I8 => (i8::MIN as i128, i8::MAX as i128),
        PrimitiveType::I16 => (i16::MIN as i128, i16::MAX as i128),
        PrimitiveType::I32 => (i32::MIN as i128, i32::MAX as i128),
        PrimitiveType::I64 => (i64::MIN as i128, i64::MAX as i128),
        PrimitiveType::U8 => (0, u8::MAX as i128),
        PrimitiveType::U16 => (0, u16::MAX as i128),
        PrimitiveType::U32 => (0, u32::MAX as i128),
        PrimitiveType::U64 => (0, u64::MAX as i128),
        _ => (i64::MIN as i128, i64::MAX as i128), // fallback
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn goal_widening_i32_i64() {
        let goal = ProofGoalGenerator::widening_is_lossless(
            &PrimitiveType::I32,
            &PrimitiveType::I64,
            ProverKind::Coq,
        );
        assert!(goal.contains("Int32"));
        assert!(goal.contains("forall"));
        assert!(goal.contains("widening_lossless"));
    }

    #[test]
    fn goal_narrowing_produces_checked() {
        let goal = ProofGoalGenerator::narrowing_is_checked(
            &PrimitiveType::I64,
            &PrimitiveType::I32,
            ProverKind::Z3,
        );
        assert!(goal.contains("Int64"));
        // The goal should contain the I32 range bounds.
        assert!(goal.contains(&i32::MIN.to_string()));
        assert!(goal.contains(&i32::MAX.to_string()));
    }

    #[test]
    fn goal_transport_class() {
        let goal = ProofGoalGenerator::transport_class_correct(
            &PrimitiveType::I32,
            &PrimitiveType::I64,
            98,
            ProverKind::Coq,
        );
        assert!(goal.contains("98"));
        assert!(goal.contains("fidelity"));
    }
}
