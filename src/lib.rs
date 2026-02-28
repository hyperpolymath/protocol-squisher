// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! # Protocol Squisher — Universal Interoperability Engine.
//!
//! Protocol Squisher automates the synthesis of data adapters between
//! disparate serialization formats. It allows high-level languages
//! (Python, JS) to talk to low-level systems (Rust, Zig) without manual
//! FFI boilerplate.
//!
//! THE SQUISHER INVARIANT: "If it compiles, it carries."
//! This system guarantees that ANY two schemas can be bridged, even if the
//! transport is lossy or requires fallback to JSON.

pub mod ir {
    //! Intermediate Representation (IR) for schema definitions.
    pub use protocol_squisher_ir::*;
}

pub mod rust_analyzer {
    //! Analyzes Rust `struct` and `enum` definitions to generate IR.
    pub use protocol_squisher_rust_analyzer::*;
}

/// TRANSPORT CLASSES: Categorizes the quality and performance of a synthesized adapter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TransportClass {
    /// CONCORDE: Zero-copy, bit-for-bit identical layout. Highest performance.
    Concorde,
    /// BUSINESS CLASS: Minor overhead (e.g. string encoding), full type fidelity.
    BusinessClass,
    /// ECONOMY: Moderate overhead, some minor data loss (e.g. precision reduction).
    Economy,
    /// WHEELBARROW: High overhead, significant losses, fallback to generic types.
    Wheelbarrow,
}

/// ANALYSIS RESULT: The outcome of a compatibility check between two schemas.
#[derive(Debug, Clone)]
pub struct CompatibilityResult {
    /// Quality classification.
    pub class: TransportClass,
    /// Fidelity score (0-100%).
    pub fidelity: u8,
    /// Predicted performance hit (percentage).
    pub overhead: i8,
    /// Human-readable list of what will be lost during transport.
    pub losses: Vec<String>,
    /// INVARIANT: In the Squisher ecosystem, transport is ALWAYS viable.
    pub viable: bool,
}
