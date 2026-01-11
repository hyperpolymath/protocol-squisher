// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! # Protocol Squisher
//!
//! Universal protocol interoperability through automatic adapter synthesis.
//!
//! ## The Invariant
//!
//! > If it compiles, it carries.
//!
//! Every data serialization format can talk to every other format.
//! Always. Even if slow. Even if lossy. But it *will* transport.

pub mod ir {
    pub use protocol_squisher_ir::*;
}

pub mod rust_analyzer {
    pub use protocol_squisher_rust_analyzer::*;
}

pub mod python_analyzer {
    pub use protocol_squisher_python_analyzer::*;
}

pub mod compat {
    pub use protocol_squisher_compat::*;
}

pub mod pyo3_codegen {
    pub use protocol_squisher_pyo3_codegen::*;
}

pub mod json_fallback {
    pub use protocol_squisher_json_fallback::*;
}

/// Transport class classification for adapter quality
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TransportClass {
    /// Zero-copy, full fidelity, maximum performance
    Concorde,
    /// Minor overhead, full fidelity
    BusinessClass,
    /// Moderate overhead, documented losses
    Economy,
    /// High overhead, significant losses, but it works
    Wheelbarrow,
}

impl TransportClass {
    /// Minimum fidelity percentage for this class
    pub fn min_fidelity(&self) -> u8 {
        match self {
            TransportClass::Concorde => 100,
            TransportClass::BusinessClass => 90,
            TransportClass::Economy => 70,
            TransportClass::Wheelbarrow => 0,
        }
    }
}

/// Compatibility analysis result between two schemas
#[derive(Debug, Clone)]
pub struct CompatibilityResult {
    /// Transport class classification
    pub class: TransportClass,
    /// Type fidelity percentage (0-100)
    pub fidelity: u8,
    /// Estimated performance overhead percentage
    pub overhead: i8,
    /// List of documented losses
    pub losses: Vec<String>,
    /// Whether transport is viable
    pub viable: bool,
}

impl CompatibilityResult {
    /// Create a new compatibility result
    pub fn new(fidelity: u8, overhead: i8, losses: Vec<String>) -> Self {
        let class = match fidelity {
            100 => TransportClass::Concorde,
            90..=99 => TransportClass::BusinessClass,
            70..=89 => TransportClass::Economy,
            _ => TransportClass::Wheelbarrow,
        };

        Self {
            class,
            fidelity,
            overhead,
            losses,
            viable: true, // The invariant: transport is always viable
        }
    }
}
