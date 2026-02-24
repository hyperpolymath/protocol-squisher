// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Performance-focused primitives used by Protocol Squisher.
//!
//! - Zero-copy layout checks and cast helpers
//! - SIMD-assisted byte operations for compatible buffers
//! - Lazy deserialization wrappers
//! - Streaming transformation pipelines

pub mod lazy;
pub mod simd;
pub mod streaming;
pub mod zero_copy;
