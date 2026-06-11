// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Performance-focused primitives used by Protocol Squisher.
//!
//! - Zero-copy layout checks and cast helpers
//! - SIMD-assisted byte operations for compatible buffers
//! - Lazy deserialization wrappers
//! - Streaming transformation pipelines

pub mod hardware;
pub mod lazy;
pub mod simd;
pub mod streaming;
pub mod zero_copy;
