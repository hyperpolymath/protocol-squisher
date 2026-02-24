// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Enterprise-facing capabilities for Protocol Squisher.

pub mod audit;
pub mod governance;
pub mod marketplace;
pub mod migration;
pub mod registry;

use std::time::{SystemTime, UNIX_EPOCH};

pub fn unix_timestamp_utc() -> String {
    let seconds = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();
    seconds.to_string()
}
