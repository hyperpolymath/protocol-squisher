// SPDX-License-Identifier: PMPL-1.0-or-later
// Zero-copy interop example - Concorde class

use serde::{Deserialize, Serialize};

/// Point with i64 coordinates - perfect match for Python int
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Point {
    pub x: i64,
    pub y: i64,
}

/// Person with zero-copy compatible fields
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Person {
    pub name: String,
    pub age: i64,
    pub active: bool,
}

/// Vector3D - all fields zero-copy
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Vector3D {
    pub x: f64,
    pub y: f64,
    pub z: f64,
}

/// Message with metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    pub id: i64,
    pub content: String,
    pub timestamp: i64,
    pub read: bool,
}
