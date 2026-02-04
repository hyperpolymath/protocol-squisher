// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! Zero-Copy Interop Example
//!
//! This example demonstrates Concorde-class (100% fidelity, 0% overhead)
//! conversions between Rust and Python.
//!
//! All types in this example are perfectly compatible:
//! - Rust i64 ↔ Python int (both 64-bit signed)
//! - Rust f64 ↔ Python float (both IEEE 754 double)
//! - Rust String ↔ Python str (UTF-8 strings)
//! - Rust bool ↔ Python bool (boolean values)

use pyo3::prelude::*;
use serde::{Deserialize, Serialize};

/// A 2D point with i64 coordinates (zero-copy with Python)
///
/// **Transport Class: Concorde**
/// - Both fields are i64 → Python int (perfect match)
/// - Zero serialization overhead
/// - Direct memory access via PyO3
#[pyclass]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Point {
    /// X coordinate (Concorde: i64 ↔ int)
    #[pyo3(get, set)]
    pub x: i64,

    /// Y coordinate (Concorde: i64 ↔ int)
    #[pyo3(get, set)]
    pub y: i64,
}

#[pymethods]
impl Point {
    /// Create a new point
    #[new]
    pub fn new(x: i64, y: i64) -> Self {
        Self { x, y }
    }

    /// Calculate distance from origin (pure Rust, called from Python)
    pub fn distance_from_origin(&self) -> f64 {
        ((self.x.pow(2) + self.y.pow(2)) as f64).sqrt()
    }

    /// String representation
    pub fn __repr__(&self) -> String {
        format!("Point(x={}, y={})", self.x, self.y)
    }
}

/// A person record with perfectly compatible types
///
/// **Transport Class: Concorde**
/// - name: String ↔ str (both UTF-8)
/// - age: i64 ↔ int (both 64-bit signed)
/// - active: bool ↔ bool (both boolean)
#[pyclass]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Person {
    /// Person's name (Concorde: String ↔ str)
    #[pyo3(get, set)]
    pub name: String,

    /// Person's age in years (Concorde: i64 ↔ int)
    #[pyo3(get, set)]
    pub age: i64,

    /// Whether person is active (Concorde: bool ↔ bool)
    #[pyo3(get, set)]
    pub active: bool,
}

#[pymethods]
impl Person {
    /// Create a new person
    #[new]
    pub fn new(name: String, age: i64, active: bool) -> Self {
        Self { name, age, active }
    }

    /// Check if person is adult (age >= 18)
    pub fn is_adult(&self) -> bool {
        self.age >= 18
    }

    /// Increment age by one year
    pub fn birthday(&mut self) {
        self.age += 1;
    }

    /// String representation
    pub fn __repr__(&self) -> String {
        format!(
            "Person(name='{}', age={}, active={})",
            self.name, self.age, self.active
        )
    }
}

/// A 3D vector with f64 components (zero-copy with Python)
///
/// **Transport Class: Concorde**
/// All fields are f64 → Python float (IEEE 754 double precision)
#[pyclass]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Vector3D {
    /// X component (Concorde: f64 ↔ float)
    #[pyo3(get, set)]
    pub x: f64,

    /// Y component (Concorde: f64 ↔ float)
    #[pyo3(get, set)]
    pub y: f64,

    /// Z component (Concorde: f64 ↔ float)
    #[pyo3(get, set)]
    pub z: f64,
}

#[pymethods]
impl Vector3D {
    /// Create a new 3D vector
    #[new]
    pub fn new(x: f64, y: f64, z: f64) -> Self {
        Self { x, y, z }
    }

    /// Calculate magnitude
    pub fn magnitude(&self) -> f64 {
        (self.x.powi(2) + self.y.powi(2) + self.z.powi(2)).sqrt()
    }

    /// Dot product with another vector
    pub fn dot(&self, other: &Vector3D) -> f64 {
        self.x * other.x + self.y * other.y + self.z * other.z
    }

    /// String representation
    pub fn __repr__(&self) -> String {
        format!("Vector3D(x={}, y={}, z={})", self.x, self.y, self.z)
    }
}

/// A message record with metadata
///
/// **Transport Class: Concorde**
/// All fields are perfectly compatible with Python
#[pyclass]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    /// Message ID (Concorde: i64 ↔ int)
    #[pyo3(get, set)]
    pub id: i64,

    /// Message content (Concorde: String ↔ str)
    #[pyo3(get, set)]
    pub content: String,

    /// Unix timestamp (Concorde: i64 ↔ int)
    #[pyo3(get, set)]
    pub timestamp: i64,

    /// Read flag (Concorde: bool ↔ bool)
    #[pyo3(get, set)]
    pub read: bool,
}

#[pymethods]
impl Message {
    /// Create a new message
    #[new]
    pub fn new(id: i64, content: String, timestamp: i64, read: bool) -> Self {
        Self {
            id,
            content,
            timestamp,
            read,
        }
    }

    /// Mark message as read
    pub fn mark_read(&mut self) {
        self.read = true;
    }

    /// Get message age in seconds
    pub fn age_seconds(&self, current_time: i64) -> i64 {
        current_time - self.timestamp
    }

    /// String representation
    pub fn __repr__(&self) -> String {
        format!(
            "Message(id={}, content='{}...', timestamp={}, read={})",
            self.id,
            self.content.chars().take(20).collect::<String>(),
            self.timestamp,
            self.read
        )
    }
}

/// Python module definition
#[pymodule]
fn zero_copy_demo(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<Point>()?;
    m.add_class::<Person>()?;
    m.add_class::<Vector3D>()?;
    m.add_class::<Message>()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_point_creation() {
        let p = Point::new(10, 20);
        assert_eq!(p.x, 10);
        assert_eq!(p.y, 20);
    }

    #[test]
    fn test_point_distance() {
        let p = Point::new(3, 4);
        assert_eq!(p.distance_from_origin(), 5.0);
    }

    #[test]
    fn test_person_creation() {
        let person = Person::new("Alice".to_string(), 30, true);
        assert_eq!(person.name, "Alice");
        assert_eq!(person.age, 30);
        assert!(person.active);
    }

    #[test]
    fn test_person_is_adult() {
        let adult = Person::new("Bob".to_string(), 25, true);
        let child = Person::new("Charlie".to_string(), 12, true);
        assert!(adult.is_adult());
        assert!(!child.is_adult());
    }

    #[test]
    fn test_vector3d() {
        let v = Vector3D::new(3.0, 4.0, 0.0);
        assert_eq!(v.magnitude(), 5.0);
    }

    #[test]
    fn test_vector3d_dot() {
        let v1 = Vector3D::new(1.0, 2.0, 3.0);
        let v2 = Vector3D::new(4.0, 5.0, 6.0);
        assert_eq!(v1.dot(&v2), 32.0); // 1*4 + 2*5 + 3*6 = 32
    }

    #[test]
    fn test_message() {
        let mut msg = Message::new(1, "Hello".to_string(), 1000, false);
        assert!(!msg.read);
        msg.mark_read();
        assert!(msg.read);
        assert_eq!(msg.age_seconds(1100), 100);
    }
}
