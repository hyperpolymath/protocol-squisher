// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! Mixed Transport Example
//!
//! Demonstrates Business-class (safe widening) and Wheelbarrow-class (narrowing) transport.

use pyo3::prelude::*;
use serde::{Deserialize, Serialize};

/// Business-class example: i32 fields that widen to Python int (i64)
///
/// **Transport Class: Business**
/// - count: i32 → int (i64) - safe widening, minor overhead
/// - temperature: f32 → float (f64) - safe widening
#[pyclass]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SensorReading {
    /// Sensor ID (Concorde: i64 ↔ int)
    #[pyo3(get, set)]
    pub id: i64,

    /// Reading count (Business: i32 → int, safe widening)
    #[pyo3(get, set)]
    pub count: i32,

    /// Temperature in Celsius (Business: f32 → float, safe widening)
    #[pyo3(get, set)]
    pub temperature: f32,

    /// Timestamp (Concorde: i64 ↔ int)
    #[pyo3(get, set)]
    pub timestamp: i64,
}

#[pymethods]
impl SensorReading {
    #[new]
    pub fn new(id: i64, count: i32, temperature: f32, timestamp: i64) -> Self {
        Self {
            id,
            count,
            temperature,
            timestamp,
        }
    }

    pub fn is_hot(&self) -> bool {
        self.temperature > 25.0
    }

    pub fn __repr__(&self) -> String {
        format!(
            "SensorReading(id={}, count={}, temp={:.1}°C, ts={})",
            self.id, self.count, self.temperature, self.timestamp
        )
    }
}

/// ANTI-PATTERN: Struct that would cause Wheelbarrow transport if narrowed
///
/// This struct uses large types. If the Python side tries to use smaller types,
/// it will result in Wheelbarrow-class transport (JSON fallback).
#[pyclass]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LargeData {
    /// Large number that might not fit in i32
    #[pyo3(get, set)]
    pub big_value: i64,

    /// High-precision float
    #[pyo3(get, set)]
    pub precise_value: f64,
}

#[pymethods]
impl LargeData {
    #[new]
    pub fn new(big_value: i64, precise_value: f64) -> Self {
        Self {
            big_value,
            precise_value,
        }
    }

    /// Demonstrate potential overflow if narrowing to i32
    pub fn would_overflow_i32(&self) -> bool {
        self.big_value > i32::MAX as i64 || self.big_value < i32::MIN as i64
    }

    pub fn __repr__(&self) -> String {
        format!(
            "LargeData(big_value={}, precise_value={})",
            self.big_value, self.precise_value
        )
    }
}

/// Mixed transport: some Concorde, some Business
#[pyclass]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MixedRecord {
    /// Concorde: i64 ↔ int
    #[pyo3(get, set)]
    pub id: i64,

    /// Business: i32 → int (safe widening)
    #[pyo3(get, set)]
    pub counter: i32,

    /// Concorde: String ↔ str
    #[pyo3(get, set)]
    pub label: String,

    /// Business: f32 → float (safe widening)
    #[pyo3(get, set)]
    pub score: f32,

    /// Concorde: bool ↔ bool
    #[pyo3(get, set)]
    pub active: bool,
}

#[pymethods]
impl MixedRecord {
    #[new]
    pub fn new(id: i64, counter: i32, label: String, score: f32, active: bool) -> Self {
        Self {
            id,
            counter,
            label,
            score,
            active,
        }
    }

    pub fn increment(&mut self) {
        self.counter += 1;
    }

    pub fn __repr__(&self) -> String {
        format!(
            "MixedRecord(id={}, counter={}, label='{}', score={:.2}, active={})",
            self.id, self.counter, self.label, self.score, self.active
        )
    }
}

#[pymodule]
fn mixed_transport(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<SensorReading>()?;
    m.add_class::<LargeData>()?;
    m.add_class::<MixedRecord>()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sensor_reading() {
        let reading = SensorReading::new(1, 100, 26.5, 1000);
        assert_eq!(reading.count, 100);
        assert_eq!(reading.temperature, 26.5);
        assert!(reading.is_hot());
    }

    #[test]
    fn test_large_data_overflow() {
        let large = LargeData::new(3_000_000_000, 1.23456789);
        assert!(large.would_overflow_i32());

        let small = LargeData::new(100, 1.5);
        assert!(!small.would_overflow_i32());
    }

    #[test]
    fn test_mixed_record() {
        let mut record = MixedRecord::new(
            1,
            0,
            "test".to_string(),
            95.5,
            true,
        );
        record.increment();
        assert_eq!(record.counter, 1);
    }
}
