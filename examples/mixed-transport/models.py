# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
"""
Python type definitions for mixed-transport example.

This shows how Python int (i64) and float (f64) interact with
Rust's smaller integer types (i32, f32).
"""

from pydantic import BaseModel


class SensorReading(BaseModel):
    """
    Demonstrates Business-class transport with safe widening.

    Transport Classes:
    - id: Concorde (i64 ↔ int) - Perfect match
    - count: Business (i32 → int) - Safe widening with minor overhead
    - temperature: Business (f32 → float) - Safe widening with minor overhead
    - timestamp: Concorde (i64 ↔ int) - Perfect match
    """
    id: int
    count: int  # Rust: i32, Python: int (i64) - BUSINESS CLASS
    temperature: float  # Rust: f32, Python: float (f64) - BUSINESS CLASS
    timestamp: int


class LargeData(BaseModel):
    """
    Demonstrates Concorde-class transport when types match.

    If Python tried to use smaller types (int32, float32),
    this would become Wheelbarrow-class (JSON fallback).

    Transport Classes:
    - big_value: Concorde (i64 ↔ int) - Perfect match
    - precise_value: Concorde (f64 ↔ float) - Perfect match
    """
    big_value: int  # Rust: i64, Python: int (i64) - CONCORDE
    precise_value: float  # Rust: f64, Python: float (f64) - CONCORDE


class MixedRecord(BaseModel):
    """
    Demonstrates mixed transport classes in a single struct.

    Transport Classes:
    - id: Concorde (i64 ↔ int)
    - counter: Business (i32 → int)
    - label: Concorde (String ↔ str)
    - score: Business (f32 → float)
    - active: Concorde (bool ↔ bool)

    Overall: Business-class (some fields have minor overhead)
    """
    id: int
    counter: int  # Rust: i32 - BUSINESS CLASS
    label: str
    score: float  # Rust: f32 - BUSINESS CLASS
    active: bool


# Anti-pattern example (DON'T DO THIS):
# class BadNarrowingExample(BaseModel):
#     """
#     This would cause Wheelbarrow-class transport (AVOID!):
#     - If Rust has i64 and Python uses int32
#     - If Rust has f64 and Python uses float32
#
#     Result: 100-1000x slower due to JSON fallback
#     """
#     value: int32  # Narrowing from i64 → i32 = WHEELBARROW ✗
