# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
"""
Python type definitions matching the Rust types.

These Pydantic models are perfectly compatible with the Rust types,
resulting in Concorde-class (zero-copy) transport.
"""

from pydantic import BaseModel


class Point(BaseModel):
    """2D point with integer coordinates.

    Transport Class: Concorde
    - x: int (i64) ↔ Rust i64
    - y: int (i64) ↔ Rust i64
    """
    x: int  # Python int is i64 internally
    y: int  # Perfect match with Rust i64


class Person(BaseModel):
    """Person record with basic information.

    Transport Class: Concorde
    - name: str ↔ Rust String
    - age: int (i64) ↔ Rust i64
    - active: bool ↔ Rust bool
    """
    name: str      # UTF-8 string, perfect match
    age: int       # Python int (i64)
    active: bool   # Boolean, perfect match


class Vector3D(BaseModel):
    """3D vector with floating-point components.

    Transport Class: Concorde
    - x: float (f64) ↔ Rust f64
    - y: float (f64) ↔ Rust f64
    - z: float (f64) ↔ Rust f64
    """
    x: float  # Python float is f64 (IEEE 754 double)
    y: float  # Perfect match with Rust f64
    z: float


class Message(BaseModel):
    """Message with metadata.

    Transport Class: Concorde
    - id: int (i64) ↔ Rust i64
    - content: str ↔ Rust String
    - timestamp: int (i64) ↔ Rust i64
    - read: bool ↔ Rust bool
    """
    id: int
    content: str
    timestamp: int  # Unix timestamp
    read: bool
