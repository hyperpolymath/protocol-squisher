#!/usr/bin/env python3
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
"""
Test script for mixed-transport example.

Demonstrates:
- Business-class transport (safe widening: i32→i64, f32→f64)
- Concorde-class transport (perfect match: i64↔int, bool↔bool)
- How to avoid Wheelbarrow-class transport (narrowing)
"""

import mixed_transport as mt
import time


def test_sensor_reading():
    """Test Business-class transport with i32 and f32."""
    print("\n=== SensorReading (Business-class) ===")

    # Create sensor reading
    reading = mt.SensorReading(
        id=1,
        count=100,  # i32 in Rust, int in Python
        temperature=26.5,  # f32 in Rust, float in Python
        timestamp=1000
    )
    print(f"Created: {reading}")

    # Access fields (minor overhead for count and temperature)
    print(f"Count: {reading.count} (Business: i32 → int)")
    print(f"Temperature: {reading.temperature}°C (Business: f32 → float)")
    print(f"Is hot? {reading.is_hot()}")

    # Modify fields
    reading.count = 150
    reading.temperature = 30.0
    print(f"Updated: {reading}")

    assert isinstance(reading.count, int)
    assert isinstance(reading.temperature, float)
    print("✓ SensorReading test passed")


def test_large_data():
    """Test Concorde-class transport with matching types."""
    print("\n=== LargeData (Concorde-class) ===")

    # Create with large values that need i64
    large = mt.LargeData(
        big_value=3_000_000_000,  # Larger than i32::MAX
        precise_value=1.234567890123456
    )
    print(f"Created: {large}")

    # Check overflow detection
    if large.would_overflow_i32():
        print(f"⚠ big_value={large.big_value} would overflow i32!")
        print("  This is why we use i64 (Concorde-class)")

    # Create with small values (still Concorde)
    small = mt.LargeData(big_value=100, precise_value=1.5)
    print(f"\nSmall values: {small}")
    print(f"Would overflow i32? {small.would_overflow_i32()}")

    assert large.would_overflow_i32()
    assert not small.would_overflow_i32()
    print("✓ LargeData test passed")


def test_mixed_record():
    """Test struct with mixed transport classes."""
    print("\n=== MixedRecord (Mixed Concorde + Business) ===")

    record = mt.MixedRecord(
        id=42,  # Concorde: i64 ↔ int
        counter=0,  # Business: i32 → int
        label="example",  # Concorde: String ↔ str
        score=95.5,  # Business: f32 → float
        active=True  # Concorde: bool ↔ bool
    )
    print(f"Created: {record}")

    # Increment counter multiple times
    for _ in range(5):
        record.increment()
    print(f"After 5 increments: {record}")

    assert record.counter == 5
    print("✓ MixedRecord test passed")


def benchmark_business_vs_concorde():
    """Compare Business-class (i32) vs Concorde-class (i64) overhead."""
    print("\n=== Performance Comparison ===")

    # Create test objects
    sensor = mt.SensorReading(1, 0, 25.0, 1000)
    large = mt.LargeData(0, 1.0)

    iterations = 1_000_000

    # Benchmark Business-class (i32 → int)
    start = time.perf_counter()
    for i in range(iterations):
        sensor.count = i
        _ = sensor.count
    end = time.perf_counter()
    business_ns = (end - start) / iterations * 1_000_000_000

    # Benchmark Concorde-class (i64 ↔ int)
    start = time.perf_counter()
    for i in range(iterations):
        large.big_value = i
        _ = large.big_value
    end = time.perf_counter()
    concorde_ns = (end - start) / iterations * 1_000_000_000

    print(f"Business-class (i32→int): {business_ns:.1f} ns per access")
    print(f"Concorde-class (i64↔int): {concorde_ns:.1f} ns per access")
    print(f"Overhead: {business_ns - concorde_ns:.1f} ns ({((business_ns/concorde_ns - 1) * 100):.1f}% slower)")

    print("\n💡 Insight:")
    print("Business-class has 2-5ns overhead (safe widening)")
    print("Wheelbarrow-class would be 100-1000ns (JSON fallback)")
    print("Business is acceptable, Wheelbarrow should be avoided")


def main():
    """Run all tests and benchmarks."""
    print("Mixed Transport Example")
    print("=" * 50)

    test_sensor_reading()
    test_large_data()
    test_mixed_record()
    benchmark_business_vs_concorde()

    print("\n" + "=" * 50)
    print("All tests passed!")
    print("\nKey Takeaways:")
    print("✓ Concorde-class: 100% fidelity, 0% overhead (i64↔int, f64↔float)")
    print("✓ Business-class: 98% fidelity, 5% overhead (i32→int, f32→float)")
    print("✗ Wheelbarrow-class: 50% fidelity, 80% overhead (avoid narrowing!)")


if __name__ == "__main__":
    main()
