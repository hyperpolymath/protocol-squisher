// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

use std::process::Command;

#[test]
fn performance_text_output_succeeds() {
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");

    let output = Command::new(exe)
        .arg("performance")
        .arg("--sample-size")
        .arg("32768")
        .output()
        .expect("failed to execute protocol-squisher CLI");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "performance command failed (status: {:?})\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );

    assert!(stdout.contains("Performance Optimization Report"));
    assert!(stdout.contains("Zero-copy possible:"));
    assert!(stdout.contains("Streaming transform:"));
}

#[test]
fn performance_json_output_is_valid() {
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");

    let output = Command::new(exe)
        .arg("performance")
        .arg("--sample-size")
        .arg("16384")
        .arg("--format")
        .arg("json")
        .output()
        .expect("failed to execute protocol-squisher CLI");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "performance json command failed (status: {:?})\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );

    let parsed: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid performance json output");
    assert!(parsed.get("zero_copy_possible").is_some());
    assert!(parsed.get("streamed_records").is_some());
    assert!(parsed.get("simd_ns").is_some());
}
