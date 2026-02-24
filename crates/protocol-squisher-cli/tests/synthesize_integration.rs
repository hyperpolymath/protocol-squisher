// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

use std::path::PathBuf;
use std::process::Command;

fn sample_rust_schema() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/zero-copy-demo/src/lib.rs")
}

#[test]
fn synthesize_text_output_succeeds() {
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");

    let output = Command::new(exe)
        .arg("synthesize")
        .arg("--from-format")
        .arg("rust")
        .arg("--to-format")
        .arg("rust")
        .arg("--from")
        .arg(sample_rust_schema())
        .arg("--to")
        .arg(sample_rust_schema())
        .output()
        .expect("failed to execute protocol-squisher CLI");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "synthesize command failed (status: {:?})\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );

    assert!(stdout.contains("miniKanren Synthesis Plan"));
    assert!(stdout.contains("Satisfiable:"));
    assert!(stdout.contains("Steps:"));
}

#[test]
fn synthesize_json_output_is_valid() {
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");

    let output = Command::new(exe)
        .arg("synthesize")
        .arg("--from-format")
        .arg("rust")
        .arg("--to-format")
        .arg("rust")
        .arg("--from")
        .arg(sample_rust_schema())
        .arg("--to")
        .arg(sample_rust_schema())
        .arg("--format")
        .arg("json")
        .output()
        .expect("failed to execute protocol-squisher CLI");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "synthesize json command failed (status: {:?})\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );

    let parsed: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid json synthesis plan");
    assert!(parsed.get("satisfiable").is_some());
    assert!(parsed.get("steps").is_some());
}
