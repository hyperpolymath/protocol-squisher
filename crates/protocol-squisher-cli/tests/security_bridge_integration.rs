// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

use std::process::Command;

#[test]
fn security_bridge_accepts_secure_tls13_profile() {
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");

    let output = Command::new(exe)
        .arg("security-bridge")
        .arg("--tls-version")
        .arg("1.3")
        .arg("--key-exchange")
        .arg("ecdhe")
        .arg("--mutual-auth")
        .output()
        .expect("failed to execute protocol-squisher CLI");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "security-bridge command failed (status: {:?})\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );

    assert!(stdout.contains("Security Bridge: ACCEPT"));
    assert!(stdout.contains("Noise Pattern"));
}

#[test]
fn security_bridge_rejects_legacy_tls() {
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");

    let output = Command::new(exe)
        .arg("security-bridge")
        .arg("--tls-version")
        .arg("1.0")
        .arg("--key-exchange")
        .arg("ecdhe")
        .output()
        .expect("failed to execute protocol-squisher CLI");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "security-bridge command failed unexpectedly (status: {:?})\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );

    assert!(stdout.contains("Security Bridge: REJECT"));
}
