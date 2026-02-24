// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn unique_temp_dir(prefix: &str) -> PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after unix epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("protocol-squisher-cli-{prefix}-{nonce}"));
    fs::create_dir_all(&dir).expect("failed to create temp dir for integration test");
    dir
}

fn sample_rust_schema() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/zero-copy-demo/src/lib.rs")
}

#[test]
fn compile_rust_to_protobuf_generates_proto_schema() {
    let output_dir = unique_temp_dir("compile-protobuf");
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");

    let output = Command::new(exe)
        .arg("compile")
        .arg("--from")
        .arg("rust")
        .arg("--to")
        .arg("protobuf")
        .arg("--input")
        .arg(sample_rust_schema())
        .arg("--output")
        .arg(&output_dir)
        .output()
        .expect("failed to execute protocol-squisher CLI");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "compile command failed (status: {:?})\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );

    let generated = output_dir.join("generated.proto");
    let schema = fs::read_to_string(&generated).expect("expected generated.proto to exist");
    assert!(schema.contains("syntax = \"proto3\";"));
    assert!(schema.contains("message Point"));

    let _ = fs::remove_dir_all(&output_dir);
}

#[test]
fn compile_to_unimplemented_target_fails_clearly() {
    let output_dir = unique_temp_dir("compile-unimplemented");
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");

    let output = Command::new(exe)
        .arg("compile")
        .arg("--from")
        .arg("rust")
        .arg("--to")
        .arg("thrift")
        .arg("--input")
        .arg(sample_rust_schema())
        .arg("--output")
        .arg(&output_dir)
        .output()
        .expect("failed to execute protocol-squisher CLI");

    assert!(
        !output.status.success(),
        "expected compile to thrift to fail until thrift codegen is implemented"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("Code generation for target 'thrift' is not implemented yet."));

    let _ = fs::remove_dir_all(&output_dir);
}
