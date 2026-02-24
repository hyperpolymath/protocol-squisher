// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

fn sample_rust_schema() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/zero-copy-demo/src/lib.rs")
}

fn sample_python_schema() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/zero-copy-demo/models.py")
}

fn temp_path(name: &str) -> PathBuf {
    let nanos = match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(duration) => duration.as_nanos(),
        Err(_) => 0,
    };
    std::env::temp_dir().join(format!("protocol-squisher-{name}-{nanos}"))
}

fn command_output(cmd: &mut Command, context: &str) -> Output {
    match cmd.output() {
        Ok(output) => output,
        Err(err) => panic!("{context}: {err}"),
    }
}

fn parse_json(bytes: &[u8], context: &str) -> serde_json::Value {
    match serde_json::from_slice(bytes) {
        Ok(value) => value,
        Err(err) => panic!("{context}: {err}"),
    }
}

fn remove_file_if_exists(path: PathBuf) {
    if let Err(err) = fs::remove_file(path) {
        if err.kind() != std::io::ErrorKind::NotFound {
            panic!("cleanup file failed: {err}");
        }
    }
}

#[test]
fn optimize_ai_outputs_json_summary() {
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");
    let output = command_output(
        Command::new(exe)
            .arg("optimize-ai")
            .arg("--rust")
            .arg(sample_rust_schema())
            .arg("--python")
            .arg(sample_python_schema())
            .arg("--format")
            .arg("json"),
        "run optimize-ai",
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    if !output.status.success() && stderr.contains("Pydantic not installed") {
        eprintln!("skipping optimize-ai test: active interpreter is missing pydantic");
        return;
    }

    assert!(
        output.status.success(),
        "optimize-ai failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&output.stdout),
        stderr
    );

    let json = parse_json(&output.stdout, "parse optimize-ai json");
    assert!(json.get("summary").is_some(), "missing summary payload");
    assert!(json["summary"]["recommendation_confidence"].is_number());
}

#[test]
fn distributed_squish_runs_manifest() {
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");
    let manifest_path = temp_path("distributed-manifest.json");
    let manifest = serde_json::json!([
        {
            "id": "pair-1",
            "from_format": "rust",
            "to_format": "rust",
            "from": sample_rust_schema(),
            "to": sample_rust_schema()
        }
    ]);
    let manifest_bytes = match serde_json::to_vec_pretty(&manifest) {
        Ok(bytes) => bytes,
        Err(err) => panic!("serialize manifest: {err}"),
    };
    if let Err(err) = fs::write(&manifest_path, manifest_bytes) {
        panic!("write manifest: {err}");
    }

    let output = command_output(
        Command::new(exe)
            .arg("distributed-squish")
            .arg("--manifest")
            .arg(&manifest_path)
            .arg("--workers")
            .arg("2")
            .arg("--format")
            .arg("json"),
        "run distributed-squish",
    );

    assert!(
        output.status.success(),
        "distributed-squish failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let json = parse_json(&output.stdout, "parse distributed json");
    assert_eq!(json["task_count"], 1);
    assert!(json["results"]
        .as_array()
        .is_some_and(|rows| rows.len() == 1));

    remove_file_if_exists(manifest_path);
}

#[test]
fn hardware_accel_outputs_backend_report() {
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");
    let output = command_output(
        Command::new(exe)
            .arg("hardware-accel")
            .arg("--sample-size")
            .arg("65536")
            .arg("--backend")
            .arg("auto")
            .arg("--format")
            .arg("json"),
        "run hardware-accel",
    );

    assert!(
        output.status.success(),
        "hardware-accel failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let json = parse_json(&output.stdout, "parse hardware-accel json");
    assert!(json["backend"].is_string());
    assert!(json["elapsed_ns"].is_number());
}
