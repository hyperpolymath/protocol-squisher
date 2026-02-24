// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn pydantic_available() -> bool {
    let Ok(output) = Command::new("python3")
        .arg("-c")
        .arg("import pydantic")
        .output()
    else {
        return false;
    };

    output.status.success()
}

fn unique_temp_dir() -> PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after unix epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("protocol-squisher-cli-test-{nonce}"));
    fs::create_dir_all(&dir).expect("failed to create temp dir for integration test");
    dir
}

#[test]
fn analyze_python_file_json_output() {
    if !pydantic_available() {
        eprintln!("Skipping test: python3 does not have pydantic installed");
        return;
    }

    let temp_dir = unique_temp_dir();
    let model_path = temp_dir.join("models.py");

    let source = r#"
from pydantic import BaseModel

class User(BaseModel):
    id: int
    email: str
"#;

    fs::write(&model_path, source).expect("failed to write python model file");

    let exe = env!("CARGO_BIN_EXE_protocol-squisher");
    let output = Command::new(exe)
        .arg("analyze")
        .arg("--python")
        .arg(&model_path)
        .arg("--format")
        .arg("json")
        .output()
        .expect("failed to execute protocol-squisher CLI");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "CLI command failed (status: {:?})\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );

    assert!(stdout.contains("\"source_format\": \"pydantic\""));
    assert!(stdout.contains("\"User\""));

    let _ = fs::remove_file(&model_path);
    let _ = fs::remove_dir_all(&temp_dir);
}
