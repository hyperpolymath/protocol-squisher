// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Child, Command, Output, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

fn sample_rust_schema() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/zero-copy-demo/src/lib.rs")
}

fn temp_path(name: &str) -> PathBuf {
    let nanos = match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(duration) => duration.as_nanos(),
        Err(_) => 0,
    };
    std::env::temp_dir().join(format!("protocol-squisher-{name}-{nanos}"))
}

fn write_temp_rust_schema(path: &PathBuf, body: &str) {
    let parent = match path.parent() {
        Some(parent) => parent,
        None => panic!("temp schema file should have a parent directory"),
    };
    if let Err(err) = fs::create_dir_all(parent) {
        panic!("create schema parent dir: {err}");
    }
    if let Err(err) = fs::write(path, body) {
        panic!("write temp schema: {err}");
    }
}

fn command_output(cmd: &mut Command, context: &str) -> Output {
    match cmd.output() {
        Ok(output) => output,
        Err(err) => panic!("{context}: {err}"),
    }
}

fn command_spawn(cmd: &mut Command, context: &str) -> Child {
    match cmd.spawn() {
        Ok(child) => child,
        Err(err) => panic!("{context}: {err}"),
    }
}

fn parse_json(bytes: &[u8], context: &str) -> serde_json::Value {
    match serde_json::from_slice(bytes) {
        Ok(value) => value,
        Err(err) => panic!("{context}: {err}"),
    }
}

fn wait_with_output(child: Child, context: &str) -> Output {
    match child.wait_with_output() {
        Ok(output) => output,
        Err(err) => panic!("{context}: {err}"),
    }
}

fn write_all_or_panic(writer: &mut dyn Write, bytes: &[u8], context: &str) {
    if let Err(err) = writer.write_all(bytes) {
        panic!("{context}: {err}");
    }
}

fn remove_dir_if_exists(path: PathBuf) {
    if let Err(err) = fs::remove_dir_all(path) {
        if err.kind() != std::io::ErrorKind::NotFound {
            panic!("cleanup dir failed: {err}");
        }
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
fn schema_registry_publish_and_fetch_json() {
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");
    let registry_dir = temp_path("registry");

    let publish = command_output(
        Command::new(exe)
            .arg("schema-registry")
            .arg("--registry-dir")
            .arg(&registry_dir)
            .arg("--format")
            .arg("json")
            .arg("publish")
            .arg("--name")
            .arg("demo.user")
            .arg("--version")
            .arg("1.0.0")
            .arg("--protocol")
            .arg("rust")
            .arg("--input")
            .arg(sample_rust_schema()),
        "run schema-registry publish",
    );
    assert!(
        publish.status.success(),
        "publish failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&publish.stdout),
        String::from_utf8_lossy(&publish.stderr)
    );

    let fetch = command_output(
        Command::new(exe)
            .arg("schema-registry")
            .arg("--registry-dir")
            .arg(&registry_dir)
            .arg("--format")
            .arg("json")
            .arg("fetch")
            .arg("--name")
            .arg("demo.user")
            .arg("--version")
            .arg("1.0.0"),
        "run schema-registry fetch",
    );
    assert!(
        fetch.status.success(),
        "fetch failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&fetch.stdout),
        String::from_utf8_lossy(&fetch.stderr)
    );

    let json = parse_json(&fetch.stdout, "parse fetch response json");
    assert_eq!(json["name"], "demo.user");
    assert_eq!(json["version"], "1.0.0");

    remove_dir_if_exists(registry_dir);
}

#[test]
fn migrate_and_governance_commands_work() {
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");

    let migrate = command_output(
        Command::new(exe)
            .arg("migrate")
            .arg("--from-format")
            .arg("rust")
            .arg("--to-format")
            .arg("rust")
            .arg("--from")
            .arg(sample_rust_schema())
            .arg("--to")
            .arg(sample_rust_schema())
            .arg("--format")
            .arg("json"),
        "run migrate",
    );
    assert!(
        migrate.status.success(),
        "migrate failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&migrate.stdout),
        String::from_utf8_lossy(&migrate.stderr)
    );
    let migrate_json = parse_json(&migrate.stdout, "parse migrate json");
    assert!(migrate_json.get("steps").is_some());

    let from_path = temp_path("gov-source.rs");
    let to_path = temp_path("gov-target.rs");
    write_temp_rust_schema(
        &from_path,
        r#"
        use serde::{Serialize, Deserialize};
        #[derive(Serialize, Deserialize)]
        pub struct Record { pub id: i64, pub legacy: i64 }
        "#,
    );
    write_temp_rust_schema(
        &to_path,
        r#"
        use serde::{Serialize, Deserialize};
        #[derive(Serialize, Deserialize)]
        pub struct Record { pub id: i64 }
        "#,
    );

    let governance = command_output(
        Command::new(exe)
            .arg("governance-check")
            .arg("--from-format")
            .arg("rust")
            .arg("--to-format")
            .arg("rust")
            .arg("--from")
            .arg(&from_path)
            .arg("--to")
            .arg(&to_path)
            .arg("--max-breaking-changes")
            .arg("0")
            .arg("--minimum-class")
            .arg("business")
            .arg("--format")
            .arg("json"),
        "run governance-check",
    );
    assert!(
        governance.status.success(),
        "governance failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&governance.stdout),
        String::from_utf8_lossy(&governance.stderr)
    );
    let governance_json = parse_json(&governance.stdout, "parse governance json");
    assert_eq!(governance_json["allowed"], false);

    remove_file_if_exists(from_path);
    remove_file_if_exists(to_path);
}

#[test]
fn marketplace_and_explorer_commands_work() {
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");
    let marketplace_dir = temp_path("marketplace");

    let publish = command_output(
        Command::new(exe)
            .arg("marketplace")
            .arg("--marketplace-dir")
            .arg(&marketplace_dir)
            .arg("--format")
            .arg("json")
            .arg("publish")
            .arg("--id")
            .arg("rust-python-v1")
            .arg("--name")
            .arg("Rust->Python")
            .arg("--from-format")
            .arg("rust")
            .arg("--to-format")
            .arg("python")
            .arg("--version")
            .arg("1.0.0")
            .arg("--description")
            .arg("Interop adapter")
            .arg("--tags")
            .arg("safe,prod"),
        "run marketplace publish",
    );
    assert!(
        publish.status.success(),
        "marketplace publish failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&publish.stdout),
        String::from_utf8_lossy(&publish.stderr)
    );

    let list = command_output(
        Command::new(exe)
            .arg("marketplace")
            .arg("--marketplace-dir")
            .arg(&marketplace_dir)
            .arg("--format")
            .arg("json")
            .arg("list")
            .arg("--from-format")
            .arg("rust"),
        "run marketplace list",
    );
    assert!(
        list.status.success(),
        "marketplace list failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&list.stdout),
        String::from_utf8_lossy(&list.stderr)
    );
    let list_json = parse_json(&list.stdout, "parse marketplace list json");
    assert!(list_json.as_array().is_some_and(|a| !a.is_empty()));

    let explore = command_output(
        Command::new(exe)
            .arg("explore")
            .arg("--from-format")
            .arg("rust")
            .arg("--to-format")
            .arg("rust")
            .arg("--from")
            .arg(sample_rust_schema())
            .arg("--to")
            .arg(sample_rust_schema()),
        "run explorer",
    );
    assert!(
        explore.status.success(),
        "explore failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&explore.stdout),
        String::from_utf8_lossy(&explore.stderr)
    );
    assert!(
        String::from_utf8_lossy(&explore.stdout).contains("Compatibility Explorer"),
        "explore output missing expected heading"
    );

    remove_dir_if_exists(marketplace_dir);
}

#[test]
fn playground_dump_and_lsp_once_smoke() {
    let exe = env!("CARGO_BIN_EXE_protocol-squisher");

    let html = command_output(
        Command::new(exe).arg("playground").arg("--dump-html"),
        "run playground --dump-html",
    );
    assert!(
        html.status.success(),
        "playground dump failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&html.stdout),
        String::from_utf8_lossy(&html.stderr)
    );
    assert!(
        String::from_utf8_lossy(&html.stdout).contains("Protocol Squisher Playground"),
        "playground HTML missing title"
    );

    let mut child = command_spawn(
        Command::new(exe)
            .arg("lsp")
            .arg("--once")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped()),
        "spawn lsp command",
    );

    let request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": {}
    })
    .to_string();
    let framed = format!("Content-Length: {}\r\n\r\n{}", request.len(), request);

    {
        let stdin = match child.stdin.as_mut() {
            Some(stdin) => stdin,
            None => panic!("child stdin missing"),
        };
        write_all_or_panic(stdin, framed.as_bytes(), "write initialize request");
    }

    let output = wait_with_output(child, "wait for lsp process");
    assert!(
        output.status.success(),
        "lsp failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Content-Length:"),
        "lsp output missing framing"
    );
    assert!(
        stdout.contains("capabilities"),
        "lsp output missing capabilities"
    );
}
