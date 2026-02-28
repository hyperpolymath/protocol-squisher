// SPDX-License-Identifier: PMPL-1.0-or-later
// Build script to compile ephapax IR sources to WASM

use std::path::Path;
use std::process::Command;

fn emit_warning(enabled: bool, message: &str) {
    if enabled {
        println!("cargo:warning={message}");
    }
}

fn env_flag(var: &str) -> bool {
    matches!(
        std::env::var(var).as_deref(),
        Ok("1") | Ok("true") | Ok("TRUE") | Ok("yes") | Ok("YES")
    )
}

fn main() -> anyhow::Result<()> {
    println!("cargo:rerun-if-changed=src/types.eph");
    println!("cargo:rerun-if-changed=src/compat.eph");
    println!("cargo:rerun-if-env-changed=EPHAPAX_CLI");
    println!("cargo:rerun-if-env-changed=PROTOCOL_SQUISHER_WARN_ON_STUB");

    let out_dir = std::env::var("OUT_DIR")?;
    let warn_on_stub = env_flag("PROTOCOL_SQUISHER_WARN_ON_STUB");

    // Check if ephapax-cli is available
    let ephapax_cli = std::env::var("EPHAPAX_CLI").unwrap_or_else(|_| "ephapax-cli".to_string());

    // Compile types.eph to WASM
    let types_output = Path::new(&out_dir).join("types.wasm");
    let status = Command::new(&ephapax_cli)
        .args(["compile", "src/types.eph", "-o"])
        .arg(&types_output)
        .status();

    let types_compiled = matches!(status, Ok(s) if s.success());

    match status {
        Ok(s) if s.success() => {},
        Ok(s) => {
            emit_warning(
                warn_on_stub,
                &format!("ephapax-cli failed with status: {s}; falling back to stub mode"),
            );
        },
        Err(e) => {
            emit_warning(
                warn_on_stub,
                &format!("ephapax-cli not found: {e}; falling back to stub mode"),
            );
        },
    }

    // Compile compat.eph to WASM
    let compat_output = Path::new(&out_dir).join("compat.wasm");
    let status = Command::new(&ephapax_cli)
        .args(["compile", "src/compat.eph", "-o"])
        .arg(&compat_output)
        .status();

    let compat_compiled = matches!(status, Ok(s) if s.success());

    match status {
        Ok(s) if s.success() => {},
        _ => {
            emit_warning(warn_on_stub, "Skipping compat.eph compilation");
        },
    }

    let mode = if types_compiled && compat_compiled {
        "verified"
    } else {
        "stub"
    };
    println!("cargo:rustc-env=PROTOCOL_SQUISHER_EPHAPAX_MODE={mode}");
    if mode == "stub" {
        emit_warning(
            warn_on_stub,
            "Building in fallback mode (set EPHAPAX_CLI to enable verified backend)",
        );
    }

    Ok(())
}
