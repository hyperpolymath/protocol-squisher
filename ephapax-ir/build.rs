// SPDX-License-Identifier: PMPL-1.0-or-later
// Build script to compile ephapax IR sources to WASM

use std::path::Path;
use std::process::Command;

fn main() -> anyhow::Result<()> {
    println!("cargo:rerun-if-changed=src/types.eph");
    println!("cargo:rerun-if-changed=src/compat.eph");
    println!("cargo:rerun-if-env-changed=EPHAPAX_CLI");

    let out_dir = std::env::var("OUT_DIR")?;

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
        Ok(s) if s.success() => {
            println!("cargo:warning=Compiled types.eph to WASM");
        },
        Ok(s) => {
            println!("cargo:warning=ephapax-cli failed with status: {}", s);
            println!("cargo:warning=Skipping ephapax compilation (falling back to stub mode)");
        },
        Err(e) => {
            println!("cargo:warning=ephapax-cli not found: {}", e);
            println!("cargo:warning=Skipping ephapax compilation (falling back to stub mode)");
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
        Ok(s) if s.success() => {
            println!("cargo:warning=Compiled compat.eph to WASM");
        },
        _ => {
            println!("cargo:warning=Skipping compat.eph compilation");
        },
    }

    let mode = if types_compiled && compat_compiled {
        "verified"
    } else {
        "stub"
    };
    println!("cargo:rustc-env=PROTOCOL_SQUISHER_EPHAPAX_MODE={mode}");
    if mode == "stub" {
        println!(
            "cargo:warning=Building in STUB mode (set EPHAPAX_CLI to enable verified backend)"
        );
    }

    Ok(())
}
