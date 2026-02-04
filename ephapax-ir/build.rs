// SPDX-License-Identifier: PMPL-1.0-or-later
// Build script to compile ephapax IR sources to WASM

use std::process::Command;
use std::path::Path;

fn main() -> anyhow::Result<()> {
    println!("cargo:rerun-if-changed=src/types.eph");
    println!("cargo:rerun-if-changed=src/compat.eph");

    let out_dir = std::env::var("OUT_DIR")?;

    // Check if ephapax-cli is available
    let ephapax_cli = std::env::var("EPHAPAX_CLI")
        .unwrap_or_else(|_| "ephapax-cli".to_string());

    // Compile types.eph to WASM
    let types_output = Path::new(&out_dir).join("types.wasm");
    let status = Command::new(&ephapax_cli)
        .args(&["compile", "src/types.eph", "-o"])
        .arg(&types_output)
        .status();

    match status {
        Ok(s) if s.success() => {
            println!("cargo:warning=Compiled types.eph to WASM");
        },
        Ok(s) => {
            println!("cargo:warning=ephapax-cli failed with status: {}", s);
            println!("cargo:warning=Skipping ephapax compilation (ephapax not ready yet)");
        },
        Err(e) => {
            println!("cargo:warning=ephapax-cli not found: {}", e);
            println!("cargo:warning=Skipping ephapax compilation (will use stubs)");
        }
    }

    // Compile compat.eph to WASM
    let compat_output = Path::new(&out_dir).join("compat.wasm");
    let status = Command::new(&ephapax_cli)
        .args(&["compile", "src/compat.eph", "-o"])
        .arg(&compat_output)
        .status();

    match status {
        Ok(s) if s.success() => {
            println!("cargo:warning=Compiled compat.eph to WASM");
        },
        _ => {
            println!("cargo:warning=Skipping compat.eph compilation");
        }
    }

    Ok(())
}
