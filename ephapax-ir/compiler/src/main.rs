// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Ephapax compiler CLI

use ephapax_compiler::{check_source, compile_to_wat, run_source_checked, Value};
use std::env;
use std::fs;
use std::path::PathBuf;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: ephapax [--check|--wasm] <file.eph>");
        eprintln!("   or: ephapax [--check|--wasm] -e '<code>'");
        eprintln!();
        eprintln!("Options:");
        eprintln!("  --check    Type check only, don't run");
        eprintln!("  --wasm     Compile to WebAssembly Text (WAT) format");
        process::exit(1);
    }

    // Check for flags
    let check_only = args.contains(&"--check".to_string());
    let wasm_mode = args.contains(&"--wasm".to_string());
    let start_idx = if check_only || wasm_mode { 2 } else { 1 };

    if start_idx >= args.len() {
        eprintln!("Expected file or -e flag after option");
        process::exit(1);
    }

    // WASM compilation mode
    if wasm_mode {
        let source = if args[start_idx] == "-e" {
            if start_idx + 1 >= args.len() {
                eprintln!("Expected code after -e flag");
                process::exit(1);
            }
            args[start_idx + 1].clone()
        } else {
            let path = PathBuf::from(&args[start_idx]);
            match fs::read_to_string(&path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("Failed to read file: {}", e);
                    process::exit(1);
                }
            }
        };

        match compile_to_wat(&source) {
            Ok(wat) => {
                println!("{}", wat);
                process::exit(0);
            }
            Err(e) => {
                eprintln!("Compilation error: {}", e);
                process::exit(1);
            }
        }
    }

    // Type check only mode
    if check_only {
        let source = if args[start_idx] == "-e" {
            if start_idx + 1 >= args.len() {
                eprintln!("Expected code after -e flag");
                process::exit(1);
            }
            args[start_idx + 1].clone()
        } else {
            let path = PathBuf::from(&args[start_idx]);
            match fs::read_to_string(&path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("Failed to read file: {}", e);
                    process::exit(1);
                }
            }
        };

        match check_source(&source) {
            Ok(()) => {
                println!("✓ Type check passed (linear types verified)");
                process::exit(0);
            }
            Err(e) => {
                eprintln!("Type error: {}", e);
                process::exit(1);
            }
        }
    }

    // Run mode (with type checking)
    let result = if args[start_idx] == "-e" {
        if start_idx + 1 >= args.len() {
            eprintln!("Expected code after -e flag");
            process::exit(1);
        }
        run_source_checked(&args[start_idx + 1])
    } else {
        let path = PathBuf::from(&args[start_idx]);
        let source = match fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Failed to read file: {}", e);
                process::exit(1);
            }
        };
        run_source_checked(&source)
    };

    match result {
        Ok(value) => match value {
            Value::Int(n) => println!("{}", n),
            Value::Bool(b) => println!("{}", b),
        },
        Err(e) => {
            eprintln!("Error: {}", e);
            process::exit(1);
        }
    }
}
