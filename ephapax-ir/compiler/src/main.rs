// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Ephapax compiler CLI

use ephapax_compiler::{check_source, run_file, run_source_checked, Value};
use std::env;
use std::fs;
use std::path::PathBuf;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: ephapax [--check] <file.eph>");
        eprintln!("   or: ephapax [--check] -e '<code>'");
        eprintln!();
        eprintln!("Options:");
        eprintln!("  --check    Type check only, don't run");
        process::exit(1);
    }

    // Check for --check flag
    let check_only = args.contains(&"--check".to_string());
    let start_idx = if check_only { 2 } else { 1 };

    if start_idx >= args.len() {
        eprintln!("Expected file or -e flag after --check");
        process::exit(1);
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
