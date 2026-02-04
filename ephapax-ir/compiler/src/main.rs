// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Ephapax compiler CLI

use ephapax_compiler::{run_file, run_source, Value};
use std::env;
use std::path::PathBuf;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: ephapax <file.eph>");
        eprintln!("   or: ephapax -e '<code>'");
        process::exit(1);
    }

    let result = if args[1] == "-e" {
        if args.len() < 3 {
            eprintln!("Expected code after -e flag");
            process::exit(1);
        }
        run_source(&args[2])
    } else {
        let path = PathBuf::from(&args[1]);
        run_file(&path)
    };

    match result {
        Ok(value) => {
            match value {
                Value::Int(n) => println!("{}", n),
                Value::Bool(b) => println!("{}", b),
            }
        }
        Err(e) => {
            eprintln!("Error: {}", e);
            process::exit(1);
        }
    }
}
