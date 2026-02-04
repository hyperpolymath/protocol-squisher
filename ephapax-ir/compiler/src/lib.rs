// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Ephapax language compiler
//!
//! This crate provides lexing, parsing, type checking, and interpretation
//! for the ephapax language with linear types.

pub mod ast;
pub mod interpreter;
pub mod parser;
pub mod tokens;

pub use ast::{Expr, Function, Program, Type};
pub use interpreter::{Interpreter, Value};
pub use parser::Parser;
pub use tokens::Lexer;

use std::fs;
use std::path::Path;

/// Compile and run an ephapax source file
pub fn run_file(path: &Path) -> Result<Value, String> {
    let source = fs::read_to_string(path)
        .map_err(|e| format!("Failed to read file: {}", e))?;

    run_source(&source)
}

/// Compile and run ephapax source code
pub fn run_source(source: &str) -> Result<Value, String> {
    let mut parser = Parser::new(source);
    let program = parser.parse_program()?;

    let mut interp = Interpreter::new(program);
    interp.run("main")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_run_simple_program() {
        let source = "fn main() { 42 }";
        let result = run_source(source).unwrap();
        assert_eq!(result, Value::Int(42));
    }

    #[test]
    fn test_run_with_function_call() {
        let source = r#"
            fn double(x) { x + x }
            fn main() { double(21) }
        "#;
        let result = run_source(source).unwrap();
        assert_eq!(result, Value::Int(42));
    }

    #[test]
    fn test_run_with_let() {
        let source = r#"
            fn main() {
                let x = 10;
                let y = 20;
                x + y
            }
        "#;
        let result = run_source(source).unwrap();
        assert_eq!(result, Value::Int(30));
    }
}
