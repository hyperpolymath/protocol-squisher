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
pub mod typeck;

pub use ast::{Expr, Function, Program, Type};
pub use interpreter::{Interpreter, Value};
pub use parser::Parser;
pub use tokens::Lexer;
pub use typeck::{TypeChecker, TypeError};

use std::fs;
use std::path::Path;

/// Compile and run an ephapax source file (without type checking)
pub fn run_file(path: &Path) -> Result<Value, String> {
    let source = fs::read_to_string(path)
        .map_err(|e| format!("Failed to read file: {}", e))?;

    run_source(&source)
}

/// Compile and run an ephapax source file (with linear type checking)
pub fn run_file_checked(path: &Path) -> Result<Value, String> {
    let source = fs::read_to_string(path)
        .map_err(|e| format!("Failed to read file: {}", e))?;

    run_source_checked(&source)
}

/// Compile and run ephapax source code
pub fn run_source(source: &str) -> Result<Value, String> {
    let mut parser = Parser::new(source);
    let program = parser.parse_program()?;

    let mut interp = Interpreter::new(program);
    interp.run("main")
}

/// Compile and run ephapax source code with linear type checking
pub fn run_source_checked(source: &str) -> Result<Value, String> {
    let mut parser = Parser::new(source);
    let program = parser.parse_program()?;

    // Run linear type checker
    let checker = TypeChecker::new(&program);
    checker.check().map_err(|e| e.to_string())?;

    // If type checking passes, run interpreter
    let mut interp = Interpreter::new(program);
    interp.run("main")
}

/// Type check ephapax source code without running
pub fn check_source(source: &str) -> Result<(), String> {
    let mut parser = Parser::new(source);
    let program = parser.parse_program()?;

    let checker = TypeChecker::new(&program);
    checker.check().map_err(|e| e.to_string())
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
