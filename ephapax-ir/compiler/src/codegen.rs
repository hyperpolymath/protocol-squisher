// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Code generation from ephapax AST to WebAssembly Text (WAT) format

use crate::ast::*;
use std::fmt::Write;

pub struct WasmCodeGen {
    wat: String,
    local_count: usize,
    #[allow(dead_code)]  // Reserved for future loop implementation
    label_count: usize,
    locals: Vec<(String, Type)>,  // Track local variables for declaration
}

impl WasmCodeGen {
    pub fn new() -> Self {
        Self {
            wat: String::new(),
            local_count: 0,
            label_count: 0,
            locals: Vec::new(),
        }
    }

    pub fn generate(&mut self, program: &Program) -> Result<String, String> {
        // WAT module header
        writeln!(&mut self.wat, "(module").map_err(|e| e.to_string())?;

        // Generate all functions
        for func in &program.functions {
            self.generate_function(func)?;
        }

        // Export main function if it exists
        if program.functions.iter().any(|f| f.name == "main") {
            writeln!(
                &mut self.wat,
                "  (export \"main\" (func $main))"
            )
            .map_err(|e| e.to_string())?;
        }

        // Module footer
        writeln!(&mut self.wat, ")").map_err(|e| e.to_string())?;

        Ok(self.wat.clone())
    }

    fn generate_function(&mut self, func: &Function) -> Result<(), String> {
        // Reset local counter and locals list for each function
        self.local_count = func.params.len();
        self.locals.clear();

        // Generate function body to a temporary string to collect locals
        let old_wat = std::mem::take(&mut self.wat);
        self.generate_expr(&func.body, 2)?;
        let body = std::mem::take(&mut self.wat);
        self.wat = old_wat;

        // Function declaration
        write!(&mut self.wat, "  (func ${}", func.name).map_err(|e| e.to_string())?;

        // Parameters
        for param in &func.params {
            write!(&mut self.wat, " (param ${} {})", param.name, Self::wasm_type(&param.ty))
                .map_err(|e| e.to_string())?;
        }

        // Return type
        if func.return_type != Type::Infer {
            write!(
                &mut self.wat,
                " (result {})",
                Self::wasm_type(&func.return_type)
            )
            .map_err(|e| e.to_string())?;
        }

        writeln!(&mut self.wat).map_err(|e| e.to_string())?;

        // Emit local declarations
        for (name, ty) in &self.locals {
            writeln!(&mut self.wat, "    (local ${} {})", name, Self::wasm_type(ty))
                .map_err(|e| e.to_string())?;
        }

        // Function body
        write!(&mut self.wat, "{}", body).map_err(|e| e.to_string())?;

        // Function footer
        writeln!(&mut self.wat, "  )").map_err(|e| e.to_string())?;

        Ok(())
    }

    fn generate_expr(&mut self, expr: &Expr, indent: usize) -> Result<(), String> {
        let ind = "  ".repeat(indent);

        match expr {
            Expr::IntLit(n) => {
                writeln!(&mut self.wat, "{}(i64.const {})", ind, n).map_err(|e| e.to_string())?;
            }

            Expr::BoolLit(b) => {
                writeln!(
                    &mut self.wat,
                    "{}(i32.const {})",
                    ind,
                    if *b { 1 } else { 0 }
                )
                .map_err(|e| e.to_string())?;
            }

            Expr::StringLit(_s) => {
                // TODO: Implement string table and linear memory for string literals
                // For now, return null pointer (0)
                writeln!(&mut self.wat, "{}(i32.const 0) ;; String literal (not yet implemented)", ind)
                    .map_err(|e| e.to_string())?;
            }

            Expr::Var(name) => {
                writeln!(&mut self.wat, "{}(local.get ${})", ind, name)
                    .map_err(|e| e.to_string())?;
            }

            Expr::BinOp { op, left, right } => {
                self.generate_expr(left, indent)?;
                self.generate_expr(right, indent)?;
                let wasm_op = Self::wasm_binop(op);
                writeln!(&mut self.wat, "{}({})", ind, wasm_op).map_err(|e| e.to_string())?;
            }

            Expr::Call { func, args } => {
                // Evaluate arguments
                for arg in args {
                    self.generate_expr(arg, indent)?;
                }
                // Call function
                writeln!(&mut self.wat, "{}(call ${})", ind, func).map_err(|e| e.to_string())?;
            }

            Expr::Let { name, value, body } => {
                // Add local variable declaration (default to i64 for now)
                if !self.locals.iter().any(|(n, _)| n == name) {
                    self.locals.push((name.clone(), Type::I64));
                }
                // Generate code for value
                self.generate_expr(value, indent)?;
                // Store in local variable
                self.local_count += 1;
                writeln!(&mut self.wat, "{}(local.set ${})", ind, name)
                    .map_err(|e| e.to_string())?;
                // Generate code for body
                self.generate_expr(body, indent)?;
            }

            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.generate_expr(cond, indent)?;
                writeln!(&mut self.wat, "{}(if (result i64)", ind).map_err(|e| e.to_string())?;
                writeln!(&mut self.wat, "{}  (then", ind).map_err(|e| e.to_string())?;
                self.generate_expr(then_branch, indent + 2)?;
                writeln!(&mut self.wat, "{}  )", ind).map_err(|e| e.to_string())?;
                writeln!(&mut self.wat, "{}  (else", ind).map_err(|e| e.to_string())?;
                self.generate_expr(else_branch, indent + 2)?;
                writeln!(&mut self.wat, "{}  )", ind).map_err(|e| e.to_string())?;
                writeln!(&mut self.wat, "{})", ind).map_err(|e| e.to_string())?;
            }

            Expr::Block(exprs) => {
                for (i, expr) in exprs.iter().enumerate() {
                    self.generate_expr(expr, indent)?;
                    // Drop intermediate results except for the last one
                    if i < exprs.len() - 1 {
                        writeln!(&mut self.wat, "{}(drop)", ind).map_err(|e| e.to_string())?;
                    }
                }
            }

            Expr::Match { scrutinee, arms } => {
                // For now, generate as nested if-else
                // More sophisticated implementation would use br_table for integer matches
                self.generate_expr(scrutinee, indent)?;

                // Store scrutinee in a temporary local
                let temp_local = self.local_count;
                let temp_name = format!("__match_{}", temp_local);
                if !self.locals.iter().any(|(n, _)| n == &temp_name) {
                    self.locals.push((temp_name.clone(), Type::I64));
                }
                self.local_count += 1;
                writeln!(&mut self.wat, "{}(local.set ${})", ind, temp_name)
                    .map_err(|e| e.to_string())?;

                // Generate nested if-else chain
                self.generate_match_arms(arms, &temp_name, indent)?;
            }

            Expr::VecLit(_elements) => {
                // TODO: Implement vector literals with linear memory
                // For now, return null pointer (0)
                writeln!(&mut self.wat, "{}(i32.const 0) ;; Vec literal (not yet implemented)", ind)
                    .map_err(|e| e.to_string())?;
            }

            Expr::HashMapLit(_entries) => {
                // TODO: Implement HashMap literals with linear memory
                // For now, return null pointer (0)
                writeln!(&mut self.wat, "{}(i32.const 0) ;; HashMap literal (not yet implemented)", ind)
                    .map_err(|e| e.to_string())?;
            }

            Expr::Index { vec: _vec, index: _index } => {
                // TODO: Implement vector indexing with linear memory
                // For now, return 0
                writeln!(&mut self.wat, "{}(i64.const 0) ;; Vec indexing (not yet implemented)", ind)
                    .map_err(|e| e.to_string())?;
            }

            Expr::StructLit { name: _name, fields: _fields } => {
                // TODO: Implement struct literals with linear memory
                // For now, return null pointer (0)
                writeln!(&mut self.wat, "{}(i32.const 0) ;; Struct literal (not yet implemented)", ind)
                    .map_err(|e| e.to_string())?;
            }

            Expr::FieldAccess { expr: _expr, field: _field } => {
                // TODO: Implement field access with linear memory
                // For now, return 0
                writeln!(&mut self.wat, "{}(i64.const 0) ;; Field access (not yet implemented)", ind)
                    .map_err(|e| e.to_string())?;
            }

            Expr::For { var: _var, iterable: _iterable, body: _body } => {
                // TODO: Implement for loops with WASM loop constructs
                // Requires linear memory for vector iteration
                // For now, return 0
                writeln!(&mut self.wat, "{}(i32.const 0) ;; For loop (not yet implemented)", ind)
                    .map_err(|e| e.to_string())?;
            }

            Expr::While { cond: _cond, body: _body } => {
                // TODO: Implement while loops with WASM loop constructs
                // For now, return 0
                writeln!(&mut self.wat, "{}(i32.const 0) ;; While loop (not yet implemented)", ind)
                    .map_err(|e| e.to_string())?;
            }

            Expr::Some(_) | Expr::None | Expr::Ok(_) | Expr::Err(_) => {
                // TODO: Implement Option/Result with linear memory
                writeln!(&mut self.wat, "{}(i32.const 0) ;; Option/Result (not yet implemented)", ind)
                    .map_err(|e| e.to_string())?;
            }

            Expr::Borrow(expr) | Expr::Deref(expr) => {
                // Borrow and deref are type-level only, pass through
                self.generate_expr(expr, indent)?;
            }
        }

        Ok(())
    }

    fn generate_match_arms(
        &mut self,
        arms: &[MatchArm],
        scrutinee_local: &str,
        indent: usize,
    ) -> Result<(), String> {
        let ind = "  ".repeat(indent);

        if arms.is_empty() {
            return Err("Empty match expression".to_string());
        }

        for (i, arm) in arms.iter().enumerate() {
            match &arm.pattern {
                Pattern::IntLit(n) => {
                    // Load scrutinee
                    writeln!(
                        &mut self.wat,
                        "{}(local.get ${})",
                        ind, scrutinee_local
                    )
                    .map_err(|e| e.to_string())?;
                    writeln!(&mut self.wat, "{}(i64.const {})", ind, n)
                        .map_err(|e| e.to_string())?;
                    writeln!(&mut self.wat, "{}(i64.eq)", ind).map_err(|e| e.to_string())?;
                    writeln!(&mut self.wat, "{}(if (result i64)", ind)
                        .map_err(|e| e.to_string())?;
                    writeln!(&mut self.wat, "{}  (then", ind).map_err(|e| e.to_string())?;
                    self.generate_expr(&arm.body, indent + 2)?;
                    writeln!(&mut self.wat, "{}  )", ind).map_err(|e| e.to_string())?;
                    writeln!(&mut self.wat, "{}  (else", ind).map_err(|e| e.to_string())?;

                    // Continue with next arm or wildcard
                    if i == arms.len() - 1 {
                        // Last arm - should be wildcard
                        if !matches!(arm.pattern, Pattern::Wildcard | Pattern::Var(_)) {
                            writeln!(&mut self.wat, "{}    (unreachable)", ind)
                                .map_err(|e| e.to_string())?;
                        }
                    }
                }
                Pattern::BoolLit(b) => {
                    writeln!(
                        &mut self.wat,
                        "{}(local.get ${})",
                        ind, scrutinee_local
                    )
                    .map_err(|e| e.to_string())?;
                    writeln!(
                        &mut self.wat,
                        "{}(i32.const {})",
                        ind,
                        if *b { 1 } else { 0 }
                    )
                    .map_err(|e| e.to_string())?;
                    writeln!(&mut self.wat, "{}(i32.eq)", ind).map_err(|e| e.to_string())?;
                    writeln!(&mut self.wat, "{}(if (result i64)", ind)
                        .map_err(|e| e.to_string())?;
                    writeln!(&mut self.wat, "{}  (then", ind).map_err(|e| e.to_string())?;
                    self.generate_expr(&arm.body, indent + 2)?;
                    writeln!(&mut self.wat, "{}  )", ind).map_err(|e| e.to_string())?;
                    writeln!(&mut self.wat, "{}  (else", ind).map_err(|e| e.to_string())?;
                }
                Pattern::Wildcard | Pattern::Var(_) => {
                    // Wildcard always matches
                    self.generate_expr(&arm.body, indent)?;
                }
                Pattern::Some(_) | Pattern::None | Pattern::Ok(_) | Pattern::Err(_) => {
                    // TODO: Implement Option/Result pattern matching in WASM
                    writeln!(&mut self.wat, "{}    (i64.const 0) ;; Option/Result pattern (not yet implemented)", ind)
                        .map_err(|e| e.to_string())?;
                }
            }
        }

        // Close all the nested elses
        for _ in 0..arms.len() - 1 {
            writeln!(&mut self.wat, "{}  )", ind).map_err(|e| e.to_string())?;
            writeln!(&mut self.wat, "{})", ind).map_err(|e| e.to_string())?;
        }

        Ok(())
    }

    fn wasm_type(ty: &Type) -> &'static str {
        match ty {
            Type::I32 => "i32",
            Type::I64 => "i64",
            Type::Bool => "i32", // Booleans are i32 in WASM
            Type::String => "i32", // Strings are pointers to linear memory (requires memory management)
            Type::Vec(_) => "i32", // Vectors are pointers to linear memory (requires memory management)
            Type::HashMap(_, _) => "i32", // HashMaps are pointers to linear memory (requires memory management)
            Type::Struct(_) => "i32", // Structs are pointers to linear memory (requires memory management)
            Type::Ref(_) => "i32", // References are pointers (i32 for wasm32)
            Type::Option(_) => "i32", // Option is pointer to linear memory
            Type::Result(_, _) => "i32", // Result is pointer to linear memory
            Type::Infer => "i64", // Default to i64
        }
    }

    fn wasm_binop(op: &BinOp) -> &'static str {
        match op {
            BinOp::Add => "i64.add",
            BinOp::Sub => "i64.sub",
            BinOp::Mul => "i64.mul",
            BinOp::Div => "i64.div_s",
            BinOp::Mod => "i64.rem_s",
            BinOp::Eq => "i64.eq",
            BinOp::Ne => "i64.ne",
            BinOp::Lt => "i64.lt_s",
            BinOp::Gt => "i64.gt_s",
            BinOp::Le => "i64.le_s",
            BinOp::Ge => "i64.ge_s",
            BinOp::And => "i32.and",
            BinOp::Or => "i32.or",
            BinOp::BitAnd => "i64.and",
            BinOp::BitOr => "i64.or",
            BinOp::BitXor => "i64.xor",
            BinOp::Shl => "i64.shl",
            BinOp::Shr => "i64.shr_s",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    #[test]
    fn test_codegen_simple() {
        let input = "fn main() { 42 }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let mut codegen = WasmCodeGen::new();
        let wat = codegen.generate(&program).unwrap();
        assert!(wat.contains("(module"));
        assert!(wat.contains("(func $main"));
        assert!(wat.contains("(i64.const 42)"));
    }

    #[test]
    fn test_codegen_arithmetic() {
        let input = "fn main() { 1 + 2 }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let mut codegen = WasmCodeGen::new();
        let wat = codegen.generate(&program).unwrap();
        assert!(wat.contains("(i64.const 1)"));
        assert!(wat.contains("(i64.const 2)"));
        assert!(wat.contains("(i64.add)"));
    }
}
