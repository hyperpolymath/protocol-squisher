// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Interpreter for ephapax language

use crate::ast::*;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Bool(bool),
}

impl Value {
    pub fn as_int(&self) -> Result<i64, String> {
        match self {
            Value::Int(n) => Ok(*n),
            _ => Err(format!("Expected integer, got {:?}", self)),
        }
    }

    pub fn as_bool(&self) -> Result<bool, String> {
        match self {
            Value::Bool(b) => Ok(*b),
            _ => Err(format!("Expected boolean, got {:?}", self)),
        }
    }
}

pub struct Interpreter {
    functions: HashMap<String, Function>,
}

impl Interpreter {
    pub fn new(program: Program) -> Self {
        let mut functions = HashMap::new();
        for func in program.functions {
            functions.insert(func.name.clone(), func);
        }
        Self { functions }
    }

    pub fn run(&mut self, entry: &str) -> Result<Value, String> {
        let main_func = self
            .functions
            .get(entry)
            .ok_or_else(|| format!("Function '{}' not found", entry))?
            .clone();

        if !main_func.params.is_empty() {
            return Err(format!(
                "Entry function '{}' should not have parameters",
                entry
            ));
        }

        let mut env = HashMap::new();
        self.eval_expr(&main_func.body, &mut env)
    }

    fn eval_expr(
        &self,
        expr: &Expr,
        env: &mut HashMap<String, Value>,
    ) -> Result<Value, String> {
        match expr {
            Expr::IntLit(n) => Ok(Value::Int(*n)),
            Expr::BoolLit(b) => Ok(Value::Bool(*b)),

            Expr::Var(name) => env
                .get(name)
                .cloned()
                .ok_or_else(|| format!("Variable '{}' not found", name)),

            Expr::BinOp { op, left, right } => {
                let left_val = self.eval_expr(left, env)?;
                let right_val = self.eval_expr(right, env)?;

                match op {
                    BinOp::Add => {
                        let l = left_val.as_int()?;
                        let r = right_val.as_int()?;
                        Ok(Value::Int(l + r))
                    }
                    BinOp::Sub => {
                        let l = left_val.as_int()?;
                        let r = right_val.as_int()?;
                        Ok(Value::Int(l - r))
                    }
                    BinOp::Mul => {
                        let l = left_val.as_int()?;
                        let r = right_val.as_int()?;
                        Ok(Value::Int(l * r))
                    }
                    BinOp::Div => {
                        let l = left_val.as_int()?;
                        let r = right_val.as_int()?;
                        if r == 0 {
                            return Err("Division by zero".to_string());
                        }
                        Ok(Value::Int(l / r))
                    }
                    BinOp::Mod => {
                        let l = left_val.as_int()?;
                        let r = right_val.as_int()?;
                        if r == 0 {
                            return Err("Modulo by zero".to_string());
                        }
                        Ok(Value::Int(l % r))
                    }
                    BinOp::Eq => {
                        Ok(Value::Bool(left_val == right_val))
                    }
                    BinOp::Ne => {
                        Ok(Value::Bool(left_val != right_val))
                    }
                    BinOp::Lt => {
                        let l = left_val.as_int()?;
                        let r = right_val.as_int()?;
                        Ok(Value::Bool(l < r))
                    }
                    BinOp::Gt => {
                        let l = left_val.as_int()?;
                        let r = right_val.as_int()?;
                        Ok(Value::Bool(l > r))
                    }
                    BinOp::Le => {
                        let l = left_val.as_int()?;
                        let r = right_val.as_int()?;
                        Ok(Value::Bool(l <= r))
                    }
                    BinOp::Ge => {
                        let l = left_val.as_int()?;
                        let r = right_val.as_int()?;
                        Ok(Value::Bool(l >= r))
                    }
                }
            }

            Expr::Call { func, args } => {
                let func_def = self
                    .functions
                    .get(func)
                    .ok_or_else(|| format!("Function '{}' not found", func))?
                    .clone();

                if func_def.params.len() != args.len() {
                    return Err(format!(
                        "Function '{}' expects {} arguments, got {}",
                        func,
                        func_def.params.len(),
                        args.len()
                    ));
                }

                let mut new_env = HashMap::new();
                for (param, arg) in func_def.params.iter().zip(args.iter()) {
                    let arg_val = self.eval_expr(arg, env)?;
                    new_env.insert(param.name.clone(), arg_val);
                }

                self.eval_expr(&func_def.body, &mut new_env)
            }

            Expr::Let { name, value, body } => {
                let val = self.eval_expr(value, env)?;
                env.insert(name.clone(), val);
                self.eval_expr(body, env)
            }

            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_val = self.eval_expr(cond, env)?;
                let cond_bool = cond_val.as_bool()?;

                if cond_bool {
                    self.eval_expr(then_branch, env)
                } else {
                    self.eval_expr(else_branch, env)
                }
            }

            Expr::Block(exprs) => {
                let mut result = Value::Int(0);
                for expr in exprs {
                    result = self.eval_expr(expr, env)?;
                }
                Ok(result)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    #[test]
    fn test_eval_simple() {
        let input = "fn main() { 42 }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let mut interp = Interpreter::new(program);
        let result = interp.run("main").unwrap();
        assert_eq!(result, Value::Int(42));
    }

    #[test]
    fn test_eval_addition() {
        let input = "fn main() { 1 + 2 }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let mut interp = Interpreter::new(program);
        let result = interp.run("main").unwrap();
        assert_eq!(result, Value::Int(3));
    }

    #[test]
    fn test_eval_function_call() {
        let input = r#"
            fn double(x) { x + x }
            fn main() { double(21) }
        "#;
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let mut interp = Interpreter::new(program);
        let result = interp.run("main").unwrap();
        assert_eq!(result, Value::Int(42));
    }

    #[test]
    fn test_eval_let_binding() {
        let input = "fn main() { let x = 5; x + 10 }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let mut interp = Interpreter::new(program);
        let result = interp.run("main").unwrap();
        assert_eq!(result, Value::Int(15));
    }

    #[test]
    fn test_eval_if_expression() {
        let input = "fn main() { if true { 1 } else { 2 } }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let mut interp = Interpreter::new(program);
        let result = interp.run("main").unwrap();
        assert_eq!(result, Value::Int(1));
    }

    #[test]
    fn test_eval_comparison() {
        let input = "fn main() { if 5 > 3 { 100 } else { 200 } }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let mut interp = Interpreter::new(program);
        let result = interp.run("main").unwrap();
        assert_eq!(result, Value::Int(100));
    }
}
