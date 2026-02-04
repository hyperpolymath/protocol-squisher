// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Interpreter for ephapax language

use crate::ast::*;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Bool(bool),
    String(String),
    Vec(Vec<Value>),
    Struct(String, HashMap<String, Value>),  // (struct_name, fields)
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

    pub fn as_string(&self) -> Result<&str, String> {
        match self {
            Value::String(s) => Ok(s),
            _ => Err(format!("Expected string, got {:?}", self)),
        }
    }

    pub fn as_vec(&self) -> Result<&Vec<Value>, String> {
        match self {
            Value::Vec(v) => Ok(v),
            _ => Err(format!("Expected vector, got {:?}", self)),
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
            Expr::StringLit(s) => Ok(Value::String(s.clone())),

            Expr::Var(name) => env
                .get(name)
                .cloned()
                .ok_or_else(|| format!("Variable '{}' not found", name)),

            Expr::BinOp { op, left, right } => {
                // Logical AND and OR use short-circuit evaluation
                match op {
                    BinOp::And => {
                        let left_val = self.eval_expr(left, env)?;
                        let l = left_val.as_bool()?;
                        if !l {
                            return Ok(Value::Bool(false));
                        }
                        let right_val = self.eval_expr(right, env)?;
                        let r = right_val.as_bool()?;
                        Ok(Value::Bool(r))
                    }
                    BinOp::Or => {
                        let left_val = self.eval_expr(left, env)?;
                        let l = left_val.as_bool()?;
                        if l {
                            return Ok(Value::Bool(true));
                        }
                        let right_val = self.eval_expr(right, env)?;
                        let r = right_val.as_bool()?;
                        Ok(Value::Bool(r))
                    }
                    _ => {
                        // Other operators evaluate both sides
                        let left_val = self.eval_expr(left, env)?;
                        let right_val = self.eval_expr(right, env)?;

                        match op {
                            BinOp::Add => {
                                match (&left_val, &right_val) {
                                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l + r)),
                                    (Value::String(l), Value::String(r)) => {
                                        let mut result = l.clone();
                                        result.push_str(r);
                                        Ok(Value::String(result))
                                    }
                                    _ => Err(format!(
                                        "Cannot add {:?} and {:?}",
                                        left_val, right_val
                                    )),
                                }
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
                            BinOp::BitAnd => {
                                let l = left_val.as_int()?;
                                let r = right_val.as_int()?;
                                Ok(Value::Int(l & r))
                            }
                            BinOp::BitOr => {
                                let l = left_val.as_int()?;
                                let r = right_val.as_int()?;
                                Ok(Value::Int(l | r))
                            }
                            BinOp::BitXor => {
                                let l = left_val.as_int()?;
                                let r = right_val.as_int()?;
                                Ok(Value::Int(l ^ r))
                            }
                            BinOp::Shl => {
                                let l = left_val.as_int()?;
                                let r = right_val.as_int()?;
                                if r < 0 || r > 63 {
                                    return Err(format!("Shift amount {} out of range [0, 63]", r));
                                }
                                Ok(Value::Int(l << r))
                            }
                            BinOp::Shr => {
                                let l = left_val.as_int()?;
                                let r = right_val.as_int()?;
                                if r < 0 || r > 63 {
                                    return Err(format!("Shift amount {} out of range [0, 63]", r));
                                }
                                Ok(Value::Int(l >> r))
                            }
                            BinOp::And | BinOp::Or => unreachable!("Handled above"),
                        }
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

            Expr::Match { scrutinee, arms } => {
                let scrutinee_val = self.eval_expr(scrutinee, env)?;

                for arm in arms {
                    if let Some(bindings) = self.match_pattern(&arm.pattern, &scrutinee_val) {
                        // Pattern matched, bind variables and evaluate body
                        let mut new_env = env.clone();
                        for (name, value) in bindings {
                            new_env.insert(name, value);
                        }
                        return self.eval_expr(&arm.body, &mut new_env);
                    }
                }

                Err("Non-exhaustive match (no pattern matched)".to_string())
            }

            Expr::VecLit(elements) => {
                let mut values = Vec::new();
                for elem in elements {
                    values.push(self.eval_expr(elem, env)?);
                }
                Ok(Value::Vec(values))
            }

            Expr::Index { vec, index } => {
                let vec_val = self.eval_expr(vec, env)?;
                let index_val = self.eval_expr(index, env)?;

                let vec_data = vec_val.as_vec()?;
                let idx = index_val.as_int()?;

                if idx < 0 || idx as usize >= vec_data.len() {
                    return Err(format!(
                        "Index {} out of bounds for vector of length {}",
                        idx,
                        vec_data.len()
                    ));
                }

                Ok(vec_data[idx as usize].clone())
            }

            Expr::StructLit { name, fields } => {
                let mut field_values = HashMap::new();
                for (field_name, field_expr) in fields {
                    let field_val = self.eval_expr(field_expr, env)?;
                    field_values.insert(field_name.clone(), field_val);
                }
                Ok(Value::Struct(name.clone(), field_values))
            }

            Expr::FieldAccess { expr, field } => {
                let struct_val = self.eval_expr(expr, env)?;
                match struct_val {
                    Value::Struct(_name, fields) => {
                        fields.get(field).cloned().ok_or_else(|| {
                            format!("Field '{}' not found in struct", field)
                        })
                    }
                    _ => Err(format!("Field access requires a struct value, got {:?}", struct_val)),
                }
            }

            Expr::Borrow(expr) => {
                // In interpreter, borrow is a no-op (type-level only)
                self.eval_expr(expr, env)
            }

            Expr::Deref(expr) => {
                // In interpreter, deref is a no-op (type-level only)
                self.eval_expr(expr, env)
            }
        }
    }

    fn match_pattern(
        &self,
        pattern: &Pattern,
        value: &Value,
    ) -> Option<Vec<(String, Value)>> {
        match pattern {
            Pattern::IntLit(n) => {
                if let Value::Int(v) = value {
                    if *n == *v {
                        Some(Vec::new()) // Match, no bindings
                    } else {
                        None // Doesn't match
                    }
                } else {
                    None // Type mismatch
                }
            }
            Pattern::BoolLit(b) => {
                if let Value::Bool(v) = value {
                    if *b == *v {
                        Some(Vec::new()) // Match, no bindings
                    } else {
                        None // Doesn't match
                    }
                } else {
                    None // Type mismatch
                }
            }
            Pattern::Var(name) => {
                // Variable pattern always matches and binds the value
                Some(vec![(name.clone(), value.clone())])
            }
            Pattern::Wildcard => {
                // Wildcard always matches, no bindings
                Some(Vec::new())
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
