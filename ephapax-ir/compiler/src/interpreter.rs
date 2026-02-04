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
    HashMap(HashMap<String, Value>),  // HashMap<String, Value> - keys must be strings for now
    Struct(String, HashMap<String, Value>),  // (struct_name, fields)
    OptionSome(Box<Value>),  // Option::Some(value)
    OptionNone,              // Option::None
    ResultOk(Box<Value>),    // Result::Ok(value)
    ResultErr(Box<Value>),   // Result::Err(error)
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

            Expr::UnaryOp { op, operand } => {
                use crate::ast::UnaryOp;
                let operand_val = self.eval_expr(operand, env)?;

                match op {
                    UnaryOp::Not => {
                        let b = operand_val.as_bool()?;
                        Ok(Value::Bool(!b))
                    }
                    UnaryOp::Neg => {
                        let n = operand_val.as_int()?;
                        Ok(Value::Int(-n))
                    }
                }
            }

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
                // Check for built-in functions first
                match func.as_str() {
                    "read_file" => {
                        if args.len() != 1 {
                            return Err(format!("read_file expects 1 argument, got {}", args.len()));
                        }
                        let path_val = self.eval_expr(&args[0], env)?;
                        let path = path_val.as_string()?;

                        match std::fs::read_to_string(path) {
                            Ok(content) => Ok(Value::String(content)),
                            Err(e) => Err(format!("Failed to read file '{}': {}", path, e)),
                        }
                    }
                    "write_file" => {
                        if args.len() != 2 {
                            return Err(format!("write_file expects 2 arguments, got {}", args.len()));
                        }
                        let path_val = self.eval_expr(&args[0], env)?;
                        let content_val = self.eval_expr(&args[1], env)?;
                        let path = path_val.as_string()?;
                        let content = content_val.as_string()?;

                        match std::fs::write(path, content) {
                            Ok(_) => Ok(Value::Int(0)),  // Success
                            Err(e) => Err(format!("Failed to write file '{}': {}", path, e)),
                        }
                    }
                    "print" => {
                        if args.len() != 1 {
                            return Err(format!("print expects 1 argument, got {}", args.len()));
                        }
                        let val = self.eval_expr(&args[0], env)?;
                        match &val {
                            Value::Int(n) => print!("{}", n),
                            Value::Bool(b) => print!("{}", b),
                            Value::String(s) => print!("{}", s),
                            Value::Vec(elements) => {
                                print!("[");
                                for (i, elem) in elements.iter().enumerate() {
                                    if i > 0 { print!(", "); }
                                    match elem {
                                        Value::Int(n) => print!("{}", n),
                                        Value::Bool(b) => print!("{}", b),
                                        Value::String(s) => print!("{}", s),
                                        _ => print!("{:?}", elem),
                                    }
                                }
                                print!("]");
                            }
                            Value::Struct(name, fields) => {
                                print!("{} {{ ", name);
                                for (i, (field_name, field_val)) in fields.iter().enumerate() {
                                    if i > 0 { print!(", "); }
                                    print!("{}: ", field_name);
                                    match field_val {
                                        Value::Int(n) => print!("{}", n),
                                        Value::Bool(b) => print!("{}", b),
                                        Value::String(s) => print!("{}", s),
                                        _ => print!("{:?}", field_val),
                                    }
                                }
                                print!(" }}");
                            }
                            Value::HashMap(entries) => {
                                print!("{{");
                                for (i, (key, val)) in entries.iter().enumerate() {
                                    if i > 0 { print!(", "); }
                                    print!("{}: ", key);
                                    match val {
                                        Value::Int(n) => print!("{}", n),
                                        Value::Bool(b) => print!("{}", b),
                                        Value::String(s) => print!("{}", s),
                                        _ => print!("{:?}", val),
                                    }
                                }
                                print!("}}");
                            }
                            Value::OptionSome(v) => {
                                print!("Some(");
                                match v.as_ref() {
                                    Value::Int(n) => print!("{}", n),
                                    Value::Bool(b) => print!("{}", b),
                                    Value::String(s) => print!("{}", s),
                                    _ => print!("{:?}", v),
                                }
                                print!(")");
                            }
                            Value::OptionNone => print!("None"),
                            Value::ResultOk(v) => {
                                print!("Ok(");
                                match v.as_ref() {
                                    Value::Int(n) => print!("{}", n),
                                    Value::Bool(b) => print!("{}", b),
                                    Value::String(s) => print!("{}", s),
                                    _ => print!("{:?}", v),
                                }
                                print!(")");
                            }
                            Value::ResultErr(v) => {
                                print!("Err(");
                                match v.as_ref() {
                                    Value::Int(n) => print!("{}", n),
                                    Value::Bool(b) => print!("{}", b),
                                    Value::String(s) => print!("{}", s),
                                    _ => print!("{:?}", v),
                                }
                                print!(")");
                            }
                        }
                        Ok(Value::Int(0))  // Return 0 (unit placeholder)
                    }
                    "hashmap_new" => {
                        if !args.is_empty() {
                            return Err(format!("hashmap_new expects 0 arguments, got {}", args.len()));
                        }
                        Ok(Value::HashMap(HashMap::new()))
                    }
                    "hashmap_insert" => {
                        if args.len() != 3 {
                            return Err(format!("hashmap_insert expects 3 arguments (map, key, value), got {}", args.len()));
                        }
                        let map_val = self.eval_expr(&args[0], env)?;
                        let key_val = self.eval_expr(&args[1], env)?;
                        let val_val = self.eval_expr(&args[2], env)?;

                        // Extract map (consumes it due to linear types)
                        let mut map = match map_val {
                            Value::HashMap(m) => m,
                            _ => return Err("hashmap_insert expects first argument to be a HashMap".to_string()),
                        };

                        // Key must be string
                        let key_str = key_val.as_string()?.to_string();

                        // Insert and return new map
                        map.insert(key_str, val_val);
                        Ok(Value::HashMap(map))
                    }
                    "hashmap_get" => {
                        if args.len() != 2 {
                            return Err(format!("hashmap_get expects 2 arguments (map, key), got {}", args.len()));
                        }
                        let map_val = self.eval_expr(&args[0], env)?;
                        let key_val = self.eval_expr(&args[1], env)?;

                        // Get reference to map (doesn't consume it)
                        let map = match &map_val {
                            Value::HashMap(m) => m,
                            _ => return Err("hashmap_get expects first argument to be a HashMap".to_string()),
                        };

                        // Key must be string
                        let key_str = key_val.as_string()?;

                        // Lookup and return Option
                        match map.get(key_str) {
                            Some(val) => Ok(Value::OptionSome(Box::new(val.clone()))),
                            None => Ok(Value::OptionNone),
                        }
                    }
                    "hashmap_contains_key" => {
                        if args.len() != 2 {
                            return Err(format!("hashmap_contains_key expects 2 arguments (map, key), got {}", args.len()));
                        }
                        let map_val = self.eval_expr(&args[0], env)?;
                        let key_val = self.eval_expr(&args[1], env)?;

                        // Get reference to map
                        let map = match &map_val {
                            Value::HashMap(m) => m,
                            _ => return Err("hashmap_contains_key expects first argument to be a HashMap".to_string()),
                        };

                        // Key must be string
                        let key_str = key_val.as_string()?;

                        // Check existence
                        Ok(Value::Bool(map.contains_key(key_str)))
                    }
                    "hashmap_remove" => {
                        if args.len() != 2 {
                            return Err(format!("hashmap_remove expects 2 arguments (map, key), got {}", args.len()));
                        }
                        let map_val = self.eval_expr(&args[0], env)?;
                        let key_val = self.eval_expr(&args[1], env)?;

                        // Extract map (consumes it)
                        let mut map = match map_val {
                            Value::HashMap(m) => m,
                            _ => return Err("hashmap_remove expects first argument to be a HashMap".to_string()),
                        };

                        // Key must be string
                        let key_str = key_val.as_string()?.to_string();

                        // Remove and return new map
                        map.remove(&key_str);
                        Ok(Value::HashMap(map))
                    }
                    // String operations
                    "string_length" => {
                        if args.len() != 1 {
                            return Err(format!("string_length expects 1 argument, got {}", args.len()));
                        }
                        let val = self.eval_expr(&args[0], env)?;
                        let s = val.as_string()?;
                        Ok(Value::Int(s.len() as i64))
                    }
                    "string_to_upper" => {
                        if args.len() != 1 {
                            return Err(format!("string_to_upper expects 1 argument, got {}", args.len()));
                        }
                        let val = self.eval_expr(&args[0], env)?;
                        let s = val.as_string()?;
                        Ok(Value::String(s.to_uppercase()))
                    }
                    "string_to_lower" => {
                        if args.len() != 1 {
                            return Err(format!("string_to_lower expects 1 argument, got {}", args.len()));
                        }
                        let val = self.eval_expr(&args[0], env)?;
                        let s = val.as_string()?;
                        Ok(Value::String(s.to_lowercase()))
                    }
                    "string_substring" => {
                        if args.len() != 3 {
                            return Err(format!("string_substring expects 3 arguments (string, start, length), got {}", args.len()));
                        }
                        let val = self.eval_expr(&args[0], env)?;
                        let start_val = self.eval_expr(&args[1], env)?;
                        let len_val = self.eval_expr(&args[2], env)?;

                        let s = val.as_string()?;
                        let start = start_val.as_int()? as usize;
                        let len = len_val.as_int()? as usize;

                        if start > s.len() {
                            return Err("string_substring: start index out of bounds".to_string());
                        }
                        let end = std::cmp::min(start + len, s.len());
                        Ok(Value::String(s[start..end].to_string()))
                    }
                    // Math operations
                    "abs" => {
                        if args.len() != 1 {
                            return Err(format!("abs expects 1 argument, got {}", args.len()));
                        }
                        let val = self.eval_expr(&args[0], env)?;
                        let n = val.as_int()?;
                        Ok(Value::Int(n.abs()))
                    }
                    "min" => {
                        if args.len() != 2 {
                            return Err(format!("min expects 2 arguments, got {}", args.len()));
                        }
                        let val1 = self.eval_expr(&args[0], env)?;
                        let val2 = self.eval_expr(&args[1], env)?;
                        let n1 = val1.as_int()?;
                        let n2 = val2.as_int()?;
                        Ok(Value::Int(std::cmp::min(n1, n2)))
                    }
                    "max" => {
                        if args.len() != 2 {
                            return Err(format!("max expects 2 arguments, got {}", args.len()));
                        }
                        let val1 = self.eval_expr(&args[0], env)?;
                        let val2 = self.eval_expr(&args[1], env)?;
                        let n1 = val1.as_int()?;
                        let n2 = val2.as_int()?;
                        Ok(Value::Int(std::cmp::max(n1, n2)))
                    }
                    "pow" => {
                        if args.len() != 2 {
                            return Err(format!("pow expects 2 arguments (base, exponent), got {}", args.len()));
                        }
                        let base_val = self.eval_expr(&args[0], env)?;
                        let exp_val = self.eval_expr(&args[1], env)?;
                        let base = base_val.as_int()?;
                        let exp = exp_val.as_int()?;

                        if exp < 0 {
                            return Err("pow: negative exponents not supported".to_string());
                        }
                        let result = base.pow(exp as u32);
                        Ok(Value::Int(result))
                    }
                    // Vec operations
                    "vec_new" => {
                        if !args.is_empty() {
                            return Err(format!("vec_new expects 0 arguments, got {}", args.len()));
                        }
                        Ok(Value::Vec(Vec::new()))
                    }
                    "vec_push" => {
                        if args.len() != 2 {
                            return Err(format!("vec_push expects 2 arguments (vec, element), got {}", args.len()));
                        }
                        let vec_val = self.eval_expr(&args[0], env)?;
                        let elem_val = self.eval_expr(&args[1], env)?;

                        let mut vec = match vec_val {
                            Value::Vec(v) => v,
                            _ => return Err("vec_push expects first argument to be a Vec".to_string()),
                        };

                        vec.push(elem_val);
                        Ok(Value::Vec(vec))
                    }
                    "vec_pop" => {
                        if args.len() != 1 {
                            return Err(format!("vec_pop expects 1 argument, got {}", args.len()));
                        }
                        let vec_val = self.eval_expr(&args[0], env)?;

                        let mut vec = match vec_val {
                            Value::Vec(v) => v,
                            _ => return Err("vec_pop expects first argument to be a Vec".to_string()),
                        };

                        match vec.pop() {
                            Some(elem) => {
                                // Return tuple (new_vec, Some(elem)) but we don't have tuples
                                // For now, just return the popped element
                                Ok(Value::OptionSome(Box::new(elem)))
                            }
                            None => Ok(Value::OptionNone),
                        }
                    }
                    "vec_length" => {
                        if args.len() != 1 {
                            return Err(format!("vec_length expects 1 argument, got {}", args.len()));
                        }
                        let vec_val = self.eval_expr(&args[0], env)?;

                        let vec = match &vec_val {
                            Value::Vec(v) => v,
                            _ => return Err("vec_length expects first argument to be a Vec".to_string()),
                        };

                        Ok(Value::Int(vec.len() as i64))
                    }
                    "vec_get" => {
                        if args.len() != 2 {
                            return Err(format!("vec_get expects 2 arguments (vec, index), got {}", args.len()));
                        }
                        let vec_val = self.eval_expr(&args[0], env)?;
                        let idx_val = self.eval_expr(&args[1], env)?;

                        let vec = match &vec_val {
                            Value::Vec(v) => v,
                            _ => return Err("vec_get expects first argument to be a Vec".to_string()),
                        };

                        let idx = idx_val.as_int()? as usize;

                        match vec.get(idx) {
                            Some(elem) => Ok(Value::OptionSome(Box::new(elem.clone()))),
                            None => Ok(Value::OptionNone),
                        }
                    }
                    _ => {
                        // User-defined function
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
                }
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

            Expr::HashMapLit(entries) => {
                let mut map = HashMap::new();
                for (key_expr, val_expr) in entries {
                    let key_val = self.eval_expr(key_expr, env)?;
                    let val_val = self.eval_expr(val_expr, env)?;
                    // Keys must be strings
                    let key_str = key_val.as_string()?.to_string();
                    map.insert(key_str, val_val);
                }
                Ok(Value::HashMap(map))
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

            Expr::For { var, iterable, body } => {
                // Evaluate the iterable expression
                let iterable_val = self.eval_expr(iterable, env)?;
                let vec_data = iterable_val.as_vec()?;

                // Execute body for each element
                let mut last_result = Value::Int(0);
                for elem in vec_data {
                    // Create new environment with loop variable bound to element
                    let mut loop_env = env.clone();
                    loop_env.insert(var.clone(), elem.clone());

                    // Execute loop body
                    last_result = self.eval_expr(body, &mut loop_env)?;
                }

                // Return last result (or 0 if empty)
                Ok(last_result)
            }

            Expr::While { cond, body } => {
                let mut last_result = Value::Int(0);

                loop {
                    // Evaluate condition
                    let cond_val = self.eval_expr(cond, env)?;
                    let cond_bool = cond_val.as_bool()?;

                    if !cond_bool {
                        break;
                    }

                    // Execute body
                    last_result = self.eval_expr(body, env)?;
                }

                Ok(last_result)
            }

            Expr::Some(expr) => {
                let val = self.eval_expr(expr, env)?;
                Ok(Value::OptionSome(Box::new(val)))
            }

            Expr::None => Ok(Value::OptionNone),

            Expr::Ok(expr) => {
                let val = self.eval_expr(expr, env)?;
                Ok(Value::ResultOk(Box::new(val)))
            }

            Expr::Err(expr) => {
                let val = self.eval_expr(expr, env)?;
                Ok(Value::ResultErr(Box::new(val)))
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
            Pattern::Some(inner_pattern) => {
                if let Value::OptionSome(inner_val) = value {
                    self.match_pattern(inner_pattern, inner_val)
                } else {
                    None
                }
            }
            Pattern::None => {
                if matches!(value, Value::OptionNone) {
                    Some(Vec::new())
                } else {
                    None
                }
            }
            Pattern::Ok(inner_pattern) => {
                if let Value::ResultOk(inner_val) = value {
                    self.match_pattern(inner_pattern, inner_val)
                } else {
                    None
                }
            }
            Pattern::Err(inner_pattern) => {
                if let Value::ResultErr(inner_val) = value {
                    self.match_pattern(inner_pattern, inner_val)
                } else {
                    None
                }
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
