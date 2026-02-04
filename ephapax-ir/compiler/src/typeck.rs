// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Linear type checker for ephapax
//!
//! Enforces linear type constraints:
//! - Values used exactly once (no aliasing)
//! - Move semantics (ownership transfer)
//! - Resource safety (no leaks)

use crate::ast::*;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    VariableUsedTwice {
        var: String,
        var_type: Type,
        first_use: String,
        second_use: String,
    },
    VariableNotUsed {
        var: String,
        var_type: Type,
    },
    VariableNotFound {
        var: String,
    },
    TypeMismatch {
        expected: Type,
        found: Type,
        context: String,
    },
    IncompatibleTypes {
        left: Type,
        right: Type,
        op: String,
    },
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeError::VariableUsedTwice {
                var,
                var_type,
                first_use,
                second_use,
            } => {
                write!(
                    f,
                    "Linear type violation: variable '{}' of type {} used twice (first: {}, second: {})",
                    var, var_type, first_use, second_use
                )?;
                if var_type.is_copy() {
                    write!(f, "\n  note: {} is a Copy type and can be used multiple times", var_type)?;
                } else {
                    write!(f, "\n  help: {} is not Copy; consider restructuring code to use value exactly once", var_type)?;
                    write!(f, "\n        or extract logic into a separate function to avoid multiple uses")?;
                }
                Ok(())
            }
            TypeError::VariableNotUsed { var, var_type } => {
                write!(
                    f,
                    "Linear type violation: variable '{}' of type {} not used (must use exactly once)",
                    var, var_type
                )?;
                if var_type.is_copy() {
                    write!(f, "\n  note: {} is Copy, so it's okay if unused (this shouldn't happen)", var_type)?;
                } else {
                    write!(f, "\n  help: use '{}' in an expression or remove the binding", var)?;
                }
                Ok(())
            }
            TypeError::VariableNotFound { var } => {
                write!(f, "Variable '{}' not found in scope", var)?;
                write!(f, "\n  help: check variable name spelling or declare it with 'let'")?;
                Ok(())
            }
            TypeError::TypeMismatch {
                expected,
                found,
                context,
            } => {
                write!(
                    f,
                    "Type mismatch in {}: expected {}, found {}",
                    context, expected, found
                )?;
                // Suggest conversions if applicable
                if expected == &Type::I64 && found == &Type::I32 {
                    write!(f, "\n  help: i32 can be widened to i64 in future versions")?;
                } else if expected == &Type::Bool && (found == &Type::I32 || found == &Type::I64) {
                    write!(f, "\n  help: use comparison operators (==, !=, <, >, etc.) to get a bool")?;
                }
                Ok(())
            }
            TypeError::IncompatibleTypes { left, right, op } => {
                write!(
                    f,
                    "Incompatible types for operator '{}': {} and {}",
                    op, left, right
                )?;
                // Suggest fixes based on operator
                if op.contains("&&") || op.contains("||") {
                    write!(f, "\n  help: logical operators require both operands to be bool")?;
                    write!(f, "\n        use comparison operators to convert integers to bool")?;
                } else if op.contains("&") || op.contains("|") || op.contains("^") || op.contains("<<") || op.contains(">>") {
                    write!(f, "\n  help: bitwise operators require both operands to have the same integer type")?;
                } else if left != right {
                    write!(f, "\n  help: both operands must have the same type")?;
                }
                Ok(())
            }
        }
    }
}

/// Type environment tracking variable types and usage
#[derive(Debug, Clone)]
struct TypeEnv {
    /// Variable types
    types: HashMap<String, Type>,
    /// Variables that have been used (for linear checking)
    used: HashSet<String>,
    /// Variables that must be used before scope ends
    must_use: HashSet<String>,
}

impl TypeEnv {
    fn new() -> Self {
        Self {
            types: HashMap::new(),
            used: HashSet::new(),
            must_use: HashSet::new(),
        }
    }

    fn insert(&mut self, name: String, ty: Type) {
        self.types.insert(name.clone(), ty);
        self.must_use.insert(name);
    }

    fn get(&self, name: &str) -> Option<&Type> {
        self.types.get(name)
    }

    fn mark_used(&mut self, name: &str, ty: &Type) -> Result<(), TypeError> {
        // Copy types can be used multiple times
        if ty.is_copy() {
            return Ok(());
        }

        // Non-Copy types can only be used once (linear types)
        if self.used.contains(name) {
            return Err(TypeError::VariableUsedTwice {
                var: name.to_string(),
                var_type: ty.clone(),
                first_use: "previous usage".to_string(),
                second_use: "current usage".to_string(),
            });
        }
        self.used.insert(name.to_string());
        Ok(())
    }

    fn check_all_used(&self) -> Result<(), TypeError> {
        for var in &self.must_use {
            // Skip Copy types - they don't need to be used
            if let Some(ty) = self.types.get(var) {
                if ty.is_copy() {
                    continue;
                }
            }

            // Non-Copy types must be used exactly once
            if !self.used.contains(var) {
                let var_type = self.types.get(var).cloned().unwrap_or(Type::Infer);
                return Err(TypeError::VariableNotUsed {
                    var: var.clone(),
                    var_type,
                });
            }
        }
        Ok(())
    }

    fn merge(&mut self, other: &TypeEnv) {
        // Merge used variables from both branches
        for var in &other.used {
            self.used.insert(var.clone());
        }
    }
}

pub struct TypeChecker {
    structs: HashMap<String, StructDef>,
    functions: HashMap<String, Function>,
}

impl TypeChecker {
    pub fn new(program: &Program) -> Self {
        let mut structs = HashMap::new();
        for struct_def in &program.structs {
            structs.insert(struct_def.name.clone(), struct_def.clone());
        }

        let mut functions = HashMap::new();
        for func in &program.functions {
            functions.insert(func.name.clone(), func.clone());
        }

        Self { structs, functions }
    }

    pub fn check(&self) -> Result<(), TypeError> {
        // Check all functions
        for func in self.functions.values() {
            self.check_function(func)?;
        }
        Ok(())
    }

    fn check_function(&self, func: &Function) -> Result<Type, TypeError> {
        let mut env = TypeEnv::new();

        // Add parameters to environment
        for param in &func.params {
            env.insert(param.name.clone(), param.ty.clone());
        }

        // Check function body
        let body_type = self.check_expr(&func.body, &mut env)?;

        // Verify all variables were used
        env.check_all_used()?;

        // Check return type matches
        if func.return_type != Type::Infer && func.return_type != body_type {
            return Err(TypeError::TypeMismatch {
                expected: func.return_type.clone(),
                found: body_type.clone(),
                context: format!("function '{}' return type", func.name),
            });
        }

        Ok(body_type)
    }

    fn check_expr(&self, expr: &Expr, env: &mut TypeEnv) -> Result<Type, TypeError> {
        match expr {
            Expr::IntLit(_) => Ok(Type::I32),
            Expr::BoolLit(_) => Ok(Type::Bool),
            Expr::StringLit(_) => Ok(Type::String),

            Expr::Var(name) => {
                let ty = env
                    .get(name)
                    .ok_or_else(|| TypeError::VariableNotFound {
                        var: name.clone(),
                    })?
                    .clone();

                // Mark variable as used (Copy types can be used multiple times)
                env.mark_used(name, &ty)?;

                Ok(ty)
            }

            Expr::BinOp { op, left, right } => {
                let left_ty = self.check_expr(left, env)?;
                let right_ty = self.check_expr(right, env)?;

                match op {
                    BinOp::Add => {
                        // Add supports int + int and String + String
                        if left_ty != right_ty {
                            return Err(TypeError::IncompatibleTypes {
                                left: left_ty,
                                right: right_ty,
                                op: op.to_string(),
                            });
                        }
                        match left_ty {
                            Type::I32 | Type::I64 | Type::String => Ok(left_ty),
                            _ => Err(TypeError::IncompatibleTypes {
                                left: left_ty,
                                right: right_ty,
                                op: op.to_string(),
                            }),
                        }
                    }
                    BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                        if left_ty != right_ty {
                            return Err(TypeError::IncompatibleTypes {
                                left: left_ty,
                                right: right_ty,
                                op: op.to_string(),
                            });
                        }
                        match left_ty {
                            Type::I32 | Type::I64 => Ok(left_ty),
                            _ => Err(TypeError::IncompatibleTypes {
                                left: left_ty,
                                right: right_ty,
                                op: op.to_string(),
                            }),
                        }
                    }
                    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                        if left_ty != right_ty {
                            return Err(TypeError::IncompatibleTypes {
                                left: left_ty,
                                right: right_ty,
                                op: op.to_string(),
                            });
                        }
                        Ok(Type::Bool)
                    }
                    BinOp::And | BinOp::Or => {
                        if left_ty != Type::Bool {
                            return Err(TypeError::IncompatibleTypes {
                                left: left_ty,
                                right: right_ty,
                                op: op.to_string(),
                            });
                        }
                        if right_ty != Type::Bool {
                            return Err(TypeError::IncompatibleTypes {
                                left: left_ty,
                                right: right_ty,
                                op: op.to_string(),
                            });
                        }
                        Ok(Type::Bool)
                    }
                    BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                        if left_ty != right_ty {
                            return Err(TypeError::IncompatibleTypes {
                                left: left_ty,
                                right: right_ty,
                                op: op.to_string(),
                            });
                        }
                        match left_ty {
                            Type::I32 | Type::I64 => Ok(left_ty),
                            _ => Err(TypeError::IncompatibleTypes {
                                left: left_ty,
                                right: right_ty,
                                op: op.to_string(),
                            }),
                        }
                    }
                }
            }

            Expr::Call { func, args } => {
                // Check for built-in functions
                match func.as_str() {
                    "read_file" => {
                        if args.len() != 1 {
                            return Err(TypeError::TypeMismatch {
                                expected: Type::String,
                                found: Type::I32,
                                context: format!("read_file expects 1 argument, got {}", args.len()),
                            });
                        }
                        let arg_ty = self.check_expr(&args[0], env)?;
                        if arg_ty != Type::String {
                            return Err(TypeError::TypeMismatch {
                                expected: Type::String,
                                found: arg_ty,
                                context: "read_file argument must be String".to_string(),
                            });
                        }
                        Ok(Type::String)  // Returns file contents as String
                    }
                    "write_file" => {
                        if args.len() != 2 {
                            return Err(TypeError::TypeMismatch {
                                expected: Type::String,
                                found: Type::I32,
                                context: format!("write_file expects 2 arguments, got {}", args.len()),
                            });
                        }
                        let path_ty = self.check_expr(&args[0], env)?;
                        let content_ty = self.check_expr(&args[1], env)?;
                        if path_ty != Type::String {
                            return Err(TypeError::TypeMismatch {
                                expected: Type::String,
                                found: path_ty,
                                context: "write_file first argument (path) must be String".to_string(),
                            });
                        }
                        if content_ty != Type::String {
                            return Err(TypeError::TypeMismatch {
                                expected: Type::String,
                                found: content_ty,
                                context: "write_file second argument (content) must be String".to_string(),
                            });
                        }
                        Ok(Type::I32)  // Returns 0 on success
                    }
                    "print" => {
                        if args.len() != 1 {
                            return Err(TypeError::TypeMismatch {
                                expected: Type::I32,
                                found: Type::I32,
                                context: format!("print expects 1 argument, got {}", args.len()),
                            });
                        }
                        // print accepts any type
                        self.check_expr(&args[0], env)?;
                        Ok(Type::I32)  // Returns 0 (unit placeholder)
                    }
                    _ => {
                        // User-defined function
                        let func_def = self.functions.get(func).ok_or_else(|| {
                            TypeError::VariableNotFound {
                                var: func.clone(),
                            }
                        })?;

                        // Check argument types
                        for (param, arg) in func_def.params.iter().zip(args.iter()) {
                            let arg_ty = self.check_expr(arg, env)?;
                            if param.ty != Type::Infer && param.ty != arg_ty {
                                return Err(TypeError::TypeMismatch {
                                    expected: param.ty.clone(),
                                    found: arg_ty,
                                    context: format!("argument to function '{}'", func),
                                });
                            }
                        }

                        // Return type is the function's return type
                        Ok(func_def.return_type.clone())
                    }
                }
            }

            Expr::Let { name, value, body } => {
                // Check value type
                let val_ty = self.check_expr(value, env)?;

                // Create new scope with the bound variable
                let mut new_env = env.clone();
                new_env.insert(name.clone(), val_ty);

                // Check body in new scope
                let body_ty = self.check_expr(body, &mut new_env)?;

                // Verify the bound variable was used in body
                new_env.check_all_used()?;

                // Merge usage information back to parent scope
                env.merge(&new_env);

                Ok(body_ty)
            }

            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                // Check condition is bool
                let cond_ty = self.check_expr(cond, env)?;
                if cond_ty != Type::Bool {
                    return Err(TypeError::TypeMismatch {
                        expected: Type::Bool,
                        found: cond_ty,
                        context: "if condition".to_string(),
                    });
                }

                // Check both branches have same type
                let mut then_env = env.clone();
                let then_ty = self.check_expr(then_branch, &mut then_env)?;

                let mut else_env = env.clone();
                let else_ty = self.check_expr(else_branch, &mut else_env)?;

                if !self.types_compatible(&then_ty, &else_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: then_ty.clone(),
                        found: else_ty,
                        context: "if/else branches".to_string(),
                    });
                }

                // Merge usage from both branches
                env.merge(&then_env);
                env.merge(&else_env);

                // Return the more specific type (prefer concrete over Infer)
                let result_ty = self.unify_types(&then_ty, &else_ty);

                Ok(result_ty)
            }

            Expr::Block(exprs) => {
                let mut result_ty = Type::I32;
                for expr in exprs {
                    result_ty = self.check_expr(expr, env)?;
                }
                Ok(result_ty)
            }

            Expr::Match { scrutinee, arms } => {
                // Check scrutinee type
                let scrutinee_ty = self.check_expr(scrutinee, env)?;

                if arms.is_empty() {
                    return Err(TypeError::TypeMismatch {
                        expected: Type::I32,
                        found: Type::I32,
                        context: "match expression must have at least one arm".to_string(),
                    });
                }

                // Check all arms
                let mut arm_type: Option<Type> = None;
                let mut has_wildcard = false;

                for arm in arms {
                    // Check pattern type matches scrutinee
                    let pattern_ty = self.pattern_type(&arm.pattern);
                    if !self.types_compatible(&pattern_ty, &scrutinee_ty) {
                        return Err(TypeError::TypeMismatch {
                            expected: scrutinee_ty,
                            found: pattern_ty,
                            context: "match pattern".to_string(),
                        });
                    }

                    // Check for wildcard (makes match exhaustive)
                    if matches!(arm.pattern, Pattern::Wildcard | Pattern::Var(_)) {
                        has_wildcard = true;
                    }

                    // Create new environment with pattern bindings
                    let mut arm_env = env.clone();
                    self.add_pattern_bindings(&arm.pattern, &scrutinee_ty, &mut arm_env);

                    // Check arm body
                    let body_ty = self.check_expr(&arm.body, &mut arm_env)?;

                    // All arms must have compatible types
                    if let Some(ref expected_ty) = arm_type {
                        if !self.types_compatible(&body_ty, expected_ty) {
                            return Err(TypeError::TypeMismatch {
                                expected: expected_ty.clone(),
                                found: body_ty,
                                context: "match arm".to_string(),
                            });
                        }
                        // Unify to get most specific type
                        arm_type = Some(self.unify_types(expected_ty, &body_ty));
                    } else {
                        arm_type = Some(body_ty);
                    }
                }

                // Warn about non-exhaustive matches (not an error for now)
                if !has_wildcard && scrutinee_ty != Type::Bool {
                    // For non-bool types, we can't easily check exhaustiveness
                    // In a real implementation, we'd track all literal patterns
                }

                Ok(arm_type.unwrap())
            }

            Expr::VecLit(elements) => {
                // Empty vector needs type annotation (for now, default to Vec<i32>)
                if elements.is_empty() {
                    return Ok(Type::Vec(Box::new(Type::I32)));
                }

                // Check first element type
                let elem_ty = self.check_expr(&elements[0], env)?;

                // All elements must have the same type
                for (i, elem) in elements.iter().enumerate().skip(1) {
                    let ty = self.check_expr(elem, env)?;
                    if ty != elem_ty {
                        return Err(TypeError::TypeMismatch {
                            expected: elem_ty.clone(),
                            found: ty,
                            context: format!("vector element at index {}", i),
                        });
                    }
                }

                Ok(Type::Vec(Box::new(elem_ty)))
            }

            Expr::HashMapLit(entries) => {
                // Empty HashMap needs type annotation (for now, default to HashMap<String, i32>)
                if entries.is_empty() {
                    return Ok(Type::HashMap(Box::new(Type::String), Box::new(Type::I32)));
                }

                // Check first entry key and value types
                let (first_key, first_val) = &entries[0];
                let key_ty = self.check_expr(first_key, env)?;
                let val_ty = self.check_expr(first_val, env)?;

                // All keys must have same type, all values must have same type
                for (i, (key_expr, val_expr)) in entries.iter().enumerate().skip(1) {
                    let k_ty = self.check_expr(key_expr, env)?;
                    let v_ty = self.check_expr(val_expr, env)?;

                    if k_ty != key_ty {
                        return Err(TypeError::TypeMismatch {
                            expected: key_ty.clone(),
                            found: k_ty,
                            context: format!("HashMap key at index {}", i),
                        });
                    }
                    if v_ty != val_ty {
                        return Err(TypeError::TypeMismatch {
                            expected: val_ty.clone(),
                            found: v_ty,
                            context: format!("HashMap value at index {}", i),
                        });
                    }
                }

                Ok(Type::HashMap(Box::new(key_ty), Box::new(val_ty)))
            }

            Expr::Index { vec, index } => {
                // Check vector type
                let vec_ty = self.check_expr(vec, env)?;
                let elem_ty = match vec_ty {
                    Type::Vec(elem_ty) => elem_ty,
                    _ => {
                        return Err(TypeError::TypeMismatch {
                            expected: Type::Vec(Box::new(Type::Infer)),
                            found: vec_ty,
                            context: "indexing requires a vector type".to_string(),
                        });
                    }
                };

                // Check index is i32
                let index_ty = self.check_expr(index, env)?;
                if index_ty != Type::I32 {
                    return Err(TypeError::TypeMismatch {
                        expected: Type::I32,
                        found: index_ty,
                        context: "vector index".to_string(),
                    });
                }

                Ok(*elem_ty)
            }

            Expr::StructLit { name, fields } => {
                // Look up struct definition
                let struct_def = self.structs.get(name).ok_or_else(|| {
                    TypeError::VariableNotFound {
                        var: format!("struct '{}'", name),
                    }
                })?;

                // Check all fields are provided and have correct types
                for (field_name, field_expr) in fields {
                    let field_def = struct_def.fields.iter().find(|f| &f.name == field_name)
                        .ok_or_else(|| TypeError::VariableNotFound {
                            var: format!("field '{}' in struct '{}'", field_name, name),
                        })?;

                    let field_ty = self.check_expr(field_expr, env)?;
                    if field_ty != field_def.ty {
                        return Err(TypeError::TypeMismatch {
                            expected: field_def.ty.clone(),
                            found: field_ty,
                            context: format!("field '{}' in struct '{}'", field_name, name),
                        });
                    }
                }

                // Check all required fields are provided
                for field_def in &struct_def.fields {
                    if !fields.iter().any(|(name, _)| name == &field_def.name) {
                        return Err(TypeError::TypeMismatch {
                            expected: Type::Struct(name.clone()),
                            found: Type::Infer,
                            context: format!("missing field '{}' in struct '{}'", field_def.name, name),
                        });
                    }
                }

                Ok(Type::Struct(name.clone()))
            }

            Expr::FieldAccess { expr, field } => {
                // Check expression type
                let expr_ty = self.check_expr(expr, env)?;
                let struct_name = match expr_ty {
                    Type::Struct(name) => name,
                    _ => {
                        return Err(TypeError::TypeMismatch {
                            expected: Type::Struct(String::from("<any>")),
                            found: expr_ty,
                            context: "field access requires a struct type".to_string(),
                        });
                    }
                };

                // Look up struct definition
                let struct_def = self.structs.get(&struct_name).ok_or_else(|| {
                    TypeError::VariableNotFound {
                        var: format!("struct '{}'", struct_name),
                    }
                })?;

                // Find field in struct
                let field_def = struct_def.fields.iter().find(|f| &f.name == field)
                    .ok_or_else(|| TypeError::VariableNotFound {
                        var: format!("field '{}' in struct '{}'", field, struct_name),
                    })?;

                Ok(field_def.ty.clone())
            }

            Expr::For { var, iterable, body } => {
                // Check iterable is a Vec<T>
                let iterable_ty = self.check_expr(iterable, env)?;
                let elem_ty = match iterable_ty {
                    Type::Vec(elem_ty) => elem_ty,
                    _ => {
                        return Err(TypeError::TypeMismatch {
                            expected: Type::Vec(Box::new(Type::Infer)),
                            found: iterable_ty,
                            context: "for loop requires a vector".to_string(),
                        });
                    }
                };

                // Create new environment with loop variable bound to element type
                let mut loop_env = env.clone();
                loop_env.insert(var.clone(), *elem_ty);

                // Check body in loop environment
                self.check_expr(body, &mut loop_env)?;

                // For loops return unit type (for now, i32 as placeholder)
                Ok(Type::I32)
            }

            Expr::While { cond, body } => {
                // Check condition is bool
                let cond_ty = self.check_expr(cond, env)?;
                if cond_ty != Type::Bool {
                    return Err(TypeError::TypeMismatch {
                        expected: Type::Bool,
                        found: cond_ty,
                        context: "while condition".to_string(),
                    });
                }

                // Check body
                self.check_expr(body, env)?;

                // While loops return unit type (for now, i32 as placeholder)
                Ok(Type::I32)
            }

            Expr::Some(expr) => {
                let inner_ty = self.check_expr(expr, env)?;
                Ok(Type::Option(Box::new(inner_ty)))
            }

            Expr::None => {
                // None has type Option<Infer> - will be refined by context
                Ok(Type::Option(Box::new(Type::Infer)))
            }

            Expr::Ok(expr) => {
                let ok_ty = self.check_expr(expr, env)?;
                Ok(Type::Result(Box::new(ok_ty), Box::new(Type::Infer)))
            }

            Expr::Err(expr) => {
                let err_ty = self.check_expr(expr, env)?;
                Ok(Type::Result(Box::new(Type::Infer), Box::new(err_ty)))
            }

            Expr::Borrow(expr) => {
                // Borrow creates a reference to the expression's type
                let inner_ty = self.check_expr(expr, env)?;
                Ok(Type::Ref(Box::new(inner_ty)))
            }

            Expr::Deref(expr) => {
                // Dereference extracts the inner type from a reference
                let ref_ty = self.check_expr(expr, env)?;
                match ref_ty {
                    Type::Ref(inner_ty) => Ok(*inner_ty),
                    _ => Err(TypeError::TypeMismatch {
                        expected: Type::Ref(Box::new(Type::Infer)),
                        found: ref_ty,
                        context: "dereference requires a reference type".to_string(),
                    }),
                }
            }
        }
    }

    /// Check if two types are compatible (can unify)
    /// Infer type is compatible with any type
    /// Option<Infer> is compatible with Option<T> for any T
    /// Result<Infer, X> is compatible with Result<T, X>, etc.
    fn types_compatible(&self, ty1: &Type, ty2: &Type) -> bool {
        match (ty1, ty2) {
            // Infer matches anything
            (Type::Infer, _) | (_, Type::Infer) => true,

            // Identical types
            _ if ty1 == ty2 => true,

            // Option types: compatible if inner types are compatible
            (Type::Option(inner1), Type::Option(inner2)) => {
                self.types_compatible(inner1, inner2)
            }

            // Result types: compatible if both inner types are compatible
            (Type::Result(ok1, err1), Type::Result(ok2, err2)) => {
                self.types_compatible(ok1, ok2) && self.types_compatible(err1, err2)
            }

            // Vec types: compatible if element types are compatible
            (Type::Vec(elem1), Type::Vec(elem2)) => {
                self.types_compatible(elem1, elem2)
            }

            // HashMap types: compatible if key and value types are compatible
            (Type::HashMap(k1, v1), Type::HashMap(k2, v2)) => {
                self.types_compatible(k1, k2) && self.types_compatible(v1, v2)
            }

            // Ref types: compatible if inner types are compatible
            (Type::Ref(inner1), Type::Ref(inner2)) => {
                self.types_compatible(inner1, inner2)
            }

            // Otherwise incompatible
            _ => false,
        }
    }

    /// Unify two compatible types, preferring the more specific type
    /// When one type is Infer, prefer the other
    /// When Option<Infer> and Option<T>, prefer Option<T>
    fn unify_types(&self, ty1: &Type, ty2: &Type) -> Type {
        match (ty1, ty2) {
            // Prefer non-Infer type
            (Type::Infer, _) => ty2.clone(),
            (_, Type::Infer) => ty1.clone(),

            // If identical, return either
            _ if ty1 == ty2 => ty1.clone(),

            // Option types: unify inner types
            (Type::Option(inner1), Type::Option(inner2)) => {
                Type::Option(Box::new(self.unify_types(inner1, inner2)))
            }

            // Result types: unify both inner types
            (Type::Result(ok1, err1), Type::Result(ok2, err2)) => {
                Type::Result(
                    Box::new(self.unify_types(ok1, ok2)),
                    Box::new(self.unify_types(err1, err2)),
                )
            }

            // Vec types: unify element types
            (Type::Vec(elem1), Type::Vec(elem2)) => {
                Type::Vec(Box::new(self.unify_types(elem1, elem2)))
            }

            // HashMap types: unify key and value types
            (Type::HashMap(k1, v1), Type::HashMap(k2, v2)) => {
                Type::HashMap(
                    Box::new(self.unify_types(k1, k2)),
                    Box::new(self.unify_types(v1, v2)),
                )
            }

            // Ref types: unify inner types
            (Type::Ref(inner1), Type::Ref(inner2)) => {
                Type::Ref(Box::new(self.unify_types(inner1, inner2)))
            }

            // Otherwise, prefer ty1 (they should be compatible if this is called)
            _ => ty1.clone(),
        }
    }

    fn pattern_type(&self, pattern: &Pattern) -> Type {
        match pattern {
            Pattern::IntLit(_) => Type::I32,
            Pattern::BoolLit(_) => Type::Bool,
            Pattern::Var(_) | Pattern::Wildcard => Type::Infer,
            Pattern::Some(inner) => Type::Option(Box::new(self.pattern_type(inner))),
            Pattern::None => Type::Option(Box::new(Type::Infer)),
            Pattern::Ok(inner) => Type::Result(Box::new(self.pattern_type(inner)), Box::new(Type::Infer)),
            Pattern::Err(inner) => Type::Result(Box::new(Type::Infer), Box::new(self.pattern_type(inner))),
        }
    }

    fn add_pattern_bindings(&self, pattern: &Pattern, ty: &Type, env: &mut TypeEnv) {
        match pattern {
            Pattern::Var(name) => {
                env.insert(name.clone(), ty.clone());
            }
            Pattern::Some(inner_pattern) => {
                // Extract inner type from Option<T>
                if let Type::Option(inner_ty) = ty {
                    self.add_pattern_bindings(inner_pattern, inner_ty, env);
                }
            }
            Pattern::Ok(inner_pattern) => {
                // Extract ok type from Result<T, E>
                if let Type::Result(ok_ty, _err_ty) = ty {
                    self.add_pattern_bindings(inner_pattern, ok_ty, env);
                }
            }
            Pattern::Err(inner_pattern) => {
                // Extract err type from Result<T, E>
                if let Type::Result(_ok_ty, err_ty) = ty {
                    self.add_pattern_bindings(inner_pattern, err_ty, env);
                }
            }
            Pattern::None | Pattern::IntLit(_) | Pattern::BoolLit(_) | Pattern::Wildcard => {
                // No bindings for these patterns
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    #[test]
    fn test_simple_program() {
        let input = "fn main() { 42 }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let checker = TypeChecker::new(&program);
        assert!(checker.check().is_ok());
    }

    #[test]
    fn test_variable_used_once() {
        let input = "fn main() { let x = 5; x }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let checker = TypeChecker::new(&program);
        assert!(checker.check().is_ok());
    }

    #[test]
    fn test_variable_not_used() {
        // Copy types (i32) don't need to be used - this now passes
        let input = "fn main() { let x = 5; 42 }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let checker = TypeChecker::new(&program);
        let result = checker.check();
        assert!(result.is_ok()); // Copy types can be unused
    }

    #[test]
    fn test_variable_used_twice() {
        // Copy types (i32) can be used multiple times - this now passes
        let input = "fn main() { let x = 5; x + x }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let checker = TypeChecker::new(&program);
        let result = checker.check();
        assert!(result.is_ok()); // Copy types can be used multiple times
    }

    #[test]
    fn test_type_mismatch() {
        let input = "fn add(x: i32, y: i32) -> bool { x + y }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let checker = TypeChecker::new(&program);
        let result = checker.check();
        assert!(result.is_err());
    }

    #[test]
    fn test_if_expression_types() {
        let input = "fn main() { if true { 1 } else { 2 } }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let checker = TypeChecker::new(&program);
        assert!(checker.check().is_ok());
    }

    #[test]
    fn test_if_branch_type_mismatch() {
        let input = "fn main() { if true { 1 } else { true } }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        let checker = TypeChecker::new(&program);
        let result = checker.check();
        assert!(result.is_err());
    }
}
