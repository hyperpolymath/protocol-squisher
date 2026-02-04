// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Abstract Syntax Tree for ephapax language

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    I32,
    I64,
    Bool,
    String,            // String type (heap-allocated, not Copy)
    Vec(Box<Type>),    // Vector type Vec<T> (heap-allocated, not Copy)
    HashMap(Box<Type>, Box<Type>), // HashMap<K, V> type (heap-allocated, not Copy)
    Struct(String),    // Struct type (named, heap-allocated, not Copy)
    Ref(Box<Type>),    // Immutable reference type &T
    Option(Box<Type>), // Option<T> type (heap-allocated, not Copy)
    Result(Box<Type>, Box<Type>), // Result<T, E> type (heap-allocated, not Copy)
    Infer,             // Type inference placeholder
}

impl Type {
    /// Check if this type implements Copy (can be used multiple times)
    pub fn is_copy(&self) -> bool {
        match self {
            Type::I32 | Type::I64 | Type::Bool => true,
            Type::String => false, // Strings are heap-allocated, not Copy
            Type::Vec(_) => false, // Vectors are heap-allocated, not Copy
            Type::HashMap(_, _) => false, // HashMaps are heap-allocated, not Copy
            Type::Struct(_) => false, // Structs are heap-allocated, not Copy
            Type::Ref(_) => true, // References are Copy (they're just pointers)
            Type::Option(_) => false, // Option is heap-allocated, not Copy
            Type::Result(_, _) => false, // Result is heap-allocated, not Copy
            Type::Infer => false, // Unknown types are not Copy by default
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::I32 => write!(f, "i32"),
            Type::I64 => write!(f, "i64"),
            Type::Bool => write!(f, "bool"),
            Type::String => write!(f, "String"),
            Type::Vec(inner) => write!(f, "Vec<{}>", inner),
            Type::HashMap(key, val) => write!(f, "HashMap<{}, {}>", key, val),
            Type::Struct(name) => write!(f, "{}", name),
            Type::Ref(inner) => write!(f, "&{}", inner),
            Type::Option(inner) => write!(f, "Option<{}>", inner),
            Type::Result(ok_ty, err_ty) => write!(f, "Result<{}, {}>", ok_ty, err_ty),
            Type::Infer => write!(f, "_"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Program {
    pub structs: Vec<StructDef>,
    pub functions: Vec<Function>,
}

#[derive(Debug, Clone)]
pub struct StructDef {
    pub name: String,
    pub fields: Vec<StructField>,
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Type,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub enum Expr {
    // Literals
    IntLit(i64),
    BoolLit(bool),
    StringLit(String),
    VecLit(Vec<Expr>),  // Vector literal [e1, e2, ...]
    HashMapLit(Vec<(Expr, Expr)>),  // HashMap literal {key1: val1, key2: val2, ...}

    // Variable reference
    Var(String),

    // Unary operations
    UnaryOp {
        op: UnaryOp,
        operand: Box<Expr>,
    },

    // Binary operations
    BinOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },

    // Function call
    Call {
        func: String,
        args: Vec<Expr>,
    },

    // Vector indexing vec[index]
    Index {
        vec: Box<Expr>,
        index: Box<Expr>,
    },

    // Struct literal Name { field1: value1, field2: value2 }
    StructLit {
        name: String,
        fields: Vec<(String, Expr)>,  // (field_name, field_value)
    },

    // Field access struct.field
    FieldAccess {
        expr: Box<Expr>,
        field: String,
    },

    // Let binding
    Let {
        name: String,
        value: Box<Expr>,
        body: Box<Expr>,
    },

    // For loop (for var in iterable { body })
    For {
        var: String,
        iterable: Box<Expr>,
        body: Box<Expr>,
    },

    // While loop (while cond { body })
    While {
        cond: Box<Expr>,
        body: Box<Expr>,
    },

    // If expression
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },

    // Block (sequence of expressions)
    Block(Vec<Expr>),

    // Match expression
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
    },

    // Option constructors
    Some(Box<Expr>),  // Some(value)
    None,             // None

    // Result constructors
    Ok(Box<Expr>),    // Ok(value)
    Err(Box<Expr>),   // Err(error)

    // Borrow expression (&x)
    Borrow(Box<Expr>),

    // Dereference expression (*x)
    Deref(Box<Expr>),
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    /// Literal integer pattern: 42
    IntLit(i64),
    /// Literal boolean pattern: true, false
    BoolLit(bool),
    /// Variable binding pattern: x
    Var(String),
    /// Wildcard pattern: _
    Wildcard,
    /// Option::Some pattern: Some(x)
    Some(Box<Pattern>),
    /// Option::None pattern: None
    None,
    /// Result::Ok pattern: Ok(x)
    Ok(Box<Pattern>),
    /// Result::Err pattern: Err(e)
    Err(Box<Pattern>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// Logical negation: !
    Not,
    /// Arithmetic negation: - (unary minus)
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // Comparison
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,

    // Logical
    And,  // &&
    Or,   // ||

    // Bitwise
    BitAnd,  // &
    BitOr,   // |
    BitXor,  // ^
    Shl,     // <<
    Shr,     // >>
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnaryOp::Not => write!(f, "!"),
            UnaryOp::Neg => write!(f, "-"),
        }
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Mod => write!(f, "%"),
            BinOp::Eq => write!(f, "=="),
            BinOp::Ne => write!(f, "!="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Gt => write!(f, ">"),
            BinOp::Le => write!(f, "<="),
            BinOp::Ge => write!(f, ">="),
            BinOp::And => write!(f, "&&"),
            BinOp::Or => write!(f, "||"),
            BinOp::BitAnd => write!(f, "&"),
            BinOp::BitOr => write!(f, "|"),
            BinOp::BitXor => write!(f, "^"),
            BinOp::Shl => write!(f, "<<"),
            BinOp::Shr => write!(f, ">>"),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::IntLit(n) => write!(f, "{}", n),
            Expr::BoolLit(b) => write!(f, "{}", b),
            Expr::StringLit(s) => write!(f, "\"{}\"", s),
            Expr::VecLit(elements) => {
                write!(f, "[")?;
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                write!(f, "]")
            }
            Expr::HashMapLit(entries) => {
                write!(f, "{{")?;
                for (i, (key, val)) in entries.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", key, val)?;
                }
                write!(f, "}}")
            }
            Expr::Var(s) => write!(f, "{}", s),
            Expr::UnaryOp { op, operand } => {
                write!(f, "({}{})", op, operand)
            }
            Expr::BinOp { op, left, right } => {
                write!(f, "({} {} {})", left, op, right)
            }
            Expr::Call { func, args } => {
                write!(f, "{}(", func)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
            Expr::Index { vec, index } => {
                write!(f, "{}[{}]", vec, index)
            }
            Expr::StructLit { name, fields } => {
                write!(f, "{} {{", name)?;
                for (i, (field_name, field_val)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", field_name, field_val)?;
                }
                write!(f, "}}")
            }
            Expr::FieldAccess { expr, field } => {
                write!(f, "{}.{}", expr, field)
            }
            Expr::Let { name, value, body } => {
                write!(f, "(let {} = {} in {})", name, value, body)
            }
            Expr::For { var, iterable, body } => {
                write!(f, "(for {} in {} {{ {} }})", var, iterable, body)
            }
            Expr::While { cond, body } => {
                write!(f, "(while {} {{ {} }})", cond, body)
            }
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                write!(f, "(if {} then {} else {})", cond, then_branch, else_branch)
            }
            Expr::Block(exprs) => {
                write!(f, "{{ ")?;
                for (i, expr) in exprs.iter().enumerate() {
                    if i > 0 {
                        write!(f, "; ")?;
                    }
                    write!(f, "{}", expr)?;
                }
                write!(f, " }}")
            }
            Expr::Match { scrutinee, arms } => {
                write!(f, "(match {} {{", scrutinee)?;
                for arm in arms {
                    write!(f, " {} => {},", arm.pattern, arm.body)?;
                }
                write!(f, " }})")
            }
            Expr::Some(expr) => write!(f, "Some({})", expr),
            Expr::None => write!(f, "None"),
            Expr::Ok(expr) => write!(f, "Ok({})", expr),
            Expr::Err(expr) => write!(f, "Err({})", expr),
            Expr::Borrow(expr) => write!(f, "&{}", expr),
            Expr::Deref(expr) => write!(f, "*{}", expr),
        }
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pattern::IntLit(n) => write!(f, "{}", n),
            Pattern::BoolLit(b) => write!(f, "{}", b),
            Pattern::Var(s) => write!(f, "{}", s),
            Pattern::Wildcard => write!(f, "_"),
            Pattern::Some(p) => write!(f, "Some({})", p),
            Pattern::None => write!(f, "None"),
            Pattern::Ok(p) => write!(f, "Ok({})", p),
            Pattern::Err(p) => write!(f, "Err({})", p),
        }
    }
}
