// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Abstract Syntax Tree for ephapax language

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    I32,
    I64,
    Bool,
    String,          // String type (heap-allocated, not Copy)
    Vec(Box<Type>),  // Vector type Vec<T> (heap-allocated, not Copy)
    Ref(Box<Type>),  // Immutable reference type &T
    Infer,           // Type inference placeholder
}

impl Type {
    /// Check if this type implements Copy (can be used multiple times)
    pub fn is_copy(&self) -> bool {
        match self {
            Type::I32 | Type::I64 | Type::Bool => true,
            Type::String => false, // Strings are heap-allocated, not Copy
            Type::Vec(_) => false, // Vectors are heap-allocated, not Copy
            Type::Ref(_) => true, // References are Copy (they're just pointers)
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
            Type::Ref(inner) => write!(f, "&{}", inner),
            Type::Infer => write!(f, "_"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Program {
    pub functions: Vec<Function>,
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

    // Variable reference
    Var(String),

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

    // Let binding
    Let {
        name: String,
        value: Box<Expr>,
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
            Expr::Var(s) => write!(f, "{}", s),
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
            Expr::Let { name, value, body } => {
                write!(f, "(let {} = {} in {})", name, value, body)
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
        }
    }
}
