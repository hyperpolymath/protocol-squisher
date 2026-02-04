// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Lexer for ephapax language

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    // Keywords
    Fn,
    Let,
    If,
    Else,
    True,
    False,

    // Identifiers and literals
    Ident(String),
    IntLit(i64),

    // Type keywords
    I32,
    I64,
    Bool,

    // Symbols
    LParen,
    RParen,
    LBrace,
    RBrace,
    Arrow,      // ->
    Colon,
    Semi,
    Comma,

    // Operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Eq,         // ==
    Ne,         // !=
    Lt,         // <
    Gt,         // >
    Le,         // <=
    Ge,         // >=
    Assign,     // =

    // Special
    Eof,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Fn => write!(f, "fn"),
            Token::Let => write!(f, "let"),
            Token::If => write!(f, "if"),
            Token::Else => write!(f, "else"),
            Token::True => write!(f, "true"),
            Token::False => write!(f, "false"),
            Token::Ident(s) => write!(f, "{}", s),
            Token::IntLit(n) => write!(f, "{}", n),
            Token::I32 => write!(f, "i32"),
            Token::I64 => write!(f, "i64"),
            Token::Bool => write!(f, "bool"),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::Arrow => write!(f, "->"),
            Token::Colon => write!(f, ":"),
            Token::Semi => write!(f, ";"),
            Token::Comma => write!(f, ","),
            Token::Plus => write!(f, "+"),
            Token::Minus => write!(f, "-"),
            Token::Star => write!(f, "*"),
            Token::Slash => write!(f, "/"),
            Token::Percent => write!(f, "%"),
            Token::Eq => write!(f, "=="),
            Token::Ne => write!(f, "!="),
            Token::Lt => write!(f, "<"),
            Token::Gt => write!(f, ">"),
            Token::Le => write!(f, "<="),
            Token::Ge => write!(f, ">="),
            Token::Assign => write!(f, "="),
            Token::Eof => write!(f, "<EOF>"),
        }
    }
}

pub struct Lexer {
    input: Vec<char>,
    pos: usize,
}

impl Lexer {
    pub fn new(input: &str) -> Self {
        Self {
            input: input.chars().collect(),
            pos: 0,
        }
    }

    fn current(&self) -> Option<char> {
        if self.pos < self.input.len() {
            Some(self.input[self.pos])
        } else {
            None
        }
    }

    fn peek(&self, offset: usize) -> Option<char> {
        let idx = self.pos + offset;
        if idx < self.input.len() {
            Some(self.input[idx])
        } else {
            None
        }
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.current() {
            if ch.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn skip_comment(&mut self) {
        // Skip // comments
        if self.current() == Some('/') && self.peek(1) == Some('/') {
            while let Some(ch) = self.current() {
                if ch == '\n' {
                    break;
                }
                self.advance();
            }
        }
    }

    fn read_number(&mut self) -> i64 {
        let mut num = String::new();
        while let Some(ch) = self.current() {
            if ch.is_ascii_digit() {
                num.push(ch);
                self.advance();
            } else {
                break;
            }
        }
        num.parse().unwrap_or(0)
    }

    fn read_ident(&mut self) -> String {
        let mut ident = String::new();
        while let Some(ch) = self.current() {
            if ch.is_alphanumeric() || ch == '_' {
                ident.push(ch);
                self.advance();
            } else {
                break;
            }
        }
        ident
    }

    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();
        self.skip_comment();
        self.skip_whitespace();

        match self.current() {
            None => Token::Eof,
            Some(ch) => match ch {
                '(' => {
                    self.advance();
                    Token::LParen
                }
                ')' => {
                    self.advance();
                    Token::RParen
                }
                '{' => {
                    self.advance();
                    Token::LBrace
                }
                '}' => {
                    self.advance();
                    Token::RBrace
                }
                ':' => {
                    self.advance();
                    Token::Colon
                }
                ';' => {
                    self.advance();
                    Token::Semi
                }
                ',' => {
                    self.advance();
                    Token::Comma
                }
                '+' => {
                    self.advance();
                    Token::Plus
                }
                '*' => {
                    self.advance();
                    Token::Star
                }
                '/' => {
                    self.advance();
                    Token::Slash
                }
                '%' => {
                    self.advance();
                    Token::Percent
                }
                '-' => {
                    self.advance();
                    if self.current() == Some('>') {
                        self.advance();
                        Token::Arrow
                    } else {
                        Token::Minus
                    }
                }
                '=' => {
                    self.advance();
                    if self.current() == Some('=') {
                        self.advance();
                        Token::Eq
                    } else {
                        Token::Assign
                    }
                }
                '!' => {
                    self.advance();
                    if self.current() == Some('=') {
                        self.advance();
                        Token::Ne
                    } else {
                        panic!("Unexpected character after '!'");
                    }
                }
                '<' => {
                    self.advance();
                    if self.current() == Some('=') {
                        self.advance();
                        Token::Le
                    } else {
                        Token::Lt
                    }
                }
                '>' => {
                    self.advance();
                    if self.current() == Some('=') {
                        self.advance();
                        Token::Ge
                    } else {
                        Token::Gt
                    }
                }
                _ if ch.is_ascii_digit() => {
                    let num = self.read_number();
                    Token::IntLit(num)
                }
                _ if ch.is_alphabetic() || ch == '_' => {
                    let ident = self.read_ident();
                    match ident.as_str() {
                        "fn" => Token::Fn,
                        "let" => Token::Let,
                        "if" => Token::If,
                        "else" => Token::Else,
                        "true" => Token::True,
                        "false" => Token::False,
                        "i32" => Token::I32,
                        "i64" => Token::I64,
                        "bool" => Token::Bool,
                        _ => Token::Ident(ident),
                    }
                }
                _ => panic!("Unexpected character: {}", ch),
            },
        }
    }

    pub fn tokenize(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        loop {
            let tok = self.next_token();
            if tok == Token::Eof {
                tokens.push(tok);
                break;
            }
            tokens.push(tok);
        }
        tokens
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokenize_simple() {
        let mut lexer = Lexer::new("fn main() { 42 }");
        let tokens = lexer.tokenize();
        assert_eq!(
            tokens,
            vec![
                Token::Fn,
                Token::Ident("main".to_string()),
                Token::LParen,
                Token::RParen,
                Token::LBrace,
                Token::IntLit(42),
                Token::RBrace,
                Token::Eof
            ]
        );
    }

    #[test]
    fn test_tokenize_with_types() {
        let mut lexer = Lexer::new("fn add(x: i32, y: i32) -> i32 { x + y }");
        let tokens = lexer.tokenize();
        assert!(tokens.contains(&Token::Fn));
        assert!(tokens.contains(&Token::I32));
        assert!(tokens.contains(&Token::Arrow));
        assert!(tokens.contains(&Token::Plus));
    }

    #[test]
    fn test_tokenize_comparison() {
        let mut lexer = Lexer::new("if x == y { true } else { false }");
        let tokens = lexer.tokenize();
        assert!(tokens.contains(&Token::If));
        assert!(tokens.contains(&Token::Eq));
        assert!(tokens.contains(&Token::Else));
    }
}
