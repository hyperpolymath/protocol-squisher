// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Parser for ephapax language

use crate::ast::*;
use crate::tokens::{Lexer, Token};

pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    pub fn new(input: &str) -> Self {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize();
        Self { tokens, pos: 0 }
    }

    fn current(&self) -> &Token {
        &self.tokens[self.pos]
    }

    fn peek(&self, offset: usize) -> Option<&Token> {
        let idx = self.pos + offset;
        if idx < self.tokens.len() {
            Some(&self.tokens[idx])
        } else {
            None
        }
    }

    fn advance(&mut self) {
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
    }

    fn expect(&mut self, expected: Token) -> Result<(), String> {
        if self.current() == &expected {
            self.advance();
            Ok(())
        } else {
            Err(format!(
                "Expected {}, got {}",
                expected,
                self.current()
            ))
        }
    }

    pub fn parse_program(&mut self) -> Result<Program, String> {
        let mut functions = Vec::new();
        while self.current() != &Token::Eof {
            functions.push(self.parse_function()?);
        }
        Ok(Program { functions })
    }

    fn parse_function(&mut self) -> Result<Function, String> {
        self.expect(Token::Fn)?;

        let name = match self.current() {
            Token::Ident(s) => s.clone(),
            _ => return Err("Expected function name".to_string()),
        };
        self.advance();

        self.expect(Token::LParen)?;

        let mut params = Vec::new();
        while self.current() != &Token::RParen {
            let param_name = match self.current() {
                Token::Ident(s) => s.clone(),
                _ => return Err("Expected parameter name".to_string()),
            };
            self.advance();

            let param_type = if self.current() == &Token::Colon {
                self.advance();
                self.parse_type()?
            } else {
                Type::Infer
            };

            params.push(Param {
                name: param_name,
                ty: param_type,
            });

            if self.current() == &Token::Comma {
                self.advance();
            } else if self.current() != &Token::RParen {
                return Err("Expected ',' or ')' after parameter".to_string());
            }
        }
        self.expect(Token::RParen)?;

        let return_type = if self.current() == &Token::Arrow {
            self.advance();
            self.parse_type()?
        } else {
            Type::Infer
        };

        let body = self.parse_block_expr()?;

        Ok(Function {
            name,
            params,
            return_type,
            body,
        })
    }

    fn parse_type(&mut self) -> Result<Type, String> {
        match self.current() {
            Token::I32 => {
                self.advance();
                Ok(Type::I32)
            }
            Token::I64 => {
                self.advance();
                Ok(Type::I64)
            }
            Token::Bool => {
                self.advance();
                Ok(Type::Bool)
            }
            _ => Err(format!("Expected type, got {}", self.current())),
        }
    }

    fn parse_block_expr(&mut self) -> Result<Expr, String> {
        self.expect(Token::LBrace)?;

        let mut exprs = Vec::new();
        while self.current() != &Token::RBrace {
            exprs.push(self.parse_expr()?);

            // Optional semicolon between expressions
            if self.current() == &Token::Semi {
                self.advance();
            }

            if self.current() == &Token::RBrace {
                break;
            }
        }

        self.expect(Token::RBrace)?;

        if exprs.is_empty() {
            Err("Empty block".to_string())
        } else if exprs.len() == 1 {
            Ok(exprs.into_iter().next().unwrap())
        } else {
            Ok(Expr::Block(exprs))
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, String> {
        match self.current() {
            Token::Let => self.parse_let(),
            Token::If => self.parse_if(),
            Token::Match => self.parse_match(),
            _ => self.parse_comparison(),
        }
    }

    fn parse_let(&mut self) -> Result<Expr, String> {
        self.expect(Token::Let)?;

        let name = match self.current() {
            Token::Ident(s) => s.clone(),
            _ => return Err("Expected variable name after 'let'".to_string()),
        };
        self.advance();

        self.expect(Token::Assign)?;

        let value = Box::new(self.parse_expr()?);

        self.expect(Token::Semi)?;

        let body = Box::new(self.parse_expr()?);

        Ok(Expr::Let { name, value, body })
    }

    fn parse_if(&mut self) -> Result<Expr, String> {
        self.expect(Token::If)?;

        let cond = Box::new(self.parse_expr()?);

        let then_branch = Box::new(self.parse_block_expr()?);

        self.expect(Token::Else)?;

        let else_branch = Box::new(self.parse_block_expr()?);

        Ok(Expr::If {
            cond,
            then_branch,
            else_branch,
        })
    }

    fn parse_match(&mut self) -> Result<Expr, String> {
        self.expect(Token::Match)?;

        let scrutinee = Box::new(self.parse_comparison()?);

        self.expect(Token::LBrace)?;

        let mut arms = Vec::new();
        while self.current() != &Token::RBrace {
            let pattern = self.parse_pattern()?;

            self.expect(Token::FatArrow)?;

            let body = self.parse_comparison()?;

            arms.push(MatchArm { pattern, body });

            // Optional comma
            if self.current() == &Token::Comma {
                self.advance();
            }

            if self.current() == &Token::RBrace {
                break;
            }
        }

        self.expect(Token::RBrace)?;

        if arms.is_empty() {
            return Err("Match expression must have at least one arm".to_string());
        }

        Ok(Expr::Match { scrutinee, arms })
    }

    fn parse_pattern(&mut self) -> Result<Pattern, String> {
        match self.current() {
            Token::IntLit(n) => {
                let val = *n;
                self.advance();
                Ok(Pattern::IntLit(val))
            }
            Token::True => {
                self.advance();
                Ok(Pattern::BoolLit(true))
            }
            Token::False => {
                self.advance();
                Ok(Pattern::BoolLit(false))
            }
            Token::Underscore => {
                self.advance();
                Ok(Pattern::Wildcard)
            }
            Token::Ident(s) => {
                let name = s.clone();
                self.advance();
                Ok(Pattern::Var(name))
            }
            _ => Err(format!("Expected pattern, got {}", self.current())),
        }
    }

    fn parse_comparison(&mut self) -> Result<Expr, String> {
        let mut left = self.parse_additive()?;

        while matches!(
            self.current(),
            Token::Eq | Token::Ne | Token::Lt | Token::Gt | Token::Le | Token::Ge
        ) {
            let op = match self.current() {
                Token::Eq => BinOp::Eq,
                Token::Ne => BinOp::Ne,
                Token::Lt => BinOp::Lt,
                Token::Gt => BinOp::Gt,
                Token::Le => BinOp::Le,
                Token::Ge => BinOp::Ge,
                _ => unreachable!(),
            };
            self.advance();

            let right = Box::new(self.parse_additive()?);
            left = Expr::BinOp {
                op,
                left: Box::new(left),
                right,
            };
        }

        Ok(left)
    }

    fn parse_additive(&mut self) -> Result<Expr, String> {
        let mut left = self.parse_multiplicative()?;

        while matches!(self.current(), Token::Plus | Token::Minus) {
            let op = match self.current() {
                Token::Plus => BinOp::Add,
                Token::Minus => BinOp::Sub,
                _ => unreachable!(),
            };
            self.advance();

            let right = Box::new(self.parse_multiplicative()?);
            left = Expr::BinOp {
                op,
                left: Box::new(left),
                right,
            };
        }

        Ok(left)
    }

    fn parse_multiplicative(&mut self) -> Result<Expr, String> {
        let mut left = self.parse_primary()?;

        while matches!(self.current(), Token::Star | Token::Slash | Token::Percent) {
            let op = match self.current() {
                Token::Star => BinOp::Mul,
                Token::Slash => BinOp::Div,
                Token::Percent => BinOp::Mod,
                _ => unreachable!(),
            };
            self.advance();

            let right = Box::new(self.parse_primary()?);
            left = Expr::BinOp {
                op,
                left: Box::new(left),
                right,
            };
        }

        Ok(left)
    }

    fn parse_primary(&mut self) -> Result<Expr, String> {
        match self.current() {
            Token::IntLit(n) => {
                let val = *n;
                self.advance();
                Ok(Expr::IntLit(val))
            }
            Token::True => {
                self.advance();
                Ok(Expr::BoolLit(true))
            }
            Token::False => {
                self.advance();
                Ok(Expr::BoolLit(false))
            }
            Token::Ident(s) => {
                let name = s.clone();
                self.advance();

                // Check if it's a function call
                if self.current() == &Token::LParen {
                    self.advance();

                    let mut args = Vec::new();
                    while self.current() != &Token::RParen {
                        args.push(self.parse_expr()?);

                        if self.current() == &Token::Comma {
                            self.advance();
                        } else if self.current() != &Token::RParen {
                            return Err("Expected ',' or ')' in function call".to_string());
                        }
                    }
                    self.expect(Token::RParen)?;

                    Ok(Expr::Call { func: name, args })
                } else {
                    Ok(Expr::Var(name))
                }
            }
            Token::LParen => {
                self.advance();
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(expr)
            }
            Token::LBrace => self.parse_block_expr(),
            _ => Err(format!("Unexpected token: {}", self.current())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_function() {
        let input = "fn main() { 42 }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        assert_eq!(program.functions.len(), 1);
        assert_eq!(program.functions[0].name, "main");
    }

    #[test]
    fn test_parse_function_with_params() {
        let input = "fn add(x: i32, y: i32) -> i32 { x + y }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        assert_eq!(program.functions[0].params.len(), 2);
        assert_eq!(program.functions[0].params[0].name, "x");
    }

    #[test]
    fn test_parse_let_binding() {
        let input = "fn main() { let x = 5; x }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        assert_eq!(program.functions.len(), 1);
    }

    #[test]
    fn test_parse_if_expression() {
        let input = "fn main() { if true { 1 } else { 2 } }";
        let mut parser = Parser::new(input);
        let program = parser.parse_program().unwrap();
        assert_eq!(program.functions.len(), 1);
    }
}
