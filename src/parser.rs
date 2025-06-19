pub mod prelude {
    pub use super::{Parser, ParserError};
}

use std::fmt::{Debug, Display};

use crate::{
    ast::{
        BindingNode, DefineFunctionNode, DefineNode, DefineOperatorNode, DefineSetNode,
        ExpressionNode, ImplicationNode, LiteralNode, NumberNode, OperatorNode, ParenNode,
        ProgramNode, QuantifierKind, QuantifierNode, RelationKind, RelationNode, SetNode,
        StatementNode, TypeNode,
    },
    lexer::Lexer,
    token::{Token, TokenKind, WithToken},
};

/// Represents a parser error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParserError {
    Expected(String, Token),
}

impl WithToken for ParserError {
    fn token(&self) -> Token {
        match self {
            ParserError::Expected(_, token) => token.clone(),
        }
    }
}

impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParserError::Expected(msg, token) => write!(f, "Expected: {}, found: {}", msg, token),
        }
    }
}

/// Represents a parser that processes tokens from a lexer and builds an abstract syntax tree
/// (AST).
///
/// The parser uses a lexer to tokenize the input and a source map to keep track of the
/// source locations of tokens. It maintains the current token and the next token to facilitate
/// parsing operations.
pub struct Parser {
    lexer: Lexer,
    token: Token,
    next_token: Token,
}

impl Parser {
    /// Creates a new Parser with the given lexer and sourcemap.
    pub fn new(lexer: Lexer) -> Self {
        let mut parser = Parser {
            lexer,
            token: Token::default(),
            next_token: Token::default(),
        };

        parser.read();
        parser.read();

        parser
    }

    fn read(&mut self) -> Token {
        self.token = self.next_token.clone();
        self.next_token = self.lexer.next_token();

        self.token.clone()
    }

    fn parse_type(&mut self) -> Result<TypeNode, ParserError> {
        // type ::= Type ( -> Type )*
        let mut types = Vec::new();

        loop {
            if self.token.kind != TokenKind::Type {
                return Err(ParserError::Expected("type".to_string(), self.token.clone()));
            }
            let type_node = self.token.clone();
            self.read();

            types.push(type_node);

            if self.token.kind == TokenKind::Arrow {
                self.read();
            } else {
                break;
            }
        }

        Ok(TypeNode::new(types))
    }

    fn parse_quantifier(&mut self) -> Result<QuantifierNode, ParserError> {
        // quantifier ::= (forall | exists) variable ':' type
        let kind = match &self.token.kind {
            TokenKind::Forall => QuantifierKind::Forall,
            TokenKind::Exists => QuantifierKind::Exists,
            _ => {
                return Err(ParserError::Expected(
                    "quantifier (forall or exists)".to_string(),
                    self.token.clone(),
                ));
            }
        };
        self.read();

        let symbol = match &self.token.kind {
            TokenKind::Identifier => self.token.clone(),
            TokenKind::Operator => self.token.clone(),
            _ => {
                return Err(ParserError::Expected(
                    "identifier or operator after quantifier".to_string(),
                    self.token.clone(),
                ));
            }
        };
        self.read();

        if self.token.kind != TokenKind::Colon {
            return Err(ParserError::Expected(
                "':' after variable".to_string(),
                self.token.clone(),
            ));
        }
        self.read();

        let type_node = self.parse_type()?;

        Ok(QuantifierNode::new(kind, symbol, type_node))
    }

    fn parse_set(&mut self) -> Result<SetNode, ParserError> {
        match &self.token.kind {
            TokenKind::LBrace => {
                self.read();

                let mut elements = Vec::new();
                loop {
                    if self.token.kind == TokenKind::RBrace {
                        self.read();
                        break;
                    }

                    let element = self.parse_expression()?;
                    elements.push(element);

                    if self.token.kind == TokenKind::Comma {
                        self.read();
                    } else if self.token.kind == TokenKind::RBrace {
                        self.read();
                        break;
                    } else {
                        return Err(ParserError::Expected(
                            "',' or right '}'".to_string(),
                            self.token.clone(),
                        ));
                    }
                }

                Ok(SetNode::new(elements))
            }
            _ => Err(ParserError::Expected("set".to_string(), self.token.clone())),
        }
    }

    fn parse_expression(&mut self) -> Result<ExpressionNode, ParserError> {
        let expr = match &self.token.kind {
            TokenKind::Type => self.parse_type().map(ExpressionNode::Type)?,
            TokenKind::LBrace => self.parse_set().map(ExpressionNode::Set)?,
            TokenKind::Number => {
                let value = self.token.clone();
                self.read();

                ExpressionNode::Number(NumberNode::new(value))
            }
            TokenKind::Literal => {
                let value = self.token.clone();
                self.read();

                ExpressionNode::Literal(LiteralNode::new(value))
            }
            TokenKind::Identifier => {
                let name = self.token.clone();
                self.read();

                let args = match self.token.kind {
                    TokenKind::LParen => {
                        self.read();

                        let mut arguments = Vec::new();
                        loop {
                            let argument = self.parse_expression()?;
                            arguments.push(argument);

                            if self.token.kind == TokenKind::RParen {
                                self.read();
                                break;
                            } else if self.token.kind == TokenKind::Comma {
                                self.read();
                            } else {
                                return Err(ParserError::Expected(
                                    "',' or ')'".to_string(),
                                    self.token.clone(),
                                ));
                            }
                        }
                        arguments
                    }
                    _ => vec![],
                };

                ExpressionNode::Binding(BindingNode::new(name, args))
            }
            TokenKind::LParen => {
                self.read();
                let expr = self.parse_expression()?;

                if self.token.kind != TokenKind::RParen {
                    return Err(ParserError::Expected(
                        "')'".to_string(),
                        self.token.clone(),
                    ));
                }
                self.read();

                ExpressionNode::Paren(ParenNode::new(expr))
            }
            _ => {
                return Err(ParserError::Expected(
                    "expression".to_string(),
                    self.token.clone(),
                ));
            }
        };

        let expr = match self.token.kind {
            TokenKind::Operator => {
                let operator = self.token.clone();
                self.read();

                let right_expr = self.parse_expression()?;

                ExpressionNode::Operator(OperatorNode::new(operator, expr, right_expr))
            }
            _ => expr,
        };

        Ok(expr)
    }

    fn parse_relation(&mut self) -> Result<RelationNode, ParserError> {
        // relation ::= expression = expression
        let lhs = self.parse_expression()?;

        let token = self.token.clone();
        let kind = match token.kind {
            TokenKind::Equal => {
                self.read();
                RelationKind::Equality
            }
            TokenKind::GreaterThan => {
                self.read();
                RelationKind::GreaterThan
            }
            _ => {
                return Err(ParserError::Expected(
                    "relation operator (e.g., '=', '>', etc.)".to_string(),
                    token,
                ));
            }
        };

        let rhs = self.parse_expression()?;

        Ok(RelationNode::new(kind, token, lhs, rhs))
    }

    fn parse_statement(&mut self) -> Result<StatementNode, ParserError> {
        match self.token.kind {
            TokenKind::Forall | TokenKind::Exists => {
                self.parse_quantifier().map(StatementNode::Quantifier)
            }
            _ => self.parse_relation().map(StatementNode::Relation),
        }
    }

    fn parse_implication(&mut self) -> Result<ImplicationNode, ParserError> {
        // implication ::= [[statment]+ =>]? [statement]+

        let mut statements = Vec::new();
        let is_conditions = loop {
            let statement = self.parse_statement()?;
            statements.push(statement);

            match self.token.kind {
                TokenKind::Then => {
                    self.read();
                    break true;
                }
                TokenKind::Comma => {
                    self.read();
                }
                _ => {
                    break false;
                }
            }
        };

        if !is_conditions {
            return Ok(ImplicationNode::new(Vec::new(), statements));
        }

        let conditions = statements;
        let mut conclusion = Vec::new();

        loop {
            let statement = self.parse_statement()?;
            conclusion.push(statement);

            match self.token.kind {
                TokenKind::Comma => {
                    self.read();
                }
                _ => {
                    break;
                }
            }
        }

        Ok(ImplicationNode::new(conditions, conclusion))
    }

    fn parse_define(&mut self) -> Result<DefineNode, ParserError> {
        match &self.token.kind {
            TokenKind::Identifier => {
                let symbol = self.token.clone();
                self.read();

                if self.token.kind != TokenKind::Colon {
                    return Err(ParserError::Expected(
                        "':' after identifier".to_string(),
                        self.token.clone(),
                    ));
                }
                self.read();

                let type_node = self.parse_type()?;

                Ok(DefineNode::Function(DefineFunctionNode::new(
                    symbol, type_node,
                )))
            }
            TokenKind::Operator => {
                let symbol = self.token.clone();
                self.read();

                if self.token.kind != TokenKind::Colon {
                    return Err(ParserError::Expected(
                        "':' after operator".to_string(),
                        self.token.clone(),
                    ));
                }
                self.read();

                let type_node = self.parse_type()?;

                Ok(DefineNode::Operator(DefineOperatorNode::new(
                    symbol, type_node,
                )))
            }
            TokenKind::Type => {
                let symbol = self.token.clone();
                self.read();

                if self.token.kind != TokenKind::Equal {
                    return Err(ParserError::Expected(
                        "'=' after type".to_string(),
                        self.token.clone(),
                    ));
                }
                self.read();

                let set = self.parse_set()?;

                Ok(DefineNode::Set(DefineSetNode::new(symbol, set)))
            }
            _ => Err(ParserError::Expected(
                "type, identifier or operator".to_string(),
                self.token.clone(),
            )),
        }
    }

    /// Parses the entire program and returns a `ProgramNode`.
    ///
    /// # Returns
    /// A `Result<ProgramNode, ParserError>` which contains the parsed program node if successful,
    /// or a `ParserError` if an error occurred during parsing.
    ///
    /// # Note
    /// This function will read tokens from the lexer until it reaches the end of the file (EOF).
    /// It will parse definitions, implications, and evaluations in the order they appear in the
    /// source code.
    pub fn parse(&mut self) -> Result<ProgramNode, ParserError> {
        let mut defines = Vec::new();
        let mut implications = Vec::new();
        let mut evaluations = Vec::new();

        loop {
            match self.token.kind {
                TokenKind::Eof => break,
                TokenKind::Eval => {
                    self.read();
                    let expr = self.parse_expression()?;

                    evaluations.push(expr);
                }
                TokenKind::Def => {
                    self.read();
                    let define = self.parse_define()?;

                    defines.push(define);
                }
                _ => {
                    let value = self.parse_implication()?;

                    implications.push(value);
                }
            }
        }

        Ok(ProgramNode::new(defines, implications, evaluations))
    }
}
