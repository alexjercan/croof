use std::fmt::Display;

use crate::lexer::{Lexer, Token, TokenKind};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParserError {
    Todo(String),
}

pub struct Parser {
    lexer: Lexer,
    token: Token,
    next_token: Token,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeNode {
    pub types: Vec<String>,
}

impl TypeNode {
    pub fn new<S>(types: Vec<S>) -> Self
    where
        S: Into<String>,
    {
        TypeNode {
            types: types.into_iter().map(|s| s.into()).collect(),
        }
    }
}

impl Display for TypeNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.types.join(" -> "))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum QuantifierKind {
    Forall,
    Exists,
}

impl Display for QuantifierKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuantifierKind::Forall => write!(f, "forall"),
            QuantifierKind::Exists => write!(f, "exists"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QuantifierNode {
    pub kind: QuantifierKind,
    pub variable: VariableNode,
    pub type_node: TypeNode,
}

impl QuantifierNode {
    pub fn new(kind: QuantifierKind, variable: VariableNode, type_node: TypeNode) -> Self {
        QuantifierNode {
            kind,
            variable,
            type_node,
        }
    }
}

impl Display for QuantifierNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} : {}", self.kind, self.variable, self.type_node)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SetNode {
    pub elements: Vec<ExpressionNode>,
}

impl SetNode {
    pub fn new(elements: Vec<ExpressionNode>) -> Self {
        SetNode { elements }
    }
}

impl Display for SetNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let elements: Vec<String> = self.elements.iter().map(|e| e.to_string()).collect();
        write!(f, "{{{}}}", elements.join(", "))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NumberNode {
    pub value: String,
}

impl NumberNode {
    pub fn new<S>(value: S) -> Self
    where
        S: Into<String>,
    {
        NumberNode {
            value: value.into(),
        }
    }
}

impl Display for NumberNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariableNode {
    pub name: String,
}

impl VariableNode {
    pub fn new<S>(name: S) -> Self
    where
        S: Into<String>,
    {
        VariableNode { name: name.into() }
    }
}

impl Display for VariableNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionNode {
    pub name: String,
    pub arguments: Vec<ExpressionNode>,
}

impl FunctionNode {
    pub fn new<S>(name: S, arguments: Vec<ExpressionNode>) -> Self
    where
        S: Into<String>,
    {
        FunctionNode {
            name: name.into(),
            arguments,
        }
    }
}

impl Display for FunctionNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let args: Vec<String> = self.arguments.iter().map(|e| e.to_string()).collect();
        write!(f, "{}({})", self.name, args.join(", "))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OperatorNode {
    pub operator: String,
    pub left: Box<ExpressionNode>,
    pub right: Box<ExpressionNode>,
}

impl OperatorNode {
    pub fn new<S>(operator: S, left: ExpressionNode, right: ExpressionNode) -> Self
    where
        S: Into<String>,
    {
        OperatorNode {
            operator: operator.into(),
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Display for OperatorNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {}", self.left, self.operator, self.right)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParenNode {
    pub expression: Box<ExpressionNode>,
}

impl ParenNode {
    pub fn new(expression: ExpressionNode) -> Self {
        ParenNode {
            expression: Box::new(expression),
        }
    }
}

impl Display for ParenNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})", self.expression)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExpressionNode {
    Set(SetNode),
    Type(TypeNode),
    Number(NumberNode),
    Variable(VariableNode),
    Function(FunctionNode),
    Operator(OperatorNode),
    Paren(ParenNode),
}

impl Display for ExpressionNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExpressionNode::Set(set_node) => write!(f, "{}", set_node),
            ExpressionNode::Type(type_node) => write!(f, "{}", type_node),
            ExpressionNode::Number(number_node) => write!(f, "{}", number_node),
            ExpressionNode::Variable(variable_node) => write!(f, "{}", variable_node),
            ExpressionNode::Function(function_node) => write!(f, "{}", function_node),
            ExpressionNode::Operator(operator_node) => write!(f, "{}", operator_node),
            ExpressionNode::Paren(paren_node) => write!(f, "{}", paren_node),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelationKind {
    Equality,
}

impl Display for RelationKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RelationKind::Equality => write!(f, "="),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelationNode {
    pub kind: RelationKind,
    pub left: ExpressionNode,
    pub right: ExpressionNode,
}

impl RelationNode {
    pub fn new(kind: RelationKind, left: ExpressionNode, right: ExpressionNode) -> Self {
        RelationNode { kind, left, right }
    }
}

impl Display for RelationNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {}", self.left, self.kind, self.right)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatementNode {
    Quantifier(QuantifierNode),
    Relation(RelationNode),
}
impl Display for StatementNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StatementNode::Quantifier(quantifier) => write!(f, "{}", quantifier),
            StatementNode::Relation(relation) => write!(f, "{}", relation),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImplicationNode {
    pub conditions: Vec<StatementNode>,
    pub conclusion: Vec<StatementNode>,
}

impl ImplicationNode {
    pub fn new(conditions: Vec<StatementNode>, conclusion: Vec<StatementNode>) -> Self {
        ImplicationNode {
            conditions,
            conclusion,
        }
    }
}

impl Display for ImplicationNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let conditions: Vec<String> = self.conditions.iter().map(|s| s.to_string()).collect();
        let conclusion: Vec<String> = self.conclusion.iter().map(|s| s.to_string()).collect();
        if !conditions.is_empty() {
            write!(f, "{} => ", conditions.join(", "))?;
        }

        write!(f, "{}", conclusion.join(", "))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ProgramNode {
    pub implications: Vec<ImplicationNode>,
    pub evaluations: Vec<ExpressionNode>,
}

impl ProgramNode {
    pub fn new(implications: Vec<ImplicationNode>, evaluations: Vec<ExpressionNode>) -> Self {
        ProgramNode {
            implications,
            evaluations,
        }
    }
}

impl ExpressionNode {
    pub fn degree(&self) -> u64 {
        match self {
            ExpressionNode::Set(set_node) => {
                1 + set_node.elements.iter().map(|e| e.degree()).sum::<u64>()
            }
            ExpressionNode::Type(_) => 0,
            ExpressionNode::Number(_) => 0,
            ExpressionNode::Variable(_) => 1,
            ExpressionNode::Function(function_node) => {
                1 + function_node
                    .arguments
                    .iter()
                    .map(|e| e.degree())
                    .sum::<u64>()
            }
            ExpressionNode::Operator(operator_node) => {
                1 + operator_node.left.degree() + operator_node.right.degree()
            }
            ExpressionNode::Paren(paren_node) => 1 + paren_node.expression.degree(),
        }
    }
}

impl ProgramNode {
    pub fn merge(&mut self, other: ProgramNode) {
        self.implications.extend(other.implications);
        self.evaluations.extend(other.evaluations);
    }
}

impl Parser {
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
        self.next_token = self.lexer.next();

        self.token.clone()
    }

    fn parse_type(&mut self) -> Result<TypeNode, ParserError> {
        // type ::= Type ( -> Type )*
        let mut types = Vec::new();

        loop {
            if self.token.kind != TokenKind::Type {
                return Err(ParserError::Todo(format!(
                    "{}, Expected type, found {:?}",
                    self.lexer.format_pos(self.token.pos),
                    self.token.kind
                )));
            }
            let type_value = self.token.value.clone().unwrap();
            self.read(); // consume the type token

            types.push(type_value);

            if self.token.kind == TokenKind::Arrow {
                self.read(); // consume the arrow token
            } else {
                break; // no more types, exit the loop
            }
        }

        Ok(TypeNode::new(types))
    }

    fn parse_quantifier(&mut self) -> Result<QuantifierNode, ParserError> {
        // quantifier ::= (forall | exists) variable ':' type
        let kind = match &self.token.kind {
            TokenKind::Forall => QuantifierKind::Forall,
            TokenKind::Exists => QuantifierKind::Exists,
            otherwise => {
                return Err(ParserError::Todo(format!(
                    "{}, Expected quantifier (forall or exists), found {:?}",
                    self.lexer.format_pos(self.token.pos),
                    otherwise
                )));
            }
        };
        self.read(); // consume the quantifier token

        if self.token.kind != TokenKind::Identifier {
            return Err(ParserError::Todo(format!(
                "{}, Expected variable after quantifier, found {:?}",
                self.lexer.format_pos(self.token.pos),
                self.token.kind
            )));
        }
        let variable = self.token.value.clone().unwrap();
        self.read(); // consume the variable token

        if self.token.kind != TokenKind::Colon {
            return Err(ParserError::Todo(format!(
                "{}, Expected ':' after variable, found {:?}",
                self.lexer.format_pos(self.token.pos),
                self.token.kind
            )));
        }
        self.read(); // consume the colon token

        let type_node = self.parse_type()?;

        Ok(QuantifierNode::new(
            kind,
            VariableNode::new(variable),
            type_node,
        ))
    }

    fn parse_expression(&mut self) -> Result<ExpressionNode, ParserError> {
        let expr = match &self.token.kind {
            TokenKind::Type => {
                let type_node = self.parse_type()?;
                self.read(); // consume the type token

                ExpressionNode::Type(type_node)
            }
            TokenKind::LBrace => {
                self.read(); // consume the left brace token

                let mut elements = Vec::new();
                loop {
                    if self.token.kind == TokenKind::RBrace {
                        self.read(); // consume the right brace token
                        break; // end of set elements
                    }

                    let element = self.parse_expression()?;
                    elements.push(element);

                    if self.token.kind == TokenKind::Comma {
                        self.read(); // consume the comma token
                    } else if self.token.kind == TokenKind::RBrace {
                        self.read(); // consume the right brace token
                        break; // end of set elements
                    } else {
                        return Err(ParserError::Todo(format!(
                            "{}, Expected ',' or '}}', found {:?}",
                            self.lexer.format_pos(self.token.pos),
                            self.token.kind
                        )));
                    }
                }

                ExpressionNode::Set(SetNode::new(elements))
            }
            TokenKind::Number => {
                let value = self.token.value.clone().unwrap();
                self.read(); // consume the number token

                ExpressionNode::Number(NumberNode::new(value))
            }
            TokenKind::Identifier => {
                let name = self.token.value.clone().unwrap();
                self.read(); // consume the identifier token

                match self.token.kind {
                    TokenKind::LParen => {
                        self.read(); // consume the left parenthesis token

                        let mut arguments = Vec::new();
                        loop {
                            let argument = self.parse_expression()?;
                            arguments.push(argument);

                            if self.token.kind == TokenKind::RParen {
                                self.read(); // consume the right parenthesis token
                                break; // end of function arguments
                            } else if self.token.kind == TokenKind::Comma {
                                self.read(); // consume the comma token
                            } else {
                                return Err(ParserError::Todo(format!(
                                    "{}, Expected ',' or ')', found {:?}",
                                    self.lexer.format_pos(self.token.pos),
                                    self.token.kind
                                )));
                            }
                        }

                        ExpressionNode::Function(FunctionNode::new(name, arguments))
                    }
                    _ => ExpressionNode::Variable(VariableNode::new(name)),
                }
            }
            TokenKind::LParen => {
                self.read(); // consume the left parenthesis token
                let expr = self.parse_expression()?;

                if self.token.kind != TokenKind::RParen {
                    return Err(ParserError::Todo(format!(
                        "{}, Expected ')', found {:?}",
                        self.lexer.format_pos(self.token.pos),
                        self.token.kind
                    )));
                }
                self.read(); // consume the right parenthesis token

                ExpressionNode::Paren(ParenNode::new(expr))
            }
            otherwise => {
                return Err(ParserError::Todo(format!(
                    "{}, Expected expression, found {:?}",
                    self.lexer.format_pos(self.token.pos),
                    otherwise
                )));
            }
        };

        let expr = match self.token.kind {
            TokenKind::Operator => {
                let operator = self.token.value.clone().unwrap();
                self.read(); // consume the operator token

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

        let kind = match &self.token.kind {
            TokenKind::Equal => {
                self.read(); // consume the equal token
                RelationKind::Equality
            }
            otherwise => {
                return Err(ParserError::Todo(format!(
                    "{}, Expected '=', found {:?}",
                    self.lexer.format_pos(self.token.pos),
                    otherwise
                )));
            }
        };

        let rhs = self.parse_expression()?;

        Ok(RelationNode::new(kind, lhs, rhs))
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
                    self.read(); // consume the arrow token
                    break true; // if we have an arrow, we are in the conditions part
                }
                TokenKind::Comma => {
                    self.read(); // consume the comma token
                }
                _ => {
                    break false; // if we don't have an arrow, we are in the conclusion part
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
                    self.read(); // consume the comma token
                }
                _ => {
                    break; // if we don't have an arrow, we are in the conclusion part
                }
            }
        }

        Ok(ImplicationNode::new(conditions, conclusion))
    }

    pub fn parse(&mut self) -> Result<ProgramNode, ParserError> {
        let mut implications = Vec::new();
        let mut evaluations = Vec::new();

        loop {
            match self.token.kind {
                TokenKind::Eof => break,
                TokenKind::Eval => {
                    self.read(); // consume the eval token
                    let expr = self.parse_expression()?;

                    evaluations.push(expr);
                }
                _ => {
                    let value = self.parse_implication()?;

                    implications.push(value);
                }
            }
        }

        Ok(ProgramNode::new(implications, evaluations))
    }
}
