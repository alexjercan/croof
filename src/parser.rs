use std::fmt::Display;

use crate::lexer::{Lexer, SourceMap, Token, TokenKind};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParserError {
    Todo(String),
}

impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParserError::Todo(msg) => write!(f, "TODO: {}", msg),
        }
    }
}

pub struct Parser {
    lexer: Lexer,
    sourcemap: SourceMap,
    token: Token,
    next_token: Token,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeNode {
    pub types: Vec<Token>,
}

impl TypeNode {
    pub fn new(types: Vec<Token>) -> Self {
        TypeNode { types }
    }
}

impl Display for TypeNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.types
                .iter()
                .map(|t| t.value.clone().unwrap())
                .collect::<Vec<String>>()
                .join(" -> ")
        )
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
    pub symbol: Token,
    pub type_node: TypeNode,
}

impl QuantifierNode {
    pub fn new(kind: QuantifierKind, symbol: Token, type_node: TypeNode) -> Self {
        QuantifierNode {
            kind,
            symbol,
            type_node,
        }
    }
}

impl Display for QuantifierNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {} : {}",
            self.kind,
            self.symbol.value.clone().unwrap(),
            self.type_node
        )
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
    pub value: Token,
    pub type_node: Option<TypeNode>,
}

impl NumberNode {
    pub fn new(value: Token) -> Self {
        NumberNode {
            value,
            type_node: None,
        }
    }

    pub fn typed(value: Token, type_node: TypeNode) -> Self {
        NumberNode {
            value,
            type_node: Some(type_node),
        }
    }
}

impl Display for NumberNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value.value.clone().unwrap())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LiteralNode {
    pub value: Token,
    pub type_node: Option<TypeNode>,
}

impl LiteralNode {
    pub fn new(value: Token) -> Self {
        LiteralNode {
            value,
            type_node: None,
        }
    }
}

impl Display for LiteralNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO: just for visuals maybe escape the string
        write!(f, "\"{}\"", self.value.value.clone().unwrap())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariableNode {
    pub name: Token,
    pub type_node: Option<TypeNode>,
}

impl VariableNode {
    pub fn new(name: Token) -> Self {
        VariableNode {
            name,
            type_node: None,
        }
    }
}

impl Display for VariableNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name.value.clone().unwrap())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionNode {
    pub name: Token,
    pub arguments: Vec<ExpressionNode>,
    pub type_node: Option<TypeNode>,
}

impl FunctionNode {
    pub fn new(name: Token, arguments: Vec<ExpressionNode>) -> Self {
        FunctionNode {
            name,
            arguments,
            type_node: None,
        }
    }

    pub fn typed(name: Token, arguments: Vec<ExpressionNode>, type_node: TypeNode) -> Self {
        FunctionNode {
            name,
            arguments,
            type_node: Some(type_node),
        }
    }
}

impl Display for FunctionNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let args: Vec<String> = self.arguments.iter().map(|e| e.to_string()).collect();
        write!(
            f,
            "{}({})",
            self.name.value.clone().unwrap(),
            args.join(", ")
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OperatorNode {
    pub operator: Token,
    pub left: Box<ExpressionNode>,
    pub right: Box<ExpressionNode>,
    pub type_node: Option<TypeNode>,
}

impl OperatorNode {
    pub fn new(operator: Token, left: ExpressionNode, right: ExpressionNode) -> Self {
        OperatorNode {
            operator,
            left: Box::new(left),
            right: Box::new(right),
            type_node: None,
        }
    }
}

impl Display for OperatorNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {} {}",
            self.left,
            self.operator.value.clone().unwrap(),
            self.right
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParenNode {
    pub expression: Box<ExpressionNode>,
    pub type_node: Option<TypeNode>,
}

impl ParenNode {
    pub fn new(expression: ExpressionNode) -> Self {
        ParenNode {
            expression: Box::new(expression),
            type_node: None,
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
    Literal(LiteralNode),
    Variable(VariableNode),
    Function(FunctionNode),
    Operator(OperatorNode),
    Paren(ParenNode),
}

impl ExpressionNode {
    pub fn degree(&self) -> u64 {
        match self {
            ExpressionNode::Set(set_node) => {
                1 + set_node.elements.iter().map(|e| e.degree()).sum::<u64>()
            }
            ExpressionNode::Type(_) => 0,
            ExpressionNode::Number(_) => 0,
            ExpressionNode::Literal(_) => 0,
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

    pub fn token(&self) -> Token {
        match &self {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(node) => node.value.clone(),
            ExpressionNode::Literal(node) => node.value.clone(),
            ExpressionNode::Variable(node) => node.name.clone(),
            ExpressionNode::Function(node) => node.name.clone(),
            ExpressionNode::Operator(node) => node.operator.clone(),
            ExpressionNode::Paren(node) => node.expression.token(),
        }
    }

    pub fn type_node(&self) -> Option<TypeNode> {
        match self {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(node) => node.type_node.clone(),
            ExpressionNode::Literal(node) => node.type_node.clone(),
            ExpressionNode::Variable(node) => node.type_node.clone(),
            ExpressionNode::Function(node) => node.type_node.clone(),
            ExpressionNode::Operator(node) => node.type_node.clone(),
            ExpressionNode::Paren(node) => node.type_node.clone(),
        }
    }

    pub fn distance(&self, _: &Self) -> i32 {
        1
    }
}

impl Display for ExpressionNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExpressionNode::Set(set_node) => write!(f, "{}", set_node),
            ExpressionNode::Type(type_node) => write!(f, "{}", type_node),
            ExpressionNode::Number(number_node) => write!(f, "{}", number_node),
            ExpressionNode::Literal(literal_node) => write!(f, "{}", literal_node),
            ExpressionNode::Variable(variable_node) => write!(f, "{}", variable_node),
            ExpressionNode::Function(function_node) => write!(f, "{}", function_node),
            ExpressionNode::Operator(operator_node) => write!(f, "{}", operator_node),
            ExpressionNode::Paren(paren_node) => write!(f, "{}", paren_node),
        }
    }
}

impl PartialOrd for ExpressionNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ExpressionNode {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelationKind {
    Equality,
    GreaterThan,
}

impl Display for RelationKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RelationKind::Equality => write!(f, "="),
            RelationKind::GreaterThan => write!(f, ">"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelationNode {
    pub kind: RelationKind,
    pub token: Token,
    pub left: ExpressionNode,
    pub right: ExpressionNode,
}

impl RelationNode {
    pub fn new(
        kind: RelationKind,
        token: Token,
        left: ExpressionNode,
        right: ExpressionNode,
    ) -> Self {
        RelationNode {
            kind,
            token,
            left,
            right,
        }
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefineFunctionNode {
    pub symbol: Token,
    pub type_node: TypeNode,
}

impl DefineFunctionNode {
    pub fn new(symbol: Token, type_node: TypeNode) -> Self {
        DefineFunctionNode { symbol, type_node }
    }
}

impl Display for DefineFunctionNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} : {}",
            self.symbol.value.clone().unwrap(),
            self.type_node
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefineOperatorNode {
    pub symbol: Token,
    pub type_node: TypeNode,
}

impl DefineOperatorNode {
    pub fn new(symbol: Token, type_node: TypeNode) -> Self {
        DefineOperatorNode { symbol, type_node }
    }
}

impl Display for DefineOperatorNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} : {}",
            self.symbol.value.clone().unwrap(),
            self.type_node
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefineSetNode {
    pub symbol: Token,
    pub set: SetNode,
}

impl DefineSetNode {
    pub fn new(symbol: Token, set: SetNode) -> Self {
        DefineSetNode { symbol, set }
    }
}

impl Display for DefineSetNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.symbol.value.clone().unwrap(), self.set)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefineNode {
    Function(DefineFunctionNode),
    Operator(DefineOperatorNode),
    Set(DefineSetNode),
}

impl DefineNode {
    pub fn symbol(&self) -> Token {
        match self {
            DefineNode::Function(node) => node.symbol.clone(),
            DefineNode::Operator(node) => node.symbol.clone(),
            DefineNode::Set(node) => node.symbol.clone(),
        }
    }
}

impl Display for DefineNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            DefineNode::Function(node) => write!(f, "{}", node),
            DefineNode::Operator(node) => write!(f, "{}", node),
            DefineNode::Set(node) => write!(f, "{}", node),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ProgramNode {
    pub defines: Vec<DefineNode>,
    pub implications: Vec<ImplicationNode>,
    pub evaluations: Vec<ExpressionNode>,
}

impl ProgramNode {
    pub fn new(
        defines: Vec<DefineNode>,
        implications: Vec<ImplicationNode>,
        evaluations: Vec<ExpressionNode>,
    ) -> Self {
        ProgramNode {
            defines,
            implications,
            evaluations,
        }
    }

    pub fn merge(&mut self, other: ProgramNode) {
        self.defines.extend(other.defines);
        self.implications.extend(other.implications);
        self.evaluations.extend(other.evaluations);
    }
}

impl Display for ProgramNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for define in &self.defines {
            writeln!(f, "def {}", define)?;
        }

        for implication in &self.implications {
            writeln!(f, "{}", implication)?;
        }

        for eval in &self.evaluations {
            writeln!(f, "eval {}", eval)?;
        }

        Ok(())
    }
}

impl Parser {
    pub fn new(lexer: Lexer, sourcemap: &SourceMap) -> Self {
        let mut parser = Parser {
            lexer,
            sourcemap: sourcemap.clone(),
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
                return Err(ParserError::Todo(format!(
                    "{}, Expected type, found {:?}",
                    self.sourcemap.format_pos(&self.token),
                    self.token.kind
                )));
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
            otherwise => {
                return Err(ParserError::Todo(format!(
                    "{}, Expected quantifier (forall or exists), found {:?}",
                    self.sourcemap.format_pos(&self.token),
                    otherwise
                )));
            }
        };
        self.read();

        let symbol = match &self.token.kind {
            TokenKind::Identifier => self.token.clone(),
            TokenKind::Operator => self.token.clone(),
            otherwise => {
                return Err(ParserError::Todo(format!(
                    "{}, Expected identifier after quantifier, found {:?}",
                    self.sourcemap.format_pos(&self.token),
                    otherwise
                )));
            }
        };
        self.read();

        if self.token.kind != TokenKind::Colon {
            return Err(ParserError::Todo(format!(
                "{}, Expected ':' after variable, found {:?}",
                self.sourcemap.format_pos(&self.token),
                self.token.kind
            )));
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
                        return Err(ParserError::Todo(format!(
                            "{}, Expected ',' or '}}', found {:?}",
                            self.sourcemap.format_pos(&self.token),
                            self.token.kind
                        )));
                    }
                }

                Ok(SetNode::new(elements))
            }
            otherwise => Err(ParserError::Todo(format!(
                "{}, Expected set, found {:?}",
                self.sourcemap.format_pos(&self.token),
                otherwise
            ))),
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

                match self.token.kind {
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
                                return Err(ParserError::Todo(format!(
                                    "{}, Expected ',' or ')', found {:?}",
                                    self.sourcemap.format_pos(&self.token),
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
                self.read();
                let expr = self.parse_expression()?;

                if self.token.kind != TokenKind::RParen {
                    return Err(ParserError::Todo(format!(
                        "{}, Expected ')', found {:?}",
                        self.sourcemap.format_pos(&self.token),
                        self.token.kind
                    )));
                }
                self.read();

                ExpressionNode::Paren(ParenNode::new(expr))
            }
            otherwise => {
                return Err(ParserError::Todo(format!(
                    "{}, Expected expression, found {:?}",
                    self.sourcemap.format_pos(&self.token),
                    otherwise
                )));
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
            otherwise => {
                return Err(ParserError::Todo(format!(
                    "{}, Expected '=', found {:?}",
                    self.sourcemap.format_pos(&self.token),
                    otherwise
                )));
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
                    return Err(ParserError::Todo(format!(
                        "{}, Expected ':' after identifier, found {:?}",
                        self.sourcemap.format_pos(&self.token),
                        self.token.kind
                    )));
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
                    return Err(ParserError::Todo(format!(
                        "{}, Expected ':' after operator, found {:?}",
                        self.sourcemap.format_pos(&self.token),
                        self.token.kind
                    )));
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
                    return Err(ParserError::Todo(format!(
                        "{}, Expected '=' after type, found {:?}",
                        self.sourcemap.format_pos(&self.token),
                        self.token.kind
                    )));
                }
                self.read();

                let set = self.parse_set()?;

                Ok(DefineNode::Set(DefineSetNode::new(symbol, set)))
            }
            otherwise => Err(ParserError::Todo(format!(
                "{}, Expected type, identifier or operator, found {:?}",
                self.sourcemap.format_pos(&self.token),
                otherwise
            ))),
        }
    }

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
