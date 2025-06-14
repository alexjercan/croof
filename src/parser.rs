use std::collections::HashMap;
use std::fmt::Debug;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::lexer::{Lexer, SourceMap, Token, TokenKind};
use crate::typechecker::can_infer_type;

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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
                .map(|t| t.value())
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
            self.symbol.value(),
            self.type_node
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    pub node_type: Option<Vec<String>>,
}

impl NumberNode {
    pub fn new(value: Token) -> Self {
        NumberNode {
            value,
            node_type: None,
        }
    }

    pub fn with_type<S>(value: Token, node_type: S) -> Self
    where
        S: Into<String>,
    {
        NumberNode {
            value,
            node_type: Some(vec![node_type.into()]),
        }
    }
}

impl PartialOrd for NumberNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NumberNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let type_node = self.node_type.as_ref().unwrap().first().unwrap().clone();
        let type_other = other.node_type.as_ref().unwrap().first().unwrap().clone();

        if type_node == type_other {
            let number_node = self.value.value().parse::<i64>().unwrap();
            let other_node = other.value.value().parse::<i64>().unwrap();

            return number_node.cmp(&other_node);
        }

        type_node.cmp(&type_other)
    }
}

impl Display for NumberNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // match &self.node_type {
        //     Some(node_type) => write!(f, "{} : {}", self.value.value(), node_type.join(" -> ")),
        //     None => write!(f, "{}", self.value.value()),
        // }

        write!(f, "{}", self.value.value())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LiteralNode {
    pub value: Token,
    pub node_type: Option<Vec<String>>,
}

impl LiteralNode {
    pub fn new(value: Token) -> Self {
        LiteralNode {
            value,
            node_type: None,
        }
    }

    pub fn with_type<S>(value: Token, type_node: S) -> Self
    where
        S: Into<String>,
    {
        LiteralNode {
            value,
            node_type: Some(vec![type_node.into()]),
        }
    }
}

impl PartialOrd for LiteralNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LiteralNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let type_node = self.node_type.as_ref().unwrap().first().unwrap().clone();
        let type_other = other.node_type.as_ref().unwrap().first().unwrap().clone();

        if type_node == type_other {
            return self.value.value().cmp(&other.value.value());
        }

        type_node.cmp(&type_other)
    }
}

impl Display for LiteralNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // match &self.node_type {
        //     Some(node_type) => write!(f, "\"{}\" : {}", self.value.value(), node_type.join(" -> ")),
        //     None => write!(f, "\"{}\"", self.value.value()),
        // }

        write!(f, "\"{}\"", self.value.value())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BindingNode {
    pub name: Token,
    pub arguments: Vec<ExpressionNode>,
    pub node_type: Option<Vec<String>>,
}

impl BindingNode {
    pub fn new(name: Token, arguments: Vec<ExpressionNode>) -> Self {
        BindingNode {
            name,
            arguments,
            node_type: None,
        }
    }

    pub fn with_type<S>(name: Token, arguments: Vec<ExpressionNode>, node_type: Vec<S>) -> Self
    where
        S: Into<String>,
    {
        BindingNode {
            name,
            arguments,
            node_type: Some(node_type.into_iter().map(Into::into).collect()),
        }
    }
}

impl PartialOrd for BindingNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BindingNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let type_node = self.node_type.as_ref().unwrap().first().unwrap().clone();
        let type_other = other.node_type.as_ref().unwrap().first().unwrap().clone();

        if type_node == type_other {
            return self.name.value().cmp(&other.name.value());
        }

        type_node.cmp(&type_other)
    }
}

impl Display for BindingNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let args: Vec<String> = self.arguments.iter().map(|e| e.to_string()).collect();

        write!(f, "{}", self.name.value())?;
        if !args.is_empty() {
            write!(f, "({})", args.join(", "))?;
        }

        // match &self.node_type {
        //     Some(node_type) => write!(f, " : {}", node_type.join(" -> ")),
        //     None => Ok(()),
        // }

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OperatorNode {
    pub operator: Token,
    pub left: Box<ExpressionNode>,
    pub right: Box<ExpressionNode>,
    pub node_type: Option<Vec<String>>,
}

impl OperatorNode {
    pub fn new(operator: Token, left: ExpressionNode, right: ExpressionNode) -> Self {
        OperatorNode {
            operator,
            left: Box::new(left),
            right: Box::new(right),
            node_type: None,
        }
    }

    pub fn with_type<S>(
        operator: Token,
        left: ExpressionNode,
        right: ExpressionNode,
        node_type: Vec<S>,
    ) -> Self
    where
        S: Into<String>,
    {
        OperatorNode {
            operator,
            left: Box::new(left),
            right: Box::new(right),
            node_type: Some(node_type.into_iter().map(Into::into).collect()),
        }
    }
}

impl PartialOrd for OperatorNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OperatorNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let type_node = self.node_type.as_ref().unwrap().first().unwrap().clone();
        let type_other = other.node_type.as_ref().unwrap().first().unwrap().clone();

        if type_node == type_other {
            return self.operator.value().cmp(&other.operator.value());
        }

        type_node.cmp(&type_other)
    }
}

impl Display for OperatorNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // match &self.node_type {
        //     Some(node_type) => write!(
        //         f,
        //         "{} {} {} : {}",
        //         self.left, self.operator.value(), self.right, node_type.join(" -> ")
        //     ),
        //     None => write!(f, "{} {} {}", self.left, self.operator.value(), self.right),
        // }

        write!(f, "{} {} {}", self.left, self.operator.value(), self.right)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParenNode {
    pub expression: Box<ExpressionNode>,
    pub node_type: Option<Vec<String>>,
}

impl ParenNode {
    pub fn new(expression: ExpressionNode) -> Self {
        ParenNode {
            expression: Box::new(expression),
            node_type: None,
        }
    }

    pub fn with_type<S>(expression: ExpressionNode, node_type: Vec<S>) -> Self
    where
        S: Into<String>,
    {
        ParenNode {
            expression: Box::new(expression),
            node_type: Some(node_type.into_iter().map(Into::into).collect()),
        }
    }
}

impl PartialOrd for ParenNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ParenNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let type_node = self.node_type.as_ref().unwrap().first().unwrap().clone();
        let type_other = other.node_type.as_ref().unwrap().first().unwrap().clone();

        if type_node == type_other {
            return self.expression.cmp(&other.expression);
        }

        type_node.cmp(&type_other)
    }
}

impl Display for ParenNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // match &self.node_type {
        //     Some(node_type) => write!(
        //         f,
        //         "({}) : {}",
        //         self.expression, node_type.join(" -> ")
        //     ),
        //     None => write!(f, "({})", self.expression),
        // }

        write!(f, "({})", self.expression)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExpressionNode {
    Set(SetNode),
    Type(TypeNode),
    Number(NumberNode),
    Literal(LiteralNode),
    Binding(BindingNode),
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
            ExpressionNode::Binding(node) => {
                1 + node.arguments.iter().map(|e| e.degree()).sum::<u64>()
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
            ExpressionNode::Binding(node) => node.name.clone(),
            ExpressionNode::Operator(node) => node.operator.clone(),
            ExpressionNode::Paren(node) => node.expression.token(),
        }
    }

    pub fn node_type(&self) -> Option<Vec<String>> {
        match self {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(node) => node.node_type.clone(),
            ExpressionNode::Literal(node) => node.node_type.clone(),
            ExpressionNode::Binding(node) => node.node_type.clone(),
            ExpressionNode::Operator(node) => node.node_type.clone(),
            ExpressionNode::Paren(node) => node.node_type.clone(),
        }
    }

    pub fn distance(&self, _: &Self) -> i32 {
        1
    }

    pub fn apply(
        &self,
        mapping: &HashMap<ExpressionNode, ExpressionNode>,
    ) -> Option<ExpressionNode> {
        match self {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(_) => Some(self.clone()),
            ExpressionNode::Literal(_) => Some(self.clone()),
            ExpressionNode::Binding(node) => {
                // TODO: Can we do this better?
                if node.arguments.is_empty() {
                    return mapping.get(self).cloned();
                }

                let args = node
                    .arguments
                    .iter()
                    .map(|arg| arg.apply(mapping))
                    .collect::<Option<Vec<ExpressionNode>>>()?;

                let mut func_type = args
                    .iter()
                    .filter_map(|arg| arg.node_type())
                    .flatten()
                    .collect::<Vec<String>>();
                let return_type = node.clone().node_type?;
                func_type.extend(return_type.iter().cloned());

                let expr = ExpressionNode::Binding(BindingNode::with_type(
                    Token::with_value(TokenKind::Identifier, node.name.value()),
                    vec![],
                    func_type,
                ));

                let mut function_node = node.clone();
                function_node.arguments = args;
                function_node.name = mapping
                    .get(&expr)
                    .cloned()
                    .unwrap_or(ExpressionNode::Binding(function_node.clone()))
                    .token();

                Some(ExpressionNode::Binding(function_node))
            }
            ExpressionNode::Operator(node) => {
                let left = node.left.apply(mapping)?;
                let right = node.right.apply(mapping)?;

                let mut operator_node = node.clone();
                operator_node.left = Box::new(left);
                operator_node.right = Box::new(right);

                Some(ExpressionNode::Operator(operator_node))
            }
            ExpressionNode::Paren(node) => {
                let expr = node.expression.apply(mapping)?;
                let mut paren_node = node.clone();
                paren_node.expression = Box::new(expr);

                Some(ExpressionNode::Paren(paren_node))
            }
        }
    }

    fn create_mapping_helper(
        &self,
        to: &ExpressionNode,
        mapping: &mut HashMap<ExpressionNode, ExpressionNode>,
    ) -> bool {
        let Some(from_type) = self.node_type() else {
            return false;
        };
        let Some(to_type) = to.node_type() else {
            return false;
        };
        if !can_infer_type(&from_type, &to_type) {
            return false;
        }

        match to {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(to_node) => match self {
                ExpressionNode::Number(from_node) => to_node.value == from_node.value,
                _ => false,
            },
            ExpressionNode::Literal(to_node) => match self {
                ExpressionNode::Literal(from_node) => to_node.value == from_node.value,
                _ => false,
            },
            ExpressionNode::Binding(to_node) => {
                if to_node.arguments.is_empty() {
                    let has_mapping = mapping.contains_key(to);
                    let should_substitute = !has_mapping || mapping.get(to) == Some(self);

                    if !has_mapping {
                        mapping.insert(to.clone(), self.clone());
                    }

                    return should_substitute;
                }

                match self {
                    ExpressionNode::Binding(from_node) => {
                        to_node.name == from_node.name
                            && to_node.arguments.len() == from_node.arguments.len()
                            && to_node.arguments.iter().zip(&from_node.arguments).all(
                                |(to_arg, from_arg)| {
                                    from_arg.create_mapping_helper(to_arg, mapping)
                                },
                            )
                    }
                    _ => false,
                }
            }
            ExpressionNode::Operator(to_node) => match self {
                ExpressionNode::Operator(operator_node) => {
                    to_node.operator == operator_node.operator
                        && operator_node
                            .left
                            .create_mapping_helper(&to_node.left, mapping)
                        && operator_node
                            .right
                            .create_mapping_helper(&to_node.right, mapping)
                }
                _ => false,
            },
            ExpressionNode::Paren(to_node) => match self {
                ExpressionNode::Paren(paren_node) => paren_node
                    .expression
                    .create_mapping_helper(&to_node.expression, mapping),
                _ => false,
            },
        }
    }

    pub fn create_mapping(
        &self,
        expr: &ExpressionNode,
    ) -> Option<HashMap<ExpressionNode, ExpressionNode>> {
        let mut mapping = HashMap::new();
        if self.create_mapping_helper(expr, &mut mapping) {
            Some(mapping)
        } else {
            None
        }
    }
}

impl Display for ExpressionNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExpressionNode::Set(node) => write!(f, "{}", node),
            ExpressionNode::Type(node) => write!(f, "{}", node),
            ExpressionNode::Number(node) => write!(f, "{}", node),
            ExpressionNode::Literal(node) => write!(f, "{}", node),
            ExpressionNode::Binding(node) => write!(f, "{}", node),
            ExpressionNode::Operator(node) => write!(f, "{}", node),
            ExpressionNode::Paren(node) => write!(f, "{}", node),
        }
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

pub type SubstituteFn = Arc<dyn Fn(&ExpressionNode) -> Option<ExpressionNode> + Send + Sync>;

#[derive(Clone)]
pub struct BuiltinNode {
    pub display: String,
    pub substitute_fn: SubstituteFn,
}

impl Debug for BuiltinNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BuiltinNode({})", self.display)
    }
}

impl PartialEq for BuiltinNode {
    fn eq(&self, other: &Self) -> bool {
        self.display == other.display
    }
}

impl Eq for BuiltinNode {}

impl BuiltinNode {
    pub fn new<S, F>(display: S, substitute_fn: F) -> Self
    where
        S: Into<String>,
        F: 'static + Fn(&ExpressionNode) -> Option<ExpressionNode> + Send + Sync,
    {
        BuiltinNode {
            display: display.into(),
            substitute_fn: Arc::new(substitute_fn),
        }
    }

    pub fn apply(&self, expr: &ExpressionNode) -> Option<ExpressionNode> {
        (self.substitute_fn)(expr)
    }
}

impl Display for BuiltinNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatementNode {
    Quantifier(QuantifierNode),
    Relation(RelationNode),
    Builtin(BuiltinNode),
}

impl StatementNode {
    pub fn create_mapping(
        &self,
        expr: &ExpressionNode,
    ) -> Option<HashMap<ExpressionNode, ExpressionNode>> {
        match self {
            StatementNode::Quantifier(_) => todo!("Implement mapping for QuantifierNode"),
            StatementNode::Relation(node) => expr.create_mapping(&node.left),
            StatementNode::Builtin(_) => Some(HashMap::new()),
        }
    }

    pub fn apply(
        &self,
        expression: &ExpressionNode,
        mapping: &HashMap<ExpressionNode, ExpressionNode>,
    ) -> Option<ExpressionNode> {
        match self {
            StatementNode::Quantifier(_) => todo!("Implement apply for QuantifierNode"),
            StatementNode::Relation(node) => node.right.apply(mapping),
            StatementNode::Builtin(node) => node.apply(expression),
        }
    }
}

impl Display for StatementNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StatementNode::Quantifier(quantifier) => write!(f, "{}", quantifier),
            StatementNode::Relation(relation) => write!(f, "{}", relation),
            StatementNode::Builtin(builtin) => write!(f, "{}", builtin),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
        write!(f, "{} : {}", self.symbol.value(), self.type_node)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
        write!(f, "{} : {}", self.symbol.value(), self.type_node)
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

    pub fn name(symbol: Token) -> Self {
        DefineSetNode::new(symbol, SetNode::new(vec![]))
    }
}

impl Hash for DefineSetNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.symbol.hash(state);
    }
}

impl Display for DefineSetNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.symbol.value(), self.set)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
                                return Err(ParserError::Todo(format!(
                                    "{}, Expected ',' or ')', found {:?}",
                                    self.sourcemap.format_pos(&self.token),
                                    self.token.kind
                                )));
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

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use crate::{
        lexer::{Token, TokenKind},
        parser::{BindingNode, ExpressionNode, NumberNode, OperatorNode, ParenNode},
        typechecker::TYPE_N,
    };

    #[test]
    fn test_create_mapping_number_number() {
        // Arrange
        let from = ExpressionNode::Number(NumberNode::with_type(
            Token::with_value(TokenKind::Number, "42"),
            TYPE_N,
        ));
        let to = ExpressionNode::Number(NumberNode::with_type(
            Token::with_value(TokenKind::Number, "42"),
            TYPE_N,
        ));

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping.len(), 0);
    }

    #[test]
    fn test_create_mapping_variable_number() {
        // Arrange
        let from = ExpressionNode::Binding(BindingNode::new(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
        ));
        let to =
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")));

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_function_number() {
        // Arrange
        let from = ExpressionNode::Binding(BindingNode::new(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::new(Token::with_value(
                TokenKind::Number,
                "42",
            )))],
        ));
        let to =
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")));

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_number_variable() {
        // Arrange
        let from = ExpressionNode::Number(NumberNode::with_type(
            Token::with_value(TokenKind::Number, "42"),
            TYPE_N,
        ));
        let to = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
            vec![TYPE_N],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
        )]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_variable_variable() {
        // Arrange
        let from = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "y"),
            vec![],
            vec![TYPE_N],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "y"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
        )]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_function_variable() {
        // Arrange
        let from = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::new(Token::with_value(
                TokenKind::Number,
                "42",
            )))],
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
            vec![TYPE_N],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "f"),
                vec![ExpressionNode::Number(NumberNode::new(Token::with_value(
                    TokenKind::Number,
                    "42",
                )))],
                vec![TYPE_N],
            )),
        )]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_operator_variable() {
        // Arrange
        let from = ExpressionNode::Operator(OperatorNode::with_type(
            Token::with_value(TokenKind::Operator, "+"),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "1"),
                TYPE_N,
            )),
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
            vec![TYPE_N],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Operator(OperatorNode::with_type(
                Token::with_value(TokenKind::Operator, "+"),
                ExpressionNode::Number(NumberNode::with_type(
                    Token::with_value(TokenKind::Number, "42"),
                    TYPE_N,
                )),
                ExpressionNode::Number(NumberNode::with_type(
                    Token::with_value(TokenKind::Number, "1"),
                    TYPE_N,
                )),
                vec![TYPE_N],
            )),
        )]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_paren_variable() {
        // Arrange
        let from = ExpressionNode::Paren(ParenNode::with_type(
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
            vec![TYPE_N],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Paren(ParenNode::with_type(
                ExpressionNode::Number(NumberNode::with_type(
                    Token::with_value(TokenKind::Number, "42"),
                    TYPE_N,
                )),
                vec![TYPE_N],
            )),
        )]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_number_function() {
        // Arrange
        let from =
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")));
        let to = ExpressionNode::Binding(BindingNode::new(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::new(Token::with_value(
                TokenKind::Number,
                "42",
            )))],
        ));

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_function_function() {
        // Arrange
        let from = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            ))],
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            ))],
            vec![TYPE_N],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
        )]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_function_operator() {
        // Arrange
        let from = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            ))],
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Operator(OperatorNode::new(
            Token::with_value(TokenKind::Operator, "+"),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42"))),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "1"))),
        ));

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_operator_operator() {
        // Arrange
        let from = ExpressionNode::Operator(OperatorNode::with_type(
            Token::with_value(TokenKind::Operator, "+"),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "1"),
                TYPE_N,
            )),
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Operator(OperatorNode::with_type(
            Token::with_value(TokenKind::Operator, "+"),
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "y"),
                vec![],
                vec![TYPE_N],
            )),
            vec![TYPE_N],
        ));
        let expected = HashMap::from([
            (
                ExpressionNode::Binding(BindingNode::with_type(
                    Token::with_value(TokenKind::Identifier, "x"),
                    vec![],
                    vec![TYPE_N],
                )),
                ExpressionNode::Number(NumberNode::with_type(
                    Token::with_value(TokenKind::Number, "42"),
                    TYPE_N,
                )),
            ),
            (
                ExpressionNode::Binding(BindingNode::with_type(
                    Token::with_value(TokenKind::Identifier, "y"),
                    vec![],
                    vec![TYPE_N],
                )),
                ExpressionNode::Number(NumberNode::with_type(
                    Token::with_value(TokenKind::Number, "1"),
                    TYPE_N,
                )),
            ),
        ]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_variable_paren() {
        // Arrange
        let from = ExpressionNode::Binding(BindingNode::new(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
        ));
        let to = ExpressionNode::Paren(ParenNode::new(ExpressionNode::Number(NumberNode::new(
            Token::with_value(TokenKind::Number, "42"),
        ))));

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_paren_paren() {
        // Arrange
        let from = ExpressionNode::Paren(ParenNode::with_type(
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Paren(ParenNode::with_type(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            vec![TYPE_N],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
        )]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_apply_mapping_number() {
        // Arrange
        let expression =
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")));
        let mapping = HashMap::new();
        let expected =
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")));

        // Act
        let result = expression.apply(&mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }

    #[test]
    fn test_apply_mapping_variable() {
        // Arrange
        let expression = ExpressionNode::Binding(BindingNode::new(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
        ));
        let mapping = HashMap::from([(
            ExpressionNode::Binding(BindingNode::new(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
            )),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42"))),
        )]);
        let expected =
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")));

        // Act
        let result = expression.apply(&mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }

    #[test]
    fn test_apply_mapping_function() {
        // Arrange
        let expression = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Binding(BindingNode::new(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
            ))],
            vec![TYPE_N],
        ));
        let mapping = HashMap::from([(
            ExpressionNode::Binding(BindingNode::new(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
            )),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
        )]);
        let expected = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            ))],
            vec![TYPE_N],
        ));

        // Act
        let result = expression.apply(&mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }

    #[test]
    fn test_apply_mapping_operator() {
        // Arrange
        let expression = ExpressionNode::Operator(OperatorNode::new(
            Token::with_value(TokenKind::Operator, "+"),
            ExpressionNode::Binding(BindingNode::new(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
            )),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "1"))),
        ));
        let mapping = HashMap::from([(
            ExpressionNode::Binding(BindingNode::new(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
            )),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42"))),
        )]);
        let expected = ExpressionNode::Operator(OperatorNode::new(
            Token::with_value(TokenKind::Operator, "+"),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42"))),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "1"))),
        ));

        // Act
        let result = expression.apply(&mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }

    #[test]
    fn test_apply_mapping_paren() {
        // Arrange
        let expression = ExpressionNode::Paren(ParenNode::new(ExpressionNode::Binding(
            BindingNode::new(Token::with_value(TokenKind::Identifier, "x"), vec![]),
        )));
        let mapping = HashMap::from([(
            ExpressionNode::Binding(BindingNode::new(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
            )),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42"))),
        )]);
        let expected = ExpressionNode::Paren(ParenNode::new(ExpressionNode::Number(
            NumberNode::new(Token::with_value(TokenKind::Number, "42")),
        )));

        // Act
        let result = expression.apply(&mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }
}
