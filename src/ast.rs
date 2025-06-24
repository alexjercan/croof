pub mod prelude {
    pub use super::{
        BindingNode, EvaluationNode, ExpressionNode, ImplicationNode, LiteralNode, NumberNode,
        OperatorNode, ParenNode, ProgramNode, QuantifierKind, QuantifierNode, RelationKind,
        SetNode, StatementNode, TypeNode,
    };
}

use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    sync::Arc,
};

use crate::token::{Token, TokenKind};

/// The TypeNode represents a sequence of types in the abstract syntax tree.
///
/// It is used to represent function types, where each type in the sequence corresponds to
/// a parameter type, and the last type corresponds to the return type of the function.
///
/// # Example
/// ```croof
/// N -> N -> N
/// ```
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeNode {
    pub types: Vec<Token>,
}

impl TypeNode {
    /// Creates a new TypeNode with the given types.
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

/// The QuantifierKind represents the kind of quantifier used in the abstract syntax tree.
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

/// The QuantifierNode represents a quantifier in the abstract syntax tree.
///
/// It contains the kind of quantifier, the symbol representing the quantifier,
/// and the type node associated with the quantifier.
///
/// # Example
/// ```croof
/// forall f : N -> N -> N
/// exists x : N
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QuantifierNode {
    pub kind: QuantifierKind,
    pub symbol: Token,
    pub type_node: TypeNode,
}

impl QuantifierNode {
    /// Creates a new QuantifierNode with the given kind, symbol, and type node.
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

/// The SetNode represents a set of elements in the abstract syntax tree.
///
/// It contains a vector of `ExpressionNode` elements, which can be any valid expression
///
/// # Example
/// ```croof
/// {1, 2, 3}
/// {f(1), g(2)}
/// ```
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SetNode {
    pub elements: Vec<ExpressionNode>,
}

impl SetNode {
    /// Creates a new SetNode with the given elements.
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

/// The NumberNode represents a numeric value in the abstract syntax tree.
///
/// It contains a `Token` representing the numeric value and an optional type node.
///
/// # Example
/// ```croof
/// 42
/// -3
/// ```
#[derive(Debug, Clone)]
pub struct NumberNode {
    pub value: Token,

    // NOTE: types should be ignored in equality checks or hashing because they are added and used
    // only by the type checker.
    pub node_type: Option<Vec<String>>,
}

impl NumberNode {
    /// Creates a new NumberNode with the given value.
    pub fn new(value: Token) -> Self {
        NumberNode {
            value,
            node_type: None,
        }
    }

    /// Creates a new NumberNode with the given value and type.
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

impl PartialEq for NumberNode {
    fn eq(&self, other: &Self) -> bool {
        self.value.value() == other.value.value()
    }
}

impl Eq for NumberNode {}

impl Hash for NumberNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.value().hash(state);
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

/// The LiteralNode represents a literal value in the abstract syntax tree.
///
/// It contains a `Token` representing the literal value and an optional type node.
///
/// # Example
/// ```croof
/// "Hello, World!"
/// "42"
/// ```
#[derive(Debug, Clone)]
pub struct LiteralNode {
    pub value: Token,
    pub node_type: Option<Vec<String>>,
}

impl LiteralNode {
    /// Creates a new LiteralNode with the given value.
    pub fn new(value: Token) -> Self {
        LiteralNode {
            value,
            node_type: None,
        }
    }

    /// Creates a new LiteralNode with the given value and type.
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

impl PartialEq for LiteralNode {
    fn eq(&self, other: &Self) -> bool {
        self.value.value() == other.value.value()
    }
}

impl Eq for LiteralNode {}

impl Hash for LiteralNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.value().hash(state);
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

/// The BindingNode represents a function or a binding in the abstract syntax tree.
///
/// It contains a `Token` representing the name of the binding, a vector of `ExpressionNode`
/// arguments, and an optional type node that represents the type of the binding.
///
/// # Note
/// The `node_type` should be filled with the type of the binding at the time of type checking.
///
/// # Example
/// ```croof
/// f(x, 1)
/// ```
#[derive(Debug, Clone)]
pub struct BindingNode {
    pub name: Token,
    pub arguments: Vec<ExpressionNode>,
    pub node_type: Option<Vec<String>>,
}

impl BindingNode {
    /// Creates a new BindingNode with the given name and arguments.
    pub fn new(name: Token, arguments: Vec<ExpressionNode>) -> Self {
        BindingNode {
            name,
            arguments,
            node_type: None,
        }
    }

    /// Creates a new BindingNode with the given name, arguments, and type.
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

impl PartialEq for BindingNode {
    fn eq(&self, other: &Self) -> bool {
        self.name.value() == other.name.value() && self.arguments == other.arguments
    }
}

impl Eq for BindingNode {}

impl Hash for BindingNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.value().hash(state);
        self.arguments.hash(state);
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

/// The OperatorNode represents an operator in the abstract syntax tree.
///
/// It contains a `Token` representing the operator, two `ExpressionNode` operands (left and
/// right), and an optional type node that represents the type of the operation.
///
/// # Example
/// ```croof
/// 1 + 2
/// f(x, y) * g(z)
/// ```
#[derive(Debug, Clone)]
pub struct OperatorNode {
    pub operator: Token,
    pub left: Box<ExpressionNode>,
    pub right: Box<ExpressionNode>,
    pub node_type: Option<Vec<String>>,
}

impl OperatorNode {
    /// Creates a new OperatorNode with the given operator, left operand, and right operand.
    pub fn new(operator: Token, left: ExpressionNode, right: ExpressionNode) -> Self {
        OperatorNode {
            operator,
            left: Box::new(left),
            right: Box::new(right),
            node_type: None,
        }
    }

    /// Creates a new OperatorNode with the given operator, left operand, right operand, and type.
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

impl PartialEq for OperatorNode {
    fn eq(&self, other: &Self) -> bool {
        self.operator.value() == other.operator.value()
            && self.left == other.left
            && self.right == other.right
    }
}

impl Eq for OperatorNode {}

impl Hash for OperatorNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.operator.value().hash(state);
        self.left.hash(state);
        self.right.hash(state);
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

/// The ParenNode represents a parenthesized expression in the abstract syntax tree.
///
/// It contains an `ExpressionNode` representing the expression inside the parentheses,
/// and an optional type node that represents the type of the expression.
///
/// # Example
/// ```croof
/// (f(x, y) + g(z))
/// ```
#[derive(Debug, Clone)]
pub struct ParenNode {
    pub expression: Box<ExpressionNode>,
    pub node_type: Option<Vec<String>>,
}

impl ParenNode {
    /// Creates a new ParenNode with the given expression.
    pub fn new(expression: ExpressionNode) -> Self {
        ParenNode {
            expression: Box::new(expression),
            node_type: None,
        }
    }

    /// Creates a new ParenNode with the given expression and type.
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

impl PartialEq for ParenNode {
    fn eq(&self, other: &Self) -> bool {
        self.expression == other.expression
    }
}

impl Eq for ParenNode {}

impl Hash for ParenNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.expression.hash(state);
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

/// The ExpressionNode enum represents different types of expression nodes in the abstract syntax
/// tree.
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
    /// Computes the degree of the expression node.
    ///
    /// The degree is defined as the number of operations in the expression.
    ///
    /// # Returns
    /// A `u64` representing the degree of the expression node.
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

    /// Returns the token associated with the expression node.
    ///
    /// # Returns
    /// A `Token` representing the token of the expression node.
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

    /// Returns the type of the expression node.
    ///
    /// # Returns
    /// An `Option<Vec<String>>` representing the type of the expression node.
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

    /// Computes the distance between two expression nodes.
    ///
    /// Right now, this function returns a constant value of 1.
    pub fn distance(&self, _: &Self) -> i32 {
        // NOTE: This is a placeholder implementation.
        1
    }

    /// Applies a mapping to the expression node.
    ///
    /// This function will traverse the expression node and apply the mapping to each sub-node.
    ///
    /// # Arguments
    /// * `mapping` - A mapping from `ExpressionNode` to `ExpressionNode`.
    ///
    /// # Returns
    /// An `Option<ExpressionNode>` which is the result of applying the mapping.
    ///
    /// # Note
    /// If the mapping does not contain a mapping for a specific node, it will return `None`.
    ///
    /// # Example
    /// ```rust
    /// use std::collections::HashMap;
    /// use croof::prelude::*;
    ///
    /// let mapping: HashMap<ExpressionNode, ExpressionNode> = HashMap::from([(
    ///     ExpressionNode::Binding(BindingNode::new(
    ///         Token::with_value(TokenKind::Identifier, "x"),
    ///         vec![],
    ///     )),
    ///     ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42"))),
    /// )]);
    ///
    /// let expr = ExpressionNode::Binding(BindingNode::new(Token::with_value(TokenKind::Identifier, "x"), vec![]));
    ///
    /// let result = expr.apply(&mapping);
    ///
    /// // assert_eq!(result, Some(ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")))));
    /// ```
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

    /// Creates a mapping from the current expression node to the given expression node.
    ///
    /// # Arguments
    /// * `expr` - The expression node to which the mapping should be created.
    ///
    /// # Returns
    /// An `Option<HashMap<ExpressionNode, ExpressionNode>>` which contains the mapping if it can
    /// be created, or `None` if it cannot be created.
    ///
    /// # Note
    /// This function will traverse the expression node and create a mapping for each sub-node.
    ///
    /// # Example
    /// ```rust
    /// use croof::prelude::*;
    /// use std::collections::HashMap;
    ///
    /// let expr1 = ExpressionNode::Binding(BindingNode::new(
    ///     Token::with_value(TokenKind::Identifier, "x"),
    ///     vec![],
    /// ));
    ///
    /// let expr2 = ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")));
    ///
    /// let mapping = expr1.create_mapping(&expr2);
    ///
    /// // assert_eq!(mapping, Some(HashMap::from([(expr1, expr2)])));
    /// ```
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

/// The RelationKind enum represents the kind of relation used in the abstract syntax tree.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

/// The RelationNode represents a relation in the abstract syntax tree.
///
/// It contains the kind of relation, a token representing the relation,
/// and two `ExpressionNode` operands (left and right).
///
/// # Example
/// ```croof
/// f(x, y) = g(z)
/// f(x, y) > 42
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelationNode {
    pub kind: RelationKind,
    pub token: Token,
    pub left: ExpressionNode,
    pub right: ExpressionNode,
}

impl RelationNode {
    /// Creates a new RelationNode with the given kind, token, left operand, and right operand.
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

/// The BuiltinNode represents a built-in function or operation in the abstract syntax tree.
///
/// It contains a display name for the built-in, and a function that can be used to substitute
/// the built-in with an expression node.
///
/// # Note
/// The `substitute_fn` is a function that takes an `ExpressionNode` and returns an
/// `Option<ExpressionNode>`. This type of node should only be added to the AST
/// after the type checking phase by the compiler.
#[derive(Clone)]
pub struct BuiltinNode {
    pub display: String,
    pub substitute_fn: SubstituteFn,
}

impl Hash for BuiltinNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.display.hash(state);
    }
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
    /// Creates a new BuiltinNode with the given display name and substitute function.
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

    /// Applies the substitute function to the given expression node.
    pub fn apply(&self, expr: &ExpressionNode) -> Option<ExpressionNode> {
        (self.substitute_fn)(expr)
    }
}

impl Display for BuiltinNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display)
    }
}

/// The StatementNode enum represents different types of statements in the abstract syntax tree.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StatementNode {
    Quantifier(QuantifierNode),
    Relation(RelationNode),
    Builtin(BuiltinNode),
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

/// The ImplicationNode represents an implication in the abstract syntax tree.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ImplicationNode {
    pub conditions: Vec<StatementNode>,
    pub conclusion: Vec<StatementNode>,
}

impl ImplicationNode {
    /// Creates a new ImplicationNode with the given conditions and conclusion.
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

/// The DefineFunctionNode represents a function definition in the abstract syntax tree.
///
/// It contains a `Token` representing the function name and a `TypeNode` representing the type of
/// the function.
///
/// # Example
/// ```croof
/// def f : N -> N -> N
/// def g : N -> N
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefineFunctionNode {
    pub symbol: Token,
    pub type_node: TypeNode,
}

impl DefineFunctionNode {
    /// Creates a new DefineFunctionNode with the given symbol and type node.
    pub fn new(symbol: Token, type_node: TypeNode) -> Self {
        DefineFunctionNode { symbol, type_node }
    }
}

impl Display for DefineFunctionNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} : {}", self.symbol.value(), self.type_node)
    }
}

/// The DefineOperatorNode represents an operator definition in the abstract syntax tree.
///
/// It contains a `Token` representing the operator symbol and a `TypeNode` representing the type
/// of the operator.
///
/// # Example
/// ```croof
/// def + : N -> N -> N
/// def * : N -> N -> N
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefineOperatorNode {
    pub symbol: Token,
    pub type_node: TypeNode,
}

impl DefineOperatorNode {
    /// Creates a new DefineOperatorNode with the given symbol and type node.
    pub fn new(symbol: Token, type_node: TypeNode) -> Self {
        DefineOperatorNode { symbol, type_node }
    }
}

impl Display for DefineOperatorNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} : {}", self.symbol.value(), self.type_node)
    }
}

/// The DefineSetNode represents a set definition in the abstract syntax tree.
///
/// It contains a `Token` representing the set name and a `SetNode` representing the set itself.
///
/// # Example
/// ```croof
/// def S = {1, 2, 3}
/// def T = {}
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefineSetNode {
    pub symbol: Token,
    pub set: SetNode,
}

impl DefineSetNode {
    /// Creates a new DefineSetNode with the given symbol and set.
    pub fn new(symbol: Token, set: SetNode) -> Self {
        DefineSetNode { symbol, set }
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

/// The DefineNode enum represents different types of definitions in the abstract syntax tree.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DefineNode {
    Function(DefineFunctionNode),
    Operator(DefineOperatorNode),
    Set(DefineSetNode),
}

impl DefineNode {
    /// Get the symbol of the define node.
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

/// The EvaluationNode represents an evaluation in the abstract syntax tree.
///
/// It contains a vector of `StatementNode` conditions and an `ExpressionNode` expression.
///
/// # Example
/// ```croof
/// eval f(x) = x => f(0)
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvaluationNode {
    pub conditions: Vec<StatementNode>,
    pub expression: ExpressionNode,
}

impl EvaluationNode {
    /// Creates a new EvaluationNode with the given conditions and expression.
    pub fn new(conditions: Vec<StatementNode>, expression: ExpressionNode) -> Self {
        EvaluationNode {
            conditions,
            expression,
        }
    }
}

impl Display for EvaluationNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let conditions: Vec<String> = self.conditions.iter().map(|s| s.to_string()).collect();

        if !conditions.is_empty() {
            write!(f, "{} => ", conditions.join(", "))?;
        }

        write!(f, "{}", self.expression)
    }
}

/// The ProgramNode represents the entire program in the abstract syntax tree.
///
/// It contains a vector of `DefineNode` for function, operator, and set definitions,
/// a vector of `ImplicationNode` for implications, and a vector of `ExpressionNode` for
/// evaluations.
///
/// # Example
/// ```croof
/// def f : N -> N -> N
/// def g : N -> N
///
/// f(x, y) => g(x) + g(y)
///
/// eval f(1, 2)
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ProgramNode {
    pub defines: Vec<DefineNode>,
    pub implications: Vec<ImplicationNode>,
    pub evaluations: Vec<EvaluationNode>,
}

impl ProgramNode {
    /// Creates a new ProgramNode with the given defines, implications, and evaluations.
    pub fn new(
        defines: Vec<DefineNode>,
        implications: Vec<ImplicationNode>,
        evaluations: Vec<EvaluationNode>,
    ) -> Self {
        ProgramNode {
            defines,
            implications,
            evaluations,
        }
    }

    /// Merges another ProgramNode into this one by extending the defines, implications, and
    /// evaluations.
    ///
    /// # Arguments
    /// * `other` - The ProgramNode to merge into this one.
    ///
    /// # Note
    /// This function will extend the current node's defines, implications, and evaluations
    /// with the ones from the other node.
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
