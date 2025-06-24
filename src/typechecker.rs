pub mod prelude {
    pub use super::{Typechecker, TypecheckerError, FUNCTION_NEG, FUNCTION_SUCC, TYPE_N, TYPE_Z, builtin_implications};
}

use std::{
    collections::{hash_map, HashMap},
    fmt::Display,
};

use crate::{
    ast::{
        BindingNode, BuiltinNode, DefineFunctionNode, DefineNode, DefineSetNode, EvaluationNode,
        ExpressionNode, ImplicationNode, LiteralNode, NumberNode, OperatorNode, ParenNode,
        ProgramNode, QuantifierNode, RelationNode, SetNode, StatementNode, TypeNode,
    },
    token::{Token, TokenKind, WithToken},
};

/// Constants for built-in types and functions
pub const TYPE_N: &str = "N";
pub const FUNCTION_SUCC: &str = "succ"; // N -> N

pub const TYPE_Z: &str = "Z";
pub const FUNCTION_NEG: &str = "neg"; // Z -> Z

/// TypecheckerError represents errors that can occur during the type checking process.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypecheckerError {
    UndefinedType(Token),
    UndefinedLiteral(Token),
    UndefinedBinding {
        token: Token,
        arg_types: Vec<String>,
    },
    UndefinedOperator {
        token: Token,
        left_type: Option<Vec<String>>,
        right_type: Option<Vec<String>>,
    },
    RelationTypeMissmatch {
        relation: Token,
        expected: Vec<String>,
        found: Vec<String>,
    },
    RedefinedType(Token),
    RedefinedBinding(Token),
    RedefinedOperator(Token),
}

impl WithToken for TypecheckerError {
    fn token(&self) -> Token {
        match self {
            TypecheckerError::UndefinedType(token) => token.clone(),
            TypecheckerError::UndefinedLiteral(token) => token.clone(),
            TypecheckerError::UndefinedBinding { token, .. } => token.clone(),
            TypecheckerError::UndefinedOperator { token, .. } => token.clone(),
            TypecheckerError::RelationTypeMissmatch { relation, .. } => relation.clone(),
            TypecheckerError::RedefinedType(token) => token.clone(),
            TypecheckerError::RedefinedBinding(token) => token.clone(),
            TypecheckerError::RedefinedOperator(token) => token.clone(),
        }
    }
}

impl Display for TypecheckerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypecheckerError::UndefinedType(token) => {
                write!(f, "Type is not defined {}", token.value())
            }
            TypecheckerError::UndefinedLiteral(token) => {
                write!(f, "Literal is not defined \"{}\"", token.value())
            }
            TypecheckerError::UndefinedBinding { token, arg_types } => {
                if arg_types.is_empty() {
                    write!(f, "Binding {} is not defined", token.value())
                } else {
                    write!(
                        f,
                        "Binding {} with input type {} is not defined",
                        token.value(),
                        arg_types.join(" -> ")
                    )
                }
            }
            TypecheckerError::UndefinedOperator {
                token,
                left_type,
                right_type,
            } => {
                write!(
                    f,
                    "Operator {} is not defined with left type {} and right type {}",
                    token.value(),
                    left_type
                        .as_ref()
                        .map(|t| t.join(" -> "))
                        .unwrap_or("?".to_string()),
                    right_type
                        .clone()
                        .map(|t| t.join(" -> "))
                        .unwrap_or("?".to_string())
                )
            }
            TypecheckerError::RelationTypeMissmatch {
                relation: _,
                expected,
                found,
            } => {
                write!(
                    f,
                    "Relation: Cannot compare Types {} and {}",
                    expected.join(" -> "),
                    found.join(" -> ")
                )
            }
            TypecheckerError::RedefinedBinding(token) => {
                write!(f, "Binding {} is already defined", token.value())
            }
            TypecheckerError::RedefinedOperator(token) => {
                write!(f, "Operator {} is already defined", token.value())
            }
            TypecheckerError::RedefinedType(token) => {
                write!(f, "Type {} is already defined", token.value())
            }
        }
    }
}

pub fn builtin_implications() -> Vec<ImplicationNode> {
    vec![
        // forall a : N => a = succ(a - 1)
        ImplicationNode::new(
            vec![],
            vec![StatementNode::Builtin(BuiltinNode::new(
                "forall a : N => a = succ(a - 1)",
                |expression| {
                    if let ExpressionNode::Number(node) = expression {
                        if let Some(TYPE_N) = node
                            .node_type
                            .as_ref()
                            .and_then(|t| t.first())
                            .cloned()
                            .as_deref()
                        {
                            let value = node.value.value().parse::<u64>().ok()?;
                            if value == 0 {
                                return None;
                            }

                            let number = NumberNode::with_type(
                                Token::with_value(TokenKind::Number, (value - 1).to_string()),
                                TYPE_N,
                            );

                            let function = BindingNode::with_type(
                                Token::with_value(TokenKind::Identifier, FUNCTION_SUCC),
                                vec![ExpressionNode::Number(number.clone())],
                                vec![TYPE_N],
                            );
                            let substitution = ExpressionNode::Binding(function);

                            return Some(substitution);
                        }
                    }

                    None
                },
            ))],
        ),
        // forall a : Z => a = succ(a - 1)
        ImplicationNode::new(
            vec![],
            vec![StatementNode::Builtin(BuiltinNode::new(
                "forall a : Z => a = succ(a - 1)",
                |expression| {
                    if let ExpressionNode::Number(node) = expression {
                        if let Some(TYPE_Z) = node
                            .node_type
                            .as_ref()
                            .and_then(|t| t.first())
                            .cloned()
                            .as_deref()
                        {
                            let value = node.value.value().parse::<i64>().ok()?;
                            if value <= 0 {
                                return None;
                            }

                            let number = NumberNode::with_type(
                                Token::with_value(TokenKind::Number, (value - 1).to_string()),
                                TYPE_N,
                            );

                            let function = BindingNode::with_type(
                                Token::with_value(TokenKind::Identifier, FUNCTION_SUCC),
                                vec![ExpressionNode::Number(number.clone())],
                                vec![TYPE_N],
                            );
                            let substitution = ExpressionNode::Binding(function);

                            return Some(substitution);
                        }
                    }

                    None
                },
            ))],
        ),
        // forall a : Z, a > 0 => -a = neg(a)
        ImplicationNode::new(
            vec![],
            vec![StatementNode::Builtin(BuiltinNode::new(
                "forall a : Z, a > 0 => -a = neg(a)",
                |expression| {
                    if let ExpressionNode::Number(node) = expression {
                        if let Some(TYPE_Z) = node
                            .node_type
                            .as_ref()
                            .and_then(|t| t.first())
                            .cloned()
                            .as_deref()
                        {
                            let value = node.value.value().parse::<i64>().ok()?;
                            if value > 0 {
                                return None;
                            }

                            let number = NumberNode::with_type(
                                Token::with_value(TokenKind::Number, (-value).to_string()),
                                TYPE_Z,
                            );

                            let function = BindingNode::with_type(
                                Token::with_value(TokenKind::Identifier, FUNCTION_NEG),
                                vec![ExpressionNode::Number(number.clone())],
                                vec![TYPE_Z],
                            );

                            let substitution = ExpressionNode::Binding(function);

                            return Some(substitution);
                        }
                    }

                    None
                },
            ))],
        ),
        // forall a : N => succ(a) = a + 1
        ImplicationNode::new(
            vec![],
            vec![StatementNode::Builtin(BuiltinNode::new(
                "forall a : N => succ(a) = a + 1",
                |expression| {
                    if let ExpressionNode::Binding(expr_node) = expression {
                        if expr_node.name.value() == FUNCTION_SUCC && expr_node.arguments.len() == 1
                        {
                            if let ExpressionNode::Number(number_node) = &expr_node.arguments[0] {
                                if let Some(TYPE_N) = number_node
                                    .node_type
                                    .as_ref()
                                    .and_then(|t| t.first())
                                    .cloned()
                                    .as_deref()
                                {
                                    let value = number_node.value.value().parse::<u64>().ok()?;
                                    let number = NumberNode::with_type(
                                        Token::with_value(
                                            TokenKind::Number,
                                            (value + 1).to_string(),
                                        ),
                                        TYPE_N,
                                    );

                                    let substitution = ExpressionNode::Number(number);

                                    return Some(substitution);
                                }
                            }
                        }
                    }

                    None
                },
            ))],
        ),
        // forall a : Z => succ(a) = a + 1
        ImplicationNode::new(
            vec![],
            vec![StatementNode::Builtin(BuiltinNode::new(
                "forall a : Z => succ(a) = a + 1",
                |expression| {
                    if let ExpressionNode::Binding(expr_node) = expression {
                        if expr_node.name.value() == FUNCTION_SUCC && expr_node.arguments.len() == 1
                        {
                            if let ExpressionNode::Number(number_node) = &expr_node.arguments[0] {
                                if let Some(TYPE_Z) = number_node
                                    .node_type
                                    .as_ref()
                                    .and_then(|t| t.first())
                                    .cloned()
                                    .as_deref()
                                {
                                    let value = number_node.value.value().parse::<i64>().ok()?;
                                    let number = NumberNode::with_type(
                                        Token::with_value(
                                            TokenKind::Number,
                                            (value + 1).to_string(),
                                        ),
                                        TYPE_Z,
                                    );

                                    let substitution = ExpressionNode::Number(number);

                                    return Some(substitution);
                                }
                            }
                        }
                    }

                    None
                },
            ))],
        ),
        // forall a : N => neg(a) = -a
        ImplicationNode::new(
            vec![],
            vec![StatementNode::Builtin(BuiltinNode::new(
                "forall a : N => neg(a) = -a",
                |expression| {
                    if let ExpressionNode::Binding(expr_node) = expression {
                        if expr_node.name.value() == FUNCTION_NEG {
                            if let ExpressionNode::Number(number_node) = &expr_node.arguments[0] {
                                if let Some(TYPE_N) = number_node
                                    .node_type
                                    .as_ref()
                                    .and_then(|t| t.first())
                                    .cloned()
                                    .as_deref()
                                {
                                    let value = number_node.value.value().parse::<i64>().ok()?;

                                    let number = NumberNode::with_type(
                                        Token::with_value(TokenKind::Number, (-value).to_string()),
                                        TYPE_Z,
                                    );

                                    let substitution = ExpressionNode::Number(number);

                                    return Some(substitution);
                                }
                            }
                        }
                    }

                    None
                },
            ))],
        ),
        // forall a : Z => neg(a) = -a
        ImplicationNode::new(
            vec![],
            vec![StatementNode::Builtin(BuiltinNode::new(
                "forall a : Z => neg(a) = -a",
                |expression| {
                    if let ExpressionNode::Binding(expr_node) = expression {
                        if expr_node.name.value() == FUNCTION_NEG {
                            if let ExpressionNode::Number(number_node) = &expr_node.arguments[0] {
                                if let Some(TYPE_Z) = number_node
                                    .node_type
                                    .as_ref()
                                    .and_then(|t| t.first())
                                    .cloned()
                                    .as_deref()
                                {
                                    let value = number_node.value.value().parse::<i64>().ok()?;

                                    let number = NumberNode::with_type(
                                        Token::with_value(TokenKind::Number, (-value).to_string()),
                                        TYPE_Z,
                                    );

                                    let substitution = ExpressionNode::Number(number);

                                    return Some(substitution);
                                }
                            }
                        }
                    }

                    None
                },
            ))],
        ),
    ]
}

fn builtin_mapping() -> HashMap<String, HashMap<Vec<String>, DefineNode>> {
    let mut mapping: HashMap<String, HashMap<Vec<String>, DefineNode>> = HashMap::new();

    // def N = { }
    mapping.insert(
        TYPE_N.to_string(),
        HashMap::from([(
            vec![],
            DefineNode::Set(DefineSetNode::new(
                Token::with_value(TokenKind::Type, TYPE_N),
                SetNode::new(vec![]),
            )),
        )]),
    );

    // def Z = { }
    mapping.insert(
        TYPE_Z.to_string(),
        HashMap::from([(
            vec![],
            DefineNode::Set(DefineSetNode::new(
                Token::with_value(TokenKind::Type, TYPE_Z),
                SetNode::new(vec![]),
            )),
        )]),
    );

    // def succ : N -> N, Z -> Z
    mapping.insert(
        FUNCTION_SUCC.to_string(),
        HashMap::from([
            (
                vec![TYPE_N.to_string()],
                DefineNode::Function(DefineFunctionNode::new(
                    Token::with_value(TokenKind::Identifier, FUNCTION_SUCC),
                    TypeNode::new(vec![
                        Token::with_value(TokenKind::Type, TYPE_N),
                        Token::with_value(TokenKind::Type, TYPE_N),
                    ]),
                )),
            ),
            (
                vec![TYPE_Z.to_string()],
                DefineNode::Function(DefineFunctionNode::new(
                    Token::with_value(TokenKind::Identifier, FUNCTION_SUCC),
                    TypeNode::new(vec![
                        Token::with_value(TokenKind::Type, TYPE_Z),
                        Token::with_value(TokenKind::Type, TYPE_Z),
                    ]),
                )),
            ),
        ]),
    );

    // def neg : Z -> Z
    mapping.insert(
        FUNCTION_NEG.to_string(),
        HashMap::from([(
            vec![TYPE_Z.to_string()],
            DefineNode::Function(DefineFunctionNode::new(
                Token::with_value(TokenKind::Identifier, FUNCTION_NEG),
                TypeNode::new(vec![
                    Token::with_value(TokenKind::Type, TYPE_Z),
                    Token::with_value(TokenKind::Type, TYPE_Z),
                ]),
            )),
        )]),
    );

    mapping
}

/// Typechecker is responsible for checking types of expressions and statements in the program.
pub struct Typechecker {
    mapping: HashMap<String, HashMap<Vec<String>, DefineNode>>,
}

impl Default for Typechecker {
    fn default() -> Self {
        Self::new()
    }
}

impl Typechecker {
    pub fn new() -> Self {
        Typechecker {
            mapping: builtin_mapping(),
        }
    }

    fn check_type(
        &self,
        type_node: &TypeNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> Vec<TypecheckerError> {
        let mut errors = vec![];

        for token in &type_node.types {
            if token.kind == TokenKind::Type {
                let name = token.value();
                if !symbols.contains_key(&name) && !self.mapping.contains_key(&name) {
                    errors.push(TypecheckerError::UndefinedType(token.clone()));
                }
            }
        }

        errors
    }

    fn overloads(
        &self,
        name: &str,
        arg_types: &[String],
        symbols: &HashMap<String, TypeNode>,
    ) -> HashMap<Vec<String>, Vec<String>> {
        let mut overloads: HashMap<Vec<String>, Vec<String>> = self
            .mapping
            .get(name)
            .cloned()
            .unwrap_or(HashMap::new())
            .into_iter()
            .filter_map(|(k, v)| match v {
                DefineNode::Function(node) => Some((k, node.type_node.types)),
                DefineNode::Operator(node) => Some((k, node.type_node.types)),
                DefineNode::Set(_) => None,
            })
            .map(|(k, v)| {
                (
                    k,
                    v.iter()
                        .skip(arg_types.len())
                        .map(|token| token.value())
                        .collect::<Vec<_>>(),
                )
            })
            .collect();

        if let Some(node_type) = symbols.get(name) {
            let input_types = node_type
                .types
                .iter()
                .take(arg_types.len())
                .map(|token| token.value())
                .collect::<Vec<_>>();
            let node_type = node_type
                .types
                .iter()
                .skip(arg_types.len())
                .map(|token| token.value())
                .collect::<Vec<_>>();
            overloads.insert(input_types, node_type);
        }

        overloads
    }

    fn check_operator(
        &self,
        node: &mut OperatorNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> (Option<Vec<String>>, Vec<TypecheckerError>) {
        let name = node.operator.value();
        let mut errors = vec![];

        let (left_type, left_errors) = self.check_expression(&mut node.left, symbols);
        errors.extend(left_errors);

        let (right_type, right_errors) = self.check_expression(&mut node.right, symbols);
        errors.extend(right_errors);

        // TODO: Maybe we want to infer some operator and still return Some type
        if !errors.is_empty() {
            errors.push(TypecheckerError::UndefinedOperator {
                token: node.operator.clone(),
                left_type,
                right_type,
            });

            return (None, errors);
        }

        let Some(left_type) = left_type else {
            unreachable!("Left type should always be Some");
        };
        let Some(right_type) = right_type else {
            unreachable!("Right type should always be Some");
        };
        let arg_types = left_type
            .iter()
            .chain(right_type.iter())
            .map(|t| t.to_string())
            .collect::<Vec<_>>();

        let overloads = self.overloads(&name, &arg_types, symbols);

        if let Some(types) = overloads.get(&arg_types) {
            node.node_type = Some(types.clone());
            return (Some(types.clone()), errors);
        }

        if left_type.len() == 1 && right_type.len() == 1 {
            let left_type = left_type[0].clone();
            let right_type = right_type[0].clone();

            // Try to relax from N to Z
            for (input_types, overload) in overloads {
                let left_input_type = input_types[0].clone();
                let right_input_type = input_types[1].clone();

                if (left_type == TYPE_N
                    && left_input_type == TYPE_Z
                    && right_type == right_input_type)
                    || (right_type == TYPE_N
                        && right_input_type == TYPE_Z
                        && left_type == left_input_type)
                {
                    node.node_type = Some(overload.clone());
                    return (Some(overload), errors);
                }
            }
        }

        errors.push(TypecheckerError::UndefinedOperator {
            token: node.operator.clone(),
            left_type: Some(left_type),
            right_type: Some(right_type),
        });
        (None, errors)
    }

    fn check_binding(
        &self,
        node: &mut BindingNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> (Option<Vec<String>>, Vec<TypecheckerError>) {
        let name = node.name.value();
        let mut errors = vec![];

        let mut arg_types: Vec<String> = vec![];
        for arg in node.arguments.iter_mut() {
            let (arg_type, arg_errors) = self.check_expression(arg, symbols);
            errors.extend(arg_errors);

            if let Some(t) = arg_type {
                arg_types.extend(t)
            }
        }

        // TODO: Maybe we want to infer some binding and still return Some type
        if !errors.is_empty() {
            errors.push(TypecheckerError::UndefinedBinding {
                token: node.name.clone(),
                arg_types,
            });

            return (None, errors);
        }

        let overloads = self.overloads(&name, &arg_types, symbols);

        if let Some(types) = overloads.get(&arg_types) {
            node.node_type = Some(types.clone());
            return (Some(types.clone()), errors);
        }

        // Try to relax from N to Z
        for (input_types, overload) in overloads {
            let mut can_use = true;

            for (arg_type, input_type) in arg_types.iter().zip(input_types.iter()) {
                can_use = can_use
                    && ((arg_type == input_type) || (arg_type == TYPE_N && input_type == TYPE_Z));
            }

            if can_use {
                node.node_type = Some(overload.clone());
                return (Some(overload), errors);
            }
        }

        errors.push(TypecheckerError::UndefinedBinding {
            token: node.name.clone(),
            arg_types,
        });
        (None, errors)
    }

    fn check_number(&self, node: &mut NumberNode) -> (Option<Vec<String>>, Vec<TypecheckerError>) {
        let Ok(number) = node.value.value().parse::<i64>() else {
            return (
                None,
                vec![TypecheckerError::UndefinedLiteral(node.value.clone())],
            );
        };
        let type_value = if number >= 0 { TYPE_N } else { TYPE_Z };

        node.node_type = Some(vec![type_value.to_string()]);

        (node.node_type.clone(), vec![])
    }

    fn check_literal(
        &self,
        node: &mut LiteralNode,
    ) -> (Option<Vec<String>>, Vec<TypecheckerError>) {
        for (symbol, defines) in &self.mapping {
            for define in defines.values() {
                if let DefineNode::Set(define) = define {
                    if define
                        .set
                        .elements
                        .contains(&ExpressionNode::Literal(node.clone()))
                    {
                        node.node_type = Some(vec![symbol.clone()]);

                        return (node.node_type.clone(), vec![]);
                    }
                };
            }
        }

        (
            None,
            vec![TypecheckerError::UndefinedLiteral(node.value.clone())],
        )
    }

    fn check_paren(
        &self,
        node: &mut ParenNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> (Option<Vec<String>>, Vec<TypecheckerError>) {
        let (type_node, paren_errors) = self.check_expression(&mut node.expression, symbols);

        node.node_type = type_node.clone();

        (type_node, paren_errors)
    }

    /// Checks the type of an expression and returns the type and any errors encountered.
    ///
    /// # Arguments
    /// * `expression` - A mutable reference to the expression node to be checked.
    /// * `symbols` - A reference to a map of symbols and their types.
    ///
    /// # Returns
    /// A tuple containing:
    /// * An `Option<Vec<String>>` representing the type of the expression if it can be determined,
    /// * a `Vec<TypecheckerError>` containing any errors encountered during the type checking
    ///     process.
    pub fn check_expression(
        &self,
        expression: &mut ExpressionNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> (Option<Vec<String>>, Vec<TypecheckerError>) {
        if let Some(node_type) = expression.node_type() {
            return (Some(node_type), vec![]);
        }

        match expression {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(node) => self.check_number(node),
            ExpressionNode::Literal(node) => self.check_literal(node),
            ExpressionNode::Binding(node) => self.check_binding(node, symbols),
            ExpressionNode::Operator(node) => self.check_operator(node, symbols),
            ExpressionNode::Paren(node) => self.check_paren(node, symbols),
        }
    }

    fn check_relation(
        &self,
        node: &mut RelationNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> Vec<TypecheckerError> {
        let mut errors = vec![];

        let (left_type, left_errors) = self.check_expression(&mut node.left, symbols);
        errors.extend(left_errors);
        let (right_type, right_errors) = self.check_expression(&mut node.right, symbols);
        errors.extend(right_errors);

        if let (Some(left_type), Some(right_type)) = (left_type, right_type) {
            if left_type.len() != right_type.len()
                || left_type.iter().zip(right_type.iter()).any(|(l, r)| l != r)
            {
                errors.push(TypecheckerError::RelationTypeMissmatch {
                    relation: node.token.clone(),
                    expected: left_type,
                    found: right_type,
                });
            }
        }

        errors
    }

    fn check_quantifier(
        &self,
        node: &mut QuantifierNode,
        symbols: &mut HashMap<String, TypeNode>,
    ) -> Vec<TypecheckerError> {
        let mut errors = vec![];

        let symbol = node.symbol.clone();
        let name = symbol.value();

        if let hash_map::Entry::Vacant(e) = symbols.entry(name) {
            e.insert(node.type_node.clone());
        } else {
            errors.push(TypecheckerError::RedefinedBinding(symbol.clone()));
        }

        errors
    }

    fn check_statement(
        &self,
        statement: &mut StatementNode,
        symbols: &mut HashMap<String, TypeNode>,
    ) -> Vec<TypecheckerError> {
        match statement {
            StatementNode::Quantifier(quantifier_node) => {
                self.check_quantifier(quantifier_node, symbols)
            }
            StatementNode::Relation(relation_node) => self.check_relation(relation_node, symbols),
            StatementNode::Builtin(_) => vec![], // Built-in statements are assumed to be valid
        }
    }

    /// Checks an implication node, validating its conditions and conclusions.
    ///
    /// # Arguments
    /// * `implication` - A mutable reference to the implication node to be checked.
    ///
    /// # Returns
    /// A vector of `TypecheckerError` containing any errors encountered during the type checking
    /// process.
    pub fn check_implication(&self, implication: &mut ImplicationNode) -> Vec<TypecheckerError> {
        let mut symbols: HashMap<String, TypeNode> = HashMap::new();
        let mut errors = vec![];

        for condition in &mut implication.conditions {
            errors.extend(self.check_statement(condition, &mut symbols));
        }

        for conclusion in &mut implication.conclusion {
            errors.extend(self.check_statement(conclusion, &mut symbols));
        }

        errors
    }

    fn check_define(&mut self, define: &mut DefineNode) -> Vec<TypecheckerError> {
        let mut errors = vec![];

        let symbol = define.symbol();
        let name = symbol.value();

        match &define {
            DefineNode::Function(node) => {
                let (_, arg_types) = node.type_node.types.split_last().unwrap();
                let arg_types: Vec<String> = arg_types.iter().map(|token| token.value()).collect();

                if self
                    .mapping
                    .get(&name)
                    .map_or(false, |arg_map| arg_map.contains_key(&arg_types))
                {
                    errors.push(TypecheckerError::RedefinedBinding(symbol));
                } else {
                    self.mapping
                        .entry(name.clone())
                        .or_default()
                        .insert(arg_types, define.clone());
                }
            }
            DefineNode::Operator(node) => {
                let left_type = node.type_node.types[0].clone().value();
                let right_type = node.type_node.types[1].clone().value();
                let arg_types = vec![left_type, right_type];

                if self
                    .mapping
                    .get(&name)
                    .map_or(false, |arg_map| arg_map.contains_key(&arg_types))
                {
                    errors.push(TypecheckerError::RedefinedOperator(symbol));
                } else {
                    self.mapping
                        .entry(name.clone())
                        .or_default()
                        .insert(arg_types, define.clone());
                }
            }
            DefineNode::Set(_) => {
                if self.mapping.contains_key(&name) {
                    errors.push(TypecheckerError::RedefinedType(symbol));
                } else {
                    self.mapping
                        .entry(name.clone())
                        .or_default()
                        .insert(vec![], define.clone());
                }
            }
        }

        match &define {
            DefineNode::Function(node) => {
                errors.extend(self.check_type(&node.type_node, &HashMap::default()));
            }
            DefineNode::Operator(node) => {
                errors.extend(self.check_type(&node.type_node, &HashMap::default()));
            }
            DefineNode::Set(_) => {
                // TODO: Check if the set is well-defined
            }
        }

        errors
    }

    pub fn check_evaluation(&self, evaluation: &mut EvaluationNode) -> Vec<TypecheckerError> {
        let mut symbols: HashMap<String, TypeNode> = HashMap::new();
        let mut errors = vec![];

        for condition in &mut evaluation.conditions {
            errors.extend(self.check_statement(condition, &mut symbols));
        }

        errors.extend(
            self.check_expression(&mut evaluation.expression, &symbols)
                .1,
        );

        errors
    }

    /// Checks a program node, validating all implications and statements.
    ///
    /// # Arguments
    /// * `program` - A mutable reference to the program node to be checked.
    ///
    /// # Returns
    /// A vector of `TypecheckerError` containing any errors encountered during the type checking
    /// process.
    pub fn check_program(&mut self, program: &mut ProgramNode) -> Vec<TypecheckerError> {
        let mut errors = vec![];

        for define in &mut program.defines {
            errors.extend(self.check_define(define));
        }

        for implication in &mut program.implications {
            errors.extend(self.check_implication(implication));
        }

        for eval in &mut program.evaluations {
            errors.extend(self.check_evaluation(eval));
        }

        errors
    }
}
