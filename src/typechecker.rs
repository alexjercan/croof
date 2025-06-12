use std::collections::{hash_map, HashMap};

use crate::{
    lexer::{SourceMap, Token, TokenKind},
    parser::{
        DefineFunctionNode, DefineNode, DefineSetNode, ExpressionNode, ImplicationNode, SetNode,
        StatementNode, TypeNode,
    },
};

pub const TYPE_N: &str = "N";
pub const FUNCTION_N: &str = "n"; // Z -> N
pub const FUNCTION_SUCC: &str = "succ"; // N -> N

pub const TYPE_Z: &str = "Z";
pub const FUNCTION_Z: &str = "z"; // N -> Z
pub const FUNCTION_NEG: &str = "neg"; // Z -> Z

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

pub struct Typechecker {
    sourcemap: SourceMap,
    defines: HashMap<String, HashMap<Vec<String>, DefineNode>>,
}

impl Typechecker {
    pub fn new(defines: Vec<DefineNode>, sourcemap: &SourceMap) -> (Self, Vec<TypecheckerError>) {
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

        // def n : Z -> N
        mapping.insert(
            FUNCTION_N.to_string(),
            HashMap::from([(
                vec![TYPE_Z.to_string()],
                DefineNode::Function(DefineFunctionNode::new(
                    Token::with_value(TokenKind::Identifier, FUNCTION_N),
                    TypeNode::new(vec![
                        Token::with_value(TokenKind::Type, TYPE_Z),
                        Token::with_value(TokenKind::Type, TYPE_N),
                    ]),
                )),
            )]),
        );

        // def succ : N -> N
        mapping.insert(
            FUNCTION_SUCC.to_string(),
            HashMap::from([(
                vec![TYPE_N.to_string()],
                DefineNode::Function(DefineFunctionNode::new(
                    Token::with_value(TokenKind::Identifier, FUNCTION_SUCC),
                    TypeNode::new(vec![
                        Token::with_value(TokenKind::Type, TYPE_N),
                        Token::with_value(TokenKind::Type, TYPE_N),
                    ]),
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

        // def z : N -> Z
        mapping.insert(
            FUNCTION_Z.to_string(),
            HashMap::from([(
                vec![TYPE_N.to_string()],
                DefineNode::Function(DefineFunctionNode::new(
                    Token::with_value(TokenKind::Identifier, FUNCTION_Z),
                    TypeNode::new(vec![
                        Token::with_value(TokenKind::Type, TYPE_N),
                        Token::with_value(TokenKind::Type, TYPE_Z),
                    ]),
                )),
            )]),
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

        let mut typechecker = Typechecker {
            sourcemap: sourcemap.clone(),
            defines: mapping,
        };

        let mut errors = vec![];

        for define in defines {
            let symbol = define.symbol();
            let name = symbol.value();

            match &define {
                DefineNode::Function(node) => {
                    let (_, arg_types) = node.type_node.types.split_last().unwrap();
                    let arg_types: Vec<String> =
                        arg_types.iter().map(|token| token.value()).collect();

                    if typechecker
                        .defines
                        .get(&name)
                        .map_or(false, |arg_map| arg_map.contains_key(&arg_types))
                    {
                        errors.push(TypecheckerError::RedefinedBinding(symbol));
                    } else {
                        typechecker
                            .defines
                            .entry(name.clone())
                            .or_default()
                            .insert(arg_types, define.clone());
                    }
                }
                DefineNode::Operator(node) => {
                    let left_type = node.type_node.types[0].clone().value();
                    let right_type = node.type_node.types[1].clone().value();
                    let arg_types = vec![left_type, right_type];

                    if typechecker
                        .defines
                        .get(&name)
                        .map_or(false, |arg_map| arg_map.contains_key(&arg_types))
                    {
                        errors.push(TypecheckerError::RedefinedOperator(symbol));
                    } else {
                        typechecker
                            .defines
                            .entry(name.clone())
                            .or_default()
                            .insert(arg_types, define.clone());
                    }
                }
                DefineNode::Set(_) => {
                    if typechecker.defines.contains_key(&name) {
                        errors.push(TypecheckerError::RedefinedType(symbol));
                    } else {
                        typechecker
                            .defines
                            .entry(name.clone())
                            .or_default()
                            .insert(vec![], define.clone());
                    }
                }
            }

            match &define {
                DefineNode::Function(node) => {
                    errors.extend(typechecker.check_type(&node.type_node, &HashMap::default()));
                }
                DefineNode::Operator(node) => {
                    errors.extend(typechecker.check_type(&node.type_node, &HashMap::default()));
                }
                DefineNode::Set(_) => {
                    // TODO: Check if the set is well-defined
                }
            }
        }

        (typechecker, errors)
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
                if !symbols.contains_key(&name) && !self.defines.contains_key(&name) {
                    errors.push(TypecheckerError::UndefinedType(token.clone()));
                }
            }
        }

        errors
    }

    pub fn check_expression(
        &self,
        expression: &mut ExpressionNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> (Option<Vec<String>>, Vec<TypecheckerError>) {
        match expression {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(number_node) => {
                let Ok(number) = number_node.value.value().parse::<i64>() else {
                    return (
                        None,
                        vec![TypecheckerError::UndefinedLiteral(
                            number_node.value.clone(),
                        )],
                    );
                };
                let type_value = if number >= 0 { TYPE_N } else { TYPE_Z };

                number_node.node_type = Some(vec![type_value.to_string()]);

                (number_node.node_type.clone(), vec![])
            }
            ExpressionNode::Literal(literal_node) => {
                for (symbol, defines) in &self.defines {
                    for (_, define) in defines {
                        if let DefineNode::Set(node) = define {
                            if node
                                .set
                                .elements
                                .contains(&ExpressionNode::Literal(literal_node.clone()))
                            {
                                literal_node.node_type = Some(vec![symbol.clone()]);

                                return (literal_node.node_type.clone(), vec![]);
                            }
                        };
                    }
                }

                (
                    None,
                    vec![TypecheckerError::UndefinedLiteral(
                        literal_node.value.clone(),
                    )],
                )
            }
            ExpressionNode::Binding(node) => {
                let mut errors = vec![];
                let mut can_find = true;

                let mut arg_types: Vec<String> = vec![];
                for arg in node.arguments.iter_mut() {
                    let (arg_type, arg_errors) = self.check_expression(arg, symbols);
                    errors.extend(arg_errors);

                    match arg_type {
                        Some(t) => arg_types.extend(t),
                        None => can_find = false,
                    }
                }

                if !can_find {
                    errors.push(TypecheckerError::UndefinedBinding {
                        token: node.name.clone(),
                        arg_types,
                    });
                    return (None, errors);
                }

                let name = node.name.value();
                let Some(node_type) = symbols.get(&name).or(
                    match self.defines.get(&name).and_then(|arg_map| {
                        arg_map.get(&arg_types).or(arg_map
                            .values()
                            .collect::<Vec<_>>()
                            .first()
                            .cloned())
                    }) {
                        Some(DefineNode::Function(node)) => Some(&node.type_node),
                        _ => None,
                    },
                ) else {
                    return (
                        None,
                        vec![TypecheckerError::UndefinedBinding {
                            token: node.name.clone(),
                            arg_types,
                        }],
                    );
                };

                let node_type = node_type
                    .types
                    .iter()
                    .skip(arg_types.len())
                    .map(|token| token.value())
                    .collect::<Vec<_>>();

                node.node_type = Some(node_type);

                (node.node_type.clone(), errors)
            }
            ExpressionNode::Operator(operator_node) => {
                let mut arg_types: Vec<String> = vec![];
                let mut errors = vec![];
                let mut can_find = true;

                let (left_type, left_errors) =
                    self.check_expression(&mut operator_node.left, symbols);
                errors.extend(left_errors);

                match left_type {
                    Some(ref t) => arg_types.extend(t.clone()),
                    None => can_find = false,
                }

                let (right_type, right_errors) =
                    self.check_expression(&mut operator_node.right, symbols);
                errors.extend(right_errors);

                match right_type {
                    Some(ref t) => arg_types.extend(t.clone()),
                    None => can_find = false,
                }

                if !can_find {
                    errors.push(TypecheckerError::UndefinedOperator {
                        token: operator_node.operator.clone(),
                        left_type,
                        right_type,
                    });

                    return (None, errors);
                }

                let name = operator_node.operator.value();
                let Some(operator_type) = symbols.get(&name).or(
                    match self
                        .defines
                        .get(&name)
                        .and_then(|arg_map| arg_map.get(&arg_types))
                    {
                        Some(DefineNode::Operator(node)) => Some(&node.type_node),
                        _ => None,
                    },
                ) else {
                    errors.push(TypecheckerError::UndefinedOperator {
                        token: operator_node.operator.clone(),
                        left_type,
                        right_type,
                    });

                    return (None, errors);
                };

                let operator_type = operator_type
                    .types
                    .iter()
                    .skip(arg_types.len())
                    .map(|token| token.value())
                    .collect::<Vec<_>>();

                operator_node.node_type = Some(operator_type);

                (operator_node.node_type.clone(), errors)
            }
            ExpressionNode::Paren(paren_node) => {
                let (type_node, paren_errors) =
                    self.check_expression(&mut paren_node.expression, symbols);

                paren_node.node_type = type_node.clone();

                (type_node, paren_errors)
            }
        }
    }

    fn check_statement(
        &self,
        statement: &mut StatementNode,
        symbols: &mut HashMap<String, TypeNode>,
    ) -> Vec<TypecheckerError> {
        let mut errors = vec![];

        match statement {
            StatementNode::Quantifier(quantifier_node) => {
                let symbol = quantifier_node.symbol.clone();
                let name = symbol.value();
                if let hash_map::Entry::Vacant(e) = symbols.entry(name) {
                    e.insert(quantifier_node.type_node.clone());
                } else {
                    errors.push(TypecheckerError::RedefinedBinding(symbol.clone()));
                }
            }
            StatementNode::Relation(relation_node) => {
                let (left_type, left_errors) =
                    self.check_expression(&mut relation_node.left, symbols);
                errors.extend(left_errors);
                let (right_type, right_errors) =
                    self.check_expression(&mut relation_node.right, symbols);
                errors.extend(right_errors);

                if let (Some(left_type), Some(right_type)) = (left_type, right_type) {
                    if left_type.len() != right_type.len()
                        || left_type.iter().zip(right_type.iter()).any(|(l, r)| l != r)
                    {
                        errors.push(TypecheckerError::RelationTypeMissmatch {
                            relation: relation_node.token.clone(),
                            expected: left_type,
                            found: right_type,
                        });
                    }
                }
            }
        };

        errors
    }

    pub fn check(&self, implication: &mut ImplicationNode) -> Vec<TypecheckerError> {
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

    pub fn display_errors(&self, errors: &Vec<TypecheckerError>) {
        for error in errors {
            match error {
                TypecheckerError::UndefinedType(token) => {
                    eprintln!(
                        "{}, Type is not defined {}",
                        self.sourcemap.format_pos(token),
                        token.value()
                    );
                }
                TypecheckerError::UndefinedLiteral(token) => {
                    eprintln!(
                        "{}, Literal is not defined \"{}\"",
                        self.sourcemap.format_pos(token),
                        token.value()
                    );
                }
                TypecheckerError::UndefinedBinding { token, arg_types } => {
                    if arg_types.is_empty() {
                        eprintln!(
                            "{}, Binding {} is not defined",
                            self.sourcemap.format_pos(token),
                            token.value()
                        );
                        return;
                    } else {
                        eprintln!(
                            "{}, Binding {} with input type {} is not defined",
                            self.sourcemap.format_pos(token),
                            token.value(),
                            arg_types.join(" -> ")
                        );
                    }
                }
                TypecheckerError::UndefinedOperator {
                    token,
                    left_type,
                    right_type,
                } => {
                    eprintln!(
                        "{}, Operator {} is not defined with left type {} and right type {}",
                        self.sourcemap.format_pos(token),
                        token.value(),
                        left_type
                            .as_ref()
                            .map(|t| t.join(" -> "))
                            .unwrap_or("?".to_string()),
                        right_type
                            .clone()
                            .map(|t| t.join(" -> "))
                            .unwrap_or("?".to_string())
                    );
                }
                TypecheckerError::RelationTypeMissmatch {
                    relation,
                    expected,
                    found,
                } => {
                    eprintln!(
                        "{}, Relation: Cannot compare Types {} and {}",
                        self.sourcemap.format_pos(relation),
                        expected.join(" -> "),
                        found.join(" -> ")
                    );
                }
                TypecheckerError::RedefinedBinding(token) => {
                    eprintln!(
                        "{}, Binding is already defined {}",
                        self.sourcemap.format_pos(token),
                        token.value()
                    );
                }
                TypecheckerError::RedefinedOperator(token) => {
                    eprintln!(
                        "{}, Operator is already defined {}",
                        self.sourcemap.format_pos(token),
                        token.value()
                    );
                }
                TypecheckerError::RedefinedType(token) => {
                    eprintln!(
                        "{}, Type is already defined {}",
                        self.sourcemap.format_pos(token),
                        token.value()
                    );
                }
            }
        }
    }
}
