use std::collections::{hash_map, HashMap};

use crate::{
    lexer::{SourceMap, Token, TokenKind},
    parser::{
        DefineFunctionNode, DefineNode, DefineSetNode, ExpressionNode, ImplicationNode,
        OperatorNode, SetNode, StatementNode, TypeNode,
    },
};

pub const TYPE_N: &str = "N";
pub const FUNCTION_SUCC: &str = "succ"; // N -> N

pub const TYPE_Z: &str = "Z";
pub const FUNCTION_NEG: &str = "neg"; // Z -> Z

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

pub struct Typechecker {
    sourcemap: SourceMap,
    defines: HashMap<String, HashMap<Vec<String>, DefineNode>>,
}

pub fn can_infer_type(left_type: &[String], right_type: &[String]) -> bool {
    (left_type.len() == 1
        && right_type.len() == 1
        && (left_type[0] == TYPE_N && right_type[0] == TYPE_Z))
        || left_type == right_type
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

    fn overloads(
        &self,
        name: &str,
        arg_types: &[String],
        symbols: &HashMap<String, TypeNode>,
    ) -> HashMap<Vec<String>, Vec<String>> {
        let mut overloads: HashMap<Vec<String>, Vec<String>> = self
            .defines
            .get(name)
            .cloned()
            .unwrap_or(HashMap::new())
            .into_iter()
            .filter_map(|(k, v)| {
                if let DefineNode::Operator(node) = v {
                    Some((
                        k,
                        node.type_node
                            .types
                            .iter()
                            .skip(arg_types.len())
                            .map(|token| token.value())
                            .collect::<Vec<_>>(),
                    ))
                } else {
                    None
                }
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
                    for define in defines.values() {
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
                        if arg_types.is_empty() {
                            arg_map.get(&vec![]).or(arg_map
                                .values()
                                .collect::<Vec<_>>()
                                .first()
                                .cloned())
                        } else {
                            arg_map.get(&arg_types)
                        }
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
            ExpressionNode::Operator(operator_node) => self.check_operator(operator_node, symbols),
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
                        "{}, Binding {} is already defined",
                        self.sourcemap.format_pos(token),
                        token.value()
                    );
                }
                TypecheckerError::RedefinedOperator(token) => {
                    eprintln!(
                        "{}, Operator {} is already defined",
                        self.sourcemap.format_pos(token),
                        token.value()
                    );
                }
                TypecheckerError::RedefinedType(token) => {
                    eprintln!(
                        "{}, Type {} is already defined",
                        self.sourcemap.format_pos(token),
                        token.value()
                    );
                }
            }
        }
    }
}
