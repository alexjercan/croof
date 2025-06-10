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
    UndefinedVariable(Token),
    UndefinedFunction {
        token: Token,
        arg_types: Vec<Option<Token>>,
    },
    UndefinedOperator {
        token: Token,
        left_type: Option<Token>,
        right_type: Option<Token>,
    },
    RelationTypeMissmatch {
        relation: Token,
        expected: TypeNode,
        found: TypeNode,
    },
    RedefinedType(Token),
    RedefinedVariable(Token),
    RedefinedFunction(Token),
    RedefinedOperator(Token),
}

pub struct Typechecker {
    sourcemap: SourceMap,
    defines: HashMap<(String, Vec<Token>), DefineNode>,
}

impl Typechecker {
    pub fn new(defines: Vec<DefineNode>, sourcemap: &SourceMap) -> (Self, Vec<TypecheckerError>) {
        let mut mapping: HashMap<(String, Vec<Token>), DefineNode> = HashMap::new();

        // def N = { }
        mapping.insert(
            (TYPE_N.to_string(), vec![]),
            DefineNode::Set(DefineSetNode::new(
                Token::value(TokenKind::Type, TYPE_N),
                SetNode::new(vec![]),
            )),
        );

        // def n : Z -> N
        mapping.insert(
            (FUNCTION_N.to_string(), vec![Token::value(TokenKind::Type, TYPE_Z)]),
            DefineNode::Function(DefineFunctionNode::new(
                Token::value(TokenKind::Identifier, FUNCTION_N),
                TypeNode::new(vec![
                    Token::value(TokenKind::Type, TYPE_Z),
                    Token::value(TokenKind::Type, TYPE_N),
                ]),
            )),
        );

        // def succ : N -> N
        mapping.insert(
            (FUNCTION_SUCC.to_string(), vec![Token::value(TokenKind::Type, TYPE_N)]),
            DefineNode::Function(DefineFunctionNode::new(
                Token::value(TokenKind::Identifier, FUNCTION_SUCC),
                TypeNode::new(vec![
                    Token::value(TokenKind::Type, TYPE_N),
                    Token::value(TokenKind::Type, TYPE_N),
                ]),
            )),
        );

        // def Z = { }
        mapping.insert(
            (TYPE_Z.to_string(), vec![]),
            DefineNode::Set(DefineSetNode::new(
                Token::value(TokenKind::Type, TYPE_Z),
                SetNode::new(vec![]),
            )),
        );

        // def z : N -> Z
        mapping.insert(
            (FUNCTION_Z.to_string(), vec![Token::value(TokenKind::Type, TYPE_N)]),
            DefineNode::Function(DefineFunctionNode::new(
                Token::value(TokenKind::Identifier, FUNCTION_Z),
                TypeNode::new(vec![
                    Token::value(TokenKind::Type, TYPE_N),
                    Token::value(TokenKind::Type, TYPE_Z),
                ]),
            )),
        );

        // def neg : Z -> Z
        mapping.insert(
            (FUNCTION_NEG.to_string(), vec![Token::value(TokenKind::Type, TYPE_Z)]),
            DefineNode::Function(DefineFunctionNode::new(
                Token::value(TokenKind::Identifier, FUNCTION_NEG),
                TypeNode::new(vec![
                    Token::value(TokenKind::Type, TYPE_Z),
                    Token::value(TokenKind::Type, TYPE_Z),
                ]),
            )),
        );

        let mut typechecker = Typechecker {
            sourcemap: sourcemap.clone(),
            defines: mapping,
        };

        let mut errors = vec![];

        for define in defines {
            let symbol = define.symbol();
            let name = symbol.value.clone().unwrap();

            match &define {
                DefineNode::Function(node) => {
                    let (_, arg_types) = node.type_node.types.split_last().unwrap();

                    if typechecker.defines.contains_key(&(name.clone(), arg_types.into())) {
                        errors.push(TypecheckerError::RedefinedFunction(symbol));
                    } else {
                        typechecker.defines.insert((name, arg_types.into()), define.clone());
                    }
                },
                DefineNode::Operator(node) => {
                    let left_type = node.type_node.types[0].clone();
                    let right_type = node.type_node.types[1].clone();
                    let arg_types = vec![left_type, right_type];

                    if typechecker.defines.contains_key(&(name.clone(), arg_types.clone())) {
                        errors.push(TypecheckerError::RedefinedOperator(symbol));
                    } else {
                        typechecker.defines.insert((name, arg_types), define.clone());
                    }
                },
                DefineNode::Set(_) => {
                    if typechecker.defines.contains_key(&(name.clone(), vec![])) {
                        errors.push(TypecheckerError::RedefinedType(symbol));
                    } else {
                        typechecker.defines.insert((name, vec![]), define.clone());
                    }
                },
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
                let name = token.value.clone().unwrap();
                if !symbols.contains_key(&name) && !self.defines.contains_key(&(name, vec![])) {
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
    ) -> (Option<TypeNode>, Vec<TypecheckerError>) {
        match expression {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(number_node) => {
                let number: i64 = number_node.value.value.clone().unwrap().parse().unwrap();
                let type_value = if number >= 0 { TYPE_N } else { TYPE_Z };

                let type_node = Some(TypeNode::new(vec![Token::value(TokenKind::Type, type_value)]));

                number_node.type_node = type_node.clone();

                (type_node, vec![])
            }
            ExpressionNode::Literal(literal_node) => {
                for ((symbol, _), define) in &self.defines {
                    if let DefineNode::Set(node) = define {
                        if node
                            .set
                            .elements
                            .contains(&ExpressionNode::Literal(literal_node.clone()))
                        {
                            let type_node =
                                Some(TypeNode::new(vec![Token::value(TokenKind::Type, symbol)]));

                            literal_node.type_node = type_node.clone();

                            return (type_node, vec![]);
                        }
                    };
                }

                (
                    None,
                    vec![TypecheckerError::UndefinedLiteral(
                        literal_node.value.clone(),
                    )],
                )
            }
            ExpressionNode::Variable(variable_node) => {
                let name = variable_node.name.value.clone().unwrap();
                let mut errors = vec![];

                let type_node = match symbols.get(&name) {
                    Some(type_node) => Some(type_node.clone()),
                    None => {
                        errors.push(TypecheckerError::UndefinedVariable(
                            variable_node.name.clone(),
                        ));

                        None
                    }
                };

                variable_node.type_node = type_node.clone();

                (type_node, errors)
            }
            ExpressionNode::Function(function_node) => {
                let mut arg_types = vec![];
                let mut errors = vec![];

                for arg in function_node.arguments.iter_mut() {
                    let (arg_type, arg_errors) = self.check_expression(arg, symbols);
                    errors.extend(arg_errors);

                    arg_types.push(arg_type.map(|t| t.types.first().cloned()).flatten());
                }

                let name = function_node.name.value.clone().unwrap();

                let arg_type_tokens: Vec<Token> = arg_types
                    .iter()
                    .filter_map(|t| t.clone())
                    .collect();

                if arg_type_tokens.len() != arg_types.len() {
                    errors.push(TypecheckerError::UndefinedFunction {
                        token: function_node.name.clone(),
                        arg_types,
                    });
                    return (None, errors);
                }

                let Some(function_type) = symbols.get(&name).or(match self.defines.get(&(name, arg_type_tokens)) {
                    Some(DefineNode::Function(node)) => Some(&node.type_node),
                    _ => None,
                }) else {
                    return (
                        None,
                        vec![TypecheckerError::UndefinedFunction {
                            token: function_node.name.clone(),
                            arg_types,
                        }],
                    );
                };

                let function_type = function_type.types.last().unwrap();

                let type_node = Some(TypeNode::new(vec![function_type.clone()]));

                function_node.type_node = type_node.clone();

                (type_node, errors)
            }
            ExpressionNode::Operator(operator_node) => {
                let mut arg_types = vec![];
                let mut errors = vec![];

                let (left_type, left_errors) =
                    self.check_expression(&mut operator_node.left, symbols);
                errors.extend(left_errors);

                arg_types.push(left_type.clone().map(|t| t.types.first().cloned()).flatten());

                let (right_type, right_errors) =
                    self.check_expression(&mut operator_node.right, symbols);
                errors.extend(right_errors);

                arg_types.push(right_type.clone().map(|t| t.types.first().cloned()).flatten());

                let name = operator_node.operator.value.clone().unwrap();

                let arg_type_tokens: Vec<Token> = arg_types
                    .iter()
                    .filter_map(|t| t.clone())
                    .collect();

                if (arg_type_tokens.len() != arg_types.len())
                    || (arg_type_tokens.len() != 2)
                {
                    errors.push(TypecheckerError::UndefinedOperator {
                        token: operator_node.operator.clone(),
                        left_type: arg_types[0].clone(),
                        right_type: arg_types[1].clone(),
                    });

                    return (None, errors);
                }

                let Some(operator_type) =
                    symbols
                        .get(&name)
                        .or(match self.defines.get(&(name, arg_type_tokens)) {
                            Some(DefineNode::Operator(node)) => Some(&node.type_node),
                            _ => None,
                        })
                else {
                    errors.push(TypecheckerError::UndefinedOperator {
                        token: operator_node.operator.clone(),
                        left_type: arg_types[0].clone(),
                        right_type: arg_types[1].clone(),
                    });

                    return (None, errors);
                };

                let type_node = Some(TypeNode::new(vec![operator_type.types[2].clone()]));

                operator_node.type_node = type_node.clone();

                (type_node, errors)
            }
            ExpressionNode::Paren(paren_node) => {
                let (type_node, paren_errors) =
                    self.check_expression(&mut paren_node.expression, symbols);

                paren_node.type_node = type_node.clone();

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
                let name = symbol.value.clone().unwrap();
                if let hash_map::Entry::Vacant(e) = symbols.entry(name) {
                    e.insert(quantifier_node.type_node.clone());
                } else {
                    errors.push(TypecheckerError::RedefinedVariable(symbol.clone()));
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
                    if left_type.types.len() != right_type.types.len()
                        || left_type
                            .types
                            .iter()
                            .zip(right_type.types.iter())
                            .any(|(l, r)| l.value != r.value)
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
                        token.value.clone().unwrap()
                    );
                }
                TypecheckerError::UndefinedLiteral(token) => {
                    eprintln!(
                        "{}, Literal is not defined \"{}\"",
                        self.sourcemap.format_pos(token),
                        token.value.clone().unwrap()
                    );
                }
                TypecheckerError::UndefinedVariable(token) => {
                    eprintln!(
                        "{}, Variable is not defined {}",
                        self.sourcemap.format_pos(token),
                        token.value.clone().unwrap()
                    );
                }
                TypecheckerError::UndefinedFunction { token, arg_types } => {
                    eprintln!(
                        "{}, Function {} with arguments {} is not defined",
                        self.sourcemap.format_pos(token),
                        token.value.clone().unwrap(),
                        arg_types
                            .iter()
                            .map(|t| t.clone().map(|t| t.value.clone().unwrap()).unwrap_or("?".to_string()))
                            .collect::<Vec<_>>()
                            .join(", ")
                    );
                }
                TypecheckerError::UndefinedOperator { token, left_type, right_type } => {
                    eprintln!(
                        "{}, Operator {} is not defined with left type {} and right type {}",
                        self.sourcemap.format_pos(token),
                        token.value.clone().unwrap(),
                        left_type.clone().map(|t| t.value.clone().unwrap()).unwrap_or("?".to_string()),
                        right_type.clone().map(|t| t.value.clone().unwrap()).unwrap_or("?".to_string())
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
                        expected,
                        found,
                    );
                }
                TypecheckerError::RedefinedVariable(token) => {
                    eprintln!(
                        "{}, Variable is already defined {}",
                        self.sourcemap.format_pos(token),
                        token.value.clone().unwrap()
                    );
                }
                TypecheckerError::RedefinedFunction(token) => {
                    eprintln!(
                        "{}, Function is already defined {}",
                        self.sourcemap.format_pos(token),
                        token.value.clone().unwrap()
                    );
                }
                TypecheckerError::RedefinedOperator(token) => {
                    eprintln!(
                        "{}, Operator is already defined {}",
                        self.sourcemap.format_pos(token),
                        token.value.clone().unwrap()
                    );
                }
                TypecheckerError::RedefinedType(token) => {
                    eprintln!(
                        "{}, Type is already defined {}",
                        self.sourcemap.format_pos(token),
                        token.value.clone().unwrap()
                    );
                }
            }
        }
    }
}
