use std::collections::HashMap;

use crate::{
    lexer::{SourceMap, Token, TokenKind},
    parser::{
        DefineFunctionNode, DefineNode, DefineSetNode, ExpressionNode, ImplicationNode, SetNode,
        StatementNode, TypeNode,
    },
};

pub const FUNCTION_SUCC: &str = "succ";
pub const TYPE_N: &str = "N";

pub enum TypecheckerError {
    UndefinedType(Token),
    UndefinedLiteral(Token),
    UndefinedVariable(Token),
    UndefinedFunction(Token),
    UndefinedOperator(Token),
    ArgumentTypeMissmatch {
        function: Token,
        argument: ExpressionNode,
        expected: TypeNode,
        found: TypeNode,
    },
    OperatorTypeMissmatch {
        operator: Token,
        expected: TypeNode,
        found: TypeNode,
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
    defines: HashMap<String, DefineNode>,
}

impl Typechecker {
    pub fn new(defines: Vec<DefineNode>, sourcemap: &SourceMap) -> (Self, Vec<TypecheckerError>) {
        let mut mapping = HashMap::new();

        // def N = { }
        mapping.insert(
            TYPE_N.to_string(),
            DefineNode::Set(DefineSetNode::new(
                Token::value(TokenKind::Identifier, TYPE_N),
                SetNode::new(vec![]),
            )),
        );

        // def succ : N -> N
        mapping.insert(
            FUNCTION_SUCC.to_string(),
            DefineNode::Function(DefineFunctionNode::new(
                Token::value(TokenKind::Identifier, FUNCTION_SUCC),
                TypeNode::new(vec![
                    Token::value(TokenKind::Type, TYPE_N),
                    Token::value(TokenKind::Type, TYPE_N),
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

            if typechecker.defines.contains_key(&name) {
                errors.push(match &define {
                    DefineNode::Set(_) => TypecheckerError::RedefinedType(symbol),
                    DefineNode::Function(_) => TypecheckerError::RedefinedFunction(symbol),
                    DefineNode::Operator(_) => TypecheckerError::RedefinedOperator(symbol),
                });
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

            typechecker.defines.insert(name, define.clone());
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
    ) -> (Option<TypeNode>, Vec<TypecheckerError>) {
        match expression {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(number_node) => {
                let type_node = Some(TypeNode::new(vec![Token::value(TokenKind::Type, TYPE_N)]));

                number_node.type_node = type_node.clone();

                (type_node, vec![])
            }
            ExpressionNode::Literal(literal_node) => {
                for (symbol, define) in &self.defines {
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
                let name = function_node.name.value.clone().unwrap();

                let Some(function_type) = symbols.get(&name).or(match self.defines.get(&name) {
                    Some(DefineNode::Function(node)) => Some(&node.type_node),
                    _ => None,
                }) else {
                    return (
                        None,
                        vec![TypecheckerError::UndefinedFunction(
                            function_node.name.clone(),
                        )],
                    );
                };

                let (function_type, arg_types) = function_type.types.split_last().unwrap();
                let mut errors = vec![];

                for (i, arg) in function_node.arguments.iter_mut().enumerate() {
                    let (arg_type, arg_errors) = self.check_expression(arg, symbols);
                    errors.extend(arg_errors);

                    let Some(arg_type) = arg_type else {
                        continue;
                    };

                    if arg_type.types.len() != 1 || arg_types[i].value != arg_type.types[0].value {
                        errors.push(TypecheckerError::ArgumentTypeMissmatch {
                            function: function_node.name.clone(),
                            argument: arg.clone(),
                            expected: TypeNode::new(vec![arg_types[i].clone()]),
                            found: arg_type,
                        });
                    }
                }

                let type_node = Some(TypeNode::new(vec![function_type.clone()]));

                function_node.type_node = type_node.clone();

                (type_node, errors)
            }
            ExpressionNode::Operator(operator_node) => {
                let operator = operator_node.operator.value.clone().unwrap();
                let mut errors = vec![];

                let Some(operator_type) =
                    symbols
                        .get(&operator)
                        .or(match self.defines.get(&operator) {
                            Some(DefineNode::Operator(node)) => Some(&node.type_node),
                            _ => None,
                        })
                else {
                    errors.push(TypecheckerError::UndefinedOperator(
                        operator_node.operator.clone(),
                    ));

                    let (_, left_errors) = self.check_expression(&mut operator_node.left, symbols);
                    errors.extend(left_errors);
                    let (_, right_errors) =
                        self.check_expression(&mut operator_node.right, symbols);
                    errors.extend(right_errors);

                    return (None, errors);
                };

                let (left_type, left_errors) =
                    self.check_expression(&mut operator_node.left, symbols);
                errors.extend(left_errors);
                if let Some(left_type) = left_type {
                    if left_type.types.len() != 1
                        || left_type.types[0].value != operator_type.types[0].value
                    {
                        errors.push(TypecheckerError::OperatorTypeMissmatch {
                            operator: operator_node.operator.clone(),
                            expected: TypeNode::new(vec![operator_type.types[0].clone()]),
                            found: left_type,
                        });
                    }
                }

                let (right_type, right_errors) =
                    self.check_expression(&mut operator_node.right, symbols);
                errors.extend(right_errors);
                if let Some(right_type) = right_type {
                    if right_type.types.len() != 1
                        || right_type.types[0].value != operator_type.types[1].value
                    {
                        errors.push(TypecheckerError::OperatorTypeMissmatch {
                            operator: operator_node.operator.clone(),
                            expected: TypeNode::new(vec![operator_type.types[1].clone()]),
                            found: right_type,
                        });
                    }
                }

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
                if symbols.contains_key(&name) {
                    errors.push(TypecheckerError::RedefinedVariable(symbol.clone()));
                } else {
                    symbols.insert(name, quantifier_node.type_node.clone());
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
                },
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
                TypecheckerError::UndefinedFunction(token) => {
                    eprintln!(
                        "{}, Function is not defined {}",
                        self.sourcemap.format_pos(token),
                        token.value.clone().unwrap()
                    );
                }
                TypecheckerError::UndefinedOperator(token) => {
                    eprintln!(
                        "{}, Operator is not defined {}",
                        self.sourcemap.format_pos(token),
                        token.value.clone().unwrap()
                    );
                }
                TypecheckerError::ArgumentTypeMissmatch {
                    function,
                    argument,
                    expected,
                    found,
                } => {
                    eprintln!(
                        "{}, Function {}: Expected Type {} but found Type {} for argument ({})",
                        self.sourcemap.format_pos(&argument.token()),
                        function.value.clone().unwrap(),
                        expected,
                        found,
                        argument,
                    );
                }
                TypecheckerError::OperatorTypeMissmatch {
                    operator,
                    expected,
                    found,
                } => {
                    eprintln!(
                        "{}, Operator {}: Expected Type {} but found Type {}",
                        self.sourcemap.format_pos(operator),
                        operator.value.clone().unwrap(),
                        expected,
                        found,
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
