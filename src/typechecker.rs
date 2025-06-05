use std::collections::HashMap;

use crate::{lexer::{SourceMap, Token, TokenKind}, parser::{DefineNode, ExpressionNode, ImplicationNode, StatementNode, TypeNode}};

pub const FUNCTION_SUCC: &str = "succ";
pub const TYPE_N: &str = "N";

pub struct Typechecker {
    sourcemap: SourceMap,
    defines: HashMap<String, TypeNode>,
}

impl Typechecker {
    pub fn new(defines: Vec<DefineNode>, sourcemap: &SourceMap) -> Self {
        let mut defines = defines
            .iter()
            .map(|define| (define.symbol.value.clone().unwrap(), define.type_node.clone()))
            .collect::<HashMap<_, _>>();

        // def succ : N -> N
        defines.insert(
            FUNCTION_SUCC.to_string(),
            TypeNode::new(
                vec![
                    Token::value(TokenKind::Type, TYPE_N),
                    Token::value(TokenKind::Type, TYPE_N),
                ]
            ),
        );

        Typechecker {
            sourcemap: sourcemap.clone(),
            defines,
        }
    }

    pub fn check_expression(
        &self,
        expression: &mut ExpressionNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> Option<TypeNode> {
        match expression {
            ExpressionNode::Set(set_node) => todo!(),
            ExpressionNode::Type(type_node) => todo!(),
            ExpressionNode::Number(number_node) => {
                let type_node = Some(TypeNode::new(vec![Token::value(TokenKind::Type, TYPE_N)]));

                number_node.type_node = type_node.clone();

                type_node
            },
            ExpressionNode::Variable(variable_node) => {
                let name = variable_node.name.value.clone().unwrap();

                let type_node = match symbols.get(&name) {
                    Some(type_node) => Some(type_node.clone()),
                    None => {
                        eprintln!(
                            "{}, Variable is not defined {}",
                            self.sourcemap.format_pos(&variable_node.name),
                            name
                        );
                        None
                    }
                };

                variable_node.type_node = type_node.clone();

                type_node
            }
            ExpressionNode::Function(function_node) => {
                let name = function_node.name.value.clone().unwrap();

                let Some(function_type) = symbols
                    .get(&name)
                    .or(self.defines.get(&name))
                else {
                    eprintln!(
                        "{}, Function is not defined {}",
                        self.sourcemap.format_pos(&function_node.name),
                        name
                    );
                    return None;
                };

                let (function_type, arg_types) = function_type.types.split_last().unwrap();

                for (i, arg) in function_node.arguments.iter_mut().enumerate() {
                    let Some(arg_type) = self.check_expression(arg, symbols) else {
                        continue
                    };

                    if arg_type.types.len() != 1 || arg_types[i].value != arg_type.types[0].value {
                        eprintln!(
                            "{}, Argument {} Type {} is different than Function Type {}",
                            self.sourcemap.format_pos(&function_node.name),
                            i,
                            arg_type,
                            arg_types[i].value.clone().unwrap()
                        );
                    }
                }

                let type_node = Some(TypeNode::new(vec![function_type.clone()]));

                function_node.type_node = type_node.clone();

                type_node
            }
            ExpressionNode::Operator(operator_node) => {
                let operator = operator_node.operator.value.clone().unwrap();

                let Some(operator_type) = symbols
                    .get(&operator)
                    .or(self.defines.get(&operator))
                else {
                    eprintln!(
                        "{}, Operator is not defined {}",
                        self.sourcemap.format_pos(&operator_node.operator),
                        operator
                    );
                    return None;
                };

                match self.check_expression(&mut operator_node.left, symbols) {
                    Some(left_type) => {
                        if left_type.types.len() != 1 || left_type.types[0].value != operator_type.types[0].value {
                            eprintln!(
                                "{}, Left Type {} is different than Operator {} Left Type {}",
                                self.sourcemap.format_pos(&operator_node.operator),
                                left_type,
                                operator,
                                operator_type.types[0].value.clone().unwrap()
                            );
                        }
                    }
                    None => {},
                }

                match self.check_expression(&mut operator_node.right, symbols) {
                    Some(right_type) => {
                        if right_type.types.len() != 1 || right_type.types[0].value != operator_type.types[1].value {
                            eprintln!(
                                "{}, Right Type {} is different than Operator {} Right Type {}",
                                self.sourcemap.format_pos(&operator_node.operator),
                                right_type,
                                operator,
                                operator_type.types[1].value.clone().unwrap()
                            );
                        }
                    }
                    None => {},
                }

                let type_node = Some(TypeNode::new(vec![operator_type.types[2].clone()]));

                operator_node.type_node = type_node.clone();

                type_node
            }
            ExpressionNode::Paren(paren_node) => {
                let type_node = self.check_expression(&mut paren_node.expression, symbols);

                paren_node.type_node = type_node.clone();

                type_node
            }
        }
    }

    fn check_statement(
        &self,
        statement: &mut StatementNode,
        symbols: &mut HashMap<String, TypeNode>,
    ) {
        match statement {
            StatementNode::Quantifier(quantifier_node) => {
                symbols.insert(
                    quantifier_node.symbol.value.clone().unwrap(),
                    quantifier_node.type_node.clone(),
                );
            }
            StatementNode::Relation(relation_node) => {
                let left_type = self.check_expression(&mut relation_node.left, symbols);
                let right_type = self.check_expression(&mut relation_node.right, symbols);

                match (left_type, right_type) {
                    (Some(left_type), Some(right_type)) => {
                        if left_type.types.len() != right_type.types.len() || left_type.types.iter().zip(right_type.types.iter()).any(|(l, r)| l.value != r.value) {
                            eprintln!(
                                "{}, Left Type {} is different than Right Type {}",
                                self.sourcemap.format_pos(&relation_node.token),
                                left_type,
                                right_type
                            );
                        }
                    }
                    _ => {}
                }
            }
        };
    }

    pub fn check(&self, implication: &mut ImplicationNode) {
        let mut symbols: HashMap<String, TypeNode> = HashMap::new();

        for condition in &mut implication.conditions {
            self.check_statement(condition, &mut symbols);
        }

        for conclusion in &mut implication.conclusion {
            self.check_statement(conclusion, &mut symbols);
        }
    }
}
