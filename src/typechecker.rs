use std::collections::HashMap;

use crate::{lexer::{SourceMap, Token, TokenKind}, parser::{DefineNode, ExpressionNode, ImplicationNode, StatementNode, TypeNode}};

pub const FUNCTION_SUCC: &str = "succ";
pub const TYPE_N: &str = "N";

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypecheckerError {
    Todo(String),
}

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

    fn check_expression(
        &self,
        expression: &ExpressionNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> Result<TypeNode, TypecheckerError> {
        match expression {
            ExpressionNode::Set(set_node) => todo!(),
            ExpressionNode::Type(type_node) => todo!(),
            ExpressionNode::Number(_) => Ok(TypeNode::new(vec![Token::value(TokenKind::Type, TYPE_N)])),
            ExpressionNode::Variable(variable_node) => {
                symbols
                    .get(&variable_node.name.value.clone().unwrap())
                    .ok_or(TypecheckerError::Todo(format!(
                        "{}, Variable is not defined {}",
                        self.sourcemap.format_pos(&variable_node.name),
                        variable_node.name.value.clone().unwrap()
                    )))
                    .cloned()
            }
            ExpressionNode::Function(function_node) => {
                let function_type = symbols
                    .get(&function_node.name.value.clone().unwrap())
                    .or(self.defines.get(&function_node.name.value.clone().unwrap()))
                    .ok_or(TypecheckerError::Todo(format!(
                        "{}, Function is not defined {}",
                        self.sourcemap.format_pos(&function_node.name),
                        function_node.name.value.clone().unwrap()
                    )))?;
                let (function_type, arg_types) = function_type.types.split_last().unwrap();

                for (i, arg) in function_node.arguments.iter().enumerate() {
                    let arg_type = self.check_expression(arg, symbols)?;

                    if arg_type.types.len() != 1 || arg_types[i].value != arg_type.types[0].value {
                        return Err(TypecheckerError::Todo(format!(
                            "{}, Argument {} Type {} is different than Function Type {}",
                            self.sourcemap.format_pos(&function_node.name),
                            i,
                            arg_type,
                            arg_types[i].value.clone().unwrap()
                        )));
                    }
                }

                Ok(TypeNode::new(vec![function_type.clone()]))
            }
            ExpressionNode::Operator(operator_node) => {
                let operator_type = symbols
                    .get(&operator_node.operator.value.clone().unwrap())
                    .or(self.defines.get(&operator_node.operator.value.clone().unwrap()))
                    .ok_or(TypecheckerError::Todo(format!(
                        "{}, Operator is not defined {}",
                        self.sourcemap.format_pos(&operator_node.operator),
                        operator_node.operator.value.clone().unwrap()
                    )))?;

                let left_type = self.check_expression(&operator_node.left, symbols)?;
                if left_type.types.len() != 1 || left_type.types[0].value != operator_type.types[0].value {
                    return Err(TypecheckerError::Todo(format!(
                        "{}, Left Type {} is different than Operator Left Type {}",
                        self.sourcemap.format_pos(&operator_node.operator),
                        left_type,
                        operator_type.types[0].value.clone().unwrap()
                    )));
                }

                let right_type = self.check_expression(&operator_node.right, symbols)?;
                if right_type.types.len() != 1 || right_type.types[0].value != operator_type.types[1].value {
                    return Err(TypecheckerError::Todo(format!(
                        "{}, Right Type {} is different than Operator Right Type {}",
                        self.sourcemap.format_pos(&operator_node.operator),
                        left_type,
                        operator_type.types[1].value.clone().unwrap()
                    )));
                }

                Ok(TypeNode::new(vec![operator_type.types[2].clone()]))
            }
            ExpressionNode::Paren(paren_node) => {
                self.check_expression(&paren_node.expression, symbols)
            }
        }
    }

    fn check_statement(
        &self,
        statement: &StatementNode,
        symbols: &mut HashMap<String, TypeNode>,
    ) -> Result<(), TypecheckerError> {
        match statement {
            StatementNode::Quantifier(quantifier_node) => {
                symbols.insert(
                    quantifier_node.symbol.value.clone().unwrap(),
                    quantifier_node.type_node.clone(),
                );
            }
            StatementNode::Relation(relation_node) => {
                let left_type = self.check_expression(&relation_node.left, symbols)?;
                let right_type = self.check_expression(&relation_node.right, symbols)?;

                if !left_type.types.iter().zip(right_type.types.iter()).all(|(l, r)| l.value == r.value) {
                    return Err(TypecheckerError::Todo(format!(
                        "{}, Left Type {} is different than Right Type {}",
                        self.sourcemap.format_pos(&relation_node.token),
                        left_type,
                        right_type,
                    )));
                }
            }
        };

        Ok(())
    }

    pub fn check(&self, implication: &ImplicationNode) -> Result<(), TypecheckerError> {
        let mut symbols: HashMap<String, TypeNode> = HashMap::new();

        for condition in &implication.conditions {
            self.check_statement(condition, &mut symbols)?;
        }

        for conclusion in &implication.conclusion {
            self.check_statement(conclusion, &mut symbols)?;
        }

        Ok(())
    }
}
