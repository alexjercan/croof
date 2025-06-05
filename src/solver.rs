use std::{collections::{HashMap, HashSet, VecDeque}, error::Error};

use crate::{
    lexer::{Token, TokenKind},
    parser::{
        ExpressionNode, FunctionNode, ImplicationNode, NumberNode, OperatorNode, ParenNode,
        RelationKind, RelationNode, StatementNode,
    }, typechecker::FUNCTION_SUCC,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolverError {
    Todo(String),
}

pub struct Solver {
    implications: Vec<ImplicationNode>,
}

fn create_mapping_helper(
    from: &ExpressionNode,
    to: &ExpressionNode,
    mapping: &mut HashMap<ExpressionNode, ExpressionNode>,
) -> bool {
    match to {
        ExpressionNode::Set(_) => todo!(),
        ExpressionNode::Type(_) => todo!(),
        ExpressionNode::Number(to_node) => match from {
            ExpressionNode::Number(from_node) => to_node.value == from_node.value,
            _ => false,
        },
        ExpressionNode::Variable(_) => {
            let has_mapping = mapping.contains_key(to);
            let should_substitute = !has_mapping || mapping.get(to) == Some(from);

            if !has_mapping {
                mapping.insert(to.clone(), from.clone());
            }

            should_substitute
        }
        ExpressionNode::Function(to_node) => {
            match from {
                ExpressionNode::Function(function_node) => {
                    to_node.name == function_node.name
                        && to_node.arguments.len() == function_node.arguments.len()
                        && to_node.arguments.iter().zip(&function_node.arguments).all(
                            |(to_arg, from_arg)| create_mapping_helper(from_arg, to_arg, mapping),
                        )
                }
                _ => false,
            }
        }
        ExpressionNode::Operator(to_node) => match from {
            ExpressionNode::Operator(operator_node) => {
                to_node.operator == operator_node.operator
                    && create_mapping_helper(&operator_node.left, &to_node.left, mapping)
                    && create_mapping_helper(&operator_node.right, &to_node.right, mapping)
            }
            _ => false,
        },
        ExpressionNode::Paren(to_node) => match from {
            ExpressionNode::Paren(paren_node) => {
                create_mapping_helper(&paren_node.expression, &to_node.expression, mapping)
            }
            _ => false,
        },
    }
}

fn create_mapping(
    from: &ExpressionNode,
    to: &ExpressionNode,
) -> Option<HashMap<ExpressionNode, ExpressionNode>> {
    let mut mapping = HashMap::new();
    if create_mapping_helper(from, to, &mut mapping) {
        Some(mapping)
    } else {
        None
    }
}

fn apply_mapping(
    expression: &ExpressionNode,
    mapping: &HashMap<ExpressionNode, ExpressionNode>,
) -> Option<ExpressionNode> {
    match expression {
        ExpressionNode::Set(_) => todo!(),
        ExpressionNode::Type(_) => todo!(),
        ExpressionNode::Number(_) => Some(expression.clone()),
        ExpressionNode::Variable(_) => mapping.get(expression).cloned(),
        ExpressionNode::Function(function_node) => {
            let args = function_node
                .arguments
                .iter()
                .map(|arg| apply_mapping(arg, mapping))
                .collect::<Option<Vec<ExpressionNode>>>()?;

            Some(ExpressionNode::Function(FunctionNode::new(
                function_node.name.clone(),
                args,
            )))
        }
        ExpressionNode::Operator(operator_node) => {
            let left = apply_mapping(&operator_node.left, mapping)?;
            let right = apply_mapping(&operator_node.right, mapping)?;

            Some(ExpressionNode::Operator(OperatorNode::new(
                operator_node.operator.clone(),
                left,
                right,
            )))
        }
        ExpressionNode::Paren(paren_node) => {
            let expr = apply_mapping(&paren_node.expression, mapping)?;
            Some(ExpressionNode::Paren(ParenNode::new(expr)))
        }
    }
}

fn substitute_helper(
    expression: &ExpressionNode,
    implication: &ImplicationNode,
    substitutions: &mut Vec<ExpressionNode>,
) {
    let StatementNode::Relation(relation) = &implication.conclusion[0] else {
        todo!("Only single expression conclusions are supported for now");
    };

    match expression {
        ExpressionNode::Set(_) => todo!(),
        ExpressionNode::Type(_) => todo!(),
        ExpressionNode::Number(_) => {
            if let Some(mapping) = create_mapping(expression, &relation.left) {
                if let Some(substituted) = apply_mapping(&relation.right, &mapping) {
                    substitutions.push(substituted);
                }
            }
        }
        ExpressionNode::Variable(_) => {
            if let Some(mapping) = create_mapping(expression, &relation.left) {
                if let Some(substituted) = apply_mapping(&relation.right, &mapping) {
                    substitutions.push(substituted);
                }
            }
        }
        ExpressionNode::Function(expr_node) => {
            for (i, arg) in expr_node.arguments.iter().enumerate() {
                let arg_substitutions = substitute(arg, implication);

                for substituted in arg_substitutions {
                    let mut new_expr = expr_node.clone();
                    new_expr.arguments[i] = substituted;
                    substitutions.push(ExpressionNode::Function(new_expr.clone()));
                }
            }

            if let Some(mapping) = create_mapping(expression, &relation.left) {
                if let Some(substituted) = apply_mapping(&relation.right, &mapping) {
                    substitutions.push(substituted);
                }
            }
        }
        ExpressionNode::Operator(expr_node) => {
            let left_substitutions = substitute(&expr_node.left, implication);
            for left_substituted in left_substitutions {
                let mut new_expr = expr_node.clone();
                *new_expr.left = left_substituted;
                substitutions.push(ExpressionNode::Operator(new_expr.clone()));
            }

            let right_substitutions = substitute(&expr_node.right, implication);
            for right_substituted in right_substitutions {
                let mut new_expr = expr_node.clone();
                *new_expr.right = right_substituted;
                substitutions.push(ExpressionNode::Operator(new_expr.clone()));
            }

            if let Some(mapping) = create_mapping(expression, &relation.left) {
                if let Some(substituted) = apply_mapping(&relation.right, &mapping) {
                    substitutions.push(substituted);
                }
            }
        }
        ExpressionNode::Paren(expr_node) => {
            let expr_substitutions = substitute(&expr_node.expression, implication);
            for substituted in expr_substitutions {
                substitutions.push(ExpressionNode::Paren(ParenNode::new(substituted)));
            }

            if let Some(mapping) = create_mapping(expression, &relation.left) {
                if let Some(substituted) = apply_mapping(&relation.right, &mapping) {
                    substitutions.push(substituted);
                }
            }
        }
    }
}

fn substitute(expression: &ExpressionNode, implication: &ImplicationNode) -> Vec<ExpressionNode> {
    let mut substitutions = Vec::new();
    substitute_helper(expression, implication, &mut substitutions);

    substitutions
}

fn substitute_builtin_helper(
    expression: &ExpressionNode,
    substitutions: &mut Vec<(ExpressionNode, ImplicationNode)>,
) {
    match expression {
        ExpressionNode::Set(set_node) => todo!(),
        ExpressionNode::Type(type_node) => todo!(),
        ExpressionNode::Number(expr_node) => {
            let value = expr_node.value.value.clone().unwrap();
            let value = value.parse::<u64>().unwrap();
            if value == 0 {
                return;
            }

            let substitution = ExpressionNode::Function(FunctionNode::new(
                Token::value(TokenKind::Identifier, FUNCTION_SUCC),
                vec![ExpressionNode::Number(NumberNode::new(Token::value(
                    TokenKind::Number,
                    (value - 1).to_string(),
                )))],
            ));

            let implication = ImplicationNode::new(
                vec![],
                vec![StatementNode::Relation(RelationNode::new(
                    RelationKind::Equality,
                    Token::new(TokenKind::Equal),
                    expression.clone(),
                    substitution.clone(),
                ))],
            );

            substitutions.push((substitution.clone(), implication));
        }
        ExpressionNode::Variable(_) => {}
        ExpressionNode::Function(expr_node) => {
            match expr_node.name.value.clone().unwrap().as_ref() {
                FUNCTION_SUCC => {
                    match expr_node.arguments.first().unwrap() {
                        ExpressionNode::Number(number_node) => {
                            let value = number_node.value.value.clone().unwrap().parse::<u64>().unwrap();

                            let substitution = ExpressionNode::Number(NumberNode::new(Token::value(
                                TokenKind::Number,
                                (value + 1).to_string(),
                            )));

                            let implication = ImplicationNode::new(
                                vec![],
                                vec![StatementNode::Relation(RelationNode::new(
                                    RelationKind::Equality,
                                    Token::new(TokenKind::Equal),
                                    expression.clone(),
                                    substitution.clone(),
                                ))],
                            );

                            substitutions.push((substitution.clone(), implication));
                        },
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        ExpressionNode::Operator(expr_node) => {
            let left_substitutions = substitute_builtin(&expr_node.left);
            for (left_expr, left_impl) in left_substitutions {
                let mut new_expr = expr_node.clone();
                *new_expr.left = left_expr;
                substitutions.push((ExpressionNode::Operator(new_expr.clone()), left_impl));
            }

            let right_substitutions = substitute_builtin(&expr_node.right);
            for (right_expr, right_impl) in right_substitutions {
                let mut new_expr = expr_node.clone();
                *new_expr.right = right_expr;
                substitutions.push((ExpressionNode::Operator(new_expr.clone()), right_impl));
            }
        },
        ExpressionNode::Paren(_) => {}
    }
}

fn substitute_builtin(expression: &ExpressionNode) -> Vec<(ExpressionNode, ImplicationNode)> {
    let mut substitutions = Vec::new();
    substitute_builtin_helper(expression, &mut substitutions);

    substitutions
}

fn trace_steps(
    parent: &HashMap<ExpressionNode, (ExpressionNode, ImplicationNode)>,
    expression: &ExpressionNode,
) -> Vec<(ExpressionNode, ImplicationNode)> {
    let mut steps = Vec::new();
    let mut current = expression.clone();

    while let Some((parent_expression, implication)) = parent.get(&current) {
        steps.push((parent_expression.clone(), implication.clone()));
        current = parent_expression.clone();
    }

    steps.reverse();
    steps
}

impl Solver {
    pub fn new(implications: Vec<ImplicationNode>) -> Self {
        Solver { implications }
    }

    fn solve_dfs_helper(
        &self,
        expression: &ExpressionNode,
        visited: &mut HashSet<ExpressionNode>,
        parent: &mut HashMap<ExpressionNode, (ExpressionNode, ImplicationNode)>,
        depth: usize,
    ) {
        if depth > 50 {
            return; // Prevent deep recursion
        }

        visited.insert(expression.clone());

        for (substitution, implication) in substitute_builtin(expression) {
            if !visited.contains(&substitution) {
                parent.insert(substitution.clone(), (expression.clone(), implication));
                self.solve_dfs_helper(&substitution, visited, parent, depth + 1);
            }
        }

        for implication in &self.implications {
            for substitution in substitute(expression, implication) {
                if !visited.contains(&substitution) {
                    parent.insert(
                        substitution.clone(),
                        (expression.clone(), implication.clone()),
                    );
                    self.solve_dfs_helper(&substitution, visited, parent, depth + 1);
                }
            }
        }
    }

    pub fn solve_bfs(
        &self,
        expression: &ExpressionNode,
    ) -> Result<(Vec<(ExpressionNode, ImplicationNode)>, ExpressionNode), SolverError> {
        let mut visited = HashSet::new();
        let mut parent = HashMap::new();
        let mut queue = VecDeque::new();

        queue.push_back(expression.clone());

        while let Some(expression) = queue.pop_front() {
            if expression.degree() == 0 {
                let steps = trace_steps(&parent, &expression);

                return Ok((steps, expression.clone()));
            }

            visited.insert(expression.clone());

            for (substitution, implication) in substitute_builtin(&expression) {
                if !visited.contains(&substitution) {
                    parent.insert(substitution.clone(), (expression.clone(), implication));

                    queue.push_back(substitution);
                }
            }

            for implication in &self.implications {
                for substitution in substitute(&expression, implication) {
                    if !visited.contains(&substitution) {
                        parent.insert(
                            substitution.clone(),
                            (expression.clone(), implication.clone()),
                        );
                        queue.push_back(substitution);
                    }
                }
            }
        }

        Err(SolverError::Todo(format!("No solution was found for {}", expression)))
    }

    pub fn solve_dfs(
        &self,
        expression: &ExpressionNode,
    ) -> Result<(Vec<(ExpressionNode, ImplicationNode)>, ExpressionNode), SolverError> {
        let mut visited = HashSet::new();
        let mut parent = HashMap::new();

        self.solve_dfs_helper(expression, &mut visited, &mut parent, 0);

        let result = visited
            .iter()
            .min_by_key(|e| e.degree())
            .ok_or(SolverError::Todo("No solution found".to_string()))?;
        let steps = trace_steps(&parent, result);

        Ok((steps, result.clone()))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        lexer::{Token, TokenKind},
        parser::{
            ExpressionNode, FunctionNode, ImplicationNode, NumberNode, OperatorNode, ParenNode,
            RelationKind, RelationNode, StatementNode, VariableNode,
        },
    };

    #[test]
    fn test_create_mapping_number_number() {
        // Arrange
        let from = ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42")));
        let to = ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42")));

        // Act
        let mapping = create_mapping(&from, &to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping.len(), 0);
    }

    #[test]
    fn test_create_mapping_variable_number() {
        // Arrange
        let from =
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x")));
        let to = ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42")));

        // Act
        let mapping = create_mapping(&from, &to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_function_number() {
        // Arrange
        let from = ExpressionNode::Function(FunctionNode::new(
            Token::value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::new(Token::value(
                TokenKind::Number,
                "42",
            )))],
        ));
        let to = ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42")));

        // Act
        let mapping = create_mapping(&from, &to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_number_variable() {
        // Arrange
        let from = ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42")));
        let to =
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x")));
        let expected = HashMap::from([(
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x"))),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42"))),
        )]);

        // Act
        let mapping = create_mapping(&from, &to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_variable_variable() {
        // Arrange
        let from =
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x")));
        let to =
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "y")));
        let expected = HashMap::from([(
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "y"))),
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x"))),
        )]);

        // Act
        let mapping = create_mapping(&from, &to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_function_variable() {
        // Arrange
        let from = ExpressionNode::Function(FunctionNode::new(
            Token::value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::new(Token::value(
                TokenKind::Number,
                "42",
            )))],
        ));
        let to =
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x")));
        let expected = HashMap::from([(
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x"))),
            ExpressionNode::Function(FunctionNode::new(
                Token::value(TokenKind::Identifier, "f"),
                vec![ExpressionNode::Number(NumberNode::new(Token::value(
                    TokenKind::Number,
                    "42",
                )))],
            )),
        )]);

        // Act
        let mapping = create_mapping(&from, &to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_operator_variable() {
        // Arrange
        let from = ExpressionNode::Operator(OperatorNode::new(
            Token::value(TokenKind::Operator, "+"),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42"))),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "1"))),
        ));
        let to =
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x")));
        let expected = HashMap::from([(
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x"))),
            ExpressionNode::Operator(OperatorNode::new(
                Token::value(TokenKind::Operator, "+"),
                ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42"))),
                ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "1"))),
            )),
        )]);

        // Act
        let mapping = create_mapping(&from, &to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_paren_variable() {
        // Arrange
        let from = ExpressionNode::Paren(ParenNode::new(ExpressionNode::Number(NumberNode::new(
            Token::value(TokenKind::Number, "42"),
        ))));
        let to =
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x")));
        let expected = HashMap::from([(
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x"))),
            ExpressionNode::Paren(ParenNode::new(ExpressionNode::Number(NumberNode::new(
                Token::value(TokenKind::Number, "42"),
            )))),
        )]);

        // Act
        let mapping = create_mapping(&from, &to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_number_function() {
        // Arrange
        let from = ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42")));
        let to = ExpressionNode::Function(FunctionNode::new(
            Token::value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::new(Token::value(
                TokenKind::Number,
                "42",
            )))],
        ));

        // Act
        let mapping = create_mapping(&from, &to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_function_function() {
        // Arrange
        let from = ExpressionNode::Function(FunctionNode::new(
            Token::value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::new(Token::value(
                TokenKind::Number,
                "42",
            )))],
        ));
        let to = ExpressionNode::Function(FunctionNode::new(
            Token::value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Variable(VariableNode::new(Token::value(
                TokenKind::Identifier,
                "x",
            )))],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x"))),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42"))),
        )]);

        // Act
        let mapping = create_mapping(&from, &to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_function_operator() {
        // Arrange
        let from = ExpressionNode::Function(FunctionNode::new(
            Token::value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::new(Token::value(
                TokenKind::Number,
                "42",
            )))],
        ));
        let to = ExpressionNode::Operator(OperatorNode::new(
            Token::value(TokenKind::Operator, "+"),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42"))),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "1"))),
        ));

        // Act
        let mapping = create_mapping(&from, &to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_operator_operator() {
        // Arrange
        let from = ExpressionNode::Operator(OperatorNode::new(
            Token::value(TokenKind::Operator, "+"),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42"))),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "1"))),
        ));
        let to = ExpressionNode::Operator(OperatorNode::new(
            Token::value(TokenKind::Operator, "+"),
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x"))),
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "y"))),
        ));
        let expected = HashMap::from([
            (
                ExpressionNode::Variable(VariableNode::new(Token::value(
                    TokenKind::Identifier,
                    "x",
                ))),
                ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42"))),
            ),
            (
                ExpressionNode::Variable(VariableNode::new(Token::value(
                    TokenKind::Identifier,
                    "y",
                ))),
                ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "1"))),
            ),
        ]);

        // Act
        let mapping = create_mapping(&from, &to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_variable_paren() {
        // Arrange
        let from =
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x")));
        let to = ExpressionNode::Paren(ParenNode::new(ExpressionNode::Number(NumberNode::new(
            Token::value(TokenKind::Number, "42"),
        ))));

        // Act
        let mapping = create_mapping(&from, &to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_paren_paren() {
        // Arrange
        let from = ExpressionNode::Paren(ParenNode::new(ExpressionNode::Number(NumberNode::new(
            Token::value(TokenKind::Number, "42"),
        ))));
        let to = ExpressionNode::Paren(ParenNode::new(ExpressionNode::Variable(
            VariableNode::new(Token::value(TokenKind::Identifier, "x")),
        )));
        let expected = HashMap::from([(
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x"))),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42"))),
        )]);

        // Act
        let mapping = create_mapping(&from, &to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_apply_mapping_number() {
        // Arrange
        let expression =
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42")));
        let mapping = HashMap::new();
        let expected =
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42")));

        // Act
        let result = apply_mapping(&expression, &mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }

    #[test]
    fn test_apply_mapping_variable() {
        // Arrange
        let expression =
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x")));
        let mapping = HashMap::from([(
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x"))),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42"))),
        )]);
        let expected =
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42")));

        // Act
        let result = apply_mapping(&expression, &mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }

    #[test]
    fn test_apply_mapping_function() {
        // Arrange
        let expression = ExpressionNode::Function(FunctionNode::new(
            Token::value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Variable(VariableNode::new(Token::value(
                TokenKind::Identifier,
                "x",
            )))],
        ));
        let mapping = HashMap::from([(
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x"))),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42"))),
        )]);
        let expected = ExpressionNode::Function(FunctionNode::new(
            Token::value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::new(Token::value(
                TokenKind::Number,
                "42",
            )))],
        ));

        // Act
        let result = apply_mapping(&expression, &mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }

    #[test]
    fn test_apply_mapping_operator() {
        // Arrange
        let expression = ExpressionNode::Operator(OperatorNode::new(
            Token::value(TokenKind::Operator, "+"),
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x"))),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "1"))),
        ));
        let mapping = HashMap::from([(
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x"))),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42"))),
        )]);
        let expected = ExpressionNode::Operator(OperatorNode::new(
            Token::value(TokenKind::Operator, "+"),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42"))),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "1"))),
        ));

        // Act
        let result = apply_mapping(&expression, &mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }

    #[test]
    fn test_apply_mapping_paren() {
        // Arrange
        let expression = ExpressionNode::Paren(ParenNode::new(ExpressionNode::Variable(
            VariableNode::new(Token::value(TokenKind::Identifier, "x")),
        )));
        let mapping = HashMap::from([(
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "x"))),
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42"))),
        )]);
        let expected = ExpressionNode::Paren(ParenNode::new(ExpressionNode::Number(
            NumberNode::new(Token::value(TokenKind::Number, "42")),
        )));

        // Act
        let result = apply_mapping(&expression, &mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }

    #[test]
    fn test_substitute_number_implication_id() {
        // Arrange
        let expression =
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42")));
        let implication = ImplicationNode::new(
            Vec::new(),
            vec![StatementNode::Relation(RelationNode::new(
                RelationKind::Equality,
                Token::new(TokenKind::Equal),
                ExpressionNode::Variable(VariableNode::new(Token::value(
                    TokenKind::Identifier,
                    "a",
                ))),
                ExpressionNode::Variable(VariableNode::new(Token::value(
                    TokenKind::Identifier,
                    "a",
                ))),
            ))],
        );
        let expected = vec![ExpressionNode::Number(NumberNode::new(Token::value(
            TokenKind::Number,
            "42",
        )))];

        // Act
        let substitutions = substitute(&expression, &implication);

        // Assert
        assert_eq!(substitutions, expected);
    }

    #[test]
    fn test_substitute_operator_implication_commutative() {
        // Arrange
        let expression = ExpressionNode::Operator(OperatorNode::new(
            Token::value(TokenKind::Operator, "+"),
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "1"))),
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "2"))),
        ));
        let implication = ImplicationNode::new(
            Vec::new(),
            vec![StatementNode::Relation(RelationNode::new(
                RelationKind::Equality,
                Token::new(TokenKind::Equal),
                ExpressionNode::Operator(OperatorNode::new(
                    Token::value(TokenKind::Operator, "+"),
                    ExpressionNode::Variable(VariableNode::new(Token::value(
                        TokenKind::Identifier,
                        "b",
                    ))),
                    ExpressionNode::Variable(VariableNode::new(Token::value(
                        TokenKind::Identifier,
                        "a",
                    ))),
                )),
                ExpressionNode::Operator(OperatorNode::new(
                    Token::value(TokenKind::Operator, "+"),
                    ExpressionNode::Variable(VariableNode::new(Token::value(
                        TokenKind::Identifier,
                        "a",
                    ))),
                    ExpressionNode::Variable(VariableNode::new(Token::value(
                        TokenKind::Identifier,
                        "b",
                    ))),
                )),
            ))],
        );
        let expected = vec![ExpressionNode::Operator(OperatorNode::new(
            Token::value(TokenKind::Operator, "+"),
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "2"))),
            ExpressionNode::Variable(VariableNode::new(Token::value(TokenKind::Identifier, "1"))),
        ))];

        // Act
        let substitutions = substitute(&expression, &implication);

        // Assert
        assert_eq!(substitutions, expected);
    }
}
