use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashMap, HashSet},
};

use crate::{
    lexer::{Token, TokenKind},
    parser::{
        ExpressionNode, FunctionNode, ImplicationNode, NumberNode, ParenNode, RelationKind,
        RelationNode, StatementNode, TypeNode,
    },
    typechecker::{FUNCTION_N, FUNCTION_NEG, FUNCTION_SUCC, FUNCTION_Z, TYPE_N, TYPE_Z},
};

pub type ProofStep = (ExpressionNode, ExpressionNode, ImplicationNode);
pub type SolverStep = (ExpressionNode, ImplicationNode, Vec<ProofStep>);

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpressionWeighted(ExpressionNode, i32);

impl PartialOrd for ExpressionWeighted {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ExpressionWeighted {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

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
    if from.type_node() != to.type_node() {
        return false;
    }

    match to {
        ExpressionNode::Set(_) => todo!(),
        ExpressionNode::Type(_) => todo!(),
        ExpressionNode::Number(to_node) => match from {
            ExpressionNode::Number(from_node) => to_node.value == from_node.value,
            _ => false,
        },
        ExpressionNode::Literal(to_node) => match from {
            ExpressionNode::Literal(from_node) => to_node.value == from_node.value,
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
        ExpressionNode::Literal(_) => Some(expression.clone()),
        ExpressionNode::Variable(_) => mapping.get(expression).cloned(),
        ExpressionNode::Function(node) => {
            let args = node
                .arguments
                .iter()
                .map(|arg| apply_mapping(arg, mapping))
                .collect::<Option<Vec<ExpressionNode>>>()?;

            let mut function_node = node.clone();
            function_node.arguments = args;

            Some(ExpressionNode::Function(function_node))
        }
        ExpressionNode::Operator(node) => {
            let left = apply_mapping(&node.left, mapping)?;
            let right = apply_mapping(&node.right, mapping)?;

            let mut operator_node = node.clone();
            operator_node.left = Box::new(left);
            operator_node.right = Box::new(right);

            Some(ExpressionNode::Operator(operator_node))
        }
        ExpressionNode::Paren(node) => {
            let expr = apply_mapping(&node.expression, mapping)?;
            let mut paren_node = node.clone();
            paren_node.expression = Box::new(expr);

            Some(ExpressionNode::Paren(paren_node))
        }
    }
}

fn substitute_builtin_helper(
    expression: &ExpressionNode,
    substitutions: &mut Vec<(ExpressionNode, ImplicationNode)>,
) {
    match expression {
        ExpressionNode::Set(_) => todo!(),
        ExpressionNode::Type(_) => todo!(),
        ExpressionNode::Number(expr_node) => {
            match expr_node
                .type_node
                .clone()
                .unwrap()
                .types
                .first()
                .unwrap()
                .value
                .clone()
                .unwrap()
                .as_ref()
            {
                TYPE_N => {
                    let value = expr_node.value.value.clone().unwrap();
                    let value = value.parse::<u64>().unwrap();
                    if value == 0 {
                        return;
                    }

                    let number = NumberNode::typed(
                        Token::value(TokenKind::Number, (value - 1).to_string()),
                        TypeNode::new(vec![Token::value(TokenKind::Type, TYPE_N)]),
                    );
                    let function = FunctionNode::typed(
                        Token::value(TokenKind::Identifier, FUNCTION_SUCC),
                        vec![ExpressionNode::Number(number.clone())],
                        TypeNode::new(vec![Token::value(TokenKind::Type, TYPE_N)]),
                    );
                    let substitution = ExpressionNode::Function(function);

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
                TYPE_Z => {}
                _ => todo!(),
            }
        }
        ExpressionNode::Literal(_) => {}
        ExpressionNode::Variable(_) => {}
        ExpressionNode::Function(expr_node) => {
            match expr_node.name.value.clone().unwrap().as_ref() {
                FUNCTION_N => {
                    if let ExpressionNode::Number(number_node) =
                        expr_node.arguments.first().unwrap()
                    {
                        let value = number_node
                            .value
                            .value
                            .clone()
                            .unwrap()
                            .parse::<u64>()
                            .unwrap();

                        let number = NumberNode::typed(
                            Token::value(TokenKind::Number, value.to_string()),
                            TypeNode::new(vec![Token::value(TokenKind::Type, TYPE_N)]),
                        );
                        let substitution = ExpressionNode::Number(number);

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
                }
                FUNCTION_SUCC => {
                    if let ExpressionNode::Number(number_node) =
                        expr_node.arguments.first().unwrap()
                    {
                        let value = number_node
                            .value
                            .value
                            .clone()
                            .unwrap()
                            .parse::<u64>()
                            .unwrap();

                        let number = NumberNode::typed(
                            Token::value(TokenKind::Number, (value + 1).to_string()),
                            TypeNode::new(vec![Token::value(TokenKind::Type, TYPE_N)]),
                        );
                        let substitution = ExpressionNode::Number(number);

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
                }
                FUNCTION_Z => {
                    if let ExpressionNode::Number(number_node) =
                        expr_node.arguments.first().unwrap()
                    {
                        let value = number_node
                            .value
                            .value
                            .clone()
                            .unwrap()
                            .parse::<u64>()
                            .unwrap();

                        let number = NumberNode::typed(
                            Token::value(TokenKind::Number, value.to_string()),
                            TypeNode::new(vec![Token::value(TokenKind::Type, TYPE_Z)]),
                        );
                        let substitution = ExpressionNode::Number(number);

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
                }
                FUNCTION_NEG => {
                    if let ExpressionNode::Number(number_node) =
                        expr_node.arguments.first().unwrap()
                    {
                        let value = number_node
                            .value
                            .value
                            .clone()
                            .unwrap()
                            .parse::<i64>()
                            .unwrap();

                        let number = NumberNode::typed(
                            Token::value(TokenKind::Number, (-value).to_string()),
                            TypeNode::new(vec![Token::value(TokenKind::Type, TYPE_Z)]),
                        );
                        let substitution = ExpressionNode::Number(number);

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
                }
                _ => {}
            }

            let mut new_expr = expr_node.clone();
            for (i, arg) in expr_node.arguments.iter().enumerate() {
                let arg_substitutions = substitute_builtin(arg);
                for (substituted, impl_node) in arg_substitutions {
                    new_expr.arguments[i] = substituted;
                    substitutions.push((ExpressionNode::Function(new_expr.clone()), impl_node));
                }
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
        }
        ExpressionNode::Paren(node) => {
            let expr_substitutions = substitute_builtin(&node.expression);
            for (substituted, impl_node) in expr_substitutions {
                substitutions.push((
                    ExpressionNode::Paren(ParenNode::new(substituted)),
                    impl_node,
                ));
            }
        }
    }
}

fn substitute_builtin(expression: &ExpressionNode) -> Vec<(ExpressionNode, ImplicationNode)> {
    let mut substitutions = Vec::new();
    substitute_builtin_helper(expression, &mut substitutions);

    substitutions
}

fn trace_steps(
    parent: &HashMap<ExpressionNode, SolverStep>,
    expression: &ExpressionNode,
) -> Vec<ProofStep> {
    let mut steps = Vec::new();
    let mut current = expression.clone();

    while let Some((parent_expression, implication, extra_steps)) = parent.get(&current) {
        steps.push((
            parent_expression.clone(),
            current.clone(),
            implication.clone(),
        ));
        steps.extend(extra_steps.clone());
        current = parent_expression.clone();
    }

    steps.reverse();

    steps
}

impl Solver {
    pub fn new(implications: Vec<ImplicationNode>) -> Self {
        Solver { implications }
    }

    fn substitute_helper(
        &self,
        expression: &ExpressionNode,
        implication: &ImplicationNode,
        substitutions: &mut Vec<(ExpressionNode, Vec<ProofStep>)>,
    ) {
        let StatementNode::Relation(relation) = &implication.conclusion[0] else {
            todo!("Only single expression conclusions are supported for now");
        };

        match expression {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(_) => {
                if let Some(mapping) = create_mapping(expression, &relation.left) {
                    if let Ok(steps) = self.proof_all(&implication.conditions, &mapping) {
                        if let Some(substituted) = apply_mapping(&relation.right, &mapping) {
                            substitutions.push((substituted, steps));
                        }
                    }
                }
            }
            ExpressionNode::Literal(_) => {
                if let Some(mapping) = create_mapping(expression, &relation.left) {
                    if let Ok(steps) = self.proof_all(&implication.conditions, &mapping) {
                        if let Some(substituted) = apply_mapping(&relation.right, &mapping) {
                            substitutions.push((substituted, steps));
                        }
                    }
                }
            }
            ExpressionNode::Variable(_) => {
                if let Some(mapping) = create_mapping(expression, &relation.left) {
                    if let Ok(steps) = self.proof_all(&implication.conditions, &mapping) {
                        if let Some(substituted) = apply_mapping(&relation.right, &mapping) {
                            substitutions.push((substituted, steps));
                        }
                    }
                }
            }
            ExpressionNode::Function(node) => {
                for (i, arg) in node.arguments.iter().enumerate() {
                    let arg_substitutions = self.substitute(arg, implication);

                    for (substituted, steps) in arg_substitutions {
                        let mut new_expr = node.clone();
                        new_expr.arguments[i] = substituted;
                        substitutions.push((ExpressionNode::Function(new_expr.clone()), steps));
                    }
                }

                if let Some(mapping) = create_mapping(expression, &relation.left) {
                    if let Ok(steps) = self.proof_all(&implication.conditions, &mapping) {
                        if let Some(substituted) = apply_mapping(&relation.right, &mapping) {
                            substitutions.push((substituted, steps));
                        }
                    }
                }
            }
            ExpressionNode::Operator(node) => {
                let left_substitutions = self.substitute(&node.left, implication);
                for (left_substituted, left_steps) in left_substitutions {
                    let mut new_expr = node.clone();
                    *new_expr.left = left_substituted;
                    substitutions.push((ExpressionNode::Operator(new_expr.clone()), left_steps));
                }

                let right_substitutions = self.substitute(&node.right, implication);
                for (right_substituted, right_steps) in right_substitutions {
                    let mut new_expr = node.clone();
                    *new_expr.right = right_substituted;
                    substitutions.push((ExpressionNode::Operator(new_expr.clone()), right_steps));
                }

                if let Some(mapping) = create_mapping(expression, &relation.left) {
                    if let Ok(steps) = self.proof_all(&implication.conditions, &mapping) {
                        if let Some(substituted) = apply_mapping(&relation.right, &mapping) {
                            substitutions.push((substituted, steps));
                        }
                    }
                }
            }
            ExpressionNode::Paren(node) => {
                let expr_substitutions = self.substitute(&node.expression, implication);
                for (substituted, steps) in expr_substitutions {
                    let mut new_expr = node.clone();
                    new_expr.expression = Box::new(substituted);
                    substitutions.push((ExpressionNode::Paren(new_expr), steps));
                }

                if let Some(mapping) = create_mapping(expression, &relation.left) {
                    if let Ok(steps) = self.proof_all(&implication.conditions, &mapping) {
                        if let Some(substituted) = apply_mapping(&relation.right, &mapping) {
                            substitutions.push((substituted, steps));
                        }
                    }
                }
            }
        }
    }

    fn substitute(
        &self,
        expression: &ExpressionNode,
        implication: &ImplicationNode,
    ) -> Vec<(ExpressionNode, Vec<ProofStep>)> {
        let mut substitutions = Vec::new();
        self.substitute_helper(expression, implication, &mut substitutions);

        substitutions
    }

    fn solve_astar(
        &self,
        expression: &ExpressionNode,
        is_target: impl Fn(&ExpressionNode) -> bool,
        heuristic: impl Fn(&ExpressionNode) -> i32,
    ) -> Result<(Vec<ProofStep>, ExpressionNode), SolverError> {
        let mut parent = HashMap::new();
        let mut queue: BinaryHeap<Reverse<ExpressionWeighted>> = BinaryHeap::new();
        let mut open_set: HashSet<ExpressionNode> = HashSet::new();

        let mut g_score: HashMap<ExpressionNode, i32> = HashMap::new();
        g_score.insert(expression.clone(), 0);

        let mut f_score: HashMap<ExpressionNode, i32> = HashMap::new();
        let h = heuristic(expression);
        f_score.insert(expression.clone(), h);

        queue.push(Reverse(ExpressionWeighted(expression.clone(), h)));
        open_set.insert(expression.clone());

        while let Some(Reverse(ExpressionWeighted(expression, _))) = queue.pop() {
            open_set.remove(&expression);

            if is_target(&expression) {
                let steps = trace_steps(&parent, &expression);

                return Ok((steps, expression.clone()));
            }

            for (substitution, implication, steps) in self.substitutions(&expression) {
                let d = expression.distance(&substitution);
                let tentative_g_score: i32 = g_score.get(&expression).unwrap_or(&i32::MAX) + d;
                if &tentative_g_score < g_score.get(&substitution).unwrap_or(&i32::MAX) {
                    parent.insert(
                        substitution.clone(),
                        (expression.clone(), implication.clone(), steps.clone()),
                    );
                    g_score.insert(substitution.clone(), tentative_g_score);
                    let f = tentative_g_score + heuristic(&substitution);
                    f_score.insert(substitution.clone(), f);
                    if !open_set.contains(&substitution) {
                        queue.push(Reverse(ExpressionWeighted(substitution.clone(), f)));
                        open_set.insert(substitution.clone());
                    }
                }
            }
        }

        Err(SolverError::Todo(format!(
            "No solution was found for {}",
            expression
        )))
    }

    pub fn solve(
        &self,
        expression: &ExpressionNode,
    ) -> Result<(Vec<ProofStep>, ExpressionNode), SolverError> {
        self.solve_astar(
            expression,
            |expr| expr.degree() == 0,
            |expr| expr.degree() as i32,
        )
    }

    pub fn proof(&self, relation: &RelationNode) -> Result<Vec<ProofStep>, SolverError> {
        let (mut right_steps, right_expr) = self.solve_astar(
            &relation.right,
            |expr| expr.degree() == 0,
            |expr| expr.degree() as i32,
        )?;

        match &relation.kind {
            RelationKind::Equality => self.solve_astar(
                &relation.left,
                |expr| expr == &right_expr,
                |expr| expr.degree() as i32,
            ),
            RelationKind::GreaterThan => self.solve_astar(
                &relation.left,
                |expr| expr > &right_expr,
                |expr| expr.degree() as i32,
            ),
        }
        .map(|(mut steps, _)| {
            steps.append(&mut right_steps);
            steps
        })
    }

    fn proof_all(
        &self,
        conditions: &[StatementNode],
        mapping: &HashMap<ExpressionNode, ExpressionNode>,
    ) -> Result<Vec<ProofStep>, SolverError> {
        let mut steps = Vec::new();

        for condition in conditions {
            if let StatementNode::Relation(relation) = condition {
                let left = apply_mapping(&relation.left, mapping);
                let right = apply_mapping(&relation.right, mapping);

                match (left, right) {
                    (Some(left), Some(right)) => {
                        let mut relation = relation.clone();
                        relation.left = left;
                        relation.right = right;

                        steps.extend(self.proof(&relation)?);
                        steps.reverse();
                    }
                    _ => {
                        return Err(SolverError::Todo(format!(
                            "Failed to apply mapping for relation: {}",
                            relation
                        )))
                    }
                }
            }
        }

        Ok(steps)
    }

    pub fn substitutions(&self, expression: &ExpressionNode) -> Vec<SolverStep> {
        let mut substitutions = Vec::new();

        for (substitution, implication) in substitute_builtin(expression) {
            substitutions.push((substitution, implication, vec![]));
        }

        for implication in &self.implications {
            for (substituted, steps) in self.substitute(expression, implication) {
                substitutions.push((substituted, implication.clone(), steps));
            }
        }

        substitutions
    }

    pub fn display_solution(
        &self,
        expression: &ExpressionNode,
        steps: &[ProofStep],
        result: &ExpressionNode,
    ) {
        println!("Expression: {}", expression);
        for (parent, target, implication) in steps {
            println!("  - {} => {} (apply {})", parent, target, implication);
        }
        println!("Result: {}", result);
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
        let expected = vec![(
            ExpressionNode::Number(NumberNode::new(Token::value(TokenKind::Number, "42"))),
            vec![],
        )];
        let solver = Solver::new(vec![implication.clone()]);

        // Act
        let substitutions = solver.substitute(&expression, &implication);

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
        let expected = vec![(
            ExpressionNode::Operator(OperatorNode::new(
                Token::value(TokenKind::Operator, "+"),
                ExpressionNode::Variable(VariableNode::new(Token::value(
                    TokenKind::Identifier,
                    "2",
                ))),
                ExpressionNode::Variable(VariableNode::new(Token::value(
                    TokenKind::Identifier,
                    "1",
                ))),
            )),
            vec![],
        )];
        let solver = Solver::new(vec![implication.clone()]);

        // Act
        let substitutions = solver.substitute(&expression, &implication);

        // Assert
        assert_eq!(substitutions, expected);
    }
}
