pub mod prelude {
    pub use super::{AstarSolver, ProofStep, Solver};
}

use std::collections::{BinaryHeap, HashMap, HashSet};

use crate::{
    ast::{EvaluationNode, ExpressionNode, ImplicationNode, RelationKind, StatementNode},
    matcher::Matcher,
};

/// ProofStep represents a step in a proof, consisting of an expression, its substitution, and the
/// implication used.
pub type ProofStep = (ExpressionNode, ExpressionNode, ImplicationNode);

/// SolverError represents errors that can occur during the solving process.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolverError {
    Todo(String),
}

/// Solver trait defines the interface for solving expressions and proving statements.
pub trait Solver {
    /// solve attempts to solve the given expression and returns a tuple of proof steps and the
    /// final expression.
    ///
    /// # Arguments
    /// * `expression` - The expression to solve.
    ///
    /// # Returns
    /// A Result containing a tuple of proof steps and the final expression, or a SolverError if
    /// the solving process fails.
    fn solve(
        &self,
        evaluation: &EvaluationNode,
    ) -> Result<(Vec<ProofStep>, ExpressionNode), SolverError>;

    /// prove attempts to prove a set of statements and returns a vector of proof steps.
    ///
    /// # Arguments
    /// * `statements` - A slice of statements to prove.
    ///
    /// # Returns
    /// A Result containing a vector of proof steps, or a SolverError if the proving process fails.
    fn prove(&self, statements: &[StatementNode]) -> Result<Vec<ProofStep>, SolverError>;
}

/// ExpressionWeighted is a wrapper around ExpressionNode that includes a weight for use in A*
/// search.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpressionWeighted(ExpressionNode, i32);

impl PartialOrd for ExpressionWeighted {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ExpressionWeighted {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // We want a min-heap, so we reverse the order
        self.1.cmp(&other.1).reverse()
    }
}

/// AstarSolver implements the A* algorithm for solving expressions and proving statements.
pub struct AstarSolver {
    matcher: Matcher,
    implications: Vec<ImplicationNode>,
}

impl AstarSolver {
    /// Creates a new AstarSolver instance with the given matcher and implications.
    pub fn new(matcher: Matcher, implications: Vec<ImplicationNode>) -> Self {
        AstarSolver {
            matcher,
            implications,
        }
    }

    fn trace_steps(
        &self,
        parent: &HashMap<ExpressionNode, (ExpressionNode, ImplicationNode, Vec<ProofStep>)>,
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

    fn substitutions(
        &self,
        expression: &ExpressionNode,
        conditions: &Vec<StatementNode>,
    ) -> Vec<(ExpressionNode, ImplicationNode, Vec<ProofStep>)> {
        let mut substitutions = Vec::new();

        for condition in conditions {
            let others: Vec<_> = conditions
                .iter()
                .filter(|&c| c != condition)
                .cloned()
                .collect();
            let implication = ImplicationNode::new(others.clone(), vec![condition.clone()]);

            for (substituted, steps) in self.matcher.substitute(expression, &others, condition) {
                if let Ok(steps) = self.prove(&steps) {
                    substitutions.push((substituted, implication.clone(), steps));
                }
            }
        }

        for implication in &self.implications {
            for conclusion in &implication.conclusion {
                for (substituted, steps) in
                    self.matcher
                        .substitute(expression, &implication.conditions, conclusion)
                {
                    if let Ok(steps) = self.prove(&steps) {
                        substitutions.push((substituted, implication.clone(), steps));
                    }
                }
            }
        }

        substitutions
    }

    fn solve_astar(
        &self,
        conditions: &Vec<StatementNode>,
        expression: &ExpressionNode,
        is_target: impl Fn(&ExpressionNode) -> bool,
        heuristic: impl Fn(&ExpressionNode) -> i32,
    ) -> Result<(Vec<ProofStep>, ExpressionNode), SolverError> {
        let mut parent: HashMap<ExpressionNode, (ExpressionNode, ImplicationNode, Vec<ProofStep>)> =
            HashMap::new();
        let mut queue: BinaryHeap<ExpressionWeighted> = BinaryHeap::new();
        let mut open_set: HashSet<ExpressionNode> = HashSet::new();

        let mut g_score: HashMap<ExpressionNode, i32> = HashMap::new();
        g_score.insert(expression.clone(), 0);

        let mut f_score: HashMap<ExpressionNode, i32> = HashMap::new();
        let h = heuristic(expression);
        f_score.insert(expression.clone(), h);

        queue.push(ExpressionWeighted(expression.clone(), h));
        open_set.insert(expression.clone());

        while let Some(ExpressionWeighted(expression, _)) = queue.pop() {
            open_set.remove(&expression);

            if is_target(&expression) {
                let steps = self.trace_steps(&parent, &expression);

                return Ok((steps, expression.clone()));
            }

            for (substitution, implication, steps) in self.substitutions(&expression, conditions) {
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
                        queue.push(ExpressionWeighted(substitution.clone(), f));
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

    fn prove_statement(&self, statement: &StatementNode) -> Result<Vec<ProofStep>, SolverError> {
        match statement {
            StatementNode::Relation(node) => {
                let (mut right_steps, right_expr) = self.solve_astar(
                    &vec![],
                    &node.right,
                    |expr| expr.degree() == 0,
                    |expr| expr.degree() as i32,
                )?;

                match &node.kind {
                    RelationKind::Equality => self.solve_astar(
                        &vec![],
                        &node.left,
                        |expr| expr == &right_expr,
                        |expr| expr.degree() as i32,
                    ),
                    RelationKind::GreaterThan => self.solve_astar(
                        &vec![],
                        &node.left,
                        |expr| expr > &right_expr,
                        |expr| expr.degree() as i32,
                    ),
                }
                .map(|(mut steps, _)| {
                    steps.append(&mut right_steps);
                    steps
                })
            }
            StatementNode::Quantifier(_) => Ok(vec![]),
            StatementNode::Builtin(_) => todo!("Handle built-in statements"),
        }
    }
}

impl Solver for AstarSolver {
    fn solve(
        &self,
        evaluation: &EvaluationNode,
    ) -> Result<(Vec<ProofStep>, ExpressionNode), SolverError> {
        self.solve_astar(
            &evaluation.conditions,
            &evaluation.expression,
            |expr| expr.degree() == 0,
            |expr| expr.degree() as i32,
        )
    }

    fn prove(&self, statements: &[StatementNode]) -> Result<Vec<ProofStep>, SolverError> {
        statements
            .iter()
            .map(|statement| self.prove_statement(statement))
            .collect::<Result<Vec<_>, SolverError>>()
            .map(|steps| steps.into_iter().flatten().collect())
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use crate::prelude::*;

    #[test]
    fn test_create_mapping_number_number() {
        // Arrange
        let from = ExpressionNode::Number(NumberNode::with_type(
            Token::with_value(TokenKind::Number, "42"),
            TYPE_N,
        ));
        let to = ExpressionNode::Number(NumberNode::with_type(
            Token::with_value(TokenKind::Number, "42"),
            TYPE_N,
        ));

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping.len(), 0);
    }

    #[test]
    fn test_create_mapping_variable_number() {
        // Arrange
        let from = ExpressionNode::Binding(BindingNode::new(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
        ));
        let to =
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")));

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_function_number() {
        // Arrange
        let from = ExpressionNode::Binding(BindingNode::new(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::new(Token::with_value(
                TokenKind::Number,
                "42",
            )))],
        ));
        let to =
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")));

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_number_variable() {
        // Arrange
        let from = ExpressionNode::Number(NumberNode::with_type(
            Token::with_value(TokenKind::Number, "42"),
            TYPE_N,
        ));
        let to = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
            vec![TYPE_N],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
        )]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_variable_variable() {
        // Arrange
        let from = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "y"),
            vec![],
            vec![TYPE_N],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "y"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
        )]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_function_variable() {
        // Arrange
        let from = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::new(Token::with_value(
                TokenKind::Number,
                "42",
            )))],
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
            vec![TYPE_N],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "f"),
                vec![ExpressionNode::Number(NumberNode::new(Token::with_value(
                    TokenKind::Number,
                    "42",
                )))],
                vec![TYPE_N],
            )),
        )]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_operator_variable() {
        // Arrange
        let from = ExpressionNode::Operator(OperatorNode::with_type(
            Token::with_value(TokenKind::Operator, "+"),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "1"),
                TYPE_N,
            )),
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
            vec![TYPE_N],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Operator(OperatorNode::with_type(
                Token::with_value(TokenKind::Operator, "+"),
                ExpressionNode::Number(NumberNode::with_type(
                    Token::with_value(TokenKind::Number, "42"),
                    TYPE_N,
                )),
                ExpressionNode::Number(NumberNode::with_type(
                    Token::with_value(TokenKind::Number, "1"),
                    TYPE_N,
                )),
                vec![TYPE_N],
            )),
        )]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_paren_variable() {
        // Arrange
        let from = ExpressionNode::Paren(ParenNode::with_type(
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
            vec![TYPE_N],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Paren(ParenNode::with_type(
                ExpressionNode::Number(NumberNode::with_type(
                    Token::with_value(TokenKind::Number, "42"),
                    TYPE_N,
                )),
                vec![TYPE_N],
            )),
        )]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_number_function() {
        // Arrange
        let from =
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")));
        let to = ExpressionNode::Binding(BindingNode::new(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::new(Token::with_value(
                TokenKind::Number,
                "42",
            )))],
        ));

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_function_function() {
        // Arrange
        let from = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            ))],
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            ))],
            vec![TYPE_N],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
        )]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_function_operator() {
        // Arrange
        let from = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            ))],
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Operator(OperatorNode::new(
            Token::with_value(TokenKind::Operator, "+"),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42"))),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "1"))),
        ));

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_operator_operator() {
        // Arrange
        let from = ExpressionNode::Operator(OperatorNode::with_type(
            Token::with_value(TokenKind::Operator, "+"),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "1"),
                TYPE_N,
            )),
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Operator(OperatorNode::with_type(
            Token::with_value(TokenKind::Operator, "+"),
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "y"),
                vec![],
                vec![TYPE_N],
            )),
            vec![TYPE_N],
        ));
        let expected = HashMap::from([
            (
                ExpressionNode::Binding(BindingNode::with_type(
                    Token::with_value(TokenKind::Identifier, "x"),
                    vec![],
                    vec![TYPE_N],
                )),
                ExpressionNode::Number(NumberNode::with_type(
                    Token::with_value(TokenKind::Number, "42"),
                    TYPE_N,
                )),
            ),
            (
                ExpressionNode::Binding(BindingNode::with_type(
                    Token::with_value(TokenKind::Identifier, "y"),
                    vec![],
                    vec![TYPE_N],
                )),
                ExpressionNode::Number(NumberNode::with_type(
                    Token::with_value(TokenKind::Number, "1"),
                    TYPE_N,
                )),
            ),
        ]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_create_mapping_variable_paren() {
        // Arrange
        let from = ExpressionNode::Binding(BindingNode::new(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
        ));
        let to = ExpressionNode::Paren(ParenNode::new(ExpressionNode::Number(NumberNode::new(
            Token::with_value(TokenKind::Number, "42"),
        ))));

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_none());
    }

    #[test]
    fn test_create_mapping_paren_paren() {
        // Arrange
        let from = ExpressionNode::Paren(ParenNode::with_type(
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
            vec![TYPE_N],
        ));
        let to = ExpressionNode::Paren(ParenNode::with_type(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            vec![TYPE_N],
        ));
        let expected = HashMap::from([(
            ExpressionNode::Binding(BindingNode::with_type(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
                vec![TYPE_N],
            )),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
        )]);

        // Act
        let mapping = from.create_mapping(&to);

        // Assert
        assert!(mapping.is_some());
        let mapping = mapping.unwrap();
        assert_eq!(mapping, expected);
    }

    #[test]
    fn test_apply_mapping_number() {
        // Arrange
        let expression =
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")));
        let mapping = HashMap::new();
        let expected =
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")));

        // Act
        let result = expression.apply(&mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }

    #[test]
    fn test_apply_mapping_variable() {
        // Arrange
        let expression = ExpressionNode::Binding(BindingNode::new(
            Token::with_value(TokenKind::Identifier, "x"),
            vec![],
        ));
        let mapping = HashMap::from([(
            ExpressionNode::Binding(BindingNode::new(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
            )),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42"))),
        )]);
        let expected =
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")));

        // Act
        let result = expression.apply(&mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }

    #[test]
    fn test_apply_mapping_function() {
        // Arrange
        let expression = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Binding(BindingNode::new(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
            ))],
            vec![TYPE_N],
        ));
        let mapping = HashMap::from([(
            ExpressionNode::Binding(BindingNode::new(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
            )),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
        )]);
        let expected = ExpressionNode::Binding(BindingNode::with_type(
            Token::with_value(TokenKind::Identifier, "f"),
            vec![ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            ))],
            vec![TYPE_N],
        ));

        // Act
        let result = expression.apply(&mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }

    #[test]
    fn test_apply_mapping_operator() {
        // Arrange
        let expression = ExpressionNode::Operator(OperatorNode::new(
            Token::with_value(TokenKind::Operator, "+"),
            ExpressionNode::Binding(BindingNode::new(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
            )),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "1"))),
        ));
        let mapping = HashMap::from([(
            ExpressionNode::Binding(BindingNode::new(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
            )),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42"))),
        )]);
        let expected = ExpressionNode::Operator(OperatorNode::new(
            Token::with_value(TokenKind::Operator, "+"),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42"))),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "1"))),
        ));

        // Act
        let result = expression.apply(&mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }

    #[test]
    fn test_apply_mapping_paren() {
        // Arrange
        let expression = ExpressionNode::Paren(ParenNode::new(ExpressionNode::Binding(
            BindingNode::new(Token::with_value(TokenKind::Identifier, "x"), vec![]),
        )));
        let mapping = HashMap::from([(
            ExpressionNode::Binding(BindingNode::new(
                Token::with_value(TokenKind::Identifier, "x"),
                vec![],
            )),
            ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42"))),
        )]);
        let expected = ExpressionNode::Paren(ParenNode::new(ExpressionNode::Number(
            NumberNode::new(Token::with_value(TokenKind::Number, "42")),
        )));

        // Act
        let result = expression.apply(&mapping);

        // Assert
        assert!(result.is_some());
        assert_eq!(result.unwrap(), expected);
    }
}
