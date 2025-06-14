use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashMap, HashSet},
};

use crate::{
    lexer::{Token, TokenKind},
    parser::{
        BindingNode, BuiltinNode, ExpressionNode, ImplicationNode, NumberNode, RelationKind,
        RelationNode, StatementNode,
    },
    typechecker::{FUNCTION_NEG, FUNCTION_SUCC, TYPE_N, TYPE_Z},
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

fn builtin_implications() -> Vec<ImplicationNode> {
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
        // forall a : Z => neg(a) = -a
        ImplicationNode::new(
            vec![],
            vec![StatementNode::Builtin(BuiltinNode::new(
                "forall a : Z => neg(a) = -a",
                |expression| {
                    if let ExpressionNode::Binding(expr_node) = expression {
                        if expr_node.name.value() == FUNCTION_NEG && expr_node.arguments.len() == 1
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
        let mut implications = implications;
        implications.extend(builtin_implications());

        Solver { implications }
    }

    fn substitute_helper(
        &self,
        expression: &ExpressionNode,
        implication: &ImplicationNode,
        substitutions: &mut Vec<(ExpressionNode, Vec<ProofStep>)>,
    ) {
        let statement = &implication.conclusion[0];

        match expression {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(_) => {}
            ExpressionNode::Literal(_) => {}
            ExpressionNode::Binding(node) => {
                for (i, arg) in node.arguments.iter().enumerate() {
                    let arg_substitutions = self.substitute(arg, implication);

                    for (substituted, steps) in arg_substitutions {
                        let mut new_expr = node.clone();
                        new_expr.arguments[i] = substituted;
                        substitutions.push((ExpressionNode::Binding(new_expr.clone()), steps));
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
            }
            ExpressionNode::Paren(node) => {
                let expr_substitutions = self.substitute(&node.expression, implication);
                for (substituted, steps) in expr_substitutions {
                    let mut new_expr = node.clone();
                    new_expr.expression = Box::new(substituted);
                    substitutions.push((ExpressionNode::Paren(new_expr), steps));
                }
            }
        }

        if let Some(mapping) = statement.create_mapping(expression) {
            if let Ok(steps) = self.proof_all(&implication.conditions, &mapping) {
                if let Some(substituted) = statement.apply(expression, &mapping) {
                    substitutions.push((substituted, steps));
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
                let left = relation.left.apply(mapping);
                let right = relation.right.apply(mapping);

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
            BindingNode, ExpressionNode, ImplicationNode, NumberNode, OperatorNode, RelationKind,
            RelationNode, StatementNode,
        },
    };

    #[test]
    fn test_substitute_number_implication_id() {
        // Arrange
        let expression = ExpressionNode::Number(NumberNode::with_type(
            Token::with_value(TokenKind::Number, "42"),
            TYPE_N,
        ));
        let implication = ImplicationNode::new(
            Vec::new(),
            vec![StatementNode::Relation(RelationNode::new(
                RelationKind::Equality,
                Token::new(TokenKind::Equal),
                ExpressionNode::Binding(BindingNode::with_type(
                    Token::with_value(TokenKind::Identifier, "a"),
                    vec![],
                    vec![TYPE_N],
                )),
                ExpressionNode::Binding(BindingNode::with_type(
                    Token::with_value(TokenKind::Identifier, "a"),
                    vec![],
                    vec![TYPE_N],
                )),
            ))],
        );
        let expected = vec![(
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Number, "42"),
                TYPE_N,
            )),
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
        let expression = ExpressionNode::Operator(OperatorNode::with_type(
            Token::with_value(TokenKind::Operator, "+"),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Identifier, "1"),
                TYPE_N,
            )),
            ExpressionNode::Number(NumberNode::with_type(
                Token::with_value(TokenKind::Identifier, "2"),
                TYPE_N,
            )),
            vec![TYPE_N],
        ));
        let implication = ImplicationNode::new(
            Vec::new(),
            vec![StatementNode::Relation(RelationNode::new(
                RelationKind::Equality,
                Token::new(TokenKind::Equal),
                ExpressionNode::Operator(OperatorNode::with_type(
                    Token::with_value(TokenKind::Operator, "+"),
                    ExpressionNode::Binding(BindingNode::with_type(
                        Token::with_value(TokenKind::Identifier, "b"),
                        vec![],
                        vec![TYPE_N],
                    )),
                    ExpressionNode::Binding(BindingNode::with_type(
                        Token::with_value(TokenKind::Identifier, "a"),
                        vec![],
                        vec![TYPE_N],
                    )),
                    vec![TYPE_N],
                )),
                ExpressionNode::Operator(OperatorNode::with_type(
                    Token::with_value(TokenKind::Operator, "+"),
                    ExpressionNode::Binding(BindingNode::with_type(
                        Token::with_value(TokenKind::Identifier, "a"),
                        vec![],
                        vec![TYPE_N],
                    )),
                    ExpressionNode::Binding(BindingNode::with_type(
                        Token::with_value(TokenKind::Identifier, "b"),
                        vec![],
                        vec![TYPE_N],
                    )),
                    vec![TYPE_N],
                )),
            ))],
        );
        let expected = vec![(
            ExpressionNode::Operator(OperatorNode::with_type(
                Token::with_value(TokenKind::Operator, "+"),
                ExpressionNode::Number(NumberNode::with_type(
                    Token::with_value(TokenKind::Identifier, "2"),
                    TYPE_N,
                )),
                ExpressionNode::Number(NumberNode::with_type(
                    Token::with_value(TokenKind::Identifier, "1"),
                    TYPE_N,
                )),
                vec![TYPE_N],
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
