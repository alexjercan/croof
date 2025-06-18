use std::collections::{BinaryHeap, HashMap, HashSet};

use crate::{
    matcher::Matcher,
    parser::{ExpressionNode, ImplicationNode, RelationKind, StatementNode},
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
        expression: &ExpressionNode,
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
    ) -> Vec<(ExpressionNode, ImplicationNode, Vec<ProofStep>)> {
        let mut substitutions = Vec::new();

        for implication in &self.implications {
            for (substituted, steps) in self.matcher.substitute(expression, implication) {
                if let Some(steps) = self.prove(&steps).ok() {
                    substitutions.push((substituted, implication.clone(), steps));
                }
            }
        }

        substitutions
    }

    fn solve_astar(
        &self,
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
                    &node.right,
                    |expr| expr.degree() == 0,
                    |expr| expr.degree() as i32,
                )?;

                match &node.kind {
                    RelationKind::Equality => self.solve_astar(
                        &node.left,
                        |expr| expr == &right_expr,
                        |expr| expr.degree() as i32,
                    ),
                    RelationKind::GreaterThan => self.solve_astar(
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

impl Solver for AstarSolver {
    fn solve(
        &self,
        expression: &ExpressionNode,
    ) -> Result<(Vec<ProofStep>, ExpressionNode), SolverError> {
        self.solve_astar(
            expression,
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
