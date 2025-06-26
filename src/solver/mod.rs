pub mod astar;
pub mod interactive;

pub mod prelude {
    pub use super::{astar::AstarSolver, interactive::InteractiveSolver, EvalStep, ProofStep, Solver};
}

use crate::ast::{EvaluationNode, ExpressionNode, ImplicationNode, StatementNode};

/// EvalStep represents a step in a proof, consisting of an expression, its substitution, and the
/// implication used.
pub type EvalStep = (ExpressionNode, ExpressionNode, ImplicationNode);
pub type ProofStep = (Vec<StatementNode>, Vec<StatementNode>, ImplicationNode);

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
    ) -> Result<(Vec<EvalStep>, ExpressionNode), SolverError>;

    /// prove attempts to prove a set of statements and returns a vector of proof steps.
    ///
    /// # Arguments
    /// * `statements` - A slice of statements to prove.
    ///
    /// # Returns
    /// A Result containing a vector of proof steps, or a SolverError if the proving process fails.
    fn prove(&self, statements: &[StatementNode]) -> Result<Vec<EvalStep>, SolverError>;
}
