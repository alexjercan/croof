use std::collections::HashMap;

use crate::parser::{ExpressionNode, ImplicationNode, StatementNode};

/// Matcher is a utility for matching expressions against implications
/// and performing substitutions based on those implications.
pub struct Matcher {

}

impl Matcher {
    /// Creates a new Matcher instance.
    pub fn new() -> Self {
        Matcher {}
    }

    fn substitute_helper(
        &self,
        expression: &ExpressionNode,
        implication: &ImplicationNode,
        substitutions: &mut Vec<(ExpressionNode, Vec<StatementNode>)>,
    ) {
        // NOTE: We assume that the conclusion of the implication is a single statement.
        // TODO: Handle multiple statements in the conclusion.
        let statement = &implication.conclusion[0];

        match expression {
            ExpressionNode::Set(_) => todo!("Handle set expressions"),
            ExpressionNode::Type(_) => todo!("Handle type expressions"),
            ExpressionNode::Number(_) => {},
            ExpressionNode::Literal(_) => {},
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

        let mapping = match statement {
            StatementNode::Quantifier(_) => todo!("Implement mapping for QuantifierNode"),
            StatementNode::Relation(node) => expression.create_mapping(&node.left),
            StatementNode::Builtin(_) => Some(HashMap::new()),
        };

        if let Some(mapping) = mapping {
            if let Some(conditions) = implication.conditions.iter().map(|condition| {
                match condition {
                    StatementNode::Quantifier(node) => Some(StatementNode::Quantifier(node.clone())),
                    StatementNode::Relation(node) => {
                        let mut relation = node.clone();
                        relation.left = node.left.apply(&mapping)?;
                        relation.right = node.right.apply(&mapping)?;

                        Some(StatementNode::Relation(relation))
                    },
                    StatementNode::Builtin(_) => todo!("Handle builtin statements"),
                }
            }).collect::<Option<Vec<_>>>() {
                let substituted = match statement {
                    StatementNode::Quantifier(_) => todo!("Implement apply for QuantifierNode"),
                    StatementNode::Relation(node) => node.right.apply(&mapping),
                    StatementNode::Builtin(node) => node.apply(expression),
                };

                if let Some(substituted) = substituted {
                    substitutions.push((substituted, conditions));
                }
            }
        }
    }

    /// This function gives a list of all substitutions that can be made
    /// from the given expression by using the given implication.
    ///
    /// This function will also return the steps that require to be proved
    /// to make the substitution valid.
    ///
    /// # Arguments
    /// * `expression` - The expression to substitute.
    /// * `implication` - The implication to use for substitution.
    ///
    /// # Returns
    /// A vector of tuples, where each tuple contains:
    /// * The substituted expression.
    /// * A vector of statements that need to be proved for the substitution to be valid.
    pub fn substitute(
        &self,
        expression: &ExpressionNode,
        implication: &ImplicationNode,
    ) -> Vec<(ExpressionNode, Vec<StatementNode>)> {
        let mut substitutions = Vec::new();
        self.substitute_helper(expression, implication, &mut substitutions);

        substitutions
    }
}
