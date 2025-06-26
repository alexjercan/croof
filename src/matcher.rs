pub mod prelude {
    pub use super::Matcher;
}

use std::collections::HashMap;

use crate::ast::{ExpressionNode, StatementNode};

/// Matcher is a utility for matching expressions against implications
/// and performing substitutions based on those implications.
#[derive(Debug, Clone, Default)]
pub struct Matcher {}

impl Matcher {
    /// Creates a new Matcher instance.
    pub fn new() -> Self {
        Matcher {}
    }

    fn substitute_helper(
        &self,
        expression: &ExpressionNode,
        conditions: &Vec<StatementNode>,
        conclusion: &StatementNode,
        substitutions: &mut Vec<(ExpressionNode, Vec<StatementNode>)>,
    ) {
        match expression {
            ExpressionNode::Set(_) => todo!("Handle set expressions"),
            ExpressionNode::Type(_) => todo!("Handle type expressions"),
            ExpressionNode::Number(_) => {}
            ExpressionNode::Literal(_) => {}
            ExpressionNode::Binding(node) => {
                for (i, arg) in node.arguments.iter().enumerate() {
                    let arg_substitutions = self.substitute(arg, conditions, conclusion);

                    for (substituted, steps) in arg_substitutions {
                        let mut new_expr = node.clone();
                        new_expr.arguments[i] = substituted;
                        substitutions.push((ExpressionNode::Binding(new_expr.clone()), steps));
                    }
                }
            }
            ExpressionNode::Operator(node) => {
                let left_substitutions = self.substitute(&node.left, conditions, conclusion);
                for (left_substituted, left_steps) in left_substitutions {
                    let mut new_expr = node.clone();
                    *new_expr.left = left_substituted;
                    substitutions.push((ExpressionNode::Operator(new_expr.clone()), left_steps));
                }

                let right_substitutions = self.substitute(&node.right, conditions, conclusion);
                for (right_substituted, right_steps) in right_substitutions {
                    let mut new_expr = node.clone();
                    *new_expr.right = right_substituted;
                    substitutions.push((ExpressionNode::Operator(new_expr.clone()), right_steps));
                }
            }
            ExpressionNode::Paren(node) => {
                let expr_substitutions = self.substitute(&node.expression, conditions, conclusion);
                for (substituted, steps) in expr_substitutions {
                    let mut new_expr = node.clone();
                    new_expr.expression = Box::new(substituted);
                    substitutions.push((ExpressionNode::Paren(new_expr), steps));
                }
            }
        }

        let mapping = match conclusion {
            StatementNode::Quantifier(_) => {
                // TODO: Handle quantifier statements
                // NOTE: For now, we return None to indicate that no mapping can be created
                None
            }
            StatementNode::Relation(node) => expression.create_mapping(&node.left),
            StatementNode::Builtin(_) => Some(HashMap::new()),
        };

        if let Some(mapping) = mapping {
            let conditions = conditions
                .iter()
                .filter_map(|condition| match condition {
                    StatementNode::Quantifier(_) => None,
                    StatementNode::Relation(node) => {
                        let mut relation = node.clone();
                        relation.left = node.left.apply(&mapping)?;
                        relation.right = node.right.apply(&mapping)?;

                        Some(StatementNode::Relation(relation))
                    }
                    StatementNode::Builtin(_) => unreachable!(),
                })
                .collect::<Vec<_>>();

            let substituted = match conclusion {
                StatementNode::Quantifier(_) => {
                    unreachable!("Quantifier statements are not handled yet")
                }
                StatementNode::Relation(node) => node.right.apply(&mapping),
                StatementNode::Builtin(node) => {
                    node.apply(expression)
                }
            };

            if let Some(substituted) = substituted {
                substitutions.push((substituted, conditions));
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
        conditions: &Vec<StatementNode>,
        conclusion: &StatementNode,
    ) -> Vec<(ExpressionNode, Vec<StatementNode>)> {
        let mut substitutions = Vec::new();
        self.substitute_helper(expression, conditions, conclusion, &mut substitutions);

        substitutions
    }

    pub fn substitute_statement(
        &self,
        statement: &StatementNode,
        conditions: &Vec<StatementNode>,
        conclusion: &StatementNode,
    ) -> Vec<(StatementNode, Vec<StatementNode>)> {
        let mut substitutions = Vec::new();

        match statement {
            StatementNode::Quantifier(_) => {},
            StatementNode::Relation(node) => {
                for (substituted, steps) in
                    self.substitute(&node.left, conditions, conclusion)
                {
                    let mut node = node.clone();
                    node.left = substituted;
                    substitutions.push((StatementNode::Relation(node.clone()), steps));
                }

                for (substituted, steps) in
                    self.substitute(&node.right, conditions, conclusion)
                {
                    let mut node = node.clone();
                    node.right = substituted;
                    substitutions.push((StatementNode::Relation(node.clone()), steps));
                }

                if let Some(mapping) = statement.create_mapping(conclusion) {
                    let conditions = conditions
                        .iter()
                        .filter_map(|condition| match condition {
                            StatementNode::Quantifier(_) => None,
                            StatementNode::Relation(node) => {
                                let mut relation = node.clone();
                                relation.left = node.left.apply(&mapping)?;
                                relation.right = node.right.apply(&mapping)?;

                                Some(StatementNode::Relation(relation))
                            }
                            StatementNode::Builtin(_) => unreachable!(),
                        })
                        .collect::<Vec<_>>();

                    let substituted = match conclusion {
                        StatementNode::Quantifier(_) => {
                            unreachable!("Quantifier statements are not handled yet")
                        }
                        StatementNode::Relation(node) => {
                            match (node.left.apply(&mapping), node.right.apply(&mapping)) {
                                (Some(left), Some(right)) => {
                                    let mut relation = node.clone();
                                    relation.left = left;
                                    relation.right = right;
                                    Some(StatementNode::Relation(relation))
                                }
                                _ => None,
                            }
                        },
                        StatementNode::Builtin(_) => todo!("Handle built-in statements"),
                    };

                    if let Some(substituted) = substituted {
                        substitutions.push((substituted, conditions));
                    }
                }
            }
            StatementNode::Builtin(_) => todo!("Handle built-in statements"),
        }

        substitutions
    }
}
