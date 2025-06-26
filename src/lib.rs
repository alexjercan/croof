mod util;

pub mod ast;
pub mod lexer;
pub mod matcher;
pub mod parser;
pub mod solver;
pub mod source_file;
pub mod source_map;
pub mod token;
pub mod typechecker;

pub mod prelude {
    pub use crate::ast::prelude::*;
    pub use crate::lexer::prelude::*;
    pub use crate::matcher::prelude::*;
    pub use crate::parser::prelude::*;
    pub use crate::solver::prelude::*;
    pub use crate::source_map::prelude::*;
    pub use crate::token::prelude::*;
    pub use crate::typechecker::prelude::*;
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
