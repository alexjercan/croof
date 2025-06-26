pub mod prelude {
    pub use super::{Token, TokenKind, EOF};
}

use std::fmt::{Debug, Display};
use std::hash::{Hash, Hasher};

/// The WithToken trait is used to associate a Token with an object.
pub trait WithToken {
    /// Returns the token associated with this object.
    fn token(&self) -> Token;
}

/// End of File character, used to indicate the end of input
pub const EOF: char = '\0';

/// TokenKind represents the different types of tokens that can be recognized by the lexer.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum TokenKind {
    Eof,
    #[default]
    Illegal,
    LBrace,
    RBrace,
    LParen,
    RParen,
    Comma,
    Colon,
    Arrow,
    Equal,
    GreaterThan,
    Then,
    Operator,
    Number,
    Literal,
    Type,
    Identifier,
    Forall,
    Exists,
    Eval,
    Proof,
    Def,
}

/// Token represents a single token in the source code, including its kind, value, position, and
/// source ID.
#[derive(Debug, Clone, Default)]
pub struct Token {
    /// The kind of the token, which determines its type (e.g., identifier, number, operator).
    pub kind: TokenKind,
    value: Option<String>,

    // Token Info (should be ignored in equality checks or hashing)
    pub(crate) pos: usize,
    pub(crate) source_id: usize,
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.value == other.value
    }
}

impl Eq for Token {}

impl PartialOrd for Token {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Token {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.kind
            .cmp(&other.kind)
            .then_with(|| self.value.as_deref().cmp(&other.value.as_deref()))
    }
}

impl Hash for Token {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
        if let Some(ref value) = self.value {
            value.hash(state);
        }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.kind)?;
        if let Some(ref value) = self.value {
            match self.kind {
                TokenKind::Literal => write!(f, "(\"{}\")", value),
                _ => write!(f, "({})", value),
            }?;
        }

        Ok(())
    }
}

impl Token {
    /// Creates a new Token with the specified kind and default values for position and source ID.
    pub fn new(kind: TokenKind) -> Self {
        Token {
            kind,
            value: None,
            pos: 0,
            source_id: 0,
        }
    }

    /// Creates a new Token with the specified kind and value, setting position and source ID to 0.
    pub fn with_value<S>(kind: TokenKind, value: S) -> Self
    where
        S: Into<String>,
    {
        Token {
            kind,
            value: Some(value.into()),
            pos: 0,
            source_id: 0,
        }
    }

    /// Get the value of the token as a string.
    pub fn value(&self) -> String {
        self.value.as_deref().unwrap_or("?").to_string()
    }
}
