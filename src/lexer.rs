pub mod prelude {
    pub use super::Lexer;
}

use crate::{
    source_file::SourceFile,
    token::{Token, TokenKind, EOF},
};

/// Lexer is responsible for tokenizing the input source code into a stream of tokens.
#[derive(Debug, Clone)]
pub struct Lexer {
    source_id: usize,

    input: String,
    pos: usize,
    read_pos: usize,
    ch: char,
}

fn issymbol(c: char) -> bool {
    "+-*/=<>^&|".contains(c)
}

impl Lexer {
    fn peek(&self) -> char {
        // Peek the next character without advancing the read position
        self.input.chars().nth(self.read_pos).unwrap_or(EOF)
    }

    fn read(&mut self) -> char {
        // Read the next character and advance the read position
        self.ch = self.peek();

        self.pos = self.read_pos;
        self.read_pos += 1;

        self.ch
    }

    fn skip_whitespace(&mut self) {
        while self.ch.is_whitespace() {
            self.read();
        }
    }

    fn tokenize_symbol(&mut self) -> Token {
        if !issymbol(self.ch) {
            return Token::with_value(TokenKind::Illegal, self.ch);
        }

        let mut value = String::new();
        while issymbol(self.ch) {
            value.push(self.ch);
            self.read();
        }

        if value == "->" {
            Token::new(TokenKind::Arrow)
        } else if value == "=" {
            Token::new(TokenKind::Equal)
        } else if value == "=>" {
            Token::new(TokenKind::Then)
        } else if value == ">" {
            Token::new(TokenKind::GreaterThan)
        } else {
            Token::with_value(TokenKind::Operator, value)
        }
    }

    fn tokenize_number(&mut self) -> Token {
        if !(self.ch.is_ascii_digit() || (self.ch == '-' && self.peek().is_ascii_digit())) {
            return Token::with_value(TokenKind::Illegal, self.ch);
        }

        let mut value = String::new();
        value.push(self.ch);
        self.read();

        while self.ch.is_ascii_digit() {
            value.push(self.ch);
            self.read();
        }

        // TODO: Handle decimal numbers and scientific notation
        Token::with_value(TokenKind::Number, value)
    }

    fn tokenize_type(&mut self) -> Token {
        if !self.ch.is_uppercase() {
            return Token::with_value(TokenKind::Illegal, self.ch);
        }

        let mut value = String::new();
        while self.ch.is_alphanumeric() || self.ch == '_' {
            value.push(self.ch);
            self.read();
        }

        Token::with_value(TokenKind::Type, value)
    }

    fn tokenize_identifier(&mut self) -> Token {
        if !self.ch.is_lowercase() {
            return Token::with_value(TokenKind::Illegal, self.ch);
        }

        let mut value = String::new();
        while self.ch.is_alphanumeric() || self.ch == '_' {
            value.push(self.ch);
            self.read();
        }

        if value == "forall" {
            Token::new(TokenKind::Forall)
        } else if value == "exists" {
            Token::new(TokenKind::Exists)
        } else if value == "eval" {
            Token::new(TokenKind::Eval)
        } else if value == "proof" {
            Token::new(TokenKind::Proof)
        } else if value == "def" {
            Token::new(TokenKind::Def)
        } else {
            Token::with_value(TokenKind::Identifier, value)
        }
    }

    fn tokenize_string(&mut self) -> Token {
        if self.ch != '"' {
            return Token::with_value(TokenKind::Illegal, self.ch);
        }
        self.read();

        let mut value = String::new();
        while self.ch != '"' {
            let ch = match self.ch {
                '\\' => self.read(),
                ch => ch,
            };

            value.push(ch);
            self.read();
        }
        self.read();

        Token::with_value(TokenKind::Literal, value)
    }

    /// Creates a new Lexer instance with the given source file.
    pub fn new(file: SourceFile) -> Self {
        let mut lexer = Lexer {
            source_id: file.id,
            input: file.content,
            pos: 0,
            read_pos: 0,
            ch: EOF,
        };

        lexer.read();

        lexer
    }

    /// Returns the next token from the input, skipping whitespace and comments.
    ///
    /// This method reads characters from the input string, identifies the type of token
    /// being read (such as identifiers, numbers, operators, etc.), and returns a `Token` object
    /// representing the token. It handles various token types, including literals, operators,
    /// parentheses, and special symbols. It also skips whitespace and comments in the input.
    ///
    /// # Returns
    /// A `Token` object representing the next token in the input stream. If the end of the input
    /// is reached, it returns a token of kind `TokenKind::Eof`. If an illegal character is
    /// encountered, it returns a token of kind `TokenKind::Illegal` with the character as its
    /// value.
    ///
    /// # Notes
    /// * This method is designed to be called repeatedly to retrieve tokens one by one from the
    ///     input.
    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        let position = self.pos;
        let mut token = match self.ch {
            EOF => Token::new(TokenKind::Eof),
            '#' => {
                while self.ch != '\n' && self.ch != EOF {
                    self.read();
                }
                return self.next_token(); // Skip comments
            }
            '{' => {
                self.read();
                Token::new(TokenKind::LBrace)
            }
            '}' => {
                self.read();
                Token::new(TokenKind::RBrace)
            }
            '(' => {
                self.read();
                Token::new(TokenKind::LParen)
            }
            ')' => {
                self.read();
                Token::new(TokenKind::RParen)
            }
            ',' => {
                self.read();
                Token::new(TokenKind::Comma)
            }
            ':' => {
                self.read();
                Token::new(TokenKind::Colon)
            }
            '"' => self.tokenize_string(),
            _ if self.ch.is_ascii_digit() || (self.ch == '-' && self.peek().is_ascii_digit()) => {
                self.tokenize_number()
            }
            _ if issymbol(self.ch) => self.tokenize_symbol(),
            _ if self.ch.is_uppercase() => self.tokenize_type(),
            _ if self.ch.is_lowercase() => self.tokenize_identifier(),
            illegal => {
                self.read();
                Token::with_value(TokenKind::Illegal, illegal)
            }
        };

        token.source_id = self.source_id;
        token.pos = position;

        token
    }
}

impl Iterator for Lexer {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.next_token();

        if token.kind == TokenKind::Eof {
            None
        } else {
            Some(token)
        }
    }
}
