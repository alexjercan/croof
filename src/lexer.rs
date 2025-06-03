const EOF: char = '\0';

#[derive(Debug, Clone, PartialEq, Eq, Default)]
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
    Then,
    Operator,
    Number,
    Type,
    Identifier,
    Forall,
    Exists,
    Eval,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Token {
    pub kind: TokenKind,
    pub value: Option<String>,
    pub pos: usize,
}

#[derive(Debug, Clone)]
pub struct Lexer {
    filename: Option<String>,

    input: String,
    pos: usize,
    read_pos: usize,
    ch: char,
}

fn issymbol(c: char) -> bool {
    c == '+' || c == '-' || c == '*' || c == '/' || c == '=' || c == '<' || c == '>'
}

impl Lexer {
    fn peek(&mut self) -> char {
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
        let position = self.pos;

        if !issymbol(self.ch) {
            return Token {
                kind: TokenKind::Illegal,
                value: Some(self.ch.to_string()),
                pos: position,
            };
        }

        let mut value = String::new();
        while issymbol(self.ch) {
            value.push(self.ch);
            self.read();
        }

        if value == "->" {
            Token {
                kind: TokenKind::Arrow,
                pos: position,
                ..Default::default()
            }
        } else if value == "=" {
            return Token {
                kind: TokenKind::Equal,
                pos: position,
                ..Default::default()
            };
        } else if value == "=>" {
            return Token {
                kind: TokenKind::Then,
                pos: position,
                ..Default::default()
            };
        } else {
            return Token {
                kind: TokenKind::Operator,
                value: Some(value),
                pos: position,
            };
        }
    }

    fn tokenize_number(&mut self) -> Token {
        let position = self.pos;

        if !self.ch.is_ascii_digit() {
            return Token {
                kind: TokenKind::Illegal,
                value: Some(self.ch.to_string()),
                pos: position,
            };
        }

        let mut value = String::new();
        while self.ch.is_ascii_digit() {
            value.push(self.ch);
            self.read();
        }

        Token {
            kind: TokenKind::Number,
            value: Some(value),
            pos: position,
        }
    }

    fn tokenize_type(&mut self) -> Token {
        let position = self.pos;

        if !self.ch.is_uppercase() {
            return Token {
                kind: TokenKind::Illegal,
                value: Some(self.ch.to_string()),
                pos: position,
            };
        }

        let mut value = String::new();
        while self.ch.is_alphanumeric() || self.ch == '_' {
            value.push(self.ch);
            self.read();
        }

        Token {
            kind: TokenKind::Type,
            value: Some(value),
            pos: position,
        }
    }

    fn tokenize_identifier(&mut self) -> Token {
        let position = self.pos;

        if !self.ch.is_lowercase() {
            return Token {
                kind: TokenKind::Illegal,
                value: Some(self.ch.to_string()),
                pos: position,
            };
        }

        let mut value = String::new();
        while self.ch.is_alphanumeric() || self.ch == '_' {
            value.push(self.ch);
            self.read();
        }

        if value == "forall" {
            Token {
                kind: TokenKind::Forall,
                pos: position,
                ..Default::default()
            }
        } else if value == "exists" {
            return Token {
                kind: TokenKind::Exists,
                pos: position,
                ..Default::default()
            };
        } else if value == "eval" {
            return Token {
                kind: TokenKind::Eval,
                pos: position,
                ..Default::default()
            };
        } else {
            return Token {
                kind: TokenKind::Identifier,
                value: Some(value),
                pos: position,
            };
        }
    }

    pub fn new(input: String) -> Self {
        let mut lexer = Lexer {
            filename: None,
            input,
            pos: 0,
            read_pos: 0,
            ch: EOF,
        };

        lexer.read();

        lexer
    }

    pub fn with_filename(&mut self, filename: String) {
        self.filename = Some(filename);
    }

    pub fn next(&mut self) -> Token {
        self.skip_whitespace();

        let position = self.pos;
        match self.ch {
            EOF => Token {
                kind: TokenKind::Eof,
                pos: position,
                ..Default::default()
            },
            '#' => {
                while self.ch != '\n' && self.ch != EOF {
                    self.read();
                }
                self.next() // Skip comments
            }
            '{' => {
                self.read();
                Token {
                    kind: TokenKind::LBrace,
                    pos: position,
                    ..Default::default()
                }
            }
            '}' => {
                self.read();
                Token {
                    kind: TokenKind::RBrace,
                    pos: position,
                    ..Default::default()
                }
            }
            '(' => {
                self.read();
                Token {
                    kind: TokenKind::LParen,
                    pos: position,
                    ..Default::default()
                }
            }
            ')' => {
                self.read();
                Token {
                    kind: TokenKind::RParen,
                    pos: position,
                    ..Default::default()
                }
            }
            ',' => {
                self.read();
                Token {
                    kind: TokenKind::Comma,
                    pos: position,
                    ..Default::default()
                }
            }
            ':' => {
                self.read();
                Token {
                    kind: TokenKind::Colon,
                    pos: position,
                    ..Default::default()
                }
            }
            _ if issymbol(self.ch) => self.tokenize_symbol(),
            _ if self.ch.is_ascii_digit() => self.tokenize_number(),
            _ if self.ch.is_uppercase() => self.tokenize_type(),
            _ if self.ch.is_lowercase() => self.tokenize_identifier(),
            illegal => {
                self.read();
                Token {
                    kind: TokenKind::Illegal,
                    value: Some(illegal.to_string()),
                    pos: position,
                }
            }
        }
    }

    pub fn pos_to_lc(&self, pos: usize) -> (usize, usize) {
        let mut line = 1;
        let mut col = 1;

        for (i, ch) in self.input.char_indices() {
            if i >= pos {
                break;
            }
            if ch == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
        }

        (line, col)
    }

    pub fn format_pos(&self, pos: usize) -> String {
        let (line, col) = self.pos_to_lc(pos);
        if let Some(filename) = &self.filename {
            format!("{}:{}:{}", filename, line, col)
        } else {
            format!("{}:{}", line, col)
        }
    }

    pub fn display_tokens(&self) {
        let mut lexer = self.clone();

        loop {
            let token = lexer.next();
            if token.kind == TokenKind::Eof {
                break;
            }

            let (line, col) = lexer.pos_to_lc(token.pos);
            print!("Token: {:?}, ", token.kind);
            if let Some(value) = &token.value {
                print!("Value: '{value}', ");
            }
            println!("Position: ({}, {})", line, col);
        }
    }
}
