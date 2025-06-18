use std::fmt::Display;
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::{self, Read};

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
    pos: usize,
    source_id: usize,
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
    /// input.
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

    /// Displays all tokens from the lexer, formatted with their source positions.
    ///
    /// This method iterates through the tokens produced by the lexer, printing each token's
    /// position in the source code and its string representation. It continues until it reaches
    /// the end of the input (EOF) token.
    pub fn display_tokens(&self, sourcemap: &SourceMap) {
        let mut lexer = self.clone();

        loop {
            let token = lexer.next_token();
            if token.kind == TokenKind::Eof {
                break;
            }

            print!("{}: ", sourcemap.format_pos(&token));
            println!("{}", token);
        }
    }
}

/// SourceFile represents a source file in the source map, containing its ID, filename, and
/// content.
#[derive(Debug, Clone, Default)]
pub struct SourceFile {
    /// Unique identifier for the source file
    pub id: usize,
    /// The name of the source file, which can be a path or "<stdin>" for standard input
    pub filename: String,
    /// The content of the source file as a string
    pub content: String,
}

impl SourceFile {
    /// Creates a new SourceFile with the given ID, filename, and content.
    pub fn new(id: usize, filename: String, content: String) -> Self {
        SourceFile {
            id,
            filename,
            content,
        }
    }

    /// Converts a character position in the content to a line and column number.
    ///
    /// This method takes a character position (index) in the content string and calculates
    /// the corresponding line and column numbers. It iterates through the content, counting
    /// new lines to determine the line number and counting characters to determine the column
    /// number.
    ///
    /// # Arguments
    /// * `pos` - The character position in the content string.
    ///
    /// # Returns
    /// A tuple `(line, col)` where `line` is the line number (1-based) and `col` is the column
    pub fn pos_to_lc(&self, pos: usize) -> (usize, usize) {
        let mut line = 1;
        let mut col = 1;

        for (i, ch) in self.content.char_indices() {
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
}

/// SourceMap is a collection of source files, allowing for the management and retrieval of
/// source files and their tokens.
#[derive(Debug, Clone, Default)]
pub struct SourceMap {
    /// A vector of source files, each represented by a SourceFile struct
    pub files: Vec<SourceFile>,
}

impl SourceMap {
    /// Adds a new source file to the source map, reading its content from the specified filename.
    ///
    /// This method takes an optional filename, reads the content of the file, and creates a new
    /// SourceFile instance with a unique ID. If no filename is provided, it reads from standard
    /// input.
    ///
    /// # Arguments
    /// * `filename` - An optional string representing the filename to read. If `None`, it reads
    /// from standard input.
    ///
    /// # Returns
    /// A `Result` containing a `Lexer` instance initialized with the new source file, or an
    /// `io::Error` if reading the file fails.
    ///
    /// # Notes
    /// * The ID of the new source file is the current length of the `files` vector, ensuring
    /// that each file has a unique ID.
    pub fn add_file<S>(&mut self, filename: Option<S>) -> io::Result<Lexer>
    where
        S: Into<String>,
    {
        let id = self.files.len();
        let filename = filename.map(|s| s.into());

        let content = read_input(filename.clone())?;
        let file = SourceFile::new(
            id,
            filename.unwrap_or_else(|| "<stdin>".to_string()),
            content,
        );
        self.files.push(file);

        Ok(Lexer::new(self.files[id].clone()))
    }

    /// Formats the position of a token in the source file as a string.
    ///
    /// This method takes a `Token` and retrieves the corresponding source file from the source
    /// map. It then converts the token's position to a line and column number using the
    /// `pos_to_lc` method of the `SourceFile`. Finally, it formats the position as a string
    /// in the format "filename:line:column".
    ///
    /// # Arguments
    /// * `token` - A reference to a `Token` whose position is to be formatted.
    ///
    /// # Returns
    /// A `String` representing the position of the token in the format
    pub fn format_pos(&self, token: &Token) -> String {
        let file = self
            .files
            .get(token.source_id)
            .expect("Source file not found");

        let (line, col) = file.pos_to_lc(token.pos);
        format!("{}:{}:{}", file.filename, line, col)
    }
}

fn read_input(path: Option<String>) -> io::Result<String> {
    let mut buffer = String::new();

    match path {
        Some(p) => {
            let mut file = File::open(p)?;
            file.read_to_string(&mut buffer)?;
        }
        None => {
            let stdin = io::stdin();
            let mut handle = stdin.lock();
            handle.read_to_string(&mut buffer)?;
        }
    }

    Ok(buffer)
}
