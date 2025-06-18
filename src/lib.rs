use std::collections::{hash_map, BinaryHeap, HashMap, HashSet};
use std::fmt::{Debug, Display};
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::{self, Read};
use std::sync::Arc;

/// Reads the input from a file or standard input.
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

/// The WithToken trait is used to associate a Token with an object.
pub trait WithToken {
    /// Returns the token associated with this object.
    fn token(&self) -> Token;
}

/// End of File character, used to indicate the end of input
const EOF: char = '\0';

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

    /// Formats an error message with the token's position and a custom message.
    ///
    /// This method takes a `Token` and a custom error message, formats the token's position
    /// using the `format_pos` method, and combines it with the custom message to create a
    /// formatted error string.
    ///
    /// # Arguments
    /// * `token` - A reference to a `Token` whose position is to be included in the error message.
    /// * `message` - A string slice containing the custom error message to be included.
    ///
    /// # Returns
    /// A `String` containing the formatted error message, which includes the token's position
    /// and the custom message.
    pub fn format_error(&self, token: &Token, message: &str) -> String {
        format!("{}, {}", self.format_pos(token), message)
    }

    /// Display the error message for a given error object, formatted with the source map.
    ///
    /// # Arguments
    /// * `error` - A reference to an object that implements the `Debug`, `Display`, and
    /// `WithToken` traits.
    ///
    /// # Notes
    /// This function uses the `format_error` method of the `SourceMap` to format the error message
    /// with the token's position and the error's string representation.
    pub fn display_error<T>(&self, error: &T)
    where
        T: Debug + Display + Clone + WithToken,
    {
        eprintln!("{}", self.format_error(&error.token(), &error.to_string()));
    }

    /// Display a list of errors, formatting each error with its token's position.
    ///
    /// # Arguments
    /// * `errors` - A slice of objects that implement the `Debug`, `Display`, and `WithToken`
    /// traits.
    ///
    /// # Notes
    /// This function iterates over the provided errors and calls `display_error` for each one,
    /// displaying them in the standard error output.
    pub fn display_errors<T>(&self, errors: &[T])
    where
        T: Debug + Display + Clone + WithToken,
    {
        for error in errors {
            self.display_error(error);
        }
    }

    pub fn display_token(&self, token: &Token) {
        println!("{}: {}", self.format_pos(token), token);
    }
}

/// The TypeNode represents a sequence of types in the abstract syntax tree.
///
/// It is used to represent function types, where each type in the sequence corresponds to
/// a parameter type, and the last type corresponds to the return type of the function.
///
/// # Example
/// ```croof
/// N -> N -> N
/// ```
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeNode {
    pub types: Vec<Token>,
}

impl TypeNode {
    /// Creates a new TypeNode with the given types.
    pub fn new(types: Vec<Token>) -> Self {
        TypeNode { types }
    }
}

impl Display for TypeNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.types
                .iter()
                .map(|t| t.value())
                .collect::<Vec<String>>()
                .join(" -> ")
        )
    }
}

/// The QuantifierKind represents the kind of quantifier used in the abstract syntax tree.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum QuantifierKind {
    Forall,
    Exists,
}

impl Display for QuantifierKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuantifierKind::Forall => write!(f, "forall"),
            QuantifierKind::Exists => write!(f, "exists"),
        }
    }
}

/// The QuantifierNode represents a quantifier in the abstract syntax tree.
///
/// It contains the kind of quantifier, the symbol representing the quantifier,
/// and the type node associated with the quantifier.
///
/// # Example
/// ```croof
/// forall f : N -> N -> N
/// exists x : N
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QuantifierNode {
    pub kind: QuantifierKind,
    pub symbol: Token,
    pub type_node: TypeNode,
}

impl QuantifierNode {
    /// Creates a new QuantifierNode with the given kind, symbol, and type node.
    pub fn new(kind: QuantifierKind, symbol: Token, type_node: TypeNode) -> Self {
        QuantifierNode {
            kind,
            symbol,
            type_node,
        }
    }
}

impl Display for QuantifierNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {} : {}",
            self.kind,
            self.symbol.value(),
            self.type_node
        )
    }
}

/// The SetNode represents a set of elements in the abstract syntax tree.
///
/// It contains a vector of `ExpressionNode` elements, which can be any valid expression
///
/// # Example
/// ```croof
/// {1, 2, 3}
/// {f(1), g(2)}
/// ```
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SetNode {
    pub elements: Vec<ExpressionNode>,
}

impl SetNode {
    /// Creates a new SetNode with the given elements.
    pub fn new(elements: Vec<ExpressionNode>) -> Self {
        SetNode { elements }
    }
}

impl Display for SetNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let elements: Vec<String> = self.elements.iter().map(|e| e.to_string()).collect();
        write!(f, "{{{}}}", elements.join(", "))
    }
}

/// The NumberNode represents a numeric value in the abstract syntax tree.
///
/// It contains a `Token` representing the numeric value and an optional type node.
///
/// # Example
/// ```croof
/// 42
/// -3
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NumberNode {
    pub value: Token,
    pub node_type: Option<Vec<String>>,
}

impl NumberNode {
    /// Creates a new NumberNode with the given value.
    pub fn new(value: Token) -> Self {
        NumberNode {
            value,
            node_type: None,
        }
    }

    /// Creates a new NumberNode with the given value and type.
    pub fn with_type<S>(value: Token, node_type: S) -> Self
    where
        S: Into<String>,
    {
        NumberNode {
            value,
            node_type: Some(vec![node_type.into()]),
        }
    }
}

impl PartialOrd for NumberNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NumberNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let type_node = self.node_type.as_ref().unwrap().first().unwrap().clone();
        let type_other = other.node_type.as_ref().unwrap().first().unwrap().clone();

        if type_node == type_other {
            let number_node = self.value.value().parse::<i64>().unwrap();
            let other_node = other.value.value().parse::<i64>().unwrap();

            return number_node.cmp(&other_node);
        }

        type_node.cmp(&type_other)
    }
}

impl Display for NumberNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // match &self.node_type {
        //     Some(node_type) => write!(f, "{} : {}", self.value.value(), node_type.join(" -> ")),
        //     None => write!(f, "{}", self.value.value()),
        // }

        write!(f, "{}", self.value.value())
    }
}

/// The LiteralNode represents a literal value in the abstract syntax tree.
///
/// It contains a `Token` representing the literal value and an optional type node.
///
/// # Example
/// ```croof
/// "Hello, World!"
/// "42"
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LiteralNode {
    pub value: Token,
    pub node_type: Option<Vec<String>>,
}

impl LiteralNode {
    /// Creates a new LiteralNode with the given value.
    pub fn new(value: Token) -> Self {
        LiteralNode {
            value,
            node_type: None,
        }
    }

    /// Creates a new LiteralNode with the given value and type.
    pub fn with_type<S>(value: Token, type_node: S) -> Self
    where
        S: Into<String>,
    {
        LiteralNode {
            value,
            node_type: Some(vec![type_node.into()]),
        }
    }
}

impl PartialOrd for LiteralNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LiteralNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let type_node = self.node_type.as_ref().unwrap().first().unwrap().clone();
        let type_other = other.node_type.as_ref().unwrap().first().unwrap().clone();

        if type_node == type_other {
            return self.value.value().cmp(&other.value.value());
        }

        type_node.cmp(&type_other)
    }
}

impl Display for LiteralNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // match &self.node_type {
        //     Some(node_type) => write!(f, "\"{}\" : {}", self.value.value(), node_type.join(" -> ")),
        //     None => write!(f, "\"{}\"", self.value.value()),
        // }

        write!(f, "\"{}\"", self.value.value())
    }
}

/// The BindingNode represents a function or a binding in the abstract syntax tree.
///
/// It contains a `Token` representing the name of the binding, a vector of `ExpressionNode`
/// arguments, and an optional type node that represents the type of the binding.
///
/// # Note
/// The `node_type` should be filled with the type of the binding at the time of type checking.
///
/// # Example
/// ```croof
/// f(x, 1)
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BindingNode {
    pub name: Token,
    pub arguments: Vec<ExpressionNode>,
    pub node_type: Option<Vec<String>>,
}

impl BindingNode {
    /// Creates a new BindingNode with the given name and arguments.
    pub fn new(name: Token, arguments: Vec<ExpressionNode>) -> Self {
        BindingNode {
            name,
            arguments,
            node_type: None,
        }
    }

    /// Creates a new BindingNode with the given name, arguments, and type.
    pub fn with_type<S>(name: Token, arguments: Vec<ExpressionNode>, node_type: Vec<S>) -> Self
    where
        S: Into<String>,
    {
        BindingNode {
            name,
            arguments,
            node_type: Some(node_type.into_iter().map(Into::into).collect()),
        }
    }
}

impl PartialOrd for BindingNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BindingNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let type_node = self.node_type.as_ref().unwrap().first().unwrap().clone();
        let type_other = other.node_type.as_ref().unwrap().first().unwrap().clone();

        if type_node == type_other {
            return self.name.value().cmp(&other.name.value());
        }

        type_node.cmp(&type_other)
    }
}

impl Display for BindingNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let args: Vec<String> = self.arguments.iter().map(|e| e.to_string()).collect();

        write!(f, "{}", self.name.value())?;
        if !args.is_empty() {
            write!(f, "({})", args.join(", "))?;
        }

        // match &self.node_type {
        //     Some(node_type) => write!(f, " : {}", node_type.join(" -> ")),
        //     None => Ok(()),
        // }

        Ok(())
    }
}

/// The OperatorNode represents an operator in the abstract syntax tree.
///
/// It contains a `Token` representing the operator, two `ExpressionNode` operands (left and
/// right), and an optional type node that represents the type of the operation.
///
/// # Example
/// ```croof
/// 1 + 2
/// f(x, y) * g(z)
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OperatorNode {
    pub operator: Token,
    pub left: Box<ExpressionNode>,
    pub right: Box<ExpressionNode>,
    pub node_type: Option<Vec<String>>,
}

impl OperatorNode {
    /// Creates a new OperatorNode with the given operator, left operand, and right operand.
    pub fn new(operator: Token, left: ExpressionNode, right: ExpressionNode) -> Self {
        OperatorNode {
            operator,
            left: Box::new(left),
            right: Box::new(right),
            node_type: None,
        }
    }

    /// Creates a new OperatorNode with the given operator, left operand, right operand, and type.
    pub fn with_type<S>(
        operator: Token,
        left: ExpressionNode,
        right: ExpressionNode,
        node_type: Vec<S>,
    ) -> Self
    where
        S: Into<String>,
    {
        OperatorNode {
            operator,
            left: Box::new(left),
            right: Box::new(right),
            node_type: Some(node_type.into_iter().map(Into::into).collect()),
        }
    }
}

impl PartialOrd for OperatorNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OperatorNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let type_node = self.node_type.as_ref().unwrap().first().unwrap().clone();
        let type_other = other.node_type.as_ref().unwrap().first().unwrap().clone();

        if type_node == type_other {
            return self.operator.value().cmp(&other.operator.value());
        }

        type_node.cmp(&type_other)
    }
}

impl Display for OperatorNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // match &self.node_type {
        //     Some(node_type) => write!(
        //         f,
        //         "{} {} {} : {}",
        //         self.left, self.operator.value(), self.right, node_type.join(" -> ")
        //     ),
        //     None => write!(f, "{} {} {}", self.left, self.operator.value(), self.right),
        // }

        write!(f, "{} {} {}", self.left, self.operator.value(), self.right)
    }
}

/// The ParenNode represents a parenthesized expression in the abstract syntax tree.
///
/// It contains an `ExpressionNode` representing the expression inside the parentheses,
/// and an optional type node that represents the type of the expression.
///
/// # Example
/// ```croof
/// (f(x, y) + g(z))
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParenNode {
    pub expression: Box<ExpressionNode>,
    pub node_type: Option<Vec<String>>,
}

impl ParenNode {
    /// Creates a new ParenNode with the given expression.
    pub fn new(expression: ExpressionNode) -> Self {
        ParenNode {
            expression: Box::new(expression),
            node_type: None,
        }
    }

    /// Creates a new ParenNode with the given expression and type.
    pub fn with_type<S>(expression: ExpressionNode, node_type: Vec<S>) -> Self
    where
        S: Into<String>,
    {
        ParenNode {
            expression: Box::new(expression),
            node_type: Some(node_type.into_iter().map(Into::into).collect()),
        }
    }
}

impl PartialOrd for ParenNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ParenNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let type_node = self.node_type.as_ref().unwrap().first().unwrap().clone();
        let type_other = other.node_type.as_ref().unwrap().first().unwrap().clone();

        if type_node == type_other {
            return self.expression.cmp(&other.expression);
        }

        type_node.cmp(&type_other)
    }
}

impl Display for ParenNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // match &self.node_type {
        //     Some(node_type) => write!(
        //         f,
        //         "({}) : {}",
        //         self.expression, node_type.join(" -> ")
        //     ),
        //     None => write!(f, "({})", self.expression),
        // }

        write!(f, "({})", self.expression)
    }
}

/// The ExpressionNode enum represents different types of expression nodes in the abstract syntax
/// tree.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExpressionNode {
    Set(SetNode),
    Type(TypeNode),
    Number(NumberNode),
    Literal(LiteralNode),
    Binding(BindingNode),
    Operator(OperatorNode),
    Paren(ParenNode),
}

impl ExpressionNode {
    /// Computes the degree of the expression node.
    ///
    /// The degree is defined as the number of operations in the expression.
    ///
    /// # Returns
    /// A `u64` representing the degree of the expression node.
    pub fn degree(&self) -> u64 {
        match self {
            ExpressionNode::Set(set_node) => {
                1 + set_node.elements.iter().map(|e| e.degree()).sum::<u64>()
            }
            ExpressionNode::Type(_) => 0,
            ExpressionNode::Number(_) => 0,
            ExpressionNode::Literal(_) => 0,
            ExpressionNode::Binding(node) => {
                1 + node.arguments.iter().map(|e| e.degree()).sum::<u64>()
            }
            ExpressionNode::Operator(operator_node) => {
                1 + operator_node.left.degree() + operator_node.right.degree()
            }
            ExpressionNode::Paren(paren_node) => 1 + paren_node.expression.degree(),
        }
    }

    /// Returns the token associated with the expression node.
    ///
    /// # Returns
    /// A `Token` representing the token of the expression node.
    pub fn token(&self) -> Token {
        match &self {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(node) => node.value.clone(),
            ExpressionNode::Literal(node) => node.value.clone(),
            ExpressionNode::Binding(node) => node.name.clone(),
            ExpressionNode::Operator(node) => node.operator.clone(),
            ExpressionNode::Paren(node) => node.expression.token(),
        }
    }

    /// Returns the type of the expression node.
    ///
    /// # Returns
    /// An `Option<Vec<String>>` representing the type of the expression node.
    pub fn node_type(&self) -> Option<Vec<String>> {
        match self {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(node) => node.node_type.clone(),
            ExpressionNode::Literal(node) => node.node_type.clone(),
            ExpressionNode::Binding(node) => node.node_type.clone(),
            ExpressionNode::Operator(node) => node.node_type.clone(),
            ExpressionNode::Paren(node) => node.node_type.clone(),
        }
    }

    /// Computes the distance between two expression nodes.
    ///
    /// Right now, this function returns a constant value of 1.
    pub fn distance(&self, _: &Self) -> i32 {
        // NOTE: This is a placeholder implementation.
        1
    }

    /// Applies a mapping to the expression node.
    ///
    /// This function will traverse the expression node and apply the mapping to each sub-node.
    ///
    /// # Arguments
    /// * `mapping` - A mapping from `ExpressionNode` to `ExpressionNode`.
    ///
    /// # Returns
    /// An `Option<ExpressionNode>` which is the result of applying the mapping.
    ///
    /// # Note
    /// If the mapping does not contain a mapping for a specific node, it will return `None`.
    ///
    /// # Example
    /// ```rust
    /// use std::collections::HashMap;
    /// use croof::{ExpressionNode, BindingNode, NumberNode, Token, TokenKind};
    ///
    /// let mapping: HashMap<ExpressionNode, ExpressionNode> = HashMap::from([(
    ///     ExpressionNode::Binding(BindingNode::new(
    ///         Token::with_value(TokenKind::Identifier, "x"),
    ///         vec![],
    ///     )),
    ///     ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42"))),
    /// )]);
    ///
    /// let expr = ExpressionNode::Binding(BindingNode::new(Token::with_value(TokenKind::Identifier, "x"), vec![]));
    ///
    /// let result = expr.apply(&mapping);
    ///
    /// // assert_eq!(result, Some(ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")))));
    /// ```
    pub fn apply(
        &self,
        mapping: &HashMap<ExpressionNode, ExpressionNode>,
    ) -> Option<ExpressionNode> {
        match self {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(_) => Some(self.clone()),
            ExpressionNode::Literal(_) => Some(self.clone()),
            ExpressionNode::Binding(node) => {
                // TODO: Can we do this better?
                if node.arguments.is_empty() {
                    return mapping.get(self).cloned();
                }

                let args = node
                    .arguments
                    .iter()
                    .map(|arg| arg.apply(mapping))
                    .collect::<Option<Vec<ExpressionNode>>>()?;

                let mut func_type = args
                    .iter()
                    .filter_map(|arg| arg.node_type())
                    .flatten()
                    .collect::<Vec<String>>();
                let return_type = node.clone().node_type?;
                func_type.extend(return_type.iter().cloned());

                let expr = ExpressionNode::Binding(BindingNode::with_type(
                    Token::with_value(TokenKind::Identifier, node.name.value()),
                    vec![],
                    func_type,
                ));

                let mut function_node = node.clone();
                function_node.arguments = args;
                function_node.name = mapping
                    .get(&expr)
                    .cloned()
                    .unwrap_or(ExpressionNode::Binding(function_node.clone()))
                    .token();

                Some(ExpressionNode::Binding(function_node))
            }
            ExpressionNode::Operator(node) => {
                let left = node.left.apply(mapping)?;
                let right = node.right.apply(mapping)?;

                let mut operator_node = node.clone();
                operator_node.left = Box::new(left);
                operator_node.right = Box::new(right);

                Some(ExpressionNode::Operator(operator_node))
            }
            ExpressionNode::Paren(node) => {
                let expr = node.expression.apply(mapping)?;
                let mut paren_node = node.clone();
                paren_node.expression = Box::new(expr);

                Some(ExpressionNode::Paren(paren_node))
            }
        }
    }

    fn create_mapping_helper(
        &self,
        to: &ExpressionNode,
        mapping: &mut HashMap<ExpressionNode, ExpressionNode>,
    ) -> bool {
        let Some(from_type) = self.node_type() else {
            return false;
        };
        let Some(to_type) = to.node_type() else {
            return false;
        };
        if !can_infer_type(&from_type, &to_type) {
            return false;
        }

        match to {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(to_node) => match self {
                ExpressionNode::Number(from_node) => to_node.value == from_node.value,
                _ => false,
            },
            ExpressionNode::Literal(to_node) => match self {
                ExpressionNode::Literal(from_node) => to_node.value == from_node.value,
                _ => false,
            },
            ExpressionNode::Binding(to_node) => {
                if to_node.arguments.is_empty() {
                    let has_mapping = mapping.contains_key(to);
                    let should_substitute = !has_mapping || mapping.get(to) == Some(self);

                    if !has_mapping {
                        mapping.insert(to.clone(), self.clone());
                    }

                    return should_substitute;
                }

                match self {
                    ExpressionNode::Binding(from_node) => {
                        to_node.name == from_node.name
                            && to_node.arguments.len() == from_node.arguments.len()
                            && to_node.arguments.iter().zip(&from_node.arguments).all(
                                |(to_arg, from_arg)| {
                                    from_arg.create_mapping_helper(to_arg, mapping)
                                },
                            )
                    }
                    _ => false,
                }
            }
            ExpressionNode::Operator(to_node) => match self {
                ExpressionNode::Operator(operator_node) => {
                    to_node.operator == operator_node.operator
                        && operator_node
                            .left
                            .create_mapping_helper(&to_node.left, mapping)
                        && operator_node
                            .right
                            .create_mapping_helper(&to_node.right, mapping)
                }
                _ => false,
            },
            ExpressionNode::Paren(to_node) => match self {
                ExpressionNode::Paren(paren_node) => paren_node
                    .expression
                    .create_mapping_helper(&to_node.expression, mapping),
                _ => false,
            },
        }
    }

    /// Creates a mapping from the current expression node to the given expression node.
    ///
    /// # Arguments
    /// * `expr` - The expression node to which the mapping should be created.
    ///
    /// # Returns
    /// An `Option<HashMap<ExpressionNode, ExpressionNode>>` which contains the mapping if it can
    /// be created, or `None` if it cannot be created.
    ///
    /// # Note
    /// This function will traverse the expression node and create a mapping for each sub-node.
    ///
    /// # Example
    /// ```rust
    /// use croof::{ExpressionNode, BindingNode, NumberNode, Token, TokenKind};
    /// use std::collections::HashMap;
    ///
    /// let expr1 = ExpressionNode::Binding(BindingNode::new(
    ///     Token::with_value(TokenKind::Identifier, "x"),
    ///     vec![],
    /// ));
    ///
    /// let expr2 = ExpressionNode::Number(NumberNode::new(Token::with_value(TokenKind::Number, "42")));
    ///
    /// let mapping = expr1.create_mapping(&expr2);
    ///
    /// // assert_eq!(mapping, Some(HashMap::from([(expr1, expr2)])));
    /// ```
    pub fn create_mapping(
        &self,
        expr: &ExpressionNode,
    ) -> Option<HashMap<ExpressionNode, ExpressionNode>> {
        let mut mapping = HashMap::new();
        if self.create_mapping_helper(expr, &mut mapping) {
            Some(mapping)
        } else {
            None
        }
    }
}

impl Display for ExpressionNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExpressionNode::Set(node) => write!(f, "{}", node),
            ExpressionNode::Type(node) => write!(f, "{}", node),
            ExpressionNode::Number(node) => write!(f, "{}", node),
            ExpressionNode::Literal(node) => write!(f, "{}", node),
            ExpressionNode::Binding(node) => write!(f, "{}", node),
            ExpressionNode::Operator(node) => write!(f, "{}", node),
            ExpressionNode::Paren(node) => write!(f, "{}", node),
        }
    }
}

/// The RelationKind enum represents the kind of relation used in the abstract syntax tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelationKind {
    Equality,
    GreaterThan,
}

impl Display for RelationKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RelationKind::Equality => write!(f, "="),
            RelationKind::GreaterThan => write!(f, ">"),
        }
    }
}

/// The RelationNode represents a relation in the abstract syntax tree.
///
/// It contains the kind of relation, a token representing the relation,
/// and two `ExpressionNode` operands (left and right).
///
/// # Example
/// ```croof
/// f(x, y) = g(z)
/// f(x, y) > 42
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelationNode {
    pub kind: RelationKind,
    pub token: Token,
    pub left: ExpressionNode,
    pub right: ExpressionNode,
}

impl RelationNode {
    /// Creates a new RelationNode with the given kind, token, left operand, and right operand.
    pub fn new(
        kind: RelationKind,
        token: Token,
        left: ExpressionNode,
        right: ExpressionNode,
    ) -> Self {
        RelationNode {
            kind,
            token,
            left,
            right,
        }
    }
}

impl Display for RelationNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {}", self.left, self.kind, self.right)
    }
}

pub type SubstituteFn = Arc<dyn Fn(&ExpressionNode) -> Option<ExpressionNode> + Send + Sync>;

/// The BuiltinNode represents a built-in function or operation in the abstract syntax tree.
///
/// It contains a display name for the built-in, and a function that can be used to substitute
/// the built-in with an expression node.
///
/// # Note
/// The `substitute_fn` is a function that takes an `ExpressionNode` and returns an
/// `Option<ExpressionNode>`. This type of node should only be added to the AST
/// after the type checking phase by the compiler.
#[derive(Clone)]
pub struct BuiltinNode {
    pub display: String,
    pub substitute_fn: SubstituteFn,
}

impl Debug for BuiltinNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BuiltinNode({})", self.display)
    }
}

impl PartialEq for BuiltinNode {
    fn eq(&self, other: &Self) -> bool {
        self.display == other.display
    }
}

impl Eq for BuiltinNode {}

impl BuiltinNode {
    /// Creates a new BuiltinNode with the given display name and substitute function.
    pub fn new<S, F>(display: S, substitute_fn: F) -> Self
    where
        S: Into<String>,
        F: 'static + Fn(&ExpressionNode) -> Option<ExpressionNode> + Send + Sync,
    {
        BuiltinNode {
            display: display.into(),
            substitute_fn: Arc::new(substitute_fn),
        }
    }

    /// Applies the substitute function to the given expression node.
    pub fn apply(&self, expr: &ExpressionNode) -> Option<ExpressionNode> {
        (self.substitute_fn)(expr)
    }
}

impl Display for BuiltinNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display)
    }
}

/// The StatementNode enum represents different types of statements in the abstract syntax tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatementNode {
    Quantifier(QuantifierNode),
    Relation(RelationNode),
    Builtin(BuiltinNode),
}

impl Display for StatementNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StatementNode::Quantifier(quantifier) => write!(f, "{}", quantifier),
            StatementNode::Relation(relation) => write!(f, "{}", relation),
            StatementNode::Builtin(builtin) => write!(f, "{}", builtin),
        }
    }
}

/// The ImplicationNode represents an implication in the abstract syntax tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImplicationNode {
    pub conditions: Vec<StatementNode>,
    pub conclusion: Vec<StatementNode>,
}

impl ImplicationNode {
    /// Creates a new ImplicationNode with the given conditions and conclusion.
    pub fn new(conditions: Vec<StatementNode>, conclusion: Vec<StatementNode>) -> Self {
        ImplicationNode {
            conditions,
            conclusion,
        }
    }
}

impl Display for ImplicationNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let conditions: Vec<String> = self.conditions.iter().map(|s| s.to_string()).collect();
        let conclusion: Vec<String> = self.conclusion.iter().map(|s| s.to_string()).collect();
        if !conditions.is_empty() {
            write!(f, "{} => ", conditions.join(", "))?;
        }

        write!(f, "{}", conclusion.join(", "))
    }
}

/// The DefineFunctionNode represents a function definition in the abstract syntax tree.
///
/// It contains a `Token` representing the function name and a `TypeNode` representing the type of
/// the function.
///
/// # Example
/// ```croof
/// def f : N -> N -> N
/// def g : N -> N
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefineFunctionNode {
    pub symbol: Token,
    pub type_node: TypeNode,
}

impl DefineFunctionNode {
    /// Creates a new DefineFunctionNode with the given symbol and type node.
    pub fn new(symbol: Token, type_node: TypeNode) -> Self {
        DefineFunctionNode { symbol, type_node }
    }
}

impl Display for DefineFunctionNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} : {}", self.symbol.value(), self.type_node)
    }
}

/// The DefineOperatorNode represents an operator definition in the abstract syntax tree.
///
/// It contains a `Token` representing the operator symbol and a `TypeNode` representing the type
/// of the operator.
///
/// # Example
/// ```croof
/// def + : N -> N -> N
/// def * : N -> N -> N
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefineOperatorNode {
    pub symbol: Token,
    pub type_node: TypeNode,
}

impl DefineOperatorNode {
    /// Creates a new DefineOperatorNode with the given symbol and type node.
    pub fn new(symbol: Token, type_node: TypeNode) -> Self {
        DefineOperatorNode { symbol, type_node }
    }
}

impl Display for DefineOperatorNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} : {}", self.symbol.value(), self.type_node)
    }
}

/// The DefineSetNode represents a set definition in the abstract syntax tree.
///
/// It contains a `Token` representing the set name and a `SetNode` representing the set itself.
///
/// # Example
/// ```croof
/// def S = {1, 2, 3}
/// def T = {}
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefineSetNode {
    pub symbol: Token,
    pub set: SetNode,
}

impl DefineSetNode {
    /// Creates a new DefineSetNode with the given symbol and set.
    pub fn new(symbol: Token, set: SetNode) -> Self {
        DefineSetNode { symbol, set }
    }
}

impl Hash for DefineSetNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.symbol.hash(state);
    }
}

impl Display for DefineSetNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.symbol.value(), self.set)
    }
}

/// The DefineNode enum represents different types of definitions in the abstract syntax tree.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DefineNode {
    Function(DefineFunctionNode),
    Operator(DefineOperatorNode),
    Set(DefineSetNode),
}

impl DefineNode {
    /// Get the symbol of the define node.
    pub fn symbol(&self) -> Token {
        match self {
            DefineNode::Function(node) => node.symbol.clone(),
            DefineNode::Operator(node) => node.symbol.clone(),
            DefineNode::Set(node) => node.symbol.clone(),
        }
    }
}

impl Display for DefineNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            DefineNode::Function(node) => write!(f, "{}", node),
            DefineNode::Operator(node) => write!(f, "{}", node),
            DefineNode::Set(node) => write!(f, "{}", node),
        }
    }
}

/// The ProgramNode represents the entire program in the abstract syntax tree.
///
/// It contains a vector of `DefineNode` for function, operator, and set definitions,
/// a vector of `ImplicationNode` for implications, and a vector of `ExpressionNode` for
/// evaluations.
///
/// # Example
/// ```croof
/// def f : N -> N -> N
/// def g : N -> N
///
/// f(x, y) => g(x) + g(y)
///
/// eval f(1, 2)
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ProgramNode {
    pub defines: Vec<DefineNode>,
    pub implications: Vec<ImplicationNode>,
    pub evaluations: Vec<ExpressionNode>,
}

impl ProgramNode {
    /// Creates a new ProgramNode with the given defines, implications, and evaluations.
    pub fn new(
        defines: Vec<DefineNode>,
        implications: Vec<ImplicationNode>,
        evaluations: Vec<ExpressionNode>,
    ) -> Self {
        ProgramNode {
            defines,
            implications,
            evaluations,
        }
    }

    /// Merges another ProgramNode into this one by extending the defines, implications, and
    /// evaluations.
    ///
    /// # Arguments
    /// * `other` - The ProgramNode to merge into this one.
    ///
    /// # Note
    /// This function will extend the current node's defines, implications, and evaluations
    /// with the ones from the other node.
    pub fn merge(&mut self, other: ProgramNode) {
        self.defines.extend(other.defines);
        self.implications.extend(other.implications);
        self.evaluations.extend(other.evaluations);
    }
}

impl Display for ProgramNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for define in &self.defines {
            writeln!(f, "def {}", define)?;
        }

        for implication in &self.implications {
            writeln!(f, "{}", implication)?;
        }

        for eval in &self.evaluations {
            writeln!(f, "eval {}", eval)?;
        }

        Ok(())
    }
}

/// Represents a parser error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParserError {
    Todo(String),
}

impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParserError::Todo(msg) => write!(f, "TODO: {}", msg),
        }
    }
}

/// Represents a parser that processes tokens from a lexer and builds an abstract syntax tree
/// (AST).
///
/// The parser uses a lexer to tokenize the input and a source map to keep track of the
/// source locations of tokens. It maintains the current token and the next token to facilitate
/// parsing operations.
pub struct Parser {
    lexer: Lexer,
    sourcemap: SourceMap,
    token: Token,
    next_token: Token,
}

impl Parser {
    /// Creates a new Parser with the given lexer and sourcemap.
    pub fn new(lexer: Lexer, sourcemap: &SourceMap) -> Self {
        let mut parser = Parser {
            lexer,
            sourcemap: sourcemap.clone(),
            token: Token::default(),
            next_token: Token::default(),
        };

        parser.read();
        parser.read();

        parser
    }

    fn read(&mut self) -> Token {
        self.token = self.next_token.clone();
        self.next_token = self.lexer.next_token();

        self.token.clone()
    }

    fn parse_type(&mut self) -> Result<TypeNode, ParserError> {
        // type ::= Type ( -> Type )*
        let mut types = Vec::new();

        loop {
            if self.token.kind != TokenKind::Type {
                return Err(ParserError::Todo(format!(
                    "{}, Expected type, found {:?}",
                    self.sourcemap.format_pos(&self.token),
                    self.token.kind
                )));
            }
            let type_node = self.token.clone();
            self.read();

            types.push(type_node);

            if self.token.kind == TokenKind::Arrow {
                self.read();
            } else {
                break;
            }
        }

        Ok(TypeNode::new(types))
    }

    fn parse_quantifier(&mut self) -> Result<QuantifierNode, ParserError> {
        // quantifier ::= (forall | exists) variable ':' type
        let kind = match &self.token.kind {
            TokenKind::Forall => QuantifierKind::Forall,
            TokenKind::Exists => QuantifierKind::Exists,
            otherwise => {
                return Err(ParserError::Todo(format!(
                    "{}, Expected quantifier (forall or exists), found {:?}",
                    self.sourcemap.format_pos(&self.token),
                    otherwise
                )));
            }
        };
        self.read();

        let symbol = match &self.token.kind {
            TokenKind::Identifier => self.token.clone(),
            TokenKind::Operator => self.token.clone(),
            otherwise => {
                return Err(ParserError::Todo(format!(
                    "{}, Expected identifier after quantifier, found {:?}",
                    self.sourcemap.format_pos(&self.token),
                    otherwise
                )));
            }
        };
        self.read();

        if self.token.kind != TokenKind::Colon {
            return Err(ParserError::Todo(format!(
                "{}, Expected ':' after variable, found {:?}",
                self.sourcemap.format_pos(&self.token),
                self.token.kind
            )));
        }
        self.read();

        let type_node = self.parse_type()?;

        Ok(QuantifierNode::new(kind, symbol, type_node))
    }

    fn parse_set(&mut self) -> Result<SetNode, ParserError> {
        match &self.token.kind {
            TokenKind::LBrace => {
                self.read();

                let mut elements = Vec::new();
                loop {
                    if self.token.kind == TokenKind::RBrace {
                        self.read();
                        break;
                    }

                    let element = self.parse_expression()?;
                    elements.push(element);

                    if self.token.kind == TokenKind::Comma {
                        self.read();
                    } else if self.token.kind == TokenKind::RBrace {
                        self.read();
                        break;
                    } else {
                        return Err(ParserError::Todo(format!(
                            "{}, Expected ',' or '}}', found {:?}",
                            self.sourcemap.format_pos(&self.token),
                            self.token.kind
                        )));
                    }
                }

                Ok(SetNode::new(elements))
            }
            otherwise => Err(ParserError::Todo(format!(
                "{}, Expected set, found {:?}",
                self.sourcemap.format_pos(&self.token),
                otherwise
            ))),
        }
    }

    fn parse_expression(&mut self) -> Result<ExpressionNode, ParserError> {
        let expr = match &self.token.kind {
            TokenKind::Type => self.parse_type().map(ExpressionNode::Type)?,
            TokenKind::LBrace => self.parse_set().map(ExpressionNode::Set)?,
            TokenKind::Number => {
                let value = self.token.clone();
                self.read();

                ExpressionNode::Number(NumberNode::new(value))
            }
            TokenKind::Literal => {
                let value = self.token.clone();
                self.read();

                ExpressionNode::Literal(LiteralNode::new(value))
            }
            TokenKind::Identifier => {
                let name = self.token.clone();
                self.read();

                let args = match self.token.kind {
                    TokenKind::LParen => {
                        self.read();

                        let mut arguments = Vec::new();
                        loop {
                            let argument = self.parse_expression()?;
                            arguments.push(argument);

                            if self.token.kind == TokenKind::RParen {
                                self.read();
                                break;
                            } else if self.token.kind == TokenKind::Comma {
                                self.read();
                            } else {
                                return Err(ParserError::Todo(format!(
                                    "{}, Expected ',' or ')', found {:?}",
                                    self.sourcemap.format_pos(&self.token),
                                    self.token.kind
                                )));
                            }
                        }
                        arguments
                    }
                    _ => vec![],
                };

                ExpressionNode::Binding(BindingNode::new(name, args))
            }
            TokenKind::LParen => {
                self.read();
                let expr = self.parse_expression()?;

                if self.token.kind != TokenKind::RParen {
                    return Err(ParserError::Todo(format!(
                        "{}, Expected ')', found {:?}",
                        self.sourcemap.format_pos(&self.token),
                        self.token.kind
                    )));
                }
                self.read();

                ExpressionNode::Paren(ParenNode::new(expr))
            }
            otherwise => {
                return Err(ParserError::Todo(format!(
                    "{}, Expected expression, found {:?}",
                    self.sourcemap.format_pos(&self.token),
                    otherwise
                )));
            }
        };

        let expr = match self.token.kind {
            TokenKind::Operator => {
                let operator = self.token.clone();
                self.read();

                let right_expr = self.parse_expression()?;

                ExpressionNode::Operator(OperatorNode::new(operator, expr, right_expr))
            }
            _ => expr,
        };

        Ok(expr)
    }

    fn parse_relation(&mut self) -> Result<RelationNode, ParserError> {
        // relation ::= expression = expression
        let lhs = self.parse_expression()?;

        let token = self.token.clone();
        let kind = match token.kind {
            TokenKind::Equal => {
                self.read();
                RelationKind::Equality
            }
            TokenKind::GreaterThan => {
                self.read();
                RelationKind::GreaterThan
            }
            otherwise => {
                return Err(ParserError::Todo(format!(
                    "{}, Expected '=', found {:?}",
                    self.sourcemap.format_pos(&self.token),
                    otherwise
                )));
            }
        };

        let rhs = self.parse_expression()?;

        Ok(RelationNode::new(kind, token, lhs, rhs))
    }

    fn parse_statement(&mut self) -> Result<StatementNode, ParserError> {
        match self.token.kind {
            TokenKind::Forall | TokenKind::Exists => {
                self.parse_quantifier().map(StatementNode::Quantifier)
            }
            _ => self.parse_relation().map(StatementNode::Relation),
        }
    }

    fn parse_implication(&mut self) -> Result<ImplicationNode, ParserError> {
        // implication ::= [[statment]+ =>]? [statement]+

        let mut statements = Vec::new();
        let is_conditions = loop {
            let statement = self.parse_statement()?;
            statements.push(statement);

            match self.token.kind {
                TokenKind::Then => {
                    self.read();
                    break true;
                }
                TokenKind::Comma => {
                    self.read();
                }
                _ => {
                    break false;
                }
            }
        };

        if !is_conditions {
            return Ok(ImplicationNode::new(Vec::new(), statements));
        }

        let conditions = statements;
        let mut conclusion = Vec::new();

        loop {
            let statement = self.parse_statement()?;
            conclusion.push(statement);

            match self.token.kind {
                TokenKind::Comma => {
                    self.read();
                }
                _ => {
                    break;
                }
            }
        }

        Ok(ImplicationNode::new(conditions, conclusion))
    }

    fn parse_define(&mut self) -> Result<DefineNode, ParserError> {
        match &self.token.kind {
            TokenKind::Identifier => {
                let symbol = self.token.clone();
                self.read();

                if self.token.kind != TokenKind::Colon {
                    return Err(ParserError::Todo(format!(
                        "{}, Expected ':' after identifier, found {:?}",
                        self.sourcemap.format_pos(&self.token),
                        self.token.kind
                    )));
                }
                self.read();

                let type_node = self.parse_type()?;

                Ok(DefineNode::Function(DefineFunctionNode::new(
                    symbol, type_node,
                )))
            }
            TokenKind::Operator => {
                let symbol = self.token.clone();
                self.read();

                if self.token.kind != TokenKind::Colon {
                    return Err(ParserError::Todo(format!(
                        "{}, Expected ':' after operator, found {:?}",
                        self.sourcemap.format_pos(&self.token),
                        self.token.kind
                    )));
                }
                self.read();

                let type_node = self.parse_type()?;

                Ok(DefineNode::Operator(DefineOperatorNode::new(
                    symbol, type_node,
                )))
            }
            TokenKind::Type => {
                let symbol = self.token.clone();
                self.read();

                if self.token.kind != TokenKind::Equal {
                    return Err(ParserError::Todo(format!(
                        "{}, Expected '=' after type, found {:?}",
                        self.sourcemap.format_pos(&self.token),
                        self.token.kind
                    )));
                }
                self.read();

                let set = self.parse_set()?;

                Ok(DefineNode::Set(DefineSetNode::new(symbol, set)))
            }
            otherwise => Err(ParserError::Todo(format!(
                "{}, Expected type, identifier or operator, found {:?}",
                self.sourcemap.format_pos(&self.token),
                otherwise
            ))),
        }
    }

    /// Parses the entire program and returns a `ProgramNode`.
    ///
    /// # Returns
    /// A `Result<ProgramNode, ParserError>` which contains the parsed program node if successful,
    /// or a `ParserError` if an error occurred during parsing.
    ///
    /// # Note
    /// This function will read tokens from the lexer until it reaches the end of the file (EOF).
    /// It will parse definitions, implications, and evaluations in the order they appear in the
    /// source code.
    pub fn parse(&mut self) -> Result<ProgramNode, ParserError> {
        let mut defines = Vec::new();
        let mut implications = Vec::new();
        let mut evaluations = Vec::new();

        loop {
            match self.token.kind {
                TokenKind::Eof => break,
                TokenKind::Eval => {
                    self.read();
                    let expr = self.parse_expression()?;

                    evaluations.push(expr);
                }
                TokenKind::Def => {
                    self.read();
                    let define = self.parse_define()?;

                    defines.push(define);
                }
                _ => {
                    let value = self.parse_implication()?;

                    implications.push(value);
                }
            }
        }

        Ok(ProgramNode::new(defines, implications, evaluations))
    }
}

pub fn parse(lexer: Lexer, sourcemap: &SourceMap) -> Result<ProgramNode, ParserError> {
    let mut parser = Parser::new(lexer, sourcemap);
    parser.parse()
}

/// Constants for built-in types and functions
pub const TYPE_N: &str = "N";
pub const FUNCTION_SUCC: &str = "succ"; // N -> N

pub const TYPE_Z: &str = "Z";
pub const FUNCTION_NEG: &str = "neg"; // Z -> Z

/// TypecheckerError represents errors that can occur during the type checking process.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypecheckerError {
    UndefinedType(Token),
    UndefinedLiteral(Token),
    UndefinedBinding {
        token: Token,
        arg_types: Vec<String>,
    },
    UndefinedOperator {
        token: Token,
        left_type: Option<Vec<String>>,
        right_type: Option<Vec<String>>,
    },
    RelationTypeMissmatch {
        relation: Token,
        expected: Vec<String>,
        found: Vec<String>,
    },
    RedefinedType(Token),
    RedefinedBinding(Token),
    RedefinedOperator(Token),
}

impl WithToken for TypecheckerError {
    fn token(&self) -> Token {
        match self {
            TypecheckerError::UndefinedType(token) => token.clone(),
            TypecheckerError::UndefinedLiteral(token) => token.clone(),
            TypecheckerError::UndefinedBinding { token, .. } => token.clone(),
            TypecheckerError::UndefinedOperator { token, .. } => token.clone(),
            TypecheckerError::RelationTypeMissmatch { relation, .. } => relation.clone(),
            TypecheckerError::RedefinedType(token) => token.clone(),
            TypecheckerError::RedefinedBinding(token) => token.clone(),
            TypecheckerError::RedefinedOperator(token) => token.clone(),
        }
    }
}

impl Display for TypecheckerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypecheckerError::UndefinedType(token) => {
                write!(f, "Type is not defined {}", token.value())
            }
            TypecheckerError::UndefinedLiteral(token) => {
                write!(f, "Literal is not defined \"{}\"", token.value())
            }
            TypecheckerError::UndefinedBinding { token, arg_types } => {
                if arg_types.is_empty() {
                    write!(f, "Binding {} is not defined", token.value())
                } else {
                    write!(
                        f,
                        "Binding {} with input type {} is not defined",
                        token.value(),
                        arg_types.join(" -> ")
                    )
                }
            }
            TypecheckerError::UndefinedOperator {
                token,
                left_type,
                right_type,
            } => {
                write!(
                    f,
                    "Operator {} is not defined with left type {} and right type {}",
                    token.value(),
                    left_type
                        .as_ref()
                        .map(|t| t.join(" -> "))
                        .unwrap_or("?".to_string()),
                    right_type
                        .clone()
                        .map(|t| t.join(" -> "))
                        .unwrap_or("?".to_string())
                )
            }
            TypecheckerError::RelationTypeMissmatch {
                relation: _,
                expected,
                found,
            } => {
                write!(
                    f,
                    "Relation: Cannot compare Types {} and {}",
                    expected.join(" -> "),
                    found.join(" -> ")
                )
            }
            TypecheckerError::RedefinedBinding(token) => {
                write!(f, "Binding {} is already defined", token.value())
            }
            TypecheckerError::RedefinedOperator(token) => {
                write!(f, "Operator {} is already defined", token.value())
            }
            TypecheckerError::RedefinedType(token) => {
                write!(f, "Type {} is already defined", token.value())
            }
        }
    }
}

/// Typechecker is responsible for checking types of expressions and statements in the program.
pub struct Typechecker {
    defines: HashMap<String, HashMap<Vec<String>, DefineNode>>,
}

/// Helper function to check if two types can be inferred from each other
///
/// # Arguments
/// * `left_type` - The type of the left expression.
/// * `right_type` - The type of the right expression.
///
/// # Returns
/// `true` if the types can be inferred from each other, `false` otherwise.
///
/// # Notes
/// This function checks if the left type is `N` and the right type is `Z`, or if both types are
/// equal.
fn can_infer_type(left_type: &[String], right_type: &[String]) -> bool {
    (left_type.len() == 1
        && right_type.len() == 1
        && (left_type[0] == TYPE_N && right_type[0] == TYPE_Z))
        || left_type == right_type
}

/// Returns a list of built-in implications that can be used for type checking and inference.
/// This function provides a set of common implications that are used in the type checking process
/// to infer types and validate expressions.
///
/// # Returns
/// A vector of `ImplicationNode` instances representing built-in implications.
pub fn builtin_implications() -> Vec<ImplicationNode> {
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

impl Typechecker {
    /// Creates a new Typechecker instance with built-in definitions and checks for redefinitions.
    ///
    /// # Notes
    /// * This function initializes the typechecker with built-in types and functions such as `N`,
    /// `Z`, `succ`, and `neg`.
    /// * It also checks for redefinitions of user-defined types, functions, and operators.
    pub fn new(defines: Vec<DefineNode>) -> (Self, Vec<TypecheckerError>) {
        let mut mapping: HashMap<String, HashMap<Vec<String>, DefineNode>> = HashMap::new();

        // def N = { }
        mapping.insert(
            TYPE_N.to_string(),
            HashMap::from([(
                vec![],
                DefineNode::Set(DefineSetNode::new(
                    Token::with_value(TokenKind::Type, TYPE_N),
                    SetNode::new(vec![]),
                )),
            )]),
        );

        // def Z = { }
        mapping.insert(
            TYPE_Z.to_string(),
            HashMap::from([(
                vec![],
                DefineNode::Set(DefineSetNode::new(
                    Token::with_value(TokenKind::Type, TYPE_Z),
                    SetNode::new(vec![]),
                )),
            )]),
        );

        // def succ : N -> N, Z -> Z
        mapping.insert(
            FUNCTION_SUCC.to_string(),
            HashMap::from([
                (
                    vec![TYPE_N.to_string()],
                    DefineNode::Function(DefineFunctionNode::new(
                        Token::with_value(TokenKind::Identifier, FUNCTION_SUCC),
                        TypeNode::new(vec![
                            Token::with_value(TokenKind::Type, TYPE_N),
                            Token::with_value(TokenKind::Type, TYPE_N),
                        ]),
                    )),
                ),
                (
                    vec![TYPE_Z.to_string()],
                    DefineNode::Function(DefineFunctionNode::new(
                        Token::with_value(TokenKind::Identifier, FUNCTION_SUCC),
                        TypeNode::new(vec![
                            Token::with_value(TokenKind::Type, TYPE_Z),
                            Token::with_value(TokenKind::Type, TYPE_Z),
                        ]),
                    )),
                ),
            ]),
        );

        // def neg : Z -> Z
        mapping.insert(
            FUNCTION_NEG.to_string(),
            HashMap::from([(
                vec![TYPE_Z.to_string()],
                DefineNode::Function(DefineFunctionNode::new(
                    Token::with_value(TokenKind::Identifier, FUNCTION_NEG),
                    TypeNode::new(vec![
                        Token::with_value(TokenKind::Type, TYPE_Z),
                        Token::with_value(TokenKind::Type, TYPE_Z),
                    ]),
                )),
            )]),
        );

        let mut typechecker = Typechecker { defines: mapping };

        let mut errors = vec![];

        for define in defines {
            let symbol = define.symbol();
            let name = symbol.value();

            match &define {
                DefineNode::Function(node) => {
                    let (_, arg_types) = node.type_node.types.split_last().unwrap();
                    let arg_types: Vec<String> =
                        arg_types.iter().map(|token| token.value()).collect();

                    if typechecker
                        .defines
                        .get(&name)
                        .map_or(false, |arg_map| arg_map.contains_key(&arg_types))
                    {
                        errors.push(TypecheckerError::RedefinedBinding(symbol));
                    } else {
                        typechecker
                            .defines
                            .entry(name.clone())
                            .or_default()
                            .insert(arg_types, define.clone());
                    }
                }
                DefineNode::Operator(node) => {
                    let left_type = node.type_node.types[0].clone().value();
                    let right_type = node.type_node.types[1].clone().value();
                    let arg_types = vec![left_type, right_type];

                    if typechecker
                        .defines
                        .get(&name)
                        .map_or(false, |arg_map| arg_map.contains_key(&arg_types))
                    {
                        errors.push(TypecheckerError::RedefinedOperator(symbol));
                    } else {
                        typechecker
                            .defines
                            .entry(name.clone())
                            .or_default()
                            .insert(arg_types, define.clone());
                    }
                }
                DefineNode::Set(_) => {
                    if typechecker.defines.contains_key(&name) {
                        errors.push(TypecheckerError::RedefinedType(symbol));
                    } else {
                        typechecker
                            .defines
                            .entry(name.clone())
                            .or_default()
                            .insert(vec![], define.clone());
                    }
                }
            }

            match &define {
                DefineNode::Function(node) => {
                    errors.extend(typechecker.check_type(&node.type_node, &HashMap::default()));
                }
                DefineNode::Operator(node) => {
                    errors.extend(typechecker.check_type(&node.type_node, &HashMap::default()));
                }
                DefineNode::Set(_) => {
                    // TODO: Check if the set is well-defined
                }
            }
        }

        (typechecker, errors)
    }

    fn check_type(
        &self,
        type_node: &TypeNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> Vec<TypecheckerError> {
        let mut errors = vec![];

        for token in &type_node.types {
            if token.kind == TokenKind::Type {
                let name = token.value();
                if !symbols.contains_key(&name) && !self.defines.contains_key(&name) {
                    errors.push(TypecheckerError::UndefinedType(token.clone()));
                }
            }
        }

        errors
    }

    fn overloads(
        &self,
        name: &str,
        arg_types: &[String],
        symbols: &HashMap<String, TypeNode>,
    ) -> HashMap<Vec<String>, Vec<String>> {
        let mut overloads: HashMap<Vec<String>, Vec<String>> = self
            .defines
            .get(name)
            .cloned()
            .unwrap_or(HashMap::new())
            .into_iter()
            .filter_map(|(k, v)| match v {
                DefineNode::Function(node) => Some((k, node.type_node.types)),
                DefineNode::Operator(node) => Some((k, node.type_node.types)),
                DefineNode::Set(_) => None,
            })
            .map(|(k, v)| {
                (
                    k,
                    v.iter()
                        .skip(arg_types.len())
                        .map(|token| token.value())
                        .collect::<Vec<_>>(),
                )
            })
            .collect();

        if let Some(node_type) = symbols.get(name) {
            let input_types = node_type
                .types
                .iter()
                .take(arg_types.len())
                .map(|token| token.value())
                .collect::<Vec<_>>();
            let node_type = node_type
                .types
                .iter()
                .skip(arg_types.len())
                .map(|token| token.value())
                .collect::<Vec<_>>();
            overloads.insert(input_types, node_type);
        }

        overloads
    }

    fn check_operator(
        &self,
        node: &mut OperatorNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> (Option<Vec<String>>, Vec<TypecheckerError>) {
        let name = node.operator.value();
        let mut errors = vec![];

        let (left_type, left_errors) = self.check_expression(&mut node.left, symbols);
        errors.extend(left_errors);

        let (right_type, right_errors) = self.check_expression(&mut node.right, symbols);
        errors.extend(right_errors);

        // TODO: Maybe we want to infer some operator and still return Some type
        if !errors.is_empty() {
            errors.push(TypecheckerError::UndefinedOperator {
                token: node.operator.clone(),
                left_type,
                right_type,
            });

            return (None, errors);
        }

        let Some(left_type) = left_type else {
            unreachable!("Left type should always be Some");
        };
        let Some(right_type) = right_type else {
            unreachable!("Right type should always be Some");
        };
        let arg_types = left_type
            .iter()
            .chain(right_type.iter())
            .map(|t| t.to_string())
            .collect::<Vec<_>>();

        let overloads = self.overloads(&name, &arg_types, symbols);

        if let Some(types) = overloads.get(&arg_types) {
            node.node_type = Some(types.clone());
            return (Some(types.clone()), errors);
        }

        if left_type.len() == 1 && right_type.len() == 1 {
            let left_type = left_type[0].clone();
            let right_type = right_type[0].clone();

            // Try to relax from N to Z
            for (input_types, overload) in overloads {
                let left_input_type = input_types[0].clone();
                let right_input_type = input_types[1].clone();

                if (left_type == TYPE_N
                    && left_input_type == TYPE_Z
                    && right_type == right_input_type)
                    || (right_type == TYPE_N
                        && right_input_type == TYPE_Z
                        && left_type == left_input_type)
                {
                    node.node_type = Some(overload.clone());
                    return (Some(overload), errors);
                }
            }
        }

        errors.push(TypecheckerError::UndefinedOperator {
            token: node.operator.clone(),
            left_type: Some(left_type),
            right_type: Some(right_type),
        });
        (None, errors)
    }

    fn check_binding(
        &self,
        node: &mut BindingNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> (Option<Vec<String>>, Vec<TypecheckerError>) {
        let name = node.name.value();
        let mut errors = vec![];

        let mut arg_types: Vec<String> = vec![];
        for arg in node.arguments.iter_mut() {
            let (arg_type, arg_errors) = self.check_expression(arg, symbols);
            errors.extend(arg_errors);

            if let Some(t) = arg_type {
                arg_types.extend(t)
            }
        }

        // TODO: Maybe we want to infer some binding and still return Some type
        if !errors.is_empty() {
            errors.push(TypecheckerError::UndefinedBinding {
                token: node.name.clone(),
                arg_types,
            });

            return (None, errors);
        }

        let overloads = self.overloads(&name, &arg_types, symbols);

        if let Some(types) = overloads.get(&arg_types) {
            node.node_type = Some(types.clone());
            return (Some(types.clone()), errors);
        }

        // Try to relax from N to Z
        for (input_types, overload) in overloads {
            let mut can_use = true;

            for (arg_type, input_type) in arg_types.iter().zip(input_types.iter()) {
                can_use = can_use
                    && ((arg_type == input_type) || (arg_type == TYPE_N && input_type == TYPE_Z));
            }

            if can_use {
                node.node_type = Some(overload.clone());
                return (Some(overload), errors);
            }
        }

        errors.push(TypecheckerError::UndefinedBinding {
            token: node.name.clone(),
            arg_types,
        });
        (None, errors)
    }

    fn check_number(&self, node: &mut NumberNode) -> (Option<Vec<String>>, Vec<TypecheckerError>) {
        let Ok(number) = node.value.value().parse::<i64>() else {
            return (
                None,
                vec![TypecheckerError::UndefinedLiteral(node.value.clone())],
            );
        };
        let type_value = if number >= 0 { TYPE_N } else { TYPE_Z };

        node.node_type = Some(vec![type_value.to_string()]);

        (node.node_type.clone(), vec![])
    }

    fn check_literal(
        &self,
        node: &mut LiteralNode,
    ) -> (Option<Vec<String>>, Vec<TypecheckerError>) {
        for (symbol, defines) in &self.defines {
            for define in defines.values() {
                if let DefineNode::Set(define) = define {
                    if define
                        .set
                        .elements
                        .contains(&ExpressionNode::Literal(node.clone()))
                    {
                        node.node_type = Some(vec![symbol.clone()]);

                        return (node.node_type.clone(), vec![]);
                    }
                };
            }
        }

        (
            None,
            vec![TypecheckerError::UndefinedLiteral(node.value.clone())],
        )
    }

    fn check_paren(
        &self,
        node: &mut ParenNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> (Option<Vec<String>>, Vec<TypecheckerError>) {
        let (type_node, paren_errors) = self.check_expression(&mut node.expression, symbols);

        node.node_type = type_node.clone();

        (type_node, paren_errors)
    }

    /// Checks the type of an expression and returns the type and any errors encountered.
    ///
    /// # Arguments
    /// * `expression` - A mutable reference to the expression node to be checked.
    /// * `symbols` - A reference to a map of symbols and their types.
    ///
    /// # Returns
    /// A tuple containing:
    /// * An `Option<Vec<String>>` representing the type of the expression if it can be determined,
    /// * a `Vec<TypecheckerError>` containing any errors encountered during the type checking
    /// process.
    pub fn check_expression(
        &self,
        expression: &mut ExpressionNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> (Option<Vec<String>>, Vec<TypecheckerError>) {
        match expression {
            ExpressionNode::Set(_) => todo!(),
            ExpressionNode::Type(_) => todo!(),
            ExpressionNode::Number(node) => self.check_number(node),
            ExpressionNode::Literal(node) => self.check_literal(node),
            ExpressionNode::Binding(node) => self.check_binding(node, symbols),
            ExpressionNode::Operator(node) => self.check_operator(node, symbols),
            ExpressionNode::Paren(node) => self.check_paren(node, symbols),
        }
    }

    fn check_relation(
        &self,
        node: &mut RelationNode,
        symbols: &HashMap<String, TypeNode>,
    ) -> Vec<TypecheckerError> {
        let mut errors = vec![];

        let (left_type, left_errors) = self.check_expression(&mut node.left, symbols);
        errors.extend(left_errors);
        let (right_type, right_errors) = self.check_expression(&mut node.right, symbols);
        errors.extend(right_errors);

        if let (Some(left_type), Some(right_type)) = (left_type, right_type) {
            if left_type.len() != right_type.len()
                || left_type.iter().zip(right_type.iter()).any(|(l, r)| l != r)
            {
                errors.push(TypecheckerError::RelationTypeMissmatch {
                    relation: node.token.clone(),
                    expected: left_type,
                    found: right_type,
                });
            }
        }

        errors
    }

    fn check_quantifier(
        &self,
        node: &mut QuantifierNode,
        symbols: &mut HashMap<String, TypeNode>,
    ) -> Vec<TypecheckerError> {
        let mut errors = vec![];

        let symbol = node.symbol.clone();
        let name = symbol.value();

        if let hash_map::Entry::Vacant(e) = symbols.entry(name) {
            e.insert(node.type_node.clone());
        } else {
            errors.push(TypecheckerError::RedefinedBinding(symbol.clone()));
        }

        errors
    }

    fn check_statement(
        &self,
        statement: &mut StatementNode,
        symbols: &mut HashMap<String, TypeNode>,
    ) -> Vec<TypecheckerError> {
        match statement {
            StatementNode::Quantifier(quantifier_node) => {
                self.check_quantifier(quantifier_node, symbols)
            }
            StatementNode::Relation(relation_node) => self.check_relation(relation_node, symbols),
            StatementNode::Builtin(_) => vec![], // Built-in statements are assumed to be valid
        }
    }

    /// Checks an implication node, validating its conditions and conclusions.
    ///
    /// # Arguments
    /// * `implication` - A mutable reference to the implication node to be checked.
    ///
    /// # Returns
    /// A vector of `TypecheckerError` containing any errors encountered during the type checking
    /// process.
    pub fn check_implication(&self, implication: &mut ImplicationNode) -> Vec<TypecheckerError> {
        let mut symbols: HashMap<String, TypeNode> = HashMap::new();
        let mut errors = vec![];

        for condition in &mut implication.conditions {
            errors.extend(self.check_statement(condition, &mut symbols));
        }

        for conclusion in &mut implication.conclusion {
            errors.extend(self.check_statement(conclusion, &mut symbols));
        }

        errors
    }

    /// Checks a program node, validating all implications and statements.
    ///
    /// # Arguments
    /// * `program` - A mutable reference to the program node to be checked.
    ///
    /// # Returns
    /// A vector of `TypecheckerError` containing any errors encountered during the type checking
    /// process.
    pub fn check_program(&self, program: &mut ProgramNode) -> Vec<TypecheckerError> {
        let mut errors = vec![];

        for implication in &mut program.implications {
            errors.extend(self.check_implication(implication));
        }
        program.implications.extend(builtin_implications());

        for eval in &mut program.evaluations {
            let (_, eval_errors) = self.check_expression(eval, &HashMap::default());
            errors.extend(eval_errors);
        }

        errors
    }
}

/// Typecheck the given AST and report any errors found during type checking.
///
/// # Arguments
/// * `ast` - A mutable reference to the program node representing the AST to be typechecked.
/// * `sourcemap` - A reference to the source map used for error reporting.
///
/// # Returns
/// A vector of `TypecheckerError` containing any errors encountered during the type checking
pub fn typecheck(ast: &mut ProgramNode) -> Vec<TypecheckerError> {
    let (typechecker, mut errors) = Typechecker::new(ast.defines.clone());
    errors.extend(typechecker.check_program(ast));

    errors
}

/// Matcher is a utility for matching expressions against implications
/// and performing substitutions based on those implications.
pub struct Matcher {}

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

        let mapping = match statement {
            StatementNode::Quantifier(_) => todo!("Implement mapping for QuantifierNode"),
            StatementNode::Relation(node) => expression.create_mapping(&node.left),
            StatementNode::Builtin(_) => Some(HashMap::new()),
        };

        if let Some(mapping) = mapping {
            if let Some(conditions) = implication
                .conditions
                .iter()
                .map(|condition| match condition {
                    StatementNode::Quantifier(node) => {
                        Some(StatementNode::Quantifier(node.clone()))
                    }
                    StatementNode::Relation(node) => {
                        let mut relation = node.clone();
                        relation.left = node.left.apply(&mapping)?;
                        relation.right = node.right.apply(&mapping)?;

                        Some(StatementNode::Relation(relation))
                    }
                    StatementNode::Builtin(_) => todo!("Handle builtin statements"),
                })
                .collect::<Option<Vec<_>>>()
            {
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

/// Displays the solution of a proof, including the expression, steps taken, and the final result.
///
/// # Arguments
/// * `expression` - The original expression being proved.
/// * `steps` - A slice of proof steps taken during the proof process.
/// * `result` - The final result of the proof.
pub fn display_solution(expression: &ExpressionNode, steps: &[ProofStep], result: &ExpressionNode) {
    println!("Expression: {}", expression);
    for (parent, target, implication) in steps {
        println!("  - {} => {} (apply {})", parent, target, implication);
    }
    println!("Result: {}", result);
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use crate::{
        BindingNode, ExpressionNode, NumberNode, OperatorNode, ParenNode, Token, TokenKind, TYPE_N,
    };

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
