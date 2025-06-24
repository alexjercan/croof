pub mod prelude {
    pub use super::SourceMap;
}

use std::{
    fmt::{Debug, Display},
    io,
};

use crate::{
    lexer::Lexer,
    source_file::SourceFile,
    token::{Token, WithToken},
    util::read_input,
};

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
    ///     from standard input.
    ///
    /// # Returns
    /// A `Result` containing a `Lexer` instance initialized with the new source file, or an
    /// `io::Error` if reading the file fails.
    ///
    /// # Notes
    /// * The ID of the new source file is the current length of the `files` vector, ensuring
    ///     that each file has a unique ID.
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

    pub fn add_content<S>(&mut self, content: S) -> Lexer
    where
        S: Into<String>,
    {
        let id = self.files.len();

        let file = SourceFile::new(id, "<stdin>".to_string(), content.into());
        self.files.push(file);

        Lexer::new(self.files[id].clone())
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
    /// "filename:line:column", where `filename` is the name of the source file, `line` is the
    /// line number (1-based), and `column` is the column number (1-based).
    pub fn format_pos(&self, token: &Token) -> String {
        let file = self
            .files
            .get(token.source_id)
            .expect("Source file not found");

        let (line, col) = file.pos_to_lc(token.pos);
        format!("{}:{}:{}", file.filename, line, col)
    }

    /// Display the error message for a given error object, formatted with the source map.
    ///
    /// # Arguments
    /// * `error` - A reference to an object that implements the `Debug`, `Display`, and
    ///     `WithToken` traits.
    ///
    /// # Notes
    /// This function uses the `format_error` method of the `SourceMap` to format the error message
    /// with the token's position and the error's string representation.
    pub fn display_error<T>(&self, error: &T)
    where
        T: Debug + Display + Clone + WithToken,
    {
        eprintln!(
            "{}, {}",
            self.format_pos(&error.token()),
            &error.to_string()
        );
    }

    /// Display a list of errors, formatting each error with its token's position.
    ///
    /// # Arguments
    /// * `errors` - A slice of objects that implement the `Debug`, `Display`, and `WithToken`
    ///     traits.
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
