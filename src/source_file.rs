pub mod prelude {
    pub use super::SourceFile;
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
