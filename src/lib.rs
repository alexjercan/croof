mod util;

pub mod source_file;
pub mod source_map;
pub mod token;
pub mod lexer;
pub mod ast;
pub mod parser;
pub mod typechecker;
pub mod matcher;
pub mod solver;

pub mod prelude {
    pub use crate::source_map::prelude::*;
    pub use crate::token::prelude::*;
    pub use crate::lexer::prelude::*;
    pub use crate::ast::prelude::*;
    pub use crate::parser::prelude::*;
    pub use crate::typechecker::prelude::*;
    pub use crate::matcher::prelude::*;
    pub use crate::solver::prelude::*;
}
