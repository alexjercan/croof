use clap::Parser as ArgParser;
use std::{fs::File, io::Read};

mod lexer;
mod parser;
mod solver;

use lexer::Lexer;
use parser::{Parser, ProgramNode};
use solver::Solver;

#[derive(ArgParser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// List of files to process; if not provided, reads from stdin
    #[arg()]
    files: Vec<String>,

    /// Stop at the lexer stage
    #[arg(long, short = 'l')]
    lexer: bool,
    /// Stop at the parser stage
    #[arg(long, short = 'p')]
    parser: bool,
}

fn read_file(filename: &str) -> String {
    let mut file = File::open(filename).expect("Failed to open file");
    let mut contents = String::new();

    file.read_to_string(&mut contents)
        .expect("Failed to read file");

    contents
}

fn main() {
    let args = Args::parse();
    let mut ast: ProgramNode = ProgramNode::default();

    for file in &args.files {
        let input = read_file(file);
        let mut lexer = Lexer::new(input);
        lexer.with_filename(file.to_string());

        if args.lexer {
            lexer.display_tokens();
        }

        let mut parser = Parser::new(lexer);
        let program = parser.parse().expect("Failed to parse program");

        ast.merge(program);
    }

    if args.parser {
        println!("{:#?}", ast);
    }

    let solver = Solver::new(ast.implications.clone());
    for expression in &ast.evaluations {
        match solver.solve(expression) {
            Ok((steps, result)) => {
                println!("Expression: {}", expression);
                for (parent, implication_index) in steps {
                    println!("  - {} (apply {} [{}])", parent, ast.implications[implication_index], implication_index);
                }
                println!("Result: {}", result);
            }
            Err(e) => eprintln!("Error solving expression: {:?}", e),
        }
    }
}
