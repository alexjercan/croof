use clap::Parser as ArgParser;
use std::io;
use typechecker::Typechecker;

mod lexer;
mod parser;
mod solver;
mod typechecker;

use lexer::SourceMap;
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
    /// Stop at the typechecker stage
    #[arg(long, short = 't')]
    typechecker: bool,
}

fn main() -> io::Result<()> {
    let args = Args::parse();
    let mut sourcemap = SourceMap::default();
    let mut ast: ProgramNode = ProgramNode::default();

    for file in args.files {
        let lexer = sourcemap.add_file(Some(file))?;

        if args.lexer {
            lexer.display_tokens(&sourcemap);
            continue;
        }

        let mut parser = Parser::new(lexer, &sourcemap);
        let program = parser.parse().expect("Failed to parse program");

        ast.merge(program);
    }

    if args.lexer {
        return Ok(());
    }

    if args.parser {
        println!("{}", ast);
        return Ok(());
    }

    let typechecker = Typechecker::new(ast.defines.clone(), &sourcemap);
    for implication in &ast.implications {
        match typechecker.check(implication) {
            Ok(_) => println!("Typechecker OK"),
            Err(error) => println!("{:?}", error),
        }
    }

    if args.typechecker {
        return Ok(());
    }

    let solver = Solver::new(ast.implications.clone());
    for expression in &ast.evaluations {
        match solver.solve(expression) {
            Ok((steps, result)) => {
                println!("Expression: {}", expression);
                for (parent, implication_index) in steps {
                    println!(
                        "  - {} (apply {} [{}])",
                        parent, ast.implications[implication_index], implication_index
                    );
                }
                println!("Result: {}", result);
            }
            Err(e) => eprintln!("Error solving expression: {:?}", e),
        }
    }

    Ok(())
}

// TODO: add reference to lexer in each token such that we can display line and col and filename
// TODO: check_expression should return Option<TypeNode> so we can ignore failures and just print
// them
// TODO: In the typechecker we should annotate the AST with types -> leaf nodes from Parser should
// have a type reference
// TODO: In the solver we can use AST types to check if we can substitute (e.g a + b -> 1 + 1
// should also check if typeof(a) == typeof(1) besides just the operator being the same)
