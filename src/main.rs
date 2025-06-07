use clap::Parser as ArgParser;
use std::{collections::HashMap, process::ExitCode};
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
    typecheck: bool,
}

fn main() -> ExitCode {
    let args = Args::parse();
    let mut sourcemap = SourceMap::default();
    let mut ast: ProgramNode = ProgramNode::default();

    for file in args.files {
        let lexer = sourcemap.add_file(Some(file)).expect("Failed to create lexer");

        if args.lexer {
            lexer.display_tokens(&sourcemap);
            continue;
        }

        let mut parser = Parser::new(lexer, &sourcemap);
        let program = parser.parse().expect("Failed to parse input");

        ast.merge(program);
    }

    if args.lexer {
        return ExitCode::SUCCESS;
    }

    if args.parser {
        println!("{}", ast);
        return ExitCode::SUCCESS;
    }

    let (typechecker, mut errors) = Typechecker::new(ast.defines.clone(), &sourcemap);

    for implication in &mut ast.implications {
        errors.extend(typechecker.check(implication));
    }

    for eval in &mut ast.evaluations {
        let (_, eval_errors) = typechecker.check_expression(eval, &HashMap::default());
        errors.extend(eval_errors);
    }

    if !errors.is_empty() {
        typechecker.display_errors(&errors);
        eprintln!("Typechecking failed with {} {}", errors.len(), if errors.len() == 1 { "error" } else { "errors" });
        return ExitCode::FAILURE;
    }

    if args.typecheck {
        return ExitCode::SUCCESS;
    }

    let solver = Solver::new(ast.implications.clone());
    for expression in &ast.evaluations {
        match solver.solve(expression) {
            Ok((steps, result)) => {
                solver.display_solution(&expression, &steps, &result);
            }
            Err(e) => eprintln!("Error solving expression: {:?}", e),
        }
    }

    ExitCode::SUCCESS
}

// TODO: In the solver we can use AST types to check if we can substitute (e.g a + b -> 1 + 1
// should also check if typeof(a) == typeof(1) besides just the operator being the same)
// TODO: Maybe we want to return something like `Result<TypeNode, Vec<String>>` in the typechecker
// and collect all errors instead of printing them immediately.
