use clap::Parser as ArgParser;
use std::{collections::HashMap, process::ExitCode};

use croof::{
    lexer::SourceMap,
    parser::{Parser, ProgramNode},
    solver::Solver,
    typechecker::Typechecker,
};

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
        let lexer = sourcemap
            .add_file(Some(file))
            .expect("Failed to create lexer");

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
        eprintln!(
            "Typechecking failed with {} {}",
            errors.len(),
            if errors.len() == 1 { "error" } else { "errors" }
        );
        return ExitCode::FAILURE;
    }

    if args.typecheck {
        println!("{}", ast);
        return ExitCode::SUCCESS;
    }

    let solver = Solver::new(ast.implications.clone());
    for expression in &ast.evaluations {
        match solver.solve(expression) {
            Ok((steps, result)) => {
                solver.display_solution(expression, &steps, &result);
            }
            Err(e) => eprintln!("Error solving expression: {:?}", e),
        }
    }

    ExitCode::SUCCESS
}

// TODO: How to actually compare ExpressionNode?
