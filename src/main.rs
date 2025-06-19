use clap::Parser as ArgParser;
use std::process::ExitCode;

use croof::prelude::*;

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

fn display_tokens(files: Vec<String>) {
    let mut sourcemap = SourceMap::default();

    for file in files {
        let lexer = sourcemap
            .add_file(Some(file))
            .expect("Failed to create lexer");

        for token in lexer.into_iter() {
            sourcemap.display_token(&token);
        }
    }
}

pub fn display_solution(expression: &ExpressionNode, steps: &[ProofStep], result: &ExpressionNode) {
    println!("Expression: {}", expression);
    for (parent, target, implication) in steps {
        println!("  - {} => {} (apply {})", parent, target, implication);
    }
    println!("Result: {}", result);
}

fn main() -> ExitCode {
    let args = Args::parse();
    if args.lexer {
        display_tokens(args.files);
        return ExitCode::SUCCESS;
    }

    let mut ast = ProgramNode::default();
    let mut sourcemap = SourceMap::default();

    for file in args.files {
        let lexer = sourcemap
            .add_file(Some(file))
            .expect("Failed to create lexer");

        let program = Parser::new(lexer, &sourcemap).parse().expect("Failed to parse input");

        ast.merge(program);
    }

    if args.parser {
        println!("{}", ast);
        return ExitCode::SUCCESS;
    }

    let mut typechecker = Typechecker::new();
    let errors = typechecker.check_program(&mut ast);
    if !errors.is_empty() {
        sourcemap.display_errors(&errors);
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

    let solver = AstarSolver::new(Matcher::new(), ast.implications.clone());
    for expression in &ast.evaluations {
        match solver.solve(expression) {
            Ok((steps, result)) => {
                display_solution(expression, &steps, &result);
            }
            Err(e) => eprintln!("Error solving expression: {:?}", e),
        }
    }

    ExitCode::SUCCESS
}

// TODO: Allow eval expression to contain statements (quantifiers, relations, etc.) and then have
// the expression to be solved
// Example: `eval forall a : N, a + a`
// Then we have some steps.... and then
// Result: 2 * a
