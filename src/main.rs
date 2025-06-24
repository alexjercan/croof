use clap::Parser as ArgParser;
use std::collections::{hash_map, HashMap};
use std::io::{self, BufRead, Write};
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
    /// Run in interactive mode
    #[arg(long, short = 'i')]
    interactive: bool,
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

pub fn display_solution(evaluation: &EvaluationNode, steps: &[ProofStep], result: &ExpressionNode) {
    println!("Expression: {}", evaluation);
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
            .add_file(Some(&file))
            .expect("Failed to create lexer");

        match Parser::new(lexer).parse() {
            Ok(program) => ast.merge(program),
            Err(error) => {
                sourcemap.display_error(&error);
                eprintln!("Failed to parse file: {}", file);
                return ExitCode::FAILURE;
            }
        }
    }

    if args.parser {
        println!("{}", ast);
        return ExitCode::SUCCESS;
    }

    ast.implications.extend(builtin_implications());

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
    for evaluation in &ast.evaluations {
        match solver.solve(evaluation) {
            Ok((steps, result)) => {
                display_solution(evaluation, &steps, &result);
            }
            Err(e) => eprintln!("Error solving expression: {:?}", e),
        }
    }

    if args.interactive {
        let stdin = io::stdin();

        loop {
            let mut buffer = String::new();

            for line in stdin.lock().lines() {
                let Ok(line) = line else { break };

                if line == "." {
                    break;
                }

                buffer.push_str(&line);
            }

            let lexer = sourcemap.add_content(&buffer);

            let mut program = match Parser::new(lexer).parse() {
                Ok(program) => program,
                Err(error) => {
                    sourcemap.display_error(&error);
                    eprintln!("Failed to parse content");
                    continue;
                }
            };

            let errors = typechecker.check_program(&mut program);
            if !errors.is_empty() {
                sourcemap.display_errors(&errors);
                eprintln!(
                    "Typechecking failed with {} {}",
                    errors.len(),
                    if errors.len() == 1 { "error" } else { "errors" }
                );
                continue;
            }

            ast.merge(program.clone());

            let matcher = Matcher::new();
            for evaluation in &program.evaluations {
                let mut expression = evaluation.expression.clone();

                loop {
                    println!("eval {}", expression);

                    let mut substitutions = HashMap::<ImplicationNode, Vec<ExpressionNode>>::new();
                    for implication in &ast.implications {
                        for conclusion in &implication.conclusion {
                            for (substituted, _) in matcher.substitute(&expression, &implication.conditions, conclusion) {

                                match substitutions.entry(implication.clone()) {
                                    hash_map::Entry::Occupied(mut e) => {
                                        e.get_mut().push(substituted);
                                    },
                                    hash_map::Entry::Vacant(e) => {
                                        e.insert(vec![substituted]);
                                    },
                                };
                            }
                        }
                    }

                    let substitutions = substitutions.iter().collect::<Vec<_>>();

                    println!("Available implications: ");
                    for (i, (implication, _)) in substitutions.iter().enumerate() {
                        println!("{}: {}", i, implication);
                    }
                    print!("Which implication do you want to choose? ");
                    let _ = io::stdout().flush();

                    let Some(Ok(choice)) = stdin.lock().lines().next() else { break };
                    if choice == "." {
                        println!("DONE: {}", expression);
                        break;
                    }

                    let Ok(choice) = choice.parse::<usize>() else { break };

                    let (_, substitutions) = substitutions[choice];
                    println!("Available substitutions: ");
                    for (i, substitution) in substitutions.iter().enumerate() {
                        println!("{}: {}", i, substitution);
                    }
                    print!("Which substitution do you want to choose? ");
                    let _ = io::stdout().flush();

                    let Some(Ok(choice)) = stdin.lock().lines().next() else { break };
                    let Ok(choice) = choice.parse::<usize>() else { break };

                    expression = substitutions[choice].clone();
                }
            }
        }
    }

    ExitCode::SUCCESS
}

