//! The interactive mode will allow the user to define implications and solve expressions
//! in the terminal.
//!
//! This solve will use the parser and typechecker to ensure the expressions are valid
//! and it will add them to the implications list for solving. We can also define functions and
//! sets/types.
//!
//! We will split the lexer inputs using a `.` character, which will allow the user to
//! define multiple implications or expressions in a single input.
//!
//! To indicate that we are writing a define (a function or a set/type), we will use a
//! `def` keyword at the start, then we will parse the rest of the line as a define
//! and we will end with a `.` character (e.g. def f : N -> N -> N.)
//!
//! To indicate that we are writing an implication, we will just read everything until the `.`
//! (e.g. forall a : N, forall b : N => a + b = b + a.)
//!
//! To indicate that we are writing an expression to solve, we will use the `eval` keyword at the
//! start, then we will parse the rest of the line as a list of statements and then the expression
//! and we will end with a `.` character (e.g. eval forall a : N => a + 0.)
//!
//! Croof Shell will read and parse everything until the `.` character. Then it will go back into
//! reading mode. When in reading mode we can read again another set of implications or defines or
//! evaluations.
//!
//! Special symbols in croof shell:
//! - `help` to show the available commands (and the help messages).
//! - `begin` to start solving a new expression (here the shell will prompt the user to choose an
//! evaluation or proof to solve, this will set the current state to hold the new expression, with
//! all the steps and everything, overwritting the old one, then it will move us back to read mode).
//! - `end` to end the current solving and set the status of the current expression to solved. This
//! will also show all the steps and the final expression.
//! - `next` to move to the next step in the current solving process. The shell will print the
//! available implications that can be used, the user can choose one or cancel the operation. Then
//! after the implication is choosen, the shell will show us where to apply it. Then the shell
//! will move to the next step in the solving process, applying the chosen implication.
//! - `back` to move back to the previous step in the current solving process.
//!
//! - `.` to end the input this will move into the reading mode and it will apply the parser on the
//! input.

use console::Term;
use dialoguer::{theme::ColorfulTheme, Confirm, Input, Select};
use std::{collections::HashMap, fmt::Display, io};

use crate::{
    ast::{EvaluationNode, ExpressionNode, ImplicationNode, ProgramNode, StatementNode},
    matcher::Matcher,
    parser::{Parser, ParserError},
    prelude::{SourceMap, Typechecker, TypecheckerError},
};

use super::{EvalStep, ProofStep, Solver, SolverError};

const HELP: &str = "help";
const BEGIN: &str = "begin";
const END: &str = "end";
const NEXT: &str = "next";
const BACK: &str = "back";

#[derive(Debug)]
pub enum CroofShellError {
    InvalidCommand(String),
    ParserError(ParserError),
    TypecheckerError(Vec<TypecheckerError>),
    IoError(io::Error),
    TODO(String),
}

impl Display for CroofShellError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CroofShellError::InvalidCommand(msg) => write!(f, "Invalid command: {}", msg),
            CroofShellError::ParserError(err) => write!(f, "Parser error: {}", err),
            CroofShellError::TypecheckerError(errors) => write!(
                f,
                "Typechecker errors: {}",
                errors
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            CroofShellError::IoError(err) => write!(f, "IO error: {}", err),
            CroofShellError::TODO(msg) => write!(f, "TODO: {}", msg),
        }
    }
}

/// InteractiveSolver implements an interactive solver for expressions and statements.
pub struct InteractiveSolver {
    sourcemap: SourceMap,
    typechecker: Typechecker,
    matcher: Matcher,
    implications: Vec<ImplicationNode>,
    evaluations: Vec<EvaluationNode>,
    theorems: Vec<ImplicationNode>,
    term: Term,
    theme: ColorfulTheme,

    evaluation: Option<(EvaluationNode, Vec<EvalStep>)>,
    theorem: Option<(ImplicationNode, Vec<ProofStep>)>,

    mapping: HashMap<EvaluationNode, Vec<EvalStep>>,
}

impl InteractiveSolver {
    pub fn new(
        sourcemap: SourceMap,
        typechecker: Typechecker,
        matcher: Matcher,
        implications: Vec<ImplicationNode>,
    ) -> Self {
        InteractiveSolver {
            sourcemap,
            typechecker,
            matcher,
            implications,
            evaluations: Vec::new(),
            theorems: Vec::new(),
            term: Term::stdout(),
            theme: ColorfulTheme::default(),

            evaluation: None,
            theorem: None,
            mapping: HashMap::new(),
        }
    }

    fn read_begin(&mut self) -> Result<(), CroofShellError> {
        if self.evaluations.is_empty() {
            return Err(CroofShellError::InvalidCommand(
                "No evaluations available to begin.".to_string(),
            ));
        }

        let choices: Vec<String> = self
            .evaluations
            .iter()
            .map(|eval| format!("(E) {}", eval))
            .chain(
                self.theorems
                    .iter()
                    .map(|theorem| format!("(T) {}", theorem)),
            )
            .chain(std::iter::once("Cancel".to_string()))
            .collect();

        let selection = Select::with_theme(&self.theme)
            .with_prompt("Select an evaluation/theorem to begin solving")
            .default(0)
            .items(&choices)
            .interact_on(&self.term)
            .map_err(|e| CroofShellError::TODO(e.to_string()))?;

        if selection == choices.len() - 1 {
            return Ok(());
        }

        if selection < self.evaluations.len() {
            let evaluation = self.evaluations[selection].clone();
            self.evaluation = Some((evaluation.clone(), vec![]));
            self.theorem = None;
        } else {
            let theorem_index = selection - self.evaluations.len();
            let theorem = self.theorems[theorem_index].clone();
            self.evaluation = None;
            self.theorem = Some((theorem.clone(), vec![]));
        }

        Ok(())
    }

    fn read_parsed(&mut self, input: String) -> Result<(), CroofShellError> {
        let lexer = self.sourcemap.add_content(&input);
        let mut program = match Parser::new(lexer).parse() {
            Ok(program) => program,
            Err(error) => {
                self.sourcemap.display_error(&error);
                eprintln!("Failed to parse content");
                return Err(CroofShellError::ParserError(error));
            }
        };

        let errors = self.typechecker.check_program(&mut program);
        if !errors.is_empty() {
            self.sourcemap.display_errors(&errors);
            eprintln!(
                "Typechecking failed with {} {}",
                errors.len(),
                if errors.len() == 1 { "error" } else { "errors" }
            );
            return Err(CroofShellError::TypecheckerError(errors));
        }

        self.implications.extend(program.implications.clone());
        self.evaluations.extend(program.evaluations.clone());

        self.term
            .write_line(&format!(
                "Parsed and added {} implications and {} evaluations.",
                program.implications.len(),
                program.evaluations.len()
            ))
            .map_err(CroofShellError::IoError)?;

        return Ok(());
    }

    fn read_next_evaluation(&mut self) -> Result<(), CroofShellError> {
        let (evaluation, mut history) = self.evaluation.clone().unwrap();

        let mut options = Vec::new();

        for condition in &evaluation.conditions {
            let others: Vec<_> = evaluation
                .conditions
                .iter()
                .filter(|&c| c != condition)
                .cloned()
                .collect();
            let implication = ImplicationNode::new(others.clone(), vec![condition.clone()]);

            let mut substitutions = Vec::new();
            for (substituted, steps) in
                self.matcher
                    .substitute(&evaluation.expression, &others, condition)
            {
                substitutions.push((substituted, steps));
            }

            if substitutions.is_empty() {
                continue;
            }

            options.push((implication.clone(), substitutions));
        }

        for implication in &self.implications {
            let mut substitutions = Vec::new();
            for conclusion in &implication.conclusion {
                for (substituted, steps) in self.matcher.substitute(
                    &evaluation.expression,
                    &implication.conditions,
                    conclusion,
                ) {
                    substitutions.push((substituted, steps));
                }
            }

            if substitutions.is_empty() {
                continue;
            }

            options.push((implication.clone(), substitutions));
        }

        if options.is_empty() {
            return Err(CroofShellError::InvalidCommand(
                "No implications available to apply.".to_string(),
            ));
        }

        let choices: Vec<String> = options
            .iter()
            .map(|(implication, _)| format!("{}", implication))
            .chain(std::iter::once("Cancel".to_string()))
            .collect();

        let selection = Select::with_theme(&self.theme)
            .with_prompt("Select an implication to apply")
            .default(0)
            .items(&choices)
            .interact_on(&self.term)
            .map_err(|e| CroofShellError::TODO(e.to_string()))?;

        if selection == choices.len() - 1 {
            return Ok(());
        }

        let (implication, substitutions) = &options[selection];

        if substitutions.is_empty() {
            return Err(CroofShellError::InvalidCommand(
                "No substitutions available for the selected implication.".to_string(),
            ));
        }

        let choices: Vec<String> = substitutions
            .iter()
            .map(|(substitution, steps)| {
                if steps.is_empty() {
                    return format!("{}", substitution);
                }

                format!(
                    "{} (where {})",
                    substitution,
                    steps
                        .iter()
                        .map(|statement| format!("{}", statement))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })
            .chain(std::iter::once("Cancel".to_string()))
            .collect();

        let selection = Select::with_theme(&self.theme)
            .with_prompt("Select a substitution to apply")
            .default(0)
            .items(&choices)
            .interact_on(&self.term)
            .map_err(|e| CroofShellError::TODO(e.to_string()))?;

        if selection == choices.len() - 1 {
            return Ok(());
        }

        let (substitution, steps) = &substitutions[selection];

        for step in steps {
            let theorem = ImplicationNode::new(evaluation.conditions.clone(), vec![step.clone()]);

            self.theorems.push(theorem.clone());
        }

        history.push((evaluation.expression.clone(), substitution.clone(), implication.clone()));

        self.evaluation = Some((EvaluationNode::new(
            evaluation.conditions.clone(),
            substitution.clone(),
        ), history.clone()));

        Ok(())
    }

    fn read_next_theorem(&mut self) -> Result<(), CroofShellError> {
        let (theorem, mut history) = self.theorem.clone().unwrap();

        let mut options = Vec::new();

        for condition in &theorem.conditions {
            let others: Vec<_> = theorem
                .conditions
                .iter()
                .filter(|&c| c != condition)
                .cloned()
                .collect();
            let implication = ImplicationNode::new(others.clone(), vec![condition.clone()]);

            let mut substitutions = Vec::new();
            for conclusion in &theorem.conclusion {
                match conclusion {
                    StatementNode::Quantifier(_) => continue,
                    StatementNode::Relation(node) => {
                        for (substituted, steps) in
                            self.matcher.substitute(&node.left, &others, condition)
                        {
                            let mut node = node.clone();
                            node.left = substituted;
                            substitutions.push((StatementNode::Relation(node.clone()), steps));
                        }

                        for (substituted, steps) in
                            self.matcher.substitute(&node.right, &others, condition)
                        {
                            let mut node = node.clone();
                            node.right = substituted;
                            substitutions.push((StatementNode::Relation(node.clone()), steps));
                        }
                    }
                    StatementNode::Builtin(_) => todo!("Handle built-in statements"),
                }
            }

            if substitutions.is_empty() {
                continue;
            }

            options.push((implication.clone(), substitutions));
        }

        for implication in &self.implications {
            let mut substitutions = Vec::new();
            for condition in &implication.conclusion {
                for conclusion in &theorem.conclusion {
                    match conclusion {
                        StatementNode::Quantifier(_) => continue,
                        StatementNode::Relation(node) => {
                            for (substituted, steps) in self.matcher.substitute(
                                &node.left,
                                &implication.conditions,
                                condition,
                            ) {
                                let mut node = node.clone();
                                node.left = substituted;
                                substitutions.push((StatementNode::Relation(node.clone()), steps));
                            }

                            for (substituted, steps) in self.matcher.substitute(
                                &node.right,
                                &implication.conditions,
                                condition,
                            ) {
                                let mut node = node.clone();
                                node.right = substituted;
                                substitutions.push((StatementNode::Relation(node.clone()), steps));
                            }
                        }
                        StatementNode::Builtin(_) => todo!("Handle built-in statements"),
                    }
                }
            }

            if substitutions.is_empty() {
                continue;
            }

            options.push((implication.clone(), substitutions));
        }

        if options.is_empty() {
            return Err(CroofShellError::InvalidCommand(
                "No implications available to apply.".to_string(),
            ));
        }

        let choices: Vec<String> = options
            .iter()
            .map(|(implication, _)| format!("{}", implication))
            .chain(std::iter::once("Cancel".to_string()))
            .collect();

        let selection = Select::with_theme(&self.theme)
            .with_prompt("Select an implication to apply")
            .default(0)
            .items(&choices)
            .interact_on(&self.term)
            .map_err(|e| CroofShellError::TODO(e.to_string()))?;

        if selection == choices.len() - 1 {
            return Ok(());
        }

        let (implication, substitutions) = &options[selection];

        if substitutions.is_empty() {
            return Err(CroofShellError::InvalidCommand(
                "No substitutions available for the selected implication.".to_string(),
            ));
        }

        let choices: Vec<String> = substitutions
            .iter()
            .map(|(substitution, steps)| {
                if steps.is_empty() {
                    return format!("{}", substitution);
                }

                format!(
                    "{} (where {})",
                    substitution,
                    steps
                        .iter()
                        .map(|statement| format!("{}", statement))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })
            .chain(std::iter::once("Cancel".to_string()))
            .collect();

        let selection = Select::with_theme(&self.theme)
            .with_prompt("Select a substitution to apply")
            .default(0)
            .items(&choices)
            .interact_on(&self.term)
            .map_err(|e| CroofShellError::TODO(e.to_string()))?;

        if selection == choices.len() - 1 {
            return Ok(());
        }

        let (substitution, steps) = &substitutions[selection];

        for step in steps {
            let theorem = ImplicationNode::new(theorem.conditions.clone(), vec![step.clone()]);

            self.theorems.push(theorem.clone());
        }

        history.push((theorem.conclusion.clone(), vec![substitution.clone()], implication.clone()));

        self.theorem = Some((ImplicationNode::new(
            theorem.conditions.clone(),
            vec![substitution.clone()],
        ), history.clone()));

        Ok(())
    }

    fn read_next(&mut self) -> Result<(), CroofShellError> {
        if self.evaluation.is_some() {
            return self.read_next_evaluation();
        } else if self.theorem.is_some() {
            return self.read_next_theorem();
        } else {
            return Err(CroofShellError::InvalidCommand(
                "No evaluation or theorem selected. Please begin with an evaluation or theorem."
                    .to_string(),
            ));
        }
    }

    fn read_back_evaluation(&mut self) -> Result<(), CroofShellError> {
        let (evaluation, mut history) = self.evaluation.clone().unwrap();

        if history.is_empty() {
            self.term
                .write_line("No steps to backtrack in the current evaluation.")
                .map_err(CroofShellError::IoError)?;
            return Ok(());
        }

        let last_step = history.pop().unwrap();

        self.evaluation = Some((EvaluationNode::new(
            evaluation.conditions.clone(),
            last_step.0.clone(),
        ), history));

        self.term
            .write_line(&format!(
                "Backtracked to step: {} with implication: {}",
                last_step.0, last_step.2
            ))
            .map_err(CroofShellError::IoError)?;

        Ok(())
    }

    fn read_back_theorem(&mut self) -> Result<(), CroofShellError> {
        let (theorem, mut history) = self.theorem.clone().unwrap();

        if history.is_empty() {
            self.term
                .write_line("No steps to backtrack in the current theorem.")
                .map_err(CroofShellError::IoError)?;
            return Ok(());
        }

        let last_step = history.pop().unwrap();

        self.theorem = Some((ImplicationNode::new(
            theorem.conditions.clone(),
            last_step.0.clone(),
        ), history));

        self.term
            .write_line(&format!(
                "Backtracked to step: {} with implication: {}",
                last_step.0.iter().map(|s| s.to_string()).collect::<Vec<_>>().join(", "),
                last_step.2
            ))
            .map_err(CroofShellError::IoError)?;

        Ok(())
    }

    fn read_back(&mut self) -> Result<(), CroofShellError> {
        if self.evaluation.is_some() {
            return self.read_back_evaluation();
        } else if self.theorem.is_some() {
            return self.read_back_theorem();
        } else {
            return Err(CroofShellError::InvalidCommand(
                "No evaluation or theorem selected. Please begin with an evaluation or theorem."
                    .to_string(),
            ));
        }
    }

    fn read_end_evaluation(&mut self) -> Result<(), CroofShellError> {
        if let Some((evaluation, history)) = self.evaluation.take() {
            self.term
                .write_line(&format!(
                    "Evaluation completed with {} steps.",
                    history.len()
                ))
                .map_err(CroofShellError::IoError)?;

            let original = history.first().map_or(
                evaluation.expression.clone(),
                |(parent, _, _)| parent.clone(),
            );

            self.term
                .write_line(&format!("Expression: {}", original))
                .map_err(CroofShellError::IoError)?;

            for (parent, target, implication) in history {
                self.term
                    .write_line(&format!(
                        "  - {} => {} (apply {})",
                        parent, target, implication
                    ))
                    .map_err(CroofShellError::IoError)?;
            }

            self.term
                .write_line(&format!("Result: {}", evaluation.expression))
                .map_err(CroofShellError::IoError)?;

            Ok(())
        } else {
            Err(CroofShellError::InvalidCommand(
                "No evaluation in progress.".to_string(),
            ))
        }
    }

    fn read_end_theorem(&mut self) -> Result<(), CroofShellError> {
        if let Some((theorem, history)) = self.theorem.take() {
            self.term
                .write_line(&format!(
                    "Theorem completed with {} steps.",
                    history.len()
                ))
                .map_err(CroofShellError::IoError)?;

            let original = history.first().map_or(
                theorem.conclusion.clone(),
                |(parent, _, _)| parent.clone(),
            );

            self.term
                .write_line(&format!("Theorem: {}", original.iter().map(|s| s.to_string()).collect::<Vec<_>>().join(", ")))
                .map_err(CroofShellError::IoError)?;

            for (target, steps, implication) in history {
                self.term
                    .write_line(&format!(
                        "  - {} => {} (apply {})",
                        target.iter().map(|s| s.to_string()).collect::<Vec<_>>().join(", "),
                        steps.iter().map(|s| s.to_string()).collect::<Vec<_>>().join(", "),
                        implication
                    ))
                    .map_err(CroofShellError::IoError)?;
            }

            Ok(())
        } else {
            Err(CroofShellError::InvalidCommand(
                "No theorem in progress.".to_string(),
            ))
        }
    }

    fn read_end(&mut self) -> Result<(), CroofShellError> {
        if self.evaluation.is_some() {
            return self.read_end_evaluation();
        } else if self.theorem.is_some() {
            return self.read_end_theorem();
        } else {
            return Err(CroofShellError::InvalidCommand(
                "No evaluation or theorem selected. Please begin with an evaluation or theorem."
                    .to_string(),
            ));
        }
    }

    fn show_help(&self) -> Result<(), CroofShellError> {
        self.term
            .write_line("Available commands:")
            .map_err(CroofShellError::IoError)?;
        self.term
            .write_line("  help - Show this help message")
            .map_err(CroofShellError::IoError)?;
        self.term
            .write_line("  begin - Start solving a new evaluation")
            .map_err(CroofShellError::IoError)?;
        self.term
            .write_line("  end - End the current solving process")
            .map_err(CroofShellError::IoError)?;
        self.term
            .write_line("  next - Move to the next step in the solving process")
            .map_err(CroofShellError::IoError)?;
        self.term
            .write_line("  back - Move back to the previous step in the solving process")
            .map_err(CroofShellError::IoError)?;
        self.term
            .write_line("  . - End the input and return to read mode")
            .map_err(CroofShellError::IoError)?;
        Ok(())
    }

    fn read_item(&mut self) -> Result<(), CroofShellError> {
        let mut input = String::new();
        loop {
            let line = self
                .term
                .read_line()
                .map_err(CroofShellError::IoError)?
                .trim()
                .to_string();

            if let Some((start, _)) = line.split_once('.') {
                input.push_str(start);

                return self.read_parsed(input);
            }

            match line.as_str() {
                HELP => return self.show_help(),
                BEGIN => return self.read_begin(),
                END => return self.read_end(),
                NEXT => return self.read_next(),
                BACK => return self.read_back(),
                _ => {}
            }

            input.push_str(&line);
        }
    }

    pub fn interact(&mut self) -> Result<(), CroofShellError> {
        loop {
            match self.read_item() {
                Ok(_) => {},
                Err(err) => {
                    self.term
                        .write_line(&format!("Error: {}", err))
                        .map_err(CroofShellError::IoError)?;
                }
            }
        }
    }
}
