use std::path::PathBuf;

use crate::evm_builtins::EVMInstructions;
use crate::solver;

use yultsur::resolver::resolve;
use yultsur::yul_parser;
use yultsur::{dialect::EVMDialect, resolver::resolve_inside};

use clap::{Parser};

/// Common trait for all cli commands
pub trait Cmd: clap::Parser + Sized {
    type Output;
    fn run(self) -> eyre::Result<Self::Output>;
}


#[derive(Debug, Clone, Parser, Default)]
pub struct SymbolicArgs {
    #[clap(
        long,
        short = 'i',
        value_name = "FILE.yul",
        help = "Yul source file"
    )]
    pub input: PathBuf,
    #[clap(
        long,
        short = 'e',
        value_name = "expression",
        help = "Yul expression(s) to evaluate in the reverting execution. Separate multiple expressions by '|'."
    )]
    pub eval: Option<String>,
    #[clap(
        long,
        short = 's',
        value_name = "SOLVER",
        help = "SMT solver",
        default_value = "cvc5"
    )]
    pub solver: String,
    #[clap(
        long,
        short = 'l',
        value_name = "LOOP_UNROLL",
        help = "Loop unrolling limit",
        default_value = "10"
    )]
    pub loop_unroll: u64,
}

impl Cmd for SymbolicArgs {
    type Output = ();

    fn run(self) -> eyre::Result<Self::Output> {
        let SymbolicArgs {input, eval, solver, loop_unroll} = self;
        
        let content = std::fs::read_to_string(input).unwrap();

        let mut ast = yul_parser::parse_block(&content).unwrap();
        resolve::<EVMDialect>(&mut ast).ok();

        let loop_unroll: u64 = loop_unroll;

        let eval_strings = if let Some(eval) = eval {
            eval.split('|')
                .map(|e| e.to_string())
                .collect::<Vec<String>>()
        } else {
            vec![]
        };

        let counterexamples = eval_strings
            .iter()
            .map(|eval| {
                let mut expr = yul_parser::parse_expression(eval)?;
                resolve_inside::<EVMDialect>(&mut expr, &ast)?;
                Ok(expr)
            })
            .collect::<Result<Vec<_>, String>>().unwrap();

        let (query, counterexamples_encoded) = crate::encoder::encode_solc_panic_reachable::<
            EVMInstructions,
        >(&ast, loop_unroll, &counterexamples);

        let solver = solver::SolverConfig::new(&solver);
        let (result, values) =
            solver::query_smt_with_solver_and_eval(&query, &counterexamples_encoded, solver);

        match result {
            true => {
                println!("Revert is reachable.");
                if !eval_strings.is_empty() {
                    println!(
                        "Evaluated expressions:\n{}",
                        eval_strings
                            .iter()
                            .zip(values.iter())
                            .map(|(s, v)| { format!("{} = {}", s, v) })
                            .collect::<Vec<_>>()
                            .join("\n")
                    );
                }
            }
            false => {
                println!("All reverts are unreachable.");
            }
        }
        
        Ok(())
    }
}
