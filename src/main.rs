use std::env;
use std::path::PathBuf;

use codespan_reporting::term::termcolor::WriteColor;
use colored::Colorize;
use num_traits::ToPrimitive;
use yools::evm_builtins::EVMInstructions;
use yools::{execution_position, solver};

use yultsur::resolver::resolve;
use yultsur::yul::SourceLocation;
use yultsur::yul_parser;
use yultsur::{dialect::EVMDialect, resolver::resolve_inside};

use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};

fn main() {
    cli().unwrap_or_else(|e| {
        println!("{e}");
        std::process::exit(1);
    })
}

fn cli() -> Result<(), String> {
    let matches = App::new("Yools")
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .version(env!("CARGO_PKG_VERSION"))
        .about("Tools for Yul.")
        .subcommands(vec![symbolic_subcommand()])
        .get_matches();

    match matches.subcommand() {
        Some(("symbolic", sub_matches)) => symbolic_revert_cli(sub_matches),
        _ => unreachable!(),
    }
}

fn symbolic_subcommand() -> App<'static> {
    SubCommand::with_name("symbolic")
        .about("Symbolically execute Yul programs checking for reachability of solc panics")
        .arg(
            Arg::with_name("input")
                .short('i')
                .long("input")
                .help("Yul source file")
                .value_name("FILE.yul")
                .takes_value(true)
                .required(true),
        )
        .arg(
            Arg::with_name("calls")
                .short('c')
                .long("calls")
                .help("Comma-separated list of functions to call (selectors)")
                .value_name("CALLS")
                .takes_value(true)
                .required(false),
        )
        .arg(
            Arg::with_name("eval")
                .short('e')
                .long("eval")
                .help("Yul expression(s) to evaluate in the reverting execution. Separate multiple expressions by '|'.")
                .value_name("expression")
                .takes_value(true)
                .required(false),
        )
        .arg(
            Arg::with_name("solver")
                .short('s')
                .long("solver")
                .help("SMT solver")
                .value_name("SOLVER")
                .takes_value(true)
                .default_value("cvc5")
                .required(false),
        )
        .arg(
            Arg::with_name("loop-unroll")
                .short('l')
                .long("loop-unroll")
                .help("Loop unrolling limit")
                .value_name("LOOP_UNROLL")
                .takes_value(true)
                .default_value("10")
                .required(false),
        )
}

fn symbolic_revert_cli(sub_matches: &ArgMatches) -> Result<(), String> {
    let yul_file = PathBuf::from(sub_matches.value_of("input").unwrap());

    let source = std::fs::read_to_string(yul_file).unwrap();

    let loop_unroll: u64 = sub_matches
        .value_of("loop-unroll")
        .unwrap()
        .parse()
        .unwrap();

    let eval_strings = if let Some(eval) = sub_matches.value_of("eval") {
        eval.split('|')
            .map(|e| e.to_string())
            .collect::<Vec<String>>()
    } else {
        vec![]
    };

    let signatures = if let Some(signatures) = sub_matches.value_of("calls") {
        signatures
            .split(',')
            .map(|sig| {
                Some(
                    (0..sig.len())
                        .step_by(2)
                        .map(|i| u8::from_str_radix(&sig[i..i + 2], 16).unwrap())
                        .collect::<Vec<u8>>(),
                )
            })
            .collect()
    } else {
        vec![None]
    };
    use codespan_reporting::term::termcolor;
    let mut output = termcolor::StandardStream::stdout(termcolor::ColorChoice::Always);
    symbolic_revert(
        &source,
        signatures,
        loop_unroll,
        sub_matches.value_of("solver").unwrap(),
        eval_strings,
        &mut output,
    )
}

fn symbolic_revert(
    source: &str,
    signatures: Vec<Option<Vec<u8>>>,
    loop_unroll: u64,
    solver: &str,
    eval_strings: Vec<String>,
    output: &mut dyn codespan_reporting::term::termcolor::WriteColor,
) -> Result<(), String> {
    let mut ast = yul_parser::parse_block(source)?;
    resolve::<EVMDialect>(&mut ast)?;

    let counterexamples = eval_strings
        .iter()
        .map(|eval| {
            let mut expr = yul_parser::parse_expression(eval)?;
            resolve_inside::<EVMDialect>(&mut expr, &ast)?;
            Ok(expr)
        })
        .collect::<Result<Vec<_>, String>>()?;
    let (query, counterexamples_encoded, panic_position, position_manager) =
        yools::encoder::encode_solc_panic_reachable_with_signatures::<EVMInstructions>(
            &ast,
            signatures,
            loop_unroll,
            &counterexamples,
        );

    let cex = [counterexamples_encoded, [panic_position].to_vec()].concat();
    let solver = solver::SolverConfig::new(solver);
    let (result, mut values) = solver::query_smt_with_solver_and_eval(&query, &cex, solver);
    match result {
        true => {
            let panic_position = values.pop().unwrap();
            if let solver::ModelValue::Number(position) = panic_position {
                let pos = execution_position::PositionID(position.to_usize().unwrap());
                print_detailed_diagnostics(
                    source,
                    position_manager.calldata_at_position(pos),
                    position_manager.call_stack_at_position(pos),
                    output,
                );
            } else {
                write!(output, "Panic is reachable.").unwrap();
            }
            if !eval_strings.is_empty() {
                write!(
                    output,
                    "{}\n{}",
                    "Evaluated expressions:".bright_yellow(),
                    eval_strings
                        .iter()
                        .zip(values.iter())
                        .map(|(s, v)| { format!("{s} = {v}") })
                        .collect::<Vec<_>>()
                        .join("\n")
                )
                .unwrap();
            }
        }
        false => {
            write!(output, "All panics are unreachable.").unwrap();
        }
    }
    Ok(())
}

fn print_detailed_diagnostics(
    source: &str,
    calldata: &[Option<Vec<u8>>],
    call_stack: &[Option<SourceLocation>],
    output: &mut dyn WriteColor,
) {
    use codespan_reporting as cs;
    use cs::diagnostic::{Diagnostic, Label};
    use cs::files::SimpleFiles;

    let calldata: String = calldata
        .iter()
        .map(|c| {
            let x = c
                .clone()
                .unwrap_or_default()
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<Vec<String>>()
                .concat();
            x
        })
        .collect::<Vec<String>>()
        .join(",");

    let config = codespan_reporting::term::Config::default();
    let mut files = SimpleFiles::new();
    let file_id = files.add("input", source);
    if let [stack @ .., Some(pos)] = call_stack {
        let diagnostic = Diagnostic::error()
            .with_message(format!(
                "Panic is reachable. In last call of sequence: {calldata}"
            ))
            .with_labels(vec![Label::primary(file_id, pos.start..pos.end)
                .with_message("This revert causes a panic.")]);
        cs::term::emit(output, &config, &files, &diagnostic).unwrap();
        for (depth, pos) in stack.iter().rev().enumerate() {
            let mut diagnostic =
                Diagnostic::note().with_message(format!("Stack level {}:", depth + 1));
            diagnostic = match pos {
                Some(pos) => {
                    diagnostic.with_labels(vec![Label::primary(file_id, (pos.start)..(pos.end))
                        .with_message("Called from here.")])
                }
                None => diagnostic,
            };
            cs::term::emit(output, &config, &files, &diagnostic).unwrap();
        }
    } else {
        panic!();
    }
}

#[cfg(test)]
mod test {
    use codespan_reporting::term::termcolor;
    use std::io::BufWriter;

    use super::*;

    #[test]
    fn stack_trace() {
        let source = concat!(
            "{\n",
            "  function f() {\n",
            "    mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)\n",
            "    mstore(4, 0x11)\n",
            "    revert(0, 0x24)\n",
            "  }\n",
            "  function g() {\n",
            "    f()\n",
            "  }\n",
            "  g()\n",
            "}\n"
        ).to_string();
        let mut output = termcolor::NoColor::new(BufWriter::new(Vec::new()));
        symbolic_revert(&source, vec![None], 1, "z3", vec![], &mut output).unwrap();
        let output_str = std::str::from_utf8(output.get_ref().buffer()).unwrap();
        println!("{output_str}");
        assert_eq!(
            output_str,
            concat!(
                "error: Panic is reachable.\n",
                "  ┌─ input:5:5\n",
                "  │\n",
                "5 │     revert(0, 0x24)\n",
                "  │     ^^^^^^^^^^^^^^^ This revert causes a panic.\n",
                "\n",
                "note: Stack level 1:\n",
                "  ┌─ input:8:5\n",
                "  │\n",
                "8 │     f()\n",
                "  │     ^^^ Called from here.\n",
                "\n",
                "note: Stack level 2:\n",
                "   ┌─ input:10:3\n",
                "   │\n",
                "10 │   g()\n",
                "   │   ^^^ Called from here.\n",
                "\n"
            )
        );
    }
}
