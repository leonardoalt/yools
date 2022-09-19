use std::env;
use std::path::PathBuf;

use yools::evm_builtins::EVMInstructions;
use yools::solver;

use yultsur::dialect::EVMDialect;
use yultsur::resolver::resolve;
use yultsur::yul_parser;

use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};

fn main() {
    cli().unwrap_or_else(|e| {
        println!("{}", e);
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
        Some(("symbolic", sub_matches)) => symbolic_revert(sub_matches),
        _ => unreachable!(),
    }
}

fn symbolic_subcommand() -> App<'static> {
    SubCommand::with_name("symbolic")
        .about("Symbolically execute Yul programs checking for revert reachability")
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
            Arg::with_name("solver")
                .short('s')
                .long("solver")
                .help("SMT solver")
                .value_name("SOLVER")
                .takes_value(true)
                .default_value("cvc4")
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

fn symbolic_revert(sub_matches: &ArgMatches) -> Result<(), String> {
    let yul_file = PathBuf::from(sub_matches.value_of("input").unwrap());

    let content = std::fs::read_to_string(yul_file).unwrap();

    let mut ast = yul_parser::parse_block(&content);
    resolve::<EVMDialect>(&mut ast);

    let loop_unroll: u64 = sub_matches
        .value_of("loop-unroll")
        .unwrap()
        .parse()
        .unwrap();

    let query = yools::encoder::encode_revert_unreachable::<EVMInstructions>(&ast, loop_unroll);

    match solver::query_smt_with_solver(
        &query,
        solver::SolverConfig::new(sub_matches.value_of("solver").unwrap()),
    ) {
        true => {
            println!("Revert is reachable.");
        }
        false => {
            println!("All reverts are unreachable.");
        }
    };

    Ok(())
}
