use std::{fs, fs::File, path::Path};

use yools::encoder;
use yools::encoder::Instructions;
use yools::evaluator::Evaluator;
use yools::evm_builtins::EVMInstructions;
use yools::evm_context;
use yools::smt::{self, SMTExpr, SMTStatement, SMTVariable};
use yools::solver;
use yools::ssa_tracker::SSATracker;

use yultsur::dialect;
use yultsur::yul_parser;

#[derive(Default)]
struct EVMInstructionsWithAssert(EVMInstructions);

impl dialect::Dialect for EVMInstructionsWithAssert {
    fn builtin(name: &str) -> Option<dialect::Builtin> {
        match name {
            "assert" => Some(dialect::Builtin {
                name: "assert",
                parameters: 1,
                returns: 0,
            }),
            _ => dialect::EVMDialect::builtin(name),
        }
    }
}

impl encoder::Instructions for EVMInstructionsWithAssert {
    fn encode_builtin_call(
        &self,
        builtin: &dialect::Builtin,
        arguments: Vec<SMTVariable>,
        return_vars: &[SMTVariable],
        ssa: &mut SSATracker,
        path_conditions: &[SMTExpr],
    ) -> Vec<SMTStatement> {
        match builtin.name {
            "assert" => vec![smt::assert(smt::and_vec(vec![
                evm_context::executing_regularly(ssa),
                smt::and_vec(path_conditions.to_vec()),
                smt::eq_zero(arguments.into_iter().next().unwrap()),
            ]))],
            _ => self
                .0
                .encode_builtin_call(builtin, arguments, return_vars, ssa, path_conditions),
        }
    }
}

#[test]
fn recognize_known_contract() {
    let file = "tests/contract_creation_test.yul";
    let content = fs::read_to_string(file).expect("I need to read this file.");
    let main_ast = parse_and_resolve::<EVMInstructionsWithAssert>(&content, file);

    println!("=========== SETUP ===================");
    let mut ssa_tracker = SSATracker::default();
    let mut evaluator = Evaluator::default();
    evaluator.new_transaction(b"\x0a\x92\x54\xe4".to_vec());
    // TODO also provide calldata to encoder?
    let mut query;
    (query, evaluator, ssa_tracker) = encoder::encode_with_evaluator::<EVMInstructionsWithAssert>(
        &main_ast,
        loop_unroll_default(&content),
        evaluator,
        ssa_tracker,
    );
    println!("=========== CALL ===================");
    evaluator.new_transaction(b"\x85\x63\x28\x95".to_vec());
    let (query2, ..) = encoder::encode_with_evaluator::<EVMInstructionsWithAssert>(
        &main_ast,
        loop_unroll_default(&content),
        evaluator,
        ssa_tracker,
    );
    query += &query2;
    unsat(&query, file);
    // TODO the actual test.
}

#[test]
fn test_syntax() {
    test_dir(
        "./tests/syntax",
        test_file_syntax_no_update::<EVMInstructions>,
    );
}

#[test]
fn test_syntax_assert_pass() {
    test_dir(
        "./tests/assert_pass",
        test_file_syntax_no_update::<EVMInstructionsWithAssert>,
    );
}

#[test]
#[ignore]
fn test_syntax_update() {
    test_dir("./tests/syntax", test_file_syntax_update::<EVMInstructions>);
}

#[test]
#[ignore]
fn test_syntax_assert_pass_update() {
    test_dir(
        "./tests/assert_pass",
        test_file_syntax_update::<EVMInstructionsWithAssert>,
    );
}

fn loop_unroll(source: &str) -> Option<u64> {
    source.split('\n').find_map(|l| {
        l.starts_with("// loop_unroll:")
            .then(|| l.split(':').nth(1).unwrap().parse::<u64>().unwrap())
    })
}

fn loop_unroll_default(source: &str) -> u64 {
    loop_unroll(source).unwrap_or(10)
}

mod assert_pass {
    use super::*;
    // This function is called from tests constructed at build time
    // and included below.
    // build.rs creates one test per .yul file in the assert_pass directory.
    fn test_assert_pass(content: &str, file: &str) {
        let ast = parse_and_resolve::<EVMInstructionsWithAssert>(content, file);

        let query =
            encoder::encode::<EVMInstructionsWithAssert>(&ast, loop_unroll_default(content));
        unsat(&query, file);
    }

    include!(concat!(env!("OUT_DIR"), "/test_assert_pass.rs"));
}

mod some_revert_reachable {
    use super::*;
    // This function is called from tests constructed at build time
    // and included below.
    // build.rs creates one test per .yul file in the some_revert_reachable directory.
    fn test_some_revert_reachable(content: &str, file: &str) {
        let ast = parse_and_resolve::<EVMInstructions>(content, file);

        let query = encoder::encode_revert_reachable::<EVMInstructions>(
            &ast,
            loop_unroll_default(content),
            &[],
        )
        .0;
        sat(&query, file);
    }

    include!(concat!(env!("OUT_DIR"), "/test_some_revert_reachable.rs"));
}

mod revert_unreachable {
    use super::*;
    // This function is called from tests constructed at build time
    // and included below.
    // build.rs creates one test per .yul file in the revert_unreachable directory.
    fn test_revert_unreachable(content: &str, file: &str) {
        let ast = parse_and_resolve::<EVMInstructions>(content, file);
        let (query, _) = encoder::encode_revert_reachable::<EVMInstructions>(
            &ast,
            loop_unroll_default(content),
            &[],
        );
        unsat(&query, file);
    }

    include!(concat!(env!("OUT_DIR"), "/test_revert_unreachable.rs"));
}

mod panic_unreachable {
    use super::*;
    // This function is called from tests constructed at build time
    // and included below.
    // build.rs creates one test per .yul file in the panic_unreachable directory.
    fn test_panic_unreachable(content: &str, file: &str) {
        let ast = parse_and_resolve::<EVMInstructions>(content, file);
        let (query, ..) = encoder::encode_solc_panic_reachable::<EVMInstructions>(
            &ast,
            loop_unroll_default(content),
            &[],
        );
        unsat(&query, file);
    }

    include!(concat!(env!("OUT_DIR"), "/test_panic_unreachable.rs"));
}

mod some_panic_reachable {
    use super::*;
    // This function is called from tests constructed at build time
    // and included below.
    // build.rs creates one test per .yul file in the some_panic_reachable directory.
    fn test_some_panic_reachable(content: &str, file: &str) {
        let ast = parse_and_resolve::<EVMInstructions>(content, file);
        let (query, ..) = encoder::encode_solc_panic_reachable::<EVMInstructions>(
            &ast,
            loop_unroll_default(content),
            &[],
        );
        sat(&query, file);
    }

    include!(concat!(env!("OUT_DIR"), "/test_some_panic_reachable.rs"));
}

fn parse_and_resolve<Instr: dialect::Dialect>(content: &str, file: &str) -> yultsur::yul::Block {
    match yul_parser::parse_block(content) {
        Err(err) => {
            unreachable!("Parse error in file {file}:\n{err}");
        }
        Ok(mut ast) => {
            yultsur::resolver::resolve::<Instr>(&mut ast).expect("Resolving error.");
            ast
        }
    }
}

fn test_dir(test_dir: &str, test_file_fn: fn(&str)) {
    let dir = Path::new(test_dir);
    assert!(dir.is_dir());
    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().unwrap() == "yul" {
            test_file_fn(path.to_str().unwrap());
        }
    }
}

fn test_file_syntax_no_update<T: Instructions>(test_file: &str) {
    test_file_syntax::<T>(test_file, false);
}

fn test_file_syntax_update<T: Instructions>(test_file: &str) {
    test_file_syntax::<T>(test_file, true);
}

fn test_file_syntax<InstructionsType: encoder::Instructions>(test_file: &str, update: bool) {
    assert!(Path::new(&test_file).exists());
    let expect_name = format!("{test_file}.smt2");
    let expectation = Path::new(&expect_name);
    if !expectation.exists() {
        assert!(File::create(expectation).is_ok());
    }

    let content = fs::read_to_string(test_file).expect("I need to read this file.");

    match yul_parser::parse_block(&content) {
        Err(err) => {
            unreachable!("Parse error in file {test_file}:\n{err}")
        }
        Ok(mut ast) => {
            yultsur::resolver::resolve::<InstructionsType>(&mut ast).expect("Resolving error.");

            let (query, _) = encoder::encode_revert_reachable::<InstructionsType>(
                &ast,
                loop_unroll_default(&content),
                &[],
            );

            let expected = fs::read_to_string(&expect_name).expect("I need to read this file.");
            if query != expected {
                if update {
                    assert!(fs::write(expect_name, query).is_ok());
                } else {
                    panic!("Expected:\n{expected}\nGot:\n{query}");
                }
            }
        }
    }
}

fn unsat(query: &String, file: &str) {
    assert!(
        !solver::query_smt(query),
        "\n--------------------\n{file} FAILED\n--------------------\nShould be UNSAT. Query:\n{query}"
    );
}

fn sat(query: &String, file: &str) {
    assert!(
        solver::query_smt(query),
        "\n--------------------\n{file} FAILED\n--------------------\nShould be SAT. Query:\n{query}"
    );
}
