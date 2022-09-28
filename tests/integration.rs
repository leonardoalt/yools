use std::{fs, fs::File, path::Path};

use yools::encoder;
use yools::encoder::Instructions;
use yools::evm_builtins::EVMInstructions;
use yools::evm_context;
use yools::smt::SMTVariable;
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
    ) -> String {
        match builtin.name {
            "assert" => format!("(assert (and {} (= #x0000000000000000000000000000000000000000000000000000000000000000 {})))", evm_context::executing_regularly(ssa), arguments[0].name),
            _ => self
                .0
                .encode_builtin_call(builtin, arguments, return_vars, ssa),
        }
    }
}

#[test]
fn test_revert_unreachable() {
    test_dir("./tests/revert_unreachable", test_file_revert_unreachable);
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

// This function is called from tests constructed at build time
// and included below.
// build.rs creates one test per .yul file in the assert_pass directory
// using the template file test_assert_pass.tmpl
fn test_assert_pass(content: &str, file: &str) {
    match yul_parser::parse_block(content) {
        Err(err) => {
            assert!(false, "Parse error in file {file}:\n{err}")
        }
        Ok(mut ast) => {
            yultsur::resolver::resolve::<EVMInstructionsWithAssert>(&mut ast)
                .expect("Resolving error.");

            let query =
                encoder::encode::<EVMInstructionsWithAssert>(&ast, loop_unroll_default(content));
            unsat(&query, file);
        }
    }
}

include!(concat!(env!("OUT_DIR"), "/test_assert_pass.rs"));

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

fn test_file_revert_unreachable(test_file: &str) {
    assert!(Path::new(&test_file).exists());

    let content = fs::read_to_string(&test_file).expect("I need to read this file.");

    match yul_parser::parse_block(&content) {
        Err(err) => {
            assert!(false, "Parse error in file {test_file}:\n{err}")
        }
        Ok(mut ast) => {
            yultsur::resolver::resolve::<dialect::EVMDialect>(&mut ast).expect("Resolving error.");

            let query = encoder::encode_revert_unreachable::<EVMInstructions>(
                &ast,
                loop_unroll_default(&content),
            );
            unsat(&query, test_file);
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
    let expect_name = format!("{}.smt2", test_file);
    let expectation = Path::new(&expect_name);
    if !expectation.exists() {
        assert!(File::create(&expectation).is_ok());
    }

    let content = fs::read_to_string(&test_file).expect("I need to read this file.");

    match yul_parser::parse_block(&content) {
        Err(err) => {
            assert!(false, "Parse error in file {test_file}:\n{err}")
        }
        Ok(mut ast) => {
            yultsur::resolver::resolve::<InstructionsType>(&mut ast).expect("Resolving error.");

            let query = encoder::encode_revert_unreachable::<InstructionsType>(
                &ast,
                loop_unroll_default(&content),
            );

            let expected = fs::read_to_string(&expect_name).expect("I need to read this file.");
            if query != expected {
                if update {
                    assert!(fs::write(expect_name, query).is_ok());
                } else {
                    panic!("Expected:\n{}\nGot:\n{}", expected, query);
                }
            }
        }
    }
}

fn unsat(query: &String, file: &str) {
    assert!(
        !solver::query_smt(query),
        "\n--------------------\n{} FAILED\n--------------------\nShould be UNSAT. Query:\n{}",
        file,
        query
    );
}
