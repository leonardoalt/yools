use std::{fs, fs::File, path::Path};

use yools::common::SMTVariable;
use yools::encoder;
use yools::encoder::Instructions;
use yools::evm_builtins::EVMInstructions;
use yools::evm_context;
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
                name: name.to_string(),
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
        match builtin.name.as_str() {
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
fn test_assert_pass() {
    test_dir("./tests/assert_pass", test_file_assert_pass);
}

#[test]
fn test_syntax() {
    test_dir("./tests/syntax", test_file_syntax_no_update::<EVMInstructions>);
}

#[test]
fn test_syntax_assert_pass() {
    test_dir("./tests/assert_pass", test_file_syntax_no_update::<EVMInstructionsWithAssert>);
}

#[test]
#[ignore]
fn test_syntax_update() {
    test_dir("./tests/syntax", test_file_syntax_update::<EVMInstructions>);
}

#[test]
#[ignore]
fn test_syntax_assert_pass_update() {
    test_dir("./tests/assert_pass", test_file_syntax_update::<EVMInstructionsWithAssert>);
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

fn test_file_revert_unreachable(test_file: &str) {
    assert!(Path::new(&test_file).exists());

    let content = fs::read_to_string(&test_file).expect("I need to read this file.");

    let mut ast = yul_parser::parse_block(&content);
    let signatures = yultsur::resolver::resolve::<dialect::EVMDialect>(&mut ast);

    let query = encoder::encode_revert_unreachable::<EVMInstructions>(&ast, signatures);
    unsat(&query);
}

fn test_file_assert_pass(test_file: &str) {
    assert!(Path::new(&test_file).exists());

    let content = fs::read_to_string(&test_file).expect("I need to read this file.");

    let mut ast = yul_parser::parse_block(&content);
    let signatures = yultsur::resolver::resolve::<EVMInstructionsWithAssert>(&mut ast);

    let query = encoder::encode::<EVMInstructionsWithAssert>(&ast, signatures);
    unsat(&query);
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

    let mut ast = yul_parser::parse_block(&content);
    let signatures = yultsur::resolver::resolve::<InstructionsType>(&mut ast);

    let query = encoder::encode_revert_unreachable::<InstructionsType>(&ast, signatures);

    let expected = fs::read_to_string(&expect_name).expect("I need to read this file.");
    if query != expected {
        if update {
            assert!(fs::write(expect_name, query).is_ok());
        } else {
            panic!("Expected:\n{}\nGot:\n{}", expected, query);
        }
    }
}

fn unsat(query: &String) {
    assert!(
        !solver::query_smt(query),
        "Should be UNSAT. Query:\n{}",
        query
    );
}
