use std::{fs, path::Path};

use yools::common::SMTVariable;
use yools::solver;
use yools::ssa_tracker::SSATracker;
use yools::*;

use yultsur::dialect;
use yultsur::yul_parser;

#[derive(Default)]
struct EVMInstructionsWithAssert(evm_builtins::EVMInstructions);

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
#[ignore]
fn test_assert_pass() {
    let dir = Path::new("./tests/assert_pass");
    assert!(dir.is_dir());
    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().unwrap() == "yul" {
            test_file(path.to_str().unwrap());
        }
    }
}

fn test_file(test_file: &str) {
    assert!(Path::new(&test_file).exists());

    let content = fs::read_to_string(&test_file).expect("I need to read this file.");

    let mut ast = yul_parser::parse_block(&content);
    let signatures = yultsur::resolver::resolve::<EVMInstructionsWithAssert>(&mut ast);

    let query = encoder::encode::<EVMInstructionsWithAssert>(&ast, signatures);
    unsat(&query);
}

fn unsat(query: &String) {
    assert!(
        !solver::query_smt(query),
        "Should be UNSAT. Query:\n{}",
        query
    );
}
