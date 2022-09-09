use std::{fs, fs::File, path::Path};

use yools::encoder;
use yools::evm_builtins::EVMInstructions;
use yools::solver;

use yultsur::dialect;
use yultsur::yul_parser;

#[test]
fn test_revert_unreachable() {
    test_dir("./tests/revert_unreachable", test_file_revert_unreachable);
}

#[test]
fn test_syntax() {
    test_dir("./tests/syntax", test_file_syntax_no_update);
}

#[test]
#[ignore]
fn test_syntax_update() {
    test_dir("./tests/syntax", test_file_syntax_update);
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

fn test_file_syntax_no_update(test_file: &str) {
    test_file_syntax(test_file, false);
}

fn test_file_syntax_update(test_file: &str) {
    test_file_syntax(test_file, true);
}

fn test_file_syntax(test_file: &str, update: bool) {
    assert!(Path::new(&test_file).exists());
    let expect_name = format!("{}.expect", test_file);
    let expectation = Path::new(&expect_name);
    if !expectation.exists() {
        assert!(File::create(&expectation).is_ok());
    }

    let content = fs::read_to_string(&test_file).expect("I need to read this file.");

    let mut ast = yul_parser::parse_block(&content);
    let signatures = yultsur::resolver::resolve::<dialect::EVMDialect>(&mut ast);

    let query = encoder::encode_revert_unreachable::<EVMInstructions>(&ast, signatures);

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
