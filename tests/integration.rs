use std::io::prelude::*;
use std::{fs, fs::File, path::Path};

use yools::encoder;
use yools::solver;

use yultsur::dialect;
use yultsur::yul_parser;

fn tautology(query: &String) {
    assert!(!solver::query_smt(query), "Tautology failed.");
}

#[test]
fn test_revert_unreachable() {
    test_dir("./tests/revert_unreachable");
}

fn test_dir(test_dir: &str) {
    let dir = Path::new(test_dir);
    assert!(dir.is_dir());
    for entry in fs::read_dir(dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().unwrap() == "yul" {
            test_file(path.to_str().unwrap());
        }
    }
}

fn test_file(test_file: &str) {
    assert!(Path::new(&test_file).exists());

    let mut file = File::open(test_file).unwrap();
    let mut content = String::new();
    file.read_to_string(&mut content).unwrap();

    let mut ast = yul_parser::parse_block(&content);
    let signatures = yultsur::resolver::resolve::<dialect::EVMDialect>(&mut ast);

    let query = encoder::encode_no_revert(&ast, signatures);
    tautology(&query);
}
