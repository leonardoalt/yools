use std::env;
use std::fs::File;
use std::io::prelude::*;

use yultsur::yul;
use yultsur::yul_parser;

use yools::symb_exec::*;

fn main() {
    let yul_file = env::args().nth(1).expect("Expected Yul .yul file");

    let mut file = File::open(yul_file).unwrap();
    let mut content = String::new();
    file.read_to_string(&mut content).unwrap();

    let ast = yul_parser::parse_block(&content);

    SymbExecEngine::encode(yul::Statement::Block(ast));
}
