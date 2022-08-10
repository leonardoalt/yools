use std::env;
use std::fs::File;
use std::io::prelude::*;

use yultsur::dialect::EVMDialect;
use yultsur::resolver::resolve;
use yultsur::yul_parser;

fn main() {
    let yul_file = env::args().nth(1).expect("Expected Yul .yul file");

    let mut file = File::open(yul_file).unwrap();
    let mut content = String::new();
    file.read_to_string(&mut content).unwrap();

    let mut ast = yul_parser::parse_block(&content);
    resolve::<EVMDialect>(&mut ast);

    yools::encoder::encode(&ast);
}
