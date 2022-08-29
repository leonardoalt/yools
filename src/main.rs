use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::process::Command;

use std::io::Write;
use tempfile::NamedTempFile;

use yultsur::dialect::EVMDialect;
use yultsur::resolver::resolve;
use yultsur::yul_parser;

fn main() {
    let yul_file = env::args().nth(1).expect("Expected Yul .yul file");

    let mut file = File::open(yul_file).unwrap();
    let mut content = String::new();
    file.read_to_string(&mut content).unwrap();

    let mut ast = yul_parser::parse_block(&content);
    let signatures = resolve::<EVMDialect>(&mut ast);

    let query = yools::encoder::encode(&ast, signatures);
    let query = format!("{}\n{}", query, "(assert (not (= v_666_3 #x0000000000000000000000000000000000000000000000000000000000000000)))\n(check-sat)");

    println!("{}", query);

    let mut file = NamedTempFile::new().unwrap();
    file.write(query.as_bytes()).unwrap();

    let output = Command::new("cvc5")
        .args(["--lang", "smt2"])
        .args([file.path()])
        .output()
        .expect("failed to run query");

    match String::from_utf8(output.stdout).unwrap().as_str() {
        "sat\n" => {
            println!("SAT");
        }
        "unsat\n" => {
            println!("UNSAT");
        }
        _ => {}
    };
}
