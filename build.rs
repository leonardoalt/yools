use std::env;
use std::fs::read_dir;
use std::fs::DirEntry;
use std::fs::File;
use std::io::Write;
use std::path::Path;

/**
 * This creates a file "test_assert_pass.rs" in the target directory
 * that contains one test case for each .yul file in
 * tests/assert_pass
 */
fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let destination = Path::new(&out_dir).join("test_assert_pass.rs");
    let mut test_file = File::create(&destination).unwrap();

    write_header(&mut test_file);

    // TODO recursion
    for directory in read_dir("./tests/assert_pass/").unwrap() {
        write_test(&mut test_file, &directory.unwrap());
    }
}

fn write_test(test_file: &mut File, file: &DirEntry) {
    if let Some(file_name) = file
        .file_name()
        .to_str()
        .unwrap()
        .to_string()
        .strip_suffix(".yul")
    {
        let test_name: String = file_name
            .chars()
            .map(|c| if c.is_alphanumeric() { c } else { '_' })
            .collect();

        write!(
            test_file,
            include_str!("./tests/test_assert_pass.tmpl"),
            name = test_name,
            test_file = file.path().canonicalize().unwrap().display(),
        )
        .unwrap();
    }
}

fn write_header(test_file: &mut File) {
    write!(
        test_file,
        "{}",
        r#"
use yools::encoder;
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
fn unsat(query: &String) {
    assert!(
        !solver::query_smt(query),
        "Expected UNSAT. Query:\n{}",
        query
    );
}

"#
    )
    .unwrap();
}
