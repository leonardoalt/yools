use std::io::Write;
use std::process::Command;
use tempfile::NamedTempFile;
use yools::encoder::encode_function;
use yools::encoder::FunctionVariables;
use yultsur::dialect::EVMDialect;
use yultsur::resolver::resolve;
use yultsur::yul::*;
use yultsur::yul_parser;

fn encode_first_function(input: &str) -> (String, FunctionVariables) {
    let mut ast = yul_parser::parse_block(&std::format!("{{ {} }}", input));
    let signatures = resolve::<EVMDialect>(&mut ast);
    if let Some(Statement::FunctionDefinition(function)) = ast.statements.iter().next() {
        encode_function(function, signatures)
    } else {
        panic!("Could not find function.")
    }
}

fn query_smt(query: &String) -> bool {
    let query = format!("{}\n{}", query, "(check-sat)");

    let mut file = NamedTempFile::new().unwrap();
    file.write(query.as_bytes()).unwrap();

    let output = String::from_utf8(
        Command::new("cvc4")
            .args(["--lang", "smt2"])
            .args([file.path()])
            .output()
            .expect("failed to run query")
            .stdout,
    )
    .unwrap();

    match output.as_str() {
        "sat\n" => true,
        "unsat\n" => false,
        _ => panic!(
            "Invalid output from smt solver. Query: {}\nOutput: {}",
            &query, output
        ),
    }
}

fn tautology(q: &str, condition: &String) {
    let query = &std::format!("{q}\n(assert (not {condition}))\n");
    assert!(!query_smt(&query), "Tautology failed. Query: {query}");
}
fn satisfiable(q: &str, condition: &String) {
    let query = &std::format!("{q}\n(assert {condition})\n");
    assert!(query_smt(&query), "Satisfiability failed. Query: {query}");
}

#[test]
fn projection() {
    let (encoding, variables) = encode_first_function("function f(x, y) -> r { r := y }");
    tautology(
        &encoding,
        &std::format!(
            "(= {} {})",
            variables.returns[0].name,
            variables.parameters[1].name
        ),
    );
    satisfiable(
        &encoding,
        &std::format!(
            "(= {} {})",
            variables.returns[0].name,
            variables.parameters[0].name
        ),
    );
}

#[test]
fn zero_init() {
    let (encoding, variables) = encode_first_function("function f(x, y) -> r, t { r := y }");
    tautology(
        &encoding,
        &std::format!("(= {} #x{:064X})", variables.returns[1].name, 0),
    );
}

#[test]
fn arith_add() {
    let (encoding, variables) = encode_first_function("function f(x, y) -> r { r := add(x, y) }");
    tautology(
        &encoding,
        &std::format!(
            "(= {} (bvadd {} {}))",
            variables.returns[0].name,
            variables.parameters[0].name,
            variables.parameters[1].name
        ),
    );
}

#[test]
fn large_hex_constants_wrapping() {
    let (encoding, variables) = encode_first_function(
        r#"
        function f() -> a {
            let x := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
            a := add(x, 2)
        }"#,
    );
    tautology(
        &encoding,
        &std::format!("(= {} #x{:064X})", variables.returns[0].name, 1),
    );
}

#[test]
fn assignments() {
    let (encoding, variables) = encode_first_function(
        r#"
        function f() -> a, b {
            let x
            let y := 2
            x := add(x, y)
            y := add(y, 11)
            a := x
            b := y
        }"#,
    );
    tautology(
        &encoding,
        &std::format!(
            "(and (= {} #x{:064X}) (= {} #x{:064X}))",
            variables.returns[0].name,
            2,
            variables.returns[1].name,
            13
        ),
    );
}

#[test]
fn branches() {
    let (encoding, variables) = encode_first_function(
        r#"
        function f(x, y) -> r {
            let t := 20
            if lt(x, 2) { t := 7 }
            if gt(x, 1) { t := 8 }
            r := lt(t, 9)
        }"#,
    );
    tautology(
        &encoding,
        &std::format!("(= {} #x{:064X})", variables.returns[0].name, 1),
    );
}

#[test]
fn switch() {
    let (encoding, variables) = encode_first_function(
        r#"
        function f(x) -> r, t {
            r := 1
            switch x
                case 0 { r := 9 t := 7 }
                case 1 { r := t }
        }"#,
    );
    tautology(
        &encoding,
        &std::format!(
            "(=> (= {} #x{:064X}) (and (= {} #x{:064X}) (= {} #x{:064X})))",
            variables.parameters[0].name,
            0,
            variables.returns[0].name,
            9,
            variables.returns[1].name,
            7,
        ),
    );
    tautology(
        &encoding,
        &std::format!(
            "(=> (= {} #x{:064X}) (and (= {} #x{:064X}) (= {} #x{:064X})))",
            variables.parameters[0].name,
            1,
            variables.returns[0].name,
            0,
            variables.returns[1].name,
            0,
        ),
    );
    tautology(
        &encoding,
        &std::format!(
            "(=> (= {} #x{:064X}) (and (= {} #x{:064X}) (= {} #x{:064X})))",
            variables.parameters[0].name,
            2,
            variables.returns[0].name,
            1,
            variables.returns[1].name,
            0,
        ),
    );
}

#[test]
fn for_loop() {
    let (encoding, variables) = encode_first_function(
        r#"
        function f(x, i, p) -> r {
            let y := 3
            for {} lt(x, y) { x := add(x, i) } { x := add(x, p) }
            r := x
        }"#,
    );
    tautology(
        &encoding,
        &std::format!(
            r#"(=>
                (and (= {} #x{:064X}) (= {} #x{:064X}) (= {} #x{:064X}))
                (= {} #x{:064X})
            )"#,
            variables.parameters[0].name,
            0,
            variables.parameters[1].name,
            1,
            variables.parameters[2].name,
            0,
            variables.returns[0].name,
            3
        ),
    );
    tautology(
        &encoding,
        &std::format!(
            r#"(=>
                (and (= {} #x{:064X}) (= {} #x{:064X}) (= {} #x{:064X}))
                (= {} #x{:064X})
            )"#,
            variables.parameters[0].name,
            0,
            variables.parameters[1].name,
            2,
            variables.parameters[2].name,
            0,
            variables.returns[0].name,
            4
        ),
    );
    tautology(
        &encoding,
        &std::format!(
            r#"(=>
                (and (= {} #x{:064X}) (= {} #x{:064X}) (= {} #x{:064X}))
                (= {} #x{:064X})
            )"#,
            variables.parameters[0].name,
            0,
            variables.parameters[1].name,
            0,
            variables.parameters[2].name,
            1,
            variables.returns[0].name,
            3
        ),
    );
}

#[test]
fn for_loop_nested() {
    let (encoding, variables) = encode_first_function(
        r#"
        function f(x, y) -> r, t {
            for {} lt(x, 3) {
                for {} lt(y, 3) {
                    y := add(y, 1)
                } {}
            } { x := add(x, 1) }
            r := x
            t := y
        }"#,
    );
    tautology(
        &encoding,
        &std::format!(
            r#"(=>
                (and (= {} #x{:064X}) (= {} #x{:064X}))
                (and (= {} #x{:064X}) (= {} #x{:064X}))
            )"#,
            variables.parameters[0].name,
            0,
            variables.parameters[1].name,
            0,
            variables.returns[0].name,
            3,
            variables.returns[1].name,
            3,
        ),
    );
}

#[test]
fn address() {
    let (encoding, variables) = encode_first_function(
        r#"
        function f() -> t {
            let x := address()
            t := lt(x, 0x10000000000000000000000000000000000000000)
        }"#,
    );
    tautology(
        &encoding,
        &std::format!("(= {} #x{:064X})", variables.returns[0].name, 1,),
    );
}
