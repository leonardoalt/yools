use std::io::Write;
use std::process::Command;
use tempfile::NamedTempFile;

pub fn query_smt(query: &String) -> bool {
    let query = format!("{}\n{}", query, "(check-sat)");

    let mut file = NamedTempFile::new().unwrap();
    file.write_all(query.as_bytes()).unwrap();

    let output = Command::new("cvc4")
        .args(["--lang", "smt2"])
        .args([file.path()])
        .output()
        .expect("failed to run query");

    match (
        String::from_utf8(output.stdout),
        String::from_utf8(output.stderr),
    ) {
        (Ok(output), Ok(stderr)) => match output.as_str() {
            "sat\n" => true,
            "unsat\n" => false,
            _ => panic!(
                "Invalid output from smt solver.\nQuery: {}\nStdout: {}\nStderr: {}",
                &query,
                output.as_str(),
                stderr.as_str()
            ),
        },
        (Err(err), _) | (_, Err(err)) => {
            panic!("Could not decode output from SMT solver.\nError: {}", err)
        }
    }
}
