use crate::sexpr::SExpr;
use num_bigint::BigUint;
use num_traits::Num;
use std::fmt::{self, Display, Formatter};
use std::io::Write;
use std::process::Command;
use std::str::FromStr;
use tempfile::NamedTempFile;

pub fn query_smt(query: &String) -> bool {
    query_smt_with_solver(query, SolverConfig::new("cvc5"))
}

pub fn query_smt_with_solver(query: &String, solver: SolverConfig) -> bool {
    let (output, stderr) = query_smt_internal(&format!("{query}\n(check-sat)\n"), solver);

    match output.as_str() {
        "sat\n" => true,
        "unsat\n" => false,
        _ => panic!(
            "Invalid output from smt solver.\nQuery: {query}\nStdout: {output}\nStderr: {stderr}",
        ),
    }
}

/// A value in the model, either as a parsed number or an unparsed s-expression.
#[derive(Debug, PartialEq, Eq)]
pub enum ModelValue {
    Number(BigUint),
    String(String),
}

impl Display for ModelValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ModelValue::Number(n) => write!(f, "{n}"),
            ModelValue::String(s) => write!(f, "{s}"),
        }
    }
}

pub fn query_smt_with_solver_and_eval(
    query: &String,
    exprs_to_eval: &Vec<String>,
    solver: SolverConfig,
) -> (bool, Vec<ModelValue>) {
    let mut sat_query = format!("{query}\n(check-sat)\n");
    if !exprs_to_eval.is_empty() {
        sat_query = format!(
            "(set-option :produce-models true)\n{sat_query}(get-value ({}))\n",
            &exprs_to_eval.join(" ")
        )
    }
    let (output, stderr) = query_smt_internal(&sat_query, solver);
    let lines = output
        .split('\n')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>();
    match lines.first() {
        Some(&"sat") => {
            if exprs_to_eval.is_empty() {
                return (true, vec![]);
            }
            let values = SExpr::from_str(lines[1..].join("").trim().to_string().as_str()).unwrap();
            (
                true,
                values
                    .as_subexpr()
                    .iter()
                    .map(|e| {
                        let items = e.as_subexpr();
                        assert!(items.len() == 2);
                        match &items[1] {
                            SExpr::Symbol(symbol) => {
                                ModelValue::Number(if let Some(v) = symbol.strip_prefix("#b") {
                                    BigUint::from_str_radix(v, 2).unwrap()
                                } else if let Some(v) = symbol.strip_prefix("#x") {
                                    BigUint::from_str_radix(v, 16).unwrap()
                                } else {
                                    panic!("Invalid value: {symbol}");
                                })
                            }
                            SExpr::Expr(expr) => match &expr[0] {
                                SExpr::Symbol(symbol) => {
                                    if symbol.as_str() == "_" {
                                        assert!(expr.len() == 3);
                                        assert!(expr[1].as_symbol().starts_with("bv"));
                                        ModelValue::Number(
                                            BigUint::from_str_radix(&expr[1].as_symbol()[2..], 10)
                                                .unwrap(),
                                        )
                                    } else {
                                        ModelValue::String(format!("{}", items[1]))
                                    }
                                }
                                _ => ModelValue::String(format!("{}", items[1])),
                            },
                        }
                    })
                    .collect::<Vec<ModelValue>>(),
            )
        }
        Some(&"unsat") => (false, vec![]),
        _ => {
            panic!("Invalid output from smt solver.\nQuery: {query}\nStdout: {output}\nStderr: {stderr}")
        }
    }
}

fn query_smt_internal(query: &String, solver: SolverConfig) -> (String, String) {
    let mut file = NamedTempFile::new().unwrap();
    file.write_all(query.as_bytes()).unwrap();

    let output = Command::new(solver.cmd)
        .args(solver.args)
        .args([file.path()])
        .output()
        .expect("failed to run query");

    match (
        String::from_utf8(output.stdout),
        String::from_utf8(output.stderr),
    ) {
        (Ok(output), Ok(stderr)) => (output, stderr),
        (Err(err), _) | (_, Err(err)) => {
            panic!("Could not decode output from SMT solver.\nError: {}", err)
        }
    }
}

#[derive(Clone)]
pub struct SolverConfig {
    cmd: String,
    args: Vec<String>,
}

pub enum SMTSolver {
    Z3,
    CVC4,
    CVC5,
}

impl SolverConfig {
    pub fn new(cmd: &str) -> Self {
        match SMTSolver::from_str(cmd) {
            Ok(SMTSolver::Z3) => SolverConfig {
                cmd: cmd.into(),
                args: vec![],
            },
            Ok(SMTSolver::CVC4) => SolverConfig {
                cmd: cmd.into(),
                args: vec!["--lang".into(), "smt2".into(), "--produce-models".into()],
            },
            Ok(SMTSolver::CVC5) => SolverConfig {
                cmd: cmd.into(),
                args: vec!["--lang".into(), "smt2".into(), "--produce-models".into()],
            },
            _ => panic!(),
        }
    }
}

impl FromStr for SMTSolver {
    type Err = ();
    fn from_str(solver: &str) -> Result<SMTSolver, Self::Err> {
        match solver {
            "z3" => Ok(SMTSolver::Z3),
            "cvc4" => Ok(SMTSolver::CVC4),
            "cvc5" => Ok(SMTSolver::CVC5),
            _ => Err(()),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn all_solvers(f: impl Fn(SolverConfig)) {
        for solver in [
            SolverConfig::new("cvc4"),
            SolverConfig::new("cvc5"),
            SolverConfig::new("z3"),
        ] {
            f(solver);
        }
    }

    #[test]
    fn parse_counterexample() {
        all_solvers(|solver| {
            let (sat, eval) = query_smt_with_solver_and_eval(
                &"(declare-fun x () (_ BitVec 16))(assert (= x #x0100))".to_string(),
                &vec!["x".to_string()],
                solver,
            );
            assert_eq!(sat, true);
            assert_eq!(eval, vec![ModelValue::Number(BigUint::from(0x100u32))]);
        })
    }

    #[test]
    fn parse_counterexample_empty_eval() {
        all_solvers(|solver| {
            let (sat, eval) = query_smt_with_solver_and_eval(
                &"(declare-fun x () (_ BitVec 16))(assert (= x #x0100))".to_string(),
                &vec![],
                solver,
            );
            assert_eq!(sat, true);
            assert_eq!(eval, vec![]);
        })
    }

    #[test]
    fn query_counterexample_unsat() {
        all_solvers(|solver| {
            let (sat, eval) = query_smt_with_solver_and_eval(
                &"(declare-fun x () (_ BitVec 16))(assert (and (= x #x0100) (= x #x0000)))"
                    .to_string(),
                &vec!["x".to_string()],
                solver,
            );
            assert_eq!(sat, false);
            assert_eq!(eval, vec![]);
        })
    }

    #[test]
    fn parse_counterexample_multi() {
        all_solvers(|solver| {
            let (sat, eval) = query_smt_with_solver_and_eval(
                &"(declare-fun x () (_ BitVec 16))(assert (= x #x0100))".to_string(),
                &vec!["x".to_string(), "(bvadd x #x0001)".to_string()],
                solver,
            );
            assert_eq!(sat, true);
            assert_eq!(
                eval,
                vec![
                    ModelValue::Number(BigUint::from(0x100u32)),
                    ModelValue::Number(BigUint::from(0x101u32))
                ]
            );
        })
    }

    #[test]
    fn parse_counterexample_function() {
        all_solvers(|solver| {
            let (sat, eval) = query_smt_with_solver_and_eval(
                &"(declare-fun x ((_ BitVec 16)) (_ BitVec 8))(assert (= (x #x0011) #x01))"
                    .to_string(),
                &vec!["x".to_string()],
                solver,
            );
            assert_eq!(sat, true);
            assert_eq!(eval.len(), 1);
            match &eval[0] {
                ModelValue::String(s) => {
                    assert!(
                        s.starts_with("(lambda ((BOUND_VARIABLE_")
                            || s.starts_with("(lambda ((_arg_1 (_ BitVec 16)))")
                            || s.starts_with("(store ((as const Array"),
                        "Expected different counterexample. Found: {eval:?}"
                    );
                }
                _ => panic!("Expected different counterexample. Found: {eval:?}"),
            }
        })
    }

    #[test]
    fn parse_counterexample_array() {
        all_solvers(|solver| {
            let (sat, eval) = query_smt_with_solver_and_eval(
                &"(declare-fun x () (Array (_ BitVec 8) (_ BitVec 8)))(assert (= (select x #x01) #x01))"
                    .to_string(),
                &vec!["x".to_string()],
                solver,
            );
            assert_eq!(sat, true);
            assert_eq!(eval.len(), 1);
            match &eval[0] {
                ModelValue::String(s) => {
                    assert!(
                        s.starts_with("(store ((as const (Array (_ BitVec 8)")
                            || s.starts_with("((as const (Array (_ BitVec 8)"),
                        "Expected different counterexample. Found: {eval:?}"
                    );
                }
                _ => panic!("Expected different counterexample. Found: {eval:?}"),
            }
        })
    }
}
