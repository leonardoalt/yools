use crate::cfg::*;

use yultsur::yul;

use std::collections::HashMap;

pub struct SymbExecEngine {
    ssa: HashMap<yul::Identifier, usize>,
}

struct BV {
    width: usize,
}

struct Expr {
    symb: String,
    args: Vec<Expr>,
}

/*
enum BooleanOp {
    Neg(Expr),
    And(Vec<Expr>),
    Or(Vec<Expr>)
}

enum ArithOp {
    Add(Expr, Expr),
    Sub(Expr, Expr),
    Mul(Expr, Expr),
    Div(Expr, Expr),
}
*/

impl SymbExecEngine {
    pub fn new() -> SymbExecEngine {
        SymbExecEngine {
            ssa: HashMap::new(),
        }
    }

    fn root(cfg: &CFG) -> Node {
        let roots: Vec<_> = cfg
            .rev_graph
            .iter()
            .filter(|(_, adj)| adj.is_empty())
            .collect();

        println!("{:?}", cfg.graph);
        assert!(roots.len() == 1);

        roots[0].0.clone()
    }

    pub fn encode(ast: yul::Statement) {
        let cfg = CFGBuilder::build(ast);
        let root = SymbExecEngine::root(&cfg);

        println!("{:?}", root);
    }
}
