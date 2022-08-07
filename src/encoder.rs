use yultsur::ASTVisitor;
use yul::*;

pub struct Encoder {
    ssa_counter: HashMap<u64, u64>,
}

struct SMT {}

impl Encoder {

    fn encode_variable_declaration(&mut self, var: &VariableDeclaration) -> SMT {
    }

    fn encode_expression(&mut self, expr: &Expression) -> SMT {
}

