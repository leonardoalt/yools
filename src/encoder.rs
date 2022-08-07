use std::collections::HashMap;
use yultsur::yul;
use yultsur::yul::*;

pub struct Encoder {
    expression_counter: u64,
    ssa_counter: HashMap<u64, u64>,
    output: String,
}

struct SMTVariable {
    name: String,
}

impl Encoder {
    fn encode_variable_declaration(&mut self, var: &VariableDeclaration) -> SMTVariable {}

    fn encode_expression(&mut self, expr: &Expression) -> SMTVariable {
        match expr {
            Expression::Literal(literal) => self.encode_literal(literal),
            Expression::Identifier(identifier) => self.encode_identifier(identifier),
            Expression::FunctionCall(function) => self.encode_function_call(function),
        }
    }

    fn encode_literal(&mut self, literal: &Literal) -> SMTVariable {
        let var = new_variable();
        // TODO encode in hex
        output += "(define-const " + var.name + " (_ BitVec 256) " + literal.literal + ")";
        var
    }
    fn encode_identifier(&mut self, identifier: &Identifier) -> SMTVariable {
        to_smt_variable(identifier)
    }

    fn new_variable(&mut self) -> SMTVariable {
        self.expression_counter += 1;
        SMTVariable{name: "_" + self.expression_counter.to_string()}
    }
}
