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
    // fn encode_variable_declaration(&mut self, var: &VariableDeclaration) -> SMTVariable {

    // }

    fn encode_expression(&mut self, expr: &Expression) -> SMTVariable {
        match expr {
            Expression::Literal(literal) => self.encode_literal(literal),
            Expression::Identifier(identifier) => self.encode_identifier(identifier),
            Expression::FunctionCall(function) => self.encode_function_call(function),
        }
    }

    fn encode_literal(&mut self, literal: &Literal) -> SMTVariable {
        let var = self.new_temporary_variable();
        // TODO encode in hex
        self.out(format!("(define-const {} (_ BitVec 256) {})", &var.name, &literal.literal));
        var
    }
    fn encode_identifier(&mut self, identifier: &Identifier) -> SMTVariable {
        self.to_smt_variable(identifier)
    }
    fn encode_function_call(&mut self, _function: &FunctionCall) -> SMTVariable {
        // TODO
        self.new_temporary_variable()
    }

    fn new_temporary_variable(&mut self) -> SMTVariable {
        self.expression_counter += 1;
        SMTVariable{name: format!("_{}", self.expression_counter)}
    }

    fn to_smt_variable(&mut self, identifier: &Identifier) -> SMTVariable {
        let id = identifier.id.unwrap();
        SMTVariable{name: format!("v_{}_{}", id, self.ssa_counter[& id])}
    }

    fn out(&mut self, x: String) {
        self.output = format!("{}\n{}", self.output, x)
    }
}
