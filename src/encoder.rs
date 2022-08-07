use std::collections::HashMap;
use yultsur::yul;
use yultsur::yul::*;

pub struct Encoder {
    expression_counter: u64,
    ssa_counter: HashMap<u64, u64>,
    output: String,
}

pub fn encode(ast: &Block) -> String {
    let mut encoder = Encoder::new();
    encoder.encode_block(ast);
    encoder.output
}

struct SMTVariable {
    name: String,
}

impl Encoder {
    fn new() -> Encoder {
        Encoder{expression_counter: 0, ssa_counter: HashMap::new(), output: String::new()}
    }

    fn encode_variable_declaration(&mut self, var: &VariableDeclaration) {
        for v in &var.variables {
            self.ssa_counter.insert(v.id.unwrap(), 0);
            self.out(format!(
                "(declare-const {} (_ BitVec 256))",
                self.to_smt_variable(v).name
            ));
        }
        if let Some(value) = &var.value {
            let values = self.encode_expression(value);
            assert_eq!(values.len(), var.variables.len());
            for (v, val) in var.variables.iter().zip(values.iter()) {
                self.out(format!(
                    "(assert (= {} {}))",
                    self.to_smt_variable(v).name,
                    val.name
                ));
            }
        }
    }

    fn encode_block(&mut self, block: &yul::Block) {
        block
            .statements
            .iter()
            .for_each(|st| self.encode_statement(st));
    }

    fn encode_function_def(&mut self, fun: &yul::FunctionDefinition) {}
    fn encode_switch(&mut self, fun: &yul::Switch) {}
    fn encode_for(&mut self, fun: &yul::ForLoop) {}

    fn encode_statement(&mut self, st: &yul::Statement) {
        match st {
            yul::Statement::Block(block) => self.encode_block(block),
            yul::Statement::FunctionDefinition(fun) => self.encode_function_def(fun),
            yul::Statement::If(if_st) => self.encode_if(if_st),
            yul::Statement::Switch(switch) => self.encode_switch(switch),
            yul::Statement::ForLoop(for_loop) => self.encode_for(for_loop),
            yul::Statement::Expression(expr) => {
                assert!(self.encode_expression(expr).is_empty());
            }
            _ => {}
        };
    }

    fn encode_if(&mut self, expr: &yul::If) {
        let cond = self.encode_expression(&expr.condition);
        let prev_ssa = self.ssa_counter.clone();
    }

    fn encode_expression(&mut self, expr: &Expression) -> Vec<SMTVariable> {
        match expr {
            Expression::Literal(literal) => vec![self.encode_literal(literal)],
            Expression::Identifier(identifier) => vec![self.encode_identifier(identifier)],
            Expression::FunctionCall(function) => self.encode_function_call(function),
        }
    }

    fn encode_literal(&mut self, literal: &Literal) -> SMTVariable {
        let var = self.new_temporary_variable();
        // TODO encode in hex
        self.out(format!(
            "(define-const {} (_ BitVec 256) {})",
            &var.name, &literal.literal
        ));
        var
    }
    fn encode_identifier(&mut self, identifier: &Identifier) -> SMTVariable {
        self.to_smt_variable(identifier)
    }
    fn encode_function_call(&mut self, _function: &FunctionCall) -> Vec<SMTVariable> {
        // TODO
        vec![self.new_temporary_variable()]
    }

    fn new_temporary_variable(&mut self) -> SMTVariable {
        self.expression_counter += 1;
        SMTVariable {
            name: format!("_{}", self.expression_counter),
        }
    }

    fn to_smt_variable(&self, identifier: &Identifier) -> SMTVariable {
        let id = identifier.id.unwrap();
        SMTVariable {
            name: format!("v_{}_{}", id, self.ssa_counter[&id]),
        }
    }

    fn out(&mut self, x: String) {
        self.output = format!("{}\n{}", self.output, x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn encode_from_source(input: &str) -> String {
        let mut ast = yultsur::yul_parser::parse_block(input);
        yultsur::resolver::resolve(&mut ast);
        encode(&ast)
    }

    #[test]
    fn empty() {
        assert_eq!(
            encode_from_source("{}"),
            ""
        );
    }
}