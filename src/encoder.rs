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
        Encoder {
            expression_counter: 0,
            ssa_counter: HashMap::new(),
            output: String::new(),
        }
    }

    fn encode_variable_declaration(&mut self, var: &VariableDeclaration) {
        for v in &var.variables {
            self.ssa_counter.insert(v.id.unwrap(), 0);
            if var.value == None {
                self.out(format!(
                    "(declare-const {} (_ BitVec 256))",
                    self.to_smt_variable(v).name
                ));
            }
        }
        if let Some(value) = &var.value {
            self.encode_assignment_inner(&var.variables, value)
        }
    }

    fn encode_assignment(&mut self, assignment: &Assignment) {
        self.encode_assignment_inner(&assignment.variables, &assignment.value);
    }

    fn encode_assignment_inner(&mut self, variables: &Vec<Identifier>, value: &Expression) {
        for v in variables {
            *self.ssa_counter.get_mut(&v.id.unwrap()).unwrap() += 1;
        }
        let values = self.encode_expression(value);
        assert_eq!(values.len(), variables.len());
        for (v, val) in variables.iter().zip(values.iter()) {
            self.out(format!(
                "(define-const {} (_ BitVec 256) {})",
                self.to_smt_variable(v).name,
                val.name
            ));
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
            yul::Statement::VariableDeclaration(var_decl) => {
                self.encode_variable_declaration(var_decl)
            }
            yul::Statement::Assignment(assignment) => self.encode_assignment(assignment),
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
        assert!(cond.len() == 1);
        let prev_ssa = self.ssa_counter.clone();

        self.encode_block(&expr.body);

        let mut merge_ssa = HashMap::<u64, u64>::new();

        prev_ssa
            .iter()
            .for_each(|(key, value)| {
                let branch_ssa = *self.ssa_counter.get(key).unwrap();
                if branch_ssa > *value {
                    let new_ssa = branch_ssa + 1;
                    self.out(format!(
                        "(define-const {} (_ BitVec 256) (ite {} {} {})",
                        self.id_to_smt_variable(*key, new_ssa).name,
                        cond[0].name,
                        self.id_to_smt_variable(*key, branch_ssa).name,
                        self.id_to_smt_variable(*key, *value).name,
                    ));

                    merge_ssa.insert(key.clone(), new_ssa);
                } else {
                    merge_ssa.insert(key.clone(), value.clone());
                }
            });

        self.ssa_counter = merge_ssa;
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

    fn id_to_smt_variable(&self, id: u64, ssa_idx: u64) -> SMTVariable {
        SMTVariable {
            name: format!("v_{}_{}", id, ssa_idx),
        }
    }

    fn to_smt_variable(&self, identifier: &Identifier) -> SMTVariable {
        let id = identifier.id.unwrap();
        SMTVariable {
            name: format!("v_{}_{}", id, self.ssa_counter[&id]),
        }
    }

    fn out(&mut self, x: String) {
        self.output = format!("{}{}\n", self.output, x)
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
        assert_eq!(encode_from_source("{}"), "");
    }

    #[test]
    fn variable_declaration() {
        assert_eq!(
            encode_from_source("{ let x := 2 }"),
            "(define-const _1 (_ BitVec 256) 2)\n(define-const v_2_1 (_ BitVec 256) _1)\n"
        );
    }

    #[test]
    fn variable_declaration_empty() {
        assert_eq!(
            encode_from_source("{ let x, y }"),
            "(declare-const v_2_0 (_ BitVec 256))\n(declare-const v_3_0 (_ BitVec 256))\n"
        );
    }

    #[test]
    fn assignment() {
        assert_eq!(
            encode_from_source("{ let x, y y := 9}"),
            vec![
                "(declare-const v_2_0 (_ BitVec 256))",
                "(declare-const v_3_0 (_ BitVec 256))",
                "(define-const _1 (_ BitVec 256) 9)",
                "(define-const v_3_1 (_ BitVec 256) _1)\n"
            ]
            .join("\n")
        );
    }

    #[test]
    fn if_st() {
        assert_eq!(
            encode_from_source("{ let x := 9 let c := 1 if c { x := 666 } }"),
            vec![
                "(define-const _1 (_ BitVec 256) 9)",
                "(define-const v_2_1 (_ BitVec 256) _1)",
                "(define-const _2 (_ BitVec 256) 1)",
                "(define-const v_3_1 (_ BitVec 256) _2)",
                "(define-const _3 (_ BitVec 256) 666)",
                "(define-const v_2_2 (_ BitVec 256) _3)",
                "(define-const v_2_3 (_ BitVec 256) (ite v_3_1 v_2_2 v_2_1)\n"
            ]
            .join("\n")
        );
    }

}
