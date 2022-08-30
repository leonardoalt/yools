use std::collections::HashMap;
use yultsur::dialect::{Dialect, EVMDialect};
use yultsur::resolver::FunctionSignature;
use yultsur::yul;
use yultsur::yul::*;

struct Context {
    revert_flag: Identifier,
}

impl Context {
    fn new() -> Context {
        Context {
            revert_flag: Identifier {
                id: IdentifierID::Declaration(666),
                name: "revert_flag".to_string(),
            },
        }
    }
}

pub struct Encoder {
    function_signatures: HashMap<u64, FunctionSignature>,
    expression_counter: u64,
    /// Current SSA index for each variable
    ssa_current: HashMap<u64, u64>,
    /// Highest SSA index (used for next assignment) for each variable
    ssa_highest: HashMap<u64, u64>,
    output: String,
    context: Context,
}

pub fn encode(ast: &Block, function_signatures: HashMap<u64, FunctionSignature>) -> String {
    let mut encoder = Encoder::new(function_signatures);
    encoder.encode(ast);
    encoder.output
}

pub fn encode_function(
    function: &FunctionDefinition,
    function_signatures: HashMap<u64, FunctionSignature>,
) -> (String, FunctionVariables) {
    let mut encoder = Encoder::new(function_signatures);
    encoder.encode_context_init();
    let variables = encoder.encode_function(function);
    (encoder.output, variables)
}

#[derive(Clone, Debug, PartialEq)]
pub struct SMTVariable {
    pub name: String,
}

#[derive(Debug, PartialEq)]
pub struct FunctionVariables {
    /// smtlib2 names of the initial values of the function parameters
    pub parameters: Vec<SMTVariable>,
    /// smtlib2 names of the final values of the function return variables
    pub returns: Vec<SMTVariable>,
}

impl Encoder {
    fn new(function_signatures: HashMap<u64, FunctionSignature>) -> Encoder {
        Encoder {
            function_signatures,
            expression_counter: 0,
            ssa_current: HashMap::new(),
            ssa_highest: HashMap::new(),
            output: String::new(),
            context: Context::new(),
        }
    }

    pub fn encode(&mut self, block: &Block) {
        self.encode_context_init();
        self.encode_block(block);
        self.encode_no_revert();
    }

    /// Encodes the given function, potentially re-creating copies of all local variables
    /// if called multiple times.
    /// @returns the names of the function parameters and return variables.
    pub fn encode_function(&mut self, function: &FunctionDefinition) -> FunctionVariables {
        self.encode_variable_declaration(&VariableDeclaration {
            variables: function.parameters.clone(),
            value: None,
        });
        let parameters = self.to_smt_variables(&function.parameters);
        for r in &function.returns {
            self.encode_variable_declaration(&VariableDeclaration {
                variables: vec![r.clone()],
                value: Some(Expression::Literal(Literal::new("0"))),
            });
        }
        self.encode_block(&function.body);
        let returns = self.to_smt_variables(&function.returns);
        FunctionVariables {
            parameters,
            returns,
        }
    }

    fn encode_variable_declaration(&mut self, var: &VariableDeclaration) {
        for v in &var.variables {
            let var_id = if let IdentifierID::Declaration(id) = v.id {
                id
            } else {
                panic!();
            };
            self.allocate_new_ssa_index(var_id);
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

    fn encode_block(&mut self, block: &yul::Block) {
        block
            .statements
            .iter()
            .for_each(|st| self.encode_statement(st));
    }

    fn encode_function_def(&mut self, _fun: &yul::FunctionDefinition) {}

    fn encode_switch(&mut self, switch: &yul::Switch) {
        let discriminator = self.encode_expression(&switch.expression);
        assert!(discriminator.len() == 1);
        let pre_switch_ssa = self.ssa_current.clone();
        let mut post_switch_ssa = std::mem::take(&mut self.ssa_current);

        for Case { literal, body } in &switch.cases {
            // TODO default case is not yet implemented because
            // the ITE expression is complicated.
            assert!(*literal != None);
            self.ssa_current = pre_switch_ssa.clone();

            self.encode_block(body);

            pre_switch_ssa.iter().for_each(|(key, value)| {
                let branch_ssa = self.ssa_current[key];
                if branch_ssa > *value {
                    let new_ssa = self.allocate_new_ssa_index(*key);
                    self.out(format!(
                        "(define-const {} (_ BitVec 256) (ite (= {} {}) {} {}))",
                        self.id_to_smt_variable(*key, new_ssa).name,
                        discriminator[0].name,
                        self.encode_literal_value(literal.as_ref().unwrap()),
                        self.id_to_smt_variable(*key, branch_ssa).name,
                        self.id_to_smt_variable(*key, post_switch_ssa[key]).name,
                    ));

                    post_switch_ssa.insert(*key, new_ssa);
                }
            });
        }

        self.ssa_current = post_switch_ssa;
    }

    fn encode_for(&mut self, _fun: &yul::ForLoop) {}

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
        let mut prev_ssa = self.ssa_current.clone();

        self.encode_block(&expr.body);

        prev_ssa.iter_mut().for_each(|(key, value)| {
            let branch_ssa = *self.ssa_current.get(key).unwrap();
            if branch_ssa > *value {
                let new_ssa = self.allocate_new_ssa_index(*key);
                self.out(format!(
                    "(define-const {} (_ BitVec 256) (ite (= {} #x0000000000000000000000000000000000000000000000000000000000000000) {} {}))",
                    self.id_to_smt_variable(*key, new_ssa).name,
                    cond[0].name,
                    self.id_to_smt_variable(*key, *value).name,
                    self.id_to_smt_variable(*key, branch_ssa).name,
                ));

                *value = new_ssa;
            }
        });

        self.ssa_current = prev_ssa;
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
        self.out(format!(
            "(define-const {} (_ BitVec 256) {})",
            &var.name,
            self.encode_literal_value(literal)
        ));
        var
    }

    fn encode_identifier(&mut self, identifier: &Identifier) -> SMTVariable {
        self.to_smt_variable(identifier)
    }

    fn encode_function_call(&mut self, call: &FunctionCall) -> Vec<SMTVariable> {
        let arguments = call
            .arguments
            .iter()
            .map(|arg| {
                let mut value = self.encode_expression(arg);
                assert_eq!(value.len(), 1);
                value.pop().unwrap()
            })
            .collect::<Vec<_>>();

        match call.function.id {
            IdentifierID::BuiltinReference => {
                let returns = EVMDialect::builtin(&call.function.name).unwrap().returns;
                let vars: Vec<SMTVariable> = (0..returns)
                    .map(|_i| self.new_temporary_variable())
                    .collect();
                if let Some(builtin_call) = encode_builtin(&call.function.name, &arguments) {
                    assert_eq!(returns, 1);
                    self.out(format!(
                        "(define-const {} (_ BitVec 256) {})",
                        &vars.first().unwrap().name,
                        builtin_call
                    ));
                }
                if call.function.name.as_str() == "revert" {
                    let v = vec![Identifier {
                        id: IdentifierID::Reference(666),
                        name: "revert_flag".to_string(),
                    }];
                    let e = Expression::Literal(Literal::new("1"));
                    self.encode_assignment_inner(&v, &e);
                }
                vars
            }
            IdentifierID::Reference(id) => {
                let returns = self.function_signatures[&id].returns;
                (0..returns)
                    .map(|_i| self.new_temporary_variable())
                    .collect()
            }
            _ => panic!(
                "Unexpected reference in function call: {:?}",
                call.function.id
            ),
        }
    }

}

fn is_bool_function(name: &str) -> bool {
    matches!(name, "bvult" | "bvugt" | "bvslt" | "bvsgt")
}

fn encode_builtin(name: &str, arguments: &[SMTVariable]) -> Option<String> {
    match name {
        "add" => Some("bvadd"),
        "sub" => Some("bvsub"),
        "mul" => Some("bvmul"),
        "div" => Some("bvdiv"),
        "sdiv" => Some("bvsdiv"),
        "not" => Some("bvnot"),
        "lt" => Some("bvult"),
        "gt" => Some("bvugt"),
        "slt" => Some("bvslt"),
        "sgt" => Some("bvsgt"),
        "eq" => Some("="),
        "and" => Some("bvand"),
        "or" => Some("bvor"),
        "xor" => Some("bvxor"),
        _ => None,
    }
    .map(|smt_name| match is_bool_function(smt_name) {
        true => format!("(ite ({} {} {}) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000)", smt_name, arguments[0].name, arguments[1].name),
        false => format!("({} {} {})", smt_name, arguments[0].name, arguments[1].name)
    })

    // TODO ISZERO
}

/// Helpers.
impl Encoder {
    fn encode_context_init(&mut self) {
        let v = VariableDeclaration {
            variables: vec![self.context.revert_flag.clone()],
            value: Some(Expression::Literal(Literal::new("0"))),
        };

        self.encode_variable_declaration(&v);
    }

    fn encode_no_revert(&mut self) {
        self.out(format!("(assert (not (= {} #x0000000000000000000000000000000000000000000000000000000000000000)))", self.to_smt_variable(&self.context.revert_flag).name));
    }

    fn allocate_new_ssa_index(&mut self, var_id: u64) -> u64 {
        let ssa = *self
            .ssa_highest
            .entry(var_id)
            .and_modify(|c| *c += 1)
            .or_insert(0);
        self.ssa_current.insert(var_id, ssa);
        ssa
    }

    fn encode_assignment_inner(&mut self, variables: &Vec<Identifier>, value: &Expression) {
        for v in variables {
            let var_id = match v.id {
                IdentifierID::Declaration(id) => id,
                IdentifierID::Reference(id) => id,
                _ => panic!(),
            };
            self.allocate_new_ssa_index(var_id);
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

    fn encode_literal_value(&self, literal: &Literal) -> String {
        // TODO encode in hex
        format!("#x{:064X}", &literal.literal.parse::<u128>().unwrap())
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
        let var_id = match identifier.id {
            IdentifierID::Declaration(id) => id,
            IdentifierID::Reference(id) => id,
            _ => panic!(),
        };
        SMTVariable {
            name: format!("v_{}_{}", var_id, self.ssa_current[&var_id]),
        }
    }

    fn to_smt_variables(&self, identifiers: &[Identifier]) -> Vec<SMTVariable> {
        identifiers
            .iter()
            .map(|i| self.to_smt_variable(i))
            .collect()
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
        let signatures = yultsur::resolver::resolve::<EVMDialect>(&mut ast);
        encode(&ast, signatures)
    }

    fn encode_function_from_source(input: &str) -> (String, FunctionVariables) {
        let mut ast = yultsur::yul_parser::parse_block(input);
        let signatures = yultsur::resolver::resolve::<EVMDialect>(&mut ast);
        let mut encoder = Encoder::new(signatures);
        if let Statement::FunctionDefinition(fun) = &ast.statements[0] {
            let variables = encoder.encode_function(&fun);
            return (encoder.output, variables);
        } else {
            panic!()
        }
    }

    fn assert_encoded(input: &str, expectation: &String) {
        let encoded = encode_from_source(input);
        assert!(
            encoded == *expectation,
            "Invaling encoding. Expected:\n{:?}\nTo fix, update to:\n{}\n",
            expectation,
            encoded
                .split("\n")
                .map(|l| format!("\"{l}\",\n"))
                .collect::<String>()
        );
    }

    #[test]
    fn empty() {
        assert_encoded(
            "{}",
            &vec![
                "(define-const _1 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)",
                "(define-const v_666_1 (_ BitVec 256) _1)",
                "(assert (not (= v_666_1 #x0000000000000000000000000000000000000000000000000000000000000000)))\n",
            ]
            .join("\n")
        );
    }

    #[test]
    fn variable_declaration() {
        assert_encoded(
            "{ let x := 2 }",
            &vec![
                "(define-const _1 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)",
                "(define-const v_666_1 (_ BitVec 256) _1)",
                "(define-const _2 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000002)",
                "(define-const v_2_1 (_ BitVec 256) _2)",
                "(assert (not (= v_666_1 #x0000000000000000000000000000000000000000000000000000000000000000)))\n",
            ]
            .join("\n")
        );
    }

    #[test]
    fn variable_declaration_empty() {
        assert_encoded(
            "{ let x, y }",
            &vec![
                "(define-const _1 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)",
                "(define-const v_666_1 (_ BitVec 256) _1)",
                "(declare-const v_2_0 (_ BitVec 256))",
                "(declare-const v_3_0 (_ BitVec 256))",
                "(assert (not (= v_666_1 #x0000000000000000000000000000000000000000000000000000000000000000)))\n",
            ]
            .join("\n")       
         );
    }

    #[test]
    fn assignment() {
        assert_encoded(
            "{ let x, y y := 9}",
            &vec![
                "(define-const _1 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)",
                "(define-const v_666_1 (_ BitVec 256) _1)",
                "(declare-const v_2_0 (_ BitVec 256))",
                "(declare-const v_3_0 (_ BitVec 256))",
                "(define-const _2 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000009)",
                "(define-const v_3_1 (_ BitVec 256) _2)",
                "(assert (not (= v_666_1 #x0000000000000000000000000000000000000000000000000000000000000000)))\n",
            ]
            .join("\n")
        );
    }

    #[test]
    fn builtin_add() {
        assert_encoded(
            "{ let y := 1 let x := add(add(2, 3), y) }",
            &vec![
                "(define-const _1 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)",
                "(define-const v_666_1 (_ BitVec 256) _1)",
                "(define-const _2 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000001)",
                "(define-const v_2_1 (_ BitVec 256) _2)",
                "(define-const _3 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000002)",
                "(define-const _4 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000003)",
                "(define-const _5 (_ BitVec 256) (bvadd _3 _4))",
                "(define-const _6 (_ BitVec 256) (bvadd _5 v_2_1))",
                "(define-const v_3_1 (_ BitVec 256) _6)",
                "(assert (not (= v_666_1 #x0000000000000000000000000000000000000000000000000000000000000000)))\n",
            ]
            .join("\n")
        );
    }

    #[test]
    fn if_st() {
        assert_encoded(
            "{ let x := 9 let c := 1 if c { x := 666 } }",
            &vec![
                "(define-const _1 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)",
                "(define-const v_666_1 (_ BitVec 256) _1)",
                "(define-const _2 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000009)",
                "(define-const v_2_1 (_ BitVec 256) _2)",
                "(define-const _3 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000001)",
                "(define-const v_3_1 (_ BitVec 256) _3)",
                "(define-const _4 (_ BitVec 256) #x000000000000000000000000000000000000000000000000000000000000029A)",
                "(define-const v_2_2 (_ BitVec 256) _4)",
                "(define-const v_2_3 (_ BitVec 256) (ite (= v_3_1 #x0000000000000000000000000000000000000000000000000000000000000000) v_2_1 v_2_2))",
                "(assert (not (= v_666_1 #x0000000000000000000000000000000000000000000000000000000000000000)))\n",
            ]
            .join("\n")
        );
    }

    #[test]
    fn function() {
        let (output, variables) =
            encode_function_from_source("{ function f(a, b) -> c { c := b } }");
        assert_eq!(output,
                vec![
                    "(declare-const v_3_0 (_ BitVec 256))",
                    "(declare-const v_4_0 (_ BitVec 256))",
                    "(define-const _1 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)",
                    "(define-const v_5_1 (_ BitVec 256) _1)",
                    "(define-const v_5_2 (_ BitVec 256) v_4_0)\n"
                ].join("\n"));
        assert_eq!(
            variables,
            FunctionVariables {
                parameters: vec![
                    SMTVariable {
                        name: String::from("v_3_0")
                    },
                    SMTVariable {
                        name: String::from("v_4_0")
                    }
                ],
                returns: vec![SMTVariable {
                    name: String::from("v_5_2")
                }],
            }
        );
    }
}
