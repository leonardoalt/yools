use crate::common::SMTVariable;
use crate::evm_context;
use crate::ssa_tracker::SSATracker;

use yultsur::dialect::{Builtin, Dialect};
use yultsur::resolver::FunctionSignature;
use yultsur::yul;
use yultsur::yul::*;

use std::collections::BTreeMap;

pub trait Instructions: Default + Dialect {
    fn encode_builtin_call(
        &self,
        builtin: &Builtin,
        arguments: Vec<SMTVariable>,
        return_vars: &[SMTVariable],
        ssa: &mut SSATracker,
    ) -> String;
}

pub struct Encoder<InstructionsType> {
    function_signatures: BTreeMap<u64, FunctionSignature>,
    expression_counter: u64,
    ssa_tracker: SSATracker,
    output: String,
    interpreter: InstructionsType,
}

pub fn encode<T: Instructions>(
    ast: &Block,
    function_signatures: BTreeMap<u64, FunctionSignature>,
) -> String {
    let mut encoder = Encoder::<T>::new(function_signatures);
    encoder.encode(ast);
    encoder.output
}

pub fn encode_revert_unreachable<T: Instructions>(
    ast: &Block,
    function_signatures: BTreeMap<u64, FunctionSignature>,
) -> String {
    let mut encoder = Encoder::<T>::new(function_signatures);
    encoder.encode(ast);
    encoder.encode_revert_unreachable();
    encoder.output
}

pub fn encode_function<T: Instructions>(
    function: &FunctionDefinition,
    function_signatures: BTreeMap<u64, FunctionSignature>,
) -> (String, FunctionVariables) {
    let mut encoder = Encoder::<T>::new(function_signatures);
    encoder.encode_context_init();
    let variables = encoder.encode_function(function);
    (encoder.output, variables)
}

#[derive(Debug, PartialEq)]
pub struct FunctionVariables {
    /// smtlib2 names of the initial values of the function parameters
    pub parameters: Vec<SMTVariable>,
    /// smtlib2 names of the final values of the function return variables
    pub returns: Vec<SMTVariable>,
}

impl<InstructionsType: Instructions> Encoder<InstructionsType> {
    fn new(function_signatures: BTreeMap<u64, FunctionSignature>) -> Encoder<InstructionsType> {
        Encoder {
            function_signatures,
            expression_counter: 0,
            ssa_tracker: SSATracker::default(),
            output: String::new(),
            interpreter: InstructionsType::default(),
        }
    }

    pub fn encode_context_init(&mut self) {
        let output = evm_context::init(&mut self.ssa_tracker);
        self.out(output);
    }

    pub fn encode(&mut self, block: &Block) {
        self.encode_context_init();
        self.encode_block(block);
    }

    /// Encodes the given function, potentially re-creating copies of all local variables
    /// if called multiple times.
    /// @returns the names of the function parameters and return variables.
    pub fn encode_function(&mut self, function: &FunctionDefinition) -> FunctionVariables {
        for param in &function.parameters {
            let var = self.ssa_tracker.introduce_variable(param);
            self.out(format!("(declare-const {} (_ BitVec 256))", var.name));
        }
        let parameters = self.ssa_tracker.to_smt_variables(&function.parameters);
        self.encode_variable_declaration(&VariableDeclaration {
            variables: function.returns.clone(),
            value: None,
        });
        self.encode_block(&function.body);
        let returns = self.ssa_tracker.to_smt_variables(&function.returns);
        FunctionVariables {
            parameters,
            returns,
        }
    }

    fn encode_variable_declaration(&mut self, var: &VariableDeclaration) {
        let encoded_values = match &var.value {
            Some(value) => self.encode_expression(value),
            None => {
                let zero = self.encode_literal(&Literal {
                    literal: String::from("0"),
                });
                vec![zero; var.variables.len()]
            }
        };
        for v in &var.variables {
            self.ssa_tracker.introduce_variable(v);
        }
        self.encode_assignment_inner(&var.variables, encoded_values)
    }

    fn encode_assignment(&mut self, assignment: &Assignment) {
        let values = self.encode_expression(&assignment.value);
        self.encode_assignment_inner(&assignment.variables, values);
    }

    fn encode_block(&mut self, block: &yul::Block) {
        block
            .statements
            .iter()
            .for_each(|st| self.encode_statement(st));
    }

    fn encode_function_def(&mut self, _fun: &yul::FunctionDefinition) {}

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
        let prev_ssa = self.ssa_tracker.copy_current_ssa();

        self.encode_block(&expr.body);

        let output = self.ssa_tracker.join_branches(
            format!(
                "(= {} #x0000000000000000000000000000000000000000000000000000000000000000)",
                cond[0].name
            ),
            prev_ssa,
        );
        self.out(output);
    }

    fn encode_for(&mut self, for_loop: &yul::ForLoop) {
        // TODO this does not support break/continue/leave

        let its = 10;

        self.encode_block(&for_loop.pre);

        for _i in 0..its {
            let cond = self.encode_expression(&for_loop.condition);
            assert!(cond.len() == 1);
            let prev_ssa = self.ssa_tracker.copy_current_ssa();

            self.encode_block(&for_loop.body);
            self.encode_block(&for_loop.post);

            let output = self.ssa_tracker.join_branches(
                format!(
                    "(= {} #x0000000000000000000000000000000000000000000000000000000000000000)",
                    cond[0].name
                ),
                prev_ssa,
            );
            self.out(output);
        }
    }

    fn encode_switch(&mut self, switch: &yul::Switch) {
        let discriminator = self.encode_expression(&switch.expression);
        assert!(discriminator.len() == 1);
        let pre_switch_ssa = self.ssa_tracker.copy_current_ssa();
        let mut post_switch_ssa = self.ssa_tracker.take_current_ssa();

        for Case { literal, body } in &switch.cases {
            // TODO default case is not yet implemented because
            // the ITE expression is complicated.
            assert!(*literal != None);
            self.ssa_tracker.set_current_ssa(pre_switch_ssa.clone());

            self.encode_block(body);

            let skip_condition = format!(
                "(not (= {} {}))",
                discriminator[0].name,
                self.encode_literal_value(literal.as_ref().unwrap()),
            );
            let output = self
                .ssa_tracker
                .join_branches(skip_condition, post_switch_ssa);
            self.out(output);
            post_switch_ssa = self.ssa_tracker.take_current_ssa();
        }

        self.ssa_tracker.set_current_ssa(post_switch_ssa);
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
        self.ssa_tracker.to_smt_variable(identifier)
    }

    fn encode_function_call(&mut self, call: &FunctionCall) -> Vec<SMTVariable> {
        let arguments = call
            .arguments
            .iter()
            .rev()
            .map(|arg| {
                let mut value = self.encode_expression(arg);
                assert_eq!(value.len(), 1);
                value.pop().unwrap()
            })
            .rev()
            .collect::<Vec<_>>();

        match call.function.id {
            IdentifierID::BuiltinReference => {
                let builtin = &InstructionsType::builtin(&call.function.name).unwrap();
                let return_vars: Vec<SMTVariable> = (0..builtin.returns)
                    .map(|_i| self.new_temporary_variable())
                    .collect();

                let result = self.interpreter.encode_builtin_call(
                    builtin,
                    arguments,
                    &return_vars,
                    &mut self.ssa_tracker,
                );
                self.out(result);
                return_vars
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

/// Helpers.
impl<T> Encoder<T> {
    fn encode_revert_unreachable(&mut self) {
        let output = evm_context::encode_revert_unreachable(&mut self.ssa_tracker);
        self.out(output);
    }

    fn encode_assignment_inner(&mut self, variables: &[Identifier], values: Vec<SMTVariable>) {
        assert_eq!(values.len(), variables.len());

        for (v, val) in variables.iter().zip(values.iter()) {
            let var = self.ssa_tracker.allocate_new_ssa_index(v);
            self.out(format!(
                "(define-const {} (_ BitVec 256) {})",
                var.name, val.name
            ));
        }
    }

    fn encode_literal_value(&self, literal: &Literal) -> String {
        if literal.literal.starts_with("0x") {
            format!(
                "#x{}{}",
                "0".repeat(2 + 64 - literal.literal.len()),
                &literal.literal[2..]
            )
        } else {
            // TODO support larger decimal constants.
            format!("#x{:064X}", &literal.literal.parse::<u128>().unwrap())
        }
    }

    fn new_temporary_variable(&mut self) -> SMTVariable {
        self.expression_counter += 1;
        SMTVariable {
            name: format!("_{}", self.expression_counter),
        }
    }

    fn out(&mut self, x: String) {
        self.output = format!("{}{}\n", self.output, x)
    }
}
