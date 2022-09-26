use crate::evm_context;
use crate::smt::{self, SMTExpression, SMTFormat, SMTLiteral, SMTSort, SMTStatement, SMTVariable};
use crate::ssa_tracker::SSATracker;

use yultsur::dialect::{Builtin, Dialect};
use yultsur::visitor::ASTVisitor;
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

#[derive(Default)]
pub struct Encoder<InstructionsType> {
    function_definitions: BTreeMap<u64, yul::FunctionDefinition>,
    expression_counter: u64,
    ssa_tracker: SSATracker,
    output: String,
    interpreter: InstructionsType,
    loop_unroll: u64,
}

pub fn encode<T: Instructions>(ast: &Block, loop_unroll: u64) -> String {
    let mut encoder = Encoder::<T>::default();
    encoder.encode(ast, loop_unroll);
    encoder.output
}

pub fn encode_revert_unreachable<T: Instructions>(ast: &Block, loop_unroll: u64) -> String {
    let mut encoder = Encoder::<T>::default();
    encoder.encode(ast, loop_unroll);
    encoder.encode_revert_unreachable();
    encoder.output
}

#[derive(Debug, PartialEq, Eq)]
pub struct FunctionVariables {
    /// smtlib2 names of the initial values of the function parameters
    pub parameters: Vec<SMTVariable>,
    /// smtlib2 names of the final values of the function return variables
    pub returns: Vec<SMTVariable>,
}

#[derive(Default)]
struct FunctionDefinitionCollector {
    function_definitions: BTreeMap<u64, yul::FunctionDefinition>,
}

impl ASTVisitor for FunctionDefinitionCollector {
    fn visit_function_definition(&mut self, fun_def: &FunctionDefinition) {
        match fun_def.name.id {
            IdentifierID::Declaration(id) => {
                self.function_definitions.insert(id, fun_def.clone());
            }
            _ => panic!(),
        }
    }
}

impl<InstructionsType: Instructions> Encoder<InstructionsType> {
    pub fn encode(&mut self, block: &Block, loop_unroll: u64) {
        self.loop_unroll = loop_unroll;
        self.encode_context_init();
        self.collect_function_definitions(block);
        self.encode_block(block);
    }

    fn encode_context_init(&mut self) {
        let output = evm_context::init(&mut self.ssa_tracker);
        self.out(output);
    }

    fn collect_function_definitions(&mut self, block: &Block) {
        let mut collector = FunctionDefinitionCollector::default();
        collector.visit_block(block);
        self.function_definitions = collector.function_definitions;
    }

    /// Encodes the given function, potentially re-creating copies of all local variables
    /// if called multiple times.
    /// @returns the names of the function parameters and return variables.
    pub fn encode_function(&mut self, function: &FunctionDefinition) -> FunctionVariables {
        for param in &function.parameters {
            let var = self.ssa_tracker.introduce_variable(param);
            self.out(SMTStatement::DeclareConst(
                var.name.as_smt(),
                SMTSort::bitvec(256),
            ))
        }
        let parameters = self.ssa_tracker.to_smt_variables(&function.parameters);
        self.encode_variable_declaration(&VariableDeclaration {
            variables: function.returns.clone(),
            value: None,
            location: None,
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
                    location: None,
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

        let output = self
            .ssa_tracker
            .join_branches(smt::eq(&cond[0], &0), prev_ssa);
        self.out(output);
    }

    fn encode_for(&mut self, for_loop: &yul::ForLoop) {
        // TODO this does not support break/continue/leave

        self.encode_block(&for_loop.pre);

        for _i in 0..self.loop_unroll {
            let cond = self.encode_expression(&for_loop.condition);
            assert!(cond.len() == 1);
            let prev_ssa = self.ssa_tracker.copy_current_ssa();

            self.encode_block(&for_loop.body);
            self.encode_block(&for_loop.post);

            let output = self
                .ssa_tracker
                .join_branches(smt::eq(&cond[0], &0), prev_ssa);
            self.out(output);
        }
    }

    fn encode_switch(&mut self, switch: &yul::Switch) {
        let discriminator = self.encode_expression(&switch.expression);
        assert!(discriminator.len() == 1);
        let pre_switch_ssa = self.ssa_tracker.copy_current_ssa();
        let mut post_switch_ssa = self.ssa_tracker.take_current_ssa();

        for Case {
            literal,
            body,
            location: _,
        } in &switch.cases
        {
            // TODO default case is not yet implemented because
            // the ITE expression is complicated.
            assert!(literal.is_some());
            self.ssa_tracker.set_current_ssa(pre_switch_ssa.clone());

            self.encode_block(body);

            let skip_condition = SMTExpression::Not(Box::new(SMTExpression::Eq(
                Box::new(discriminator[0].name.clone()),
                self.encode_literal_value(literal.as_ref().unwrap()),
            )));
            let output = self
                .ssa_tracker
                .join_branches(skip_condition, post_switch_ssa);
            self.out(output);
            post_switch_ssa = self.ssa_tracker.take_current_ssa();
            post_switch_ssa.retain(|key, _| pre_switch_ssa.contains_key(key));
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
        self.out(SMTStatement::DefineConst(
            var.name.as_smt(),
            SMTSort::bitvec(256),
            self.encode_literal_value(literal).as_smt(),
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
            .collect();

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
                let fun_def = self.function_definitions[&id].clone();
                let function_vars = self.encode_function(&fun_def);
                assert!(arguments.len() == function_vars.parameters.len());
                arguments
                    .iter()
                    .zip(function_vars.parameters)
                    .for_each(|(arg, param)| {
                        self.out(SMTStatement::Assert(Box::new(SMTExpression::Eq(
                            Box::new(arg.name.clone()),
                            Box::new(param.name),
                        ))))
                    });
                function_vars.returns
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
            self.out(SMTStatement::DefineConst(
                var.name.as_smt(),
                SMTSort::bitvec(256),
                val.name.as_smt(),
            ));
        }
    }

    fn encode_literal_value(&self, literal: &Literal) -> Box<SMTLiteral> {
        Box::new(SMTLiteral::Hex(if literal.literal.starts_with("0x") {
            format!("{:0>64}", &literal.literal[2..])
        } else {
            format!(
                "{:064X}",
                literal.literal.parse::<num_bigint::BigUint>().unwrap()
            )
        }))
    }

    fn new_temporary_variable(&mut self) -> SMTVariable {
        self.expression_counter += 1;
        SMTVariable {
            name: format!("_{}", self.expression_counter),
        }
    }

    fn out(&mut self, x: impl SMTFormat) {
        self.output = format!("{}{}\n", self.output, x.as_smt())
    }
}
