use crate::evaluator::Evaluator;
use crate::execution_position::ExecutionPositionManager;
use crate::smt::{SMTExpr, SMTFormat, SMTSort, SMTStatement, SMTVariable};
use crate::ssa_tracker::SSATracker;
use crate::{evm_context, smt};

use num_traits::Num;
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
        path_conditions: &[SMTExpr],
    ) -> Vec<SMTStatement>;
}

#[derive(Default)]
pub struct Encoder<InstructionsType> {
    function_definitions: BTreeMap<u64, yul::FunctionDefinition>,
    expression_counter: u64,
    ssa_tracker: SSATracker,
    output: Vec<SMTStatement>,
    interpreter: InstructionsType,
    evaluator: Evaluator,
    loop_unroll: u64,
    path_conditions: Vec<SMTExpr>,
    execution_position: ExecutionPositionManager,
}

/// Data that is needed if you want to use multiple Encoder instances
/// for one SMT query.
#[derive(Default)]
pub struct EncoderSMTState {
    pub expression_counter: u64,
    pub ssa_tracker: SSATracker,
    pub evaluator: Evaluator,
    pub execution_position: ExecutionPositionManager,
}

impl<T: Instructions> From<EncoderSMTState> for Encoder<T> {
    fn from(state: EncoderSMTState) -> Self {
        Encoder::<T> {
            expression_counter: state.expression_counter,
            evaluator: state.evaluator,
            ssa_tracker: state.ssa_tracker,
            execution_position: state.execution_position,
            ..Default::default()
        }
    }
}

impl<T> From<Encoder<T>> for EncoderSMTState {
    fn from(encoder: Encoder<T>) -> Self {
        EncoderSMTState {
            expression_counter: encoder.expression_counter,
            ssa_tracker: encoder.ssa_tracker,
            evaluator: encoder.evaluator,
            execution_position: encoder.execution_position,
        }
    }
}

pub fn encode<T: Instructions>(ast: &Block, loop_unroll: u64) -> String {
    let mut encoder = Encoder::<T>::default();
    encoder.encode(ast, loop_unroll);
    encoder
        .output
        .iter()
        .map(|s| s.as_smt())
        .collect::<Vec<_>>()
        .join("\n")
}

pub fn encode_revert_reachable<T: Instructions>(
    ast: &Block,
    loop_unroll: u64,
    counterexamples: &[Expression],
) -> (String, Vec<String>) {
    let mut encoder = Encoder::<T>::default();
    encoder.encode(ast, loop_unroll);
    encoder.encode_revert_reachable();

    encode_with_counterexamples(&mut encoder, counterexamples)
}

pub fn encode_with_SMT_state<T: Instructions>(
    ast: &Block,
    loop_unroll: u64,
    smt_state: EncoderSMTState,
) -> (String, EncoderSMTState) {
    let mut encoder: Encoder<T> = smt_state.into();
    encoder.encode(ast, loop_unroll);
    let query = encoder
        .output
        .iter()
        .map(|s| s.as_smt())
        .collect::<Vec<_>>()
        .join("\n");
    (query, EncoderSMTState::from(encoder))
}

pub fn encode_solc_panic_reachable<T: Instructions>(
    ast: &Block,
    loop_unroll: u64,
    counterexamples: &[Expression],
) -> (String, Vec<String>, String, ExecutionPositionManager) {
    let mut encoder = Encoder::<T>::default();
    encoder.encode(ast, loop_unroll);
    encoder.encode_solc_panic_reachable();
    let revert_position = ExecutionPositionManager::smt_variable()
        .smt_var(&mut encoder.ssa_tracker)
        .as_smt();

    let (enc, cex) = encode_with_counterexamples(&mut encoder, counterexamples);
    (enc, cex, revert_position, encoder.execution_position)
}

fn encode_with_counterexamples<T: Instructions>(
    encoder: &mut Encoder<T>,
    counterexamples: &[Expression],
) -> (String, Vec<String>) {
    let encoded_counterexamples = counterexamples
        .iter()
        .map(|expr| encoder.encode_expression(expr).pop().unwrap().name)
        .collect::<Vec<_>>();
    (
        encoder
            .output
            .iter()
            .map(|s| s.as_smt())
            .collect::<Vec<_>>()
            .join("\n"),
        encoded_counterexamples,
    )
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
        let mut output = evm_context::init(&mut self.ssa_tracker);
        output.push(ExecutionPositionManager::init(&mut self.ssa_tracker));
        self.out_vec(output);
    }

    fn collect_function_definitions(&mut self, block: &Block) {
        let mut collector = FunctionDefinitionCollector::default();
        collector.visit_block(block);
        self.function_definitions = collector.function_definitions;
    }

    /// Encodes the given function, potentially re-creating copies of all local variables
    /// if called multiple times.
    /// @returns the names of the return variables.
    pub fn encode_function(
        &mut self,
        function: &FunctionDefinition,
        arguments: &[SMTVariable],
    ) -> Vec<SMTVariable> {
        assert_eq!(function.parameters.len(), arguments.len());
        for (param, arg) in function.parameters.iter().zip(arguments) {
            let var = self.ssa_tracker.introduce_variable(param);
            self.out(smt::define_const(
                var.clone(),
                smt::SMTExpr::from(arg.clone()),
            ));
            self.evaluator.define_from_variable(&var, arg);
        }

        self.encode_variable_declaration(&VariableDeclaration {
            variables: function.returns.clone(),
            value: None,
            location: None,
        });

        self.encode_block(&function.body);
        self.ssa_tracker.to_smt_variables(&function.returns)
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

    fn encode_statement(&mut self, st: &yul::Statement) {
        match st {
            yul::Statement::VariableDeclaration(var_decl) => {
                self.encode_variable_declaration(var_decl)
            }
            yul::Statement::Assignment(assignment) => self.encode_assignment(assignment),
            yul::Statement::Block(block) => self.encode_block(block),
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
        if self
            .evaluator
            .variable_known_equal(&cond[0], &"0".to_string())
        {
            return;
        }
        let prev_ssa = self.ssa_tracker.copy_current_ssa();
        let prev_eval = self.evaluator.copy_state();

        self.push_path_condition(smt::neq(cond[0].clone(), 0));
        self.encode_block(&expr.body);
        self.pop_path_condition();

        let output = self
            .ssa_tracker
            .join_branches(smt::eq(cond[0].clone(), 0), prev_ssa);
        self.evaluator.join_with_old_state(prev_eval);
        self.out_vec(output);
    }

    fn encode_for(&mut self, for_loop: &yul::ForLoop) {
        // TODO this does not support break/continue/leave

        self.encode_block(&for_loop.pre);

        for _i in 0..self.loop_unroll {
            let cond = self.encode_expression(&for_loop.condition);
            assert!(cond.len() == 1);
            let prev_ssa = self.ssa_tracker.copy_current_ssa();
            let prev_eval = self.evaluator.copy_state();
            // TODO the evaluator does not have path conditions - is that OK?

            self.push_path_condition(smt::neq(cond[0].clone(), 0));
            self.encode_block(&for_loop.body);
            self.encode_block(&for_loop.post);
            self.pop_path_condition();

            let output = self
                .ssa_tracker
                .join_branches(smt::eq(cond[0].clone(), 0), prev_ssa);
            self.evaluator.join_with_old_state(prev_eval);
            self.out_vec(output);
        }
    }

    fn encode_switch(&mut self, switch: &yul::Switch) {
        let discriminator = self.encode_expression(&switch.expression);
        assert!(discriminator.len() == 1);
        let pre_switch_ssa = self.ssa_tracker.copy_current_ssa();
        let mut post_switch_ssa = self.ssa_tracker.take_current_ssa();
        let prev_eval = self.evaluator.copy_state();

        for Case {
            literal,
            body,
            location: _,
        } in &switch.cases
        {
            let is_default = literal.is_none();
            // TODO this will always run the default case.
            // We should first go through all case labels and see if we only need to execute a single one.
            if !is_default
                && self
                    .evaluator
                    .variable_known_unequal(&discriminator[0], &literal.as_ref().unwrap().literal)
            {
                continue;
            }

            self.ssa_tracker.set_current_ssa(pre_switch_ssa.clone());

            let skip_condition = if is_default {
                smt::or_vec(
                    switch
                        .cases
                        .iter()
                        .filter(|case| case.literal.is_some())
                        .map(|case| {
                            smt::eq(
                                discriminator[0].clone(),
                                self.encode_literal_value(case.literal.as_ref().unwrap())
                                    .unwrap(),
                            )
                        })
                        .collect::<Vec<_>>(),
                )
            } else {
                smt::neq(
                    discriminator[0].clone(),
                    self.encode_literal_value(literal.as_ref().unwrap())
                        .unwrap(),
                )
            };

            self.push_path_condition(smt::not(skip_condition.clone()));
            self.encode_block(body);
            self.pop_path_condition();

            let output = self
                .ssa_tracker
                .join_branches(skip_condition, post_switch_ssa);
            self.out_vec(output);
            // TODO check if this is correct.
            self.evaluator.join_with_old_state(prev_eval.clone());
            post_switch_ssa = self.ssa_tracker.take_current_ssa();
            post_switch_ssa.retain(|key, _| pre_switch_ssa.contains_key(key));
        }
        // TODO we should actually reset thet state of the evaluator, because
        // we do not know in which branch we ended up

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
        let sort = SMTSort::BV(256);
        let var = self.new_temporary_variable(sort);
        self.evaluator.define_from_literal(&var, literal);
        if let Some(value) = self.encode_literal_value(literal) {
            self.out(smt::define_const(var.clone(), value));
        } else {
            self.out(smt::declare_const(var.clone()))
        }
        var
    }

    fn encode_identifier(&mut self, identifier: &Identifier) -> SMTVariable {
        self.ssa_tracker.to_smt_variable(identifier)
    }

    fn encode_function_call(&mut self, call: &FunctionCall) -> Vec<SMTVariable> {
        let arguments: Vec<SMTVariable> = call
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

        let record_location = match call.function.id {
            IdentifierID::Reference(_) => true,
            IdentifierID::BuiltinReference => call.function.name == "revert", // TODO more flexibility about which builtins to record.
            _ => false,
        };

        if record_location {
            self.execution_position.function_called(call);
            let record_pos = evm_context::assign_variable_if_executing_regularly(
                &mut self.ssa_tracker,
                &ExecutionPositionManager::smt_variable(),
                self.execution_position.position_id().into(),
            );
            self.out(record_pos);
        }

        let return_vars = match call.function.id {
            IdentifierID::BuiltinReference => {
                let builtin = &InstructionsType::builtin(&call.function.name).unwrap();
                let return_vars: Vec<SMTVariable> = (0..builtin.returns)
                    .map(|_i| self.new_temporary_variable(SMTSort::BV(256)))
                    .collect();

                // TODO call evaluator first or interpreter first?
                self.evaluator
                    .builtin_call(builtin, &arguments, &return_vars);
                if builtin.name == "call" {
                    // if let Some((ast, calldata)) = self.evaluator.is_call_to_knon_contract(arguments) {

                    //     // TODO
                    // }
                }
                let result = self.interpreter.encode_builtin_call(
                    builtin,
                    arguments,
                    &return_vars,
                    &mut self.ssa_tracker,
                    &self.path_conditions,
                );
                self.out_vec(result);
                return_vars
            }
            IdentifierID::Reference(id) => {
                let fun_def = self.function_definitions[&id].clone();
                self.encode_function(&fun_def, &arguments)
            }
            _ => panic!(
                "Unexpected reference in function call: {:?}",
                call.function.id
            ),
        };

        if record_location {
            self.execution_position.function_returned();
            let record_pos = evm_context::assign_variable_if_executing_regularly(
                &mut self.ssa_tracker,
                &ExecutionPositionManager::smt_variable(),
                self.execution_position.position_id().into(),
            );
            self.out(record_pos);
        }
        return_vars
    }
}

/// Helpers.
impl<T> Encoder<T> {
    fn encode_revert_reachable(&mut self) {
        let output = evm_context::encode_revert_reachable(&mut self.ssa_tracker);
        self.out(output);
    }

    fn encode_solc_panic_reachable(&mut self) {
        let output = evm_context::encode_solc_panic_reachable(&mut self.ssa_tracker);
        self.out(output);
    }

    fn encode_assignment_inner(&mut self, variables: &[Identifier], values: Vec<SMTVariable>) {
        assert_eq!(values.len(), variables.len());

        for (v, val) in variables.iter().zip(values.into_iter()) {
            let var = self.ssa_tracker.allocate_new_ssa_index(v);
            self.evaluator.define_from_variable(&var, &val);
            self.out(smt::define_const(var, val.into()));
        }
    }

    /// Returns the literal value encoded as an SMT expression.
    /// Might fail if the literal is a data object reference or something else that
    /// does not have a specific 256 bit value.
    fn encode_literal_value(&self, literal: &Literal) -> Option<SMTExpr> {
        (if let Some(hex) = literal.literal.strip_prefix("0x") {
            Some(num_bigint::BigUint::from_str_radix(hex, 16).unwrap())
        } else if let Some(string) = literal.literal.strip_prefix('\"') {
            assert!(string.len() >= 2 && string.ends_with('\"'));
            // This is usually only used for references to data objects,
            // so we do not encode it.
            None
        } else {
            Some(literal.literal.parse::<num_bigint::BigUint>().unwrap())
        })
        .map(smt::literal_32_bytes)
    }

    fn push_path_condition(&mut self, cond: SMTExpr) {
        self.path_conditions.push(cond);
    }

    fn pop_path_condition(&mut self) {
        self.path_conditions.pop().unwrap();
    }

    fn new_temporary_variable(&mut self, sort: SMTSort) -> SMTVariable {
        self.expression_counter += 1;
        SMTVariable::new(format!("_{}", self.expression_counter), sort)
    }

    fn out(&mut self, statement: SMTStatement) {
        self.output.push(statement);
    }

    fn out_vec(&mut self, statements: Vec<SMTStatement>) {
        self.output.extend(statements);
    }
}
