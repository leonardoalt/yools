use yultsur::yul::{FunctionCall, Identifier, IdentifierID, SourceLocation};

use crate::smt::{self, SMTExpr};
use crate::ssa_tracker::SSATracker;
use crate::variables::SystemVariable;

/**
 * Stores the current call stack encoded in a single number that can be used
 * during the SMT encoding.
 *
 * Can be extended in the future with other information like loop iterations.
 */
#[derive(Default)]
pub struct ExecutionPositionManager {
    positions: Vec<ExecutionPosition>,
}

pub struct PositionID(pub usize);

impl From<PositionID> for SMTExpr {
    fn from(pos: PositionID) -> Self {
        (pos.0 as u64).into()
    }
}

struct ExecutionPosition {
    call_stack: Vec<Option<SourceLocation>>,
}

impl ExecutionPositionManager {
    pub fn init(ssa_tracker: &mut SSATracker) -> smt::SMTStatement {
        Self::smt_variable().generate_definition(ssa_tracker)
    }

    /// @returns the SystemVariable that encodes the position.
    pub fn smt_variable() -> SystemVariable {
        SystemVariable {
            identifier: Identifier {
                id: IdentifierID::Reference(8128),
                name: "_exe_pos".to_string(),
                location: None,
            },
            domain: vec![],
            codomain: smt::bv(256),
            default_value: Some(0.into()),
        }
    }

    pub fn function_called(&mut self, fun: &FunctionCall) {
        self.append_position(ExecutionPosition {
            call_stack: [self.current_call_stack(), vec![fun.location.clone()]].concat(),
        });
    }

    pub fn function_returned(&mut self) {
        let mut call_stack = self.current_call_stack();
        call_stack.pop().unwrap();
        self.append_position(ExecutionPosition { call_stack })
    }

    /// Returns the current position ID that can later
    /// be translated into e.g. a call stack.
    pub fn position_id(&self) -> PositionID {
        PositionID(self.positions.len() - 1)
    }

    pub fn call_stack_at_position(&self, pos: PositionID) -> &Vec<Option<SourceLocation>> {
        &self.positions[pos.0].call_stack
    }

    fn append_position(&mut self, pos: ExecutionPosition) {
        self.positions.push(pos)
    }
    fn current_call_stack(&self) -> Vec<Option<SourceLocation>> {
        match self.positions.iter().last() {
            Some(p) => p.call_stack.clone(),
            None => vec![],
        }
    }
}
