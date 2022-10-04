use crate::encoder::Instructions;
use crate::evm_context;
use crate::evm_context::MemoryRange;
use crate::smt::{self, SMTExpr, SMTOp, SMTStatement, SMTVariable};
use crate::ssa_tracker::SSATracker;
use yultsur::dialect::{Builtin, Dialect, EVMDialect};

#[derive(Default)]
pub struct EVMInstructions;

impl Dialect for EVMInstructions {
    fn builtin(name: &str) -> Option<Builtin> {
        EVMDialect::builtin(name)
    }
}

impl Instructions for EVMInstructions {
    fn encode_builtin_call(
        &self,
        builtin: &Builtin,
        arguments: Vec<SMTVariable>,
        return_vars: &[SMTVariable],
        ssa: &mut SSATracker,
        _path_conditions: &[SMTExpr],
    ) -> Vec<SMTStatement> {
        let single_return = |value: SMTExpr| {
            assert_eq!(return_vars.len(), 1);
            vec![smt::define_const(
                return_vars.first().unwrap().clone(),
                value,
            )]
        };
        let direct = |smt_op: SMTOp| {
            let smt_encoding = SMTExpr {
                op: smt_op.clone(),
                args: arguments.clone().into_iter().map(|v| v.into()).collect(),
            };
            single_return(match is_bool_function(smt_op) {
                true => wrap_boolean(smt_encoding),
                false => smt_encoding,
            })
        };

        let mut it = arguments.clone().into_iter();
        let arg_0 = it.next();
        let arg_1 = it.next();

        match builtin.name {
            "stop" => vec![evm_context::set_stopped(ssa)],
            "add" => direct(SMTOp::BvAdd),
            "sub" => direct(SMTOp::BvSub),
            "mul" => direct(SMTOp::BvMul),
            "div" => direct(SMTOp::BvUDiv), // TODO check that the parameter oder is correct
            "sdiv" => direct(SMTOp::BvSDiv),
            "mod" => direct(SMTOp::BvURem),
            "smod" => direct(SMTOp::BvSMod), // TODO check if it is bvsmod or bvsrem (they differ in sign)
            "not" => single_return(smt::bvnot(arg_0.unwrap())),
            "lt" => direct(SMTOp::BvULt),
            "gt" => direct(SMTOp::BvUGt),
            "slt" => direct(SMTOp::BvSLt),
            "sgt" => direct(SMTOp::BvSGt),
            "eq" => direct(SMTOp::Eq),
            "iszero" => single_return(wrap_boolean(smt::eq_zero(arg_0.unwrap()))),
            "and" => direct(SMTOp::BvAnd),
            "or" => direct(SMTOp::BvOr),
            "xor" => direct(SMTOp::BvXor),
            "byte" => {
                let byte_index: SMTExpr = arg_0.unwrap().into();
                let shift_amount = smt::bvsub(248, smt::bvmul(8, byte_index.clone()));
                single_return(smt::ite(
                    smt::bvugt(byte_index, 31),
                    0,
                    smt::bvand(0xff, smt::bvlshr(arg_1.unwrap(), shift_amount)),
                ))
            }
            "shl" => single_return(smt::bvshl(arg_1.unwrap(), arg_0.unwrap())),
            "shr" => single_return(smt::bvlshr(arg_1.unwrap(), arg_0.unwrap())),
            "sar" => single_return(smt::bvashr(arg_1.unwrap(), arg_0.unwrap())),
            "addmod" => panic!("Builtin {} not implemented", builtin.name), // TODO // TODO
            "mulmod" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "signextend" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "keccak256" => single_return(evm_context::keccak256(
                MemoryRange {
                    offset: arg_0.unwrap().into(),
                    length: arg_1.unwrap().into(),
                },
                ssa,
            )),
            "address" => single_return(evm_context::address(ssa).into()),
            "balance" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "origin" => single_return(evm_context::origin(ssa).into()),
            "caller" => single_return(evm_context::caller(ssa).into()),
            "callvalue" => single_return(evm_context::callvalue(ssa).into()),
            "calldataload" => single_return(evm_context::calldataload(arg_0.unwrap().into(), ssa)),
            "calldatasize" => single_return(evm_context::calldatasize(ssa).into()),
            "calldatacopy" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "codesize" => single_return(evm_context::codesize(ssa).into()),
            "codecopy" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "gasprice" => single_return(evm_context::gasprice(ssa).into()),
            "extcodesize" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "extcodecopy" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "returndatasize" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "returndatacopy" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "extcodehash" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "blockhash" => panic!("Builtin {} not implemented", builtin.name),   // TODO
            "coinbase" => single_return(evm_context::coinbase(ssa).into()),
            "timestamp" => single_return(evm_context::timestamp(ssa).into()),
            "number" => single_return(evm_context::number(ssa).into()),
            "difficulty" => single_return(evm_context::difficulty(ssa).into()),
            "gaslimit" => single_return(evm_context::gaslimit(ssa).into()),
            "chainid" => single_return(evm_context::chainid(ssa).into()),
            "selfbalance" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "basefee" => single_return(evm_context::basefee(ssa).into()),
            "pop" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "mload" => single_return(evm_context::mload(arg_0.unwrap().into(), ssa)),
            "mstore" => vec![evm_context::mstore(
                arg_0.unwrap().into(),
                arg_1.unwrap().into(),
                ssa,
            )],
            "mstore8" => vec![evm_context::mstore8(
                arg_0.unwrap().into(),
                arg_1.unwrap().into(),
                ssa,
            )],
            "sload" => single_return(evm_context::sload(arg_0.unwrap().into(), ssa)),
            "sstore" => vec![evm_context::sstore(
                arg_0.unwrap().into(),
                arg_1.unwrap().into(),
                ssa,
            )],
            "msize" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "gas" => panic!("Builtin {} not implemented", builtin.name),   // TODO
            "log0" => panic!("Builtin {} not implemented", builtin.name),  // TODO
            "log1" => panic!("Builtin {} not implemented", builtin.name),  // TODO
            "log2" => panic!("Builtin {} not implemented", builtin.name),  // TODO
            "log3" => panic!("Builtin {} not implemented", builtin.name),  // TODO
            "log4" => panic!("Builtin {} not implemented", builtin.name),  // TODO
            "create" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "call" => panic!("Builtin {} not implemented", builtin.name),  // TODO
            "callcode" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "return" => vec![evm_context::set_stopped(ssa)],               // TODO store returndata
            "delegatecall" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "staticcall" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "create2" =>
            /* TODO handle potential storage changes */
            {
                panic!("Builtin {} not implemented", builtin.name)
            } // TODO
            "revert" => vec![evm_context::set_reverted(ssa)],
            "invalid" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "selfdestruct" => panic!("Builtin {} not implemented", builtin.name), // TODO

            "memoryguard" => single_return(arg_0.unwrap().into()),
            _ => panic!("Invalid builtin {}", builtin.name),
        }
    }
}

fn is_bool_function(op: SMTOp) -> bool {
    matches!(
        op,
        SMTOp::BvULt | SMTOp::BvUGt | SMTOp::BvSLt | SMTOp::BvSGt | SMTOp::Eq
    )
}

fn wrap_boolean(boolean_expression: SMTExpr) -> SMTExpr {
    smt::ite(boolean_expression, 1, 0)
}
