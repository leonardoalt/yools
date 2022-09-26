use crate::encoder::Instructions;
use crate::evm_context;
use crate::smt::SMTVariable;
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
    ) -> String {
        let single_return = |value: String| {
            assert_eq!(return_vars.len(), 1);
            format!(
                "(define-const {} (_ BitVec 256) {})",
                &return_vars.first().unwrap().name,
                value
            )
        };
        let direct = |smt_name: &str| {
            let smt_encoding =
                format!("({} {} {})", smt_name, arguments[0].name, arguments[1].name);
            single_return(match is_bool_function(smt_name) {
                true => wrap_boolean(smt_encoding),
                false => smt_encoding,
            })
        };

        match builtin.name.as_str() {
            "stop" => evm_context::set_stopped(ssa),
            "add" => direct("bvadd"),
            "sub" => direct("bvsub"),
            "mul" => direct("bvmul"),
            "div" => direct("bvudiv"), // TODO check that the parameter oder is correct
            "sdiv" => direct("bvsdiv"),
            "mod" => direct("bvurem"),
            "smod" => direct("bvsmod"), // TODO check if it is bvsmod or bvsrem (they differ in sign)
            "not" => single_return(format!("(bvnot {})", arguments[0].name)),
            "lt" => direct("bvult"),
            "gt" => direct("bvugt"),
            "slt" => direct("bvslt"),
            "sgt" => direct("bvsgt"),
            "eq" => direct("="),
            "iszero" => single_return(wrap_boolean(format!(
                "(= {} #x0000000000000000000000000000000000000000000000000000000000000000)",
                arguments[0].name
            ))),
            "and" => direct("bvand"),
            "or" => direct("bvor"),
            "xor" => direct("bvxor"),
            "byte" => {
                let byte_index = &arguments[0].name;
                let input = &arguments[1].name;
                let shift_amount =
                    format!("(bvsub #x{:064x} (bvmul #x{:064x} {byte_index}))", 248, 8);
                single_return(format!(
                    "(ite (bvugt {byte_index} #x{:064x}) #x{:064x} (bvand #x{:064x} (bvlshr {input} {shift_amount})))",
                    31,
                    0,
                    0xff
                ))
            }
            "shl" => single_return(format!(
                "(bvshl {} {})",
                arguments[1].name, arguments[0].name
            )),
            "shr" => single_return(format!(
                "(bvlshr {} {})",
                arguments[1].name, arguments[0].name
            )),
            "sar" => single_return(format!(
                "(bvashr {} {})",
                arguments[1].name, arguments[0].name
            )),
            "addmod" => panic!("Builtin {} not implemented", builtin.name), // TODO // TODO
            "mulmod" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "signextend" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "keccak256" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "address" => single_return(evm_context::address(ssa)),
            "balance" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "origin" => single_return(evm_context::origin(ssa)),
            "caller" => single_return(evm_context::caller(ssa)),
            "callvalue" => single_return(evm_context::callvalue(ssa)),
            "calldataload" => single_return(evm_context::calldataload(&arguments[0].name, ssa)),
            "calldatasize" => single_return(evm_context::calldatasize(ssa)),
            "calldatacopy" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "codesize" => single_return(evm_context::codesize(ssa)),
            "codecopy" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "gasprice" => single_return(evm_context::gasprice(ssa)),
            "extcodesize" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "extcodecopy" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "returndatasize" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "returndatacopy" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "extcodehash" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "blockhash" => panic!("Builtin {} not implemented", builtin.name),   // TODO
            "coinbase" => single_return(evm_context::coinbase(ssa)),
            "timestamp" => single_return(evm_context::timestamp(ssa)),
            "number" => single_return(evm_context::number(ssa)),
            "difficulty" => single_return(evm_context::difficulty(ssa)),
            "gaslimit" => single_return(evm_context::gaslimit(ssa)),
            "chainid" => single_return(evm_context::chainid(ssa)),
            "selfbalance" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "basefee" => single_return(evm_context::basefee(ssa)),
            "pop" => String::new(),
            "mload" => single_return(evm_context::mload(&arguments[0].name, ssa)),
            "mstore" => evm_context::mstore(&arguments[0].name, &arguments[1].name, ssa),
            "mstore8" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "sload" => panic!("Builtin {} not implemented", builtin.name),   // TODO
            "sstore" => panic!("Builtin {} not implemented", builtin.name),  // TODO
            "msize" => panic!("Builtin {} not implemented", builtin.name),   // TODO
            "gas" => panic!("Builtin {} not implemented", builtin.name),     // TODO
            "log0" => panic!("Builtin {} not implemented", builtin.name),    // TODO
            "log1" => panic!("Builtin {} not implemented", builtin.name),    // TODO
            "log2" => panic!("Builtin {} not implemented", builtin.name),    // TODO
            "log3" => panic!("Builtin {} not implemented", builtin.name),    // TODO
            "log4" => panic!("Builtin {} not implemented", builtin.name),    // TODO
            "create" => panic!("Builtin {} not implemented", builtin.name),  // TODO
            "call" => panic!("Builtin {} not implemented", builtin.name),    // TODO
            "callcode" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "return" => evm_context::set_stopped(ssa), // TODO store returndata
            "delegatecall" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "staticcall" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "create2" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "revert" => evm_context::set_reverted(ssa),
            "invalid" => panic!("Builtin {} not implemented", builtin.name), // TODO
            "selfdestruct" => panic!("Builtin {} not implemented", builtin.name), // TODO

            "memoryguard" => single_return(arguments[0].name.to_string()),
            _ => panic!("Invalid builtin {}", builtin.name),
        }
    }
}

fn is_bool_function(name: &str) -> bool {
    matches!(name, "bvult" | "bvugt" | "bvslt" | "bvsgt" | "=")
}

fn wrap_boolean(boolean_expression: String) -> String {
    format!("(ite {boolean_expression} #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000)")
}
