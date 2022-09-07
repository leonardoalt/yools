use crate::encoder::{EVMContext, SMTVariable};
use yultsur::dialect::Builtin;

pub fn encode_builtin_call(
    builtin: &Builtin,
    arguments: Vec<SMTVariable>,
    return_vars: &[SMTVariable],
    context: &mut impl EVMContext,
) -> String {
    let direct = |smt_name: &str| {
        let smt_encoding = format!("({} {} {})", smt_name, arguments[0].name, arguments[1].name);
        assert_eq!(return_vars.len(), 1);
        format!(
            "(define-const {} (_ BitVec 256) {})",
            &return_vars.first().unwrap().name,
            match is_bool_function(smt_name) {
                true => wrap_boolean(smt_encoding),
                false => smt_encoding,
            }
        )
    };

    match builtin.name.as_str() {
        "stop" => {
            context.set_stopped();
            String::new()
        }
        "add" => direct("bvadd"),
        "sub" => direct("bvsub"),
        "mul" => direct("bvmul"),
        "div" => direct("bvudiv"), // TODO check that the parameter oder is correct
        "sdiv" => direct("bvsdiv"),
        "mod" => direct("bvurem"),
        "smod" => direct("bvsmod"), // TODO check if it is bvsmod or bvsrem (they differ in sign)
        "not" => direct("bvnot"),
        "lt" => direct("bvult"),
        "gt" => direct("bvugt"),
        "slt" => direct("bvslt"),
        "sgt" => direct("bvsgt"),
        "eq" => direct("="),
        "iszero" => wrap_boolean(format!(
            "(= {} #x0000000000000000000000000000000000000000000000000000000000000000)",
            arguments[0].name
        )),
        "and" => direct("bvand"),
        "or" => direct("bvor"),
        "xor" => direct("bvxor"),
        "byte" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "shl" => format!("(bvshl {} {})", arguments[1].name, arguments[0].name),
        "shr" => format!("(bvlshr {} {})", arguments[1].name, arguments[0].name),
        "sar" => format!("(bvashr {} {})", arguments[1].name, arguments[0].name),
        "addmod" => panic!("Builtin {} not implemented", builtin.name), // TODO // TODO
        "mulmod" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "signextend" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "keccak256" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "address" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "balance" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "origin" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "caller" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "callvalue" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "calldataload" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "calldatasize" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "calldatacopy" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "codesize" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "codecopy" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "gasprice" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "extcodesize" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "extcodecopy" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "returndatasize" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "returndatacopy" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "extcodehash" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "blockhash" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "coinbase" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "timestamp" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "number" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "difficulty" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "gaslimit" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "chainid" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "selfbalance" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "basefee" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "pop" => panic!("Builtin {} not implemented", builtin.name),    // TODO
        "mload" => panic!("Builtin {} not implemented", builtin.name),  // TODO
        "mstore" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "mstore8" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "sload" => panic!("Builtin {} not implemented", builtin.name),  // TODO
        "sstore" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "msize" => panic!("Builtin {} not implemented", builtin.name),  // TODO
        "gas" => panic!("Builtin {} not implemented", builtin.name),    // TODO
        "log0" => panic!("Builtin {} not implemented", builtin.name),   // TODO
        "log1" => panic!("Builtin {} not implemented", builtin.name),   // TODO
        "log2" => panic!("Builtin {} not implemented", builtin.name),   // TODO
        "log3" => panic!("Builtin {} not implemented", builtin.name),   // TODO
        "log4" => panic!("Builtin {} not implemented", builtin.name),   // TODO
        "create" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "call" => panic!("Builtin {} not implemented", builtin.name),   // TODO
        "callcode" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "return" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "delegatecall" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "staticcall" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "create2" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "revert" => {
            context.set_reverted();
            String::new()
        }
        "invalid" => panic!("Builtin {} not implemented", builtin.name), // TODO
        "selfdestruct" => panic!("Builtin {} not implemented", builtin.name), // TODO
        _ => panic!("Invalid builtin {}", builtin.name),
    }
}

fn is_bool_function(name: &str) -> bool {
    matches!(name, "bvult" | "bvugt" | "bvslt" | "bvsgt" | "=")
}

fn wrap_boolean(boolean_expression: String) -> String {
    format!("(ite {boolean_expression} #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000)")
}
