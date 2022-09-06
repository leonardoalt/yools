use crate::encoder::{EVMContext, SMTVariable};
use yultsur::dialect::Builtin;

pub fn encode_builtin_call(
    builtin: &Builtin,
    arguments: Vec<SMTVariable>,
    return_vars: &[SMTVariable],
    context: &mut impl EVMContext,
) -> String {
    let returns = builtin.returns;
    if let Some(smt_encoding) = side_effect_free_builtin(&builtin.name, &arguments) {
        assert_eq!(returns, 1);
        return format!(
            "(define-const {} (_ BitVec 256) {})",
            &return_vars.first().unwrap().name,
            smt_encoding
        );
    } else if let Some(smt_encoding) = blockchain_builtin(&builtin.name, &arguments, context) {
        // TODO return variables?
        return smt_encoding;
    }
    if builtin.name.as_str() == "revert" {
        context.set_reverted();
    }
    String::new()
}

fn is_bool_function(name: &str) -> bool {
    matches!(name, "bvult" | "bvugt" | "bvslt" | "bvsgt" | "=")
}

fn wrap_boolean(boolean_expression: String) -> String {
    format!("(ite {boolean_expression} #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000)")
}

// TODO
// exp, byte, addmod, mulmod, signextend, keccak256
// address, balance, origin, caller, callvalue, ...
// pop

fn side_effect_free_builtin(name: &str, arguments: &[SMTVariable]) -> Option<String> {
    match name {
        "add" => Some("bvadd"),
        "sub" => Some("bvsub"),
        "mul" => Some("bvmul"),
        "div" => Some("bvudiv"), // TODO check that the parameter oder is correct
        "sdiv" => Some("bvsdiv"),
        "mod" => Some("bvurem"),
        "smod" => Some("bvsmod"), // TODO check if it is bvsmod or bvsrem (they differ in sign)
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
    .map(|smt_name| {
        let result = format!("({} {} {})", smt_name, arguments[0].name, arguments[1].name);
        match is_bool_function(smt_name) {
            true => wrap_boolean(result),
            false => result,
        }
    })
    .or_else(|| match name {
        "iszero" => Some(wrap_boolean(format!(
            "(= {} #x0000000000000000000000000000000000000000000000000000000000000000)",
            arguments[0].name
        ))),
        "shl" => Some(format!(
            "(bvshl {} {})",
            arguments[1].name, arguments[0].name
        )),
        "shr" => Some(format!(
            "(bvlshr {} {})",
            arguments[1].name, arguments[0].name
        )),
        "sar" => Some(format!(
            "(bvashr {} {})",
            arguments[1].name, arguments[0].name
        )),
        _ => None,
    })
}

fn blockchain_builtin(
    name: &str,
    _arguments: &[SMTVariable],
    context: &mut impl EVMContext,
) -> Option<String> {
    match name {
        "stop" => {
            context.set_stopped();
            Some(String::new())
        }
        "revert" => {
            context.set_reverted();
            Some(String::new())
        }
        _ => None,
    }
}
