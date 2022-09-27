use crate::smt;
use crate::ssa_tracker::SSATracker;
use yultsur::yul::*;

pub fn init(ssa: &mut SSATracker) -> String {
    let output = ContextVariables::all()
        .iter()
        .map(|var| {
            let smt_var = ssa.introduce_variable_of_type(
                &as_declaration(var.identifier.clone()),
                var.type_.clone(),
            );
            if let Some(default) = &var.default_value {
                format!(
                    "(define-fun {} {} {})\n",
                    smt_var.name, var.full_type, default
                )
            } else {
                format!("(declare-fun {} {})\n", smt_var.name, var.full_type)
            }
        })
        .collect::<Vec<_>>()
        .join("");
    // TODO memory is zero initially.

    // TODO assert that calldata[i] = 0 for i >= calldatasize
    let address = context().address.smt_var(ssa);
    format!(
        "{}(assert (= ((_ extract 255 160) {address}) #x000000000000000000000000))\n",
        output,
    )
}

struct ContextVariable {
    identifier: Identifier,
    /// The full type "(input) (output)"
    full_type: String,
    /// Only the output type.
    type_: String,
    default_value: Option<String>,
}

impl ContextVariable {
    pub fn smt_var(&self, ssa: &mut SSATracker) -> String {
        ssa.to_smt_variable(&self.identifier).name
    }
}

macro_rules! context_variables {
    ($($var:ident: $type:expr; $default_value:expr),*) => {
        // Declare the struct.
        struct ContextVariables {
            $($var: ContextVariable),*
        }
        // Define the default value.
        impl Default for ContextVariables {
            fn default() -> ContextVariables {
                let mut i: u64 = 2047;
                let mut id = || { i += 1; i };
                ContextVariables {
                    $($var: ContextVariable{
                        identifier: identifier(&format!("_{}", stringify!($var)), id()),
                        full_type: match $type {
                            Type::Default => "() (_ BitVec 256)".to_string(),
                            Type::Constant(t) => format!("() {t}"),
                            Type::Function(in_, out) => format!("{in_} {out}"),
                        },
                        type_: match $type {
                            Type::Default => "(_ BitVec 256)",
                            Type::Constant(t) => t,
                            Type::Function(_, out) => out,
                        }.to_string(),
                        default_value: $default_value,
                    }),*
                }
            }
        }
        // Return an iterator through the variables.
        impl ContextVariables {
            fn all() -> Vec<ContextVariable> {
                vec![
                    $(
                        ContextVariables::default().$var
                    ),*
                ]
            }
        }
    };
}

enum Type {
    Default,
    Constant(&'static str),
    Function(&'static str, &'static str),
}

context_variables! {
    address: Type::Default; None,
    basefee: Type::Default; None,
    calldatasize: Type::Default; None,
    caller: Type::Default; None,
    callvalue: Type::Default; None,
    chainid: Type::Default; None,
    codesize: Type::Default; None,
    coinbase: Type::Default; None,
    difficulty: Type::Default; None,
    gaslimit: Type::Default; None,
    gasprice: Type::Default; None,
    number: Type::Default; None,
    origin: Type::Default; None,
    timestamp: Type::Default; None,
    memory: Type::Constant("(Array (_ BitVec 256) (_ BitVec 8))"); None,
    storage: Type::Constant("(Array (_ BitVec 256) (_ BitVec 256))"); None,
    calldata: Type::Function("((_ BitVec 256))", "(_ BitVec 8)"); None,
    keccak256_32: Type::Function("((_ BitVec 256))", "(_ BitVec 256)"); None,
    keccak256_64: Type::Function("((_ BitVec 256) (_ BitVec 256))", "(_ BitVec 256)"); None,
    keccak256: Type::Function("((Array (_ BitVec 256) (_ BitVec 8)) (_ BitVec 256) (_ BitVec 256))", "(_ BitVec 256)"); None,
    revert_flag: Type::Default; Some("#x0000000000000000000000000000000000000000000000000000000000000000".to_string()),
    stop_flag: Type::Default; Some("#x0000000000000000000000000000000000000000000000000000000000000000".to_string())
}

// TODO can we make this a global variable?
fn context() -> ContextVariables {
    ContextVariables::default()
}

pub fn set_reverted(ssa: &mut SSATracker) -> String {
    assign_variable_if_executing_regularly(
        ssa,
        &context().revert_flag.identifier,
        "#x0000000000000000000000000000000000000000000000000000000000000001",
    )
}

pub fn set_stopped(ssa: &mut SSATracker) -> String {
    assign_variable_if_executing_regularly(
        ssa,
        &context().stop_flag.identifier,
        "#x0000000000000000000000000000000000000000000000000000000000000001",
    )
}

pub fn address(ssa: &mut SSATracker) -> String {
    context().address.smt_var(ssa)
}
pub fn origin(ssa: &mut SSATracker) -> String {
    context().origin.smt_var(ssa)
}
pub fn caller(ssa: &mut SSATracker) -> String {
    context().caller.smt_var(ssa)
}
pub fn callvalue(ssa: &mut SSATracker) -> String {
    context().callvalue.smt_var(ssa)
}
pub fn calldatasize(ssa: &mut SSATracker) -> String {
    context().calldatasize.smt_var(ssa)
}
pub fn codesize(ssa: &mut SSATracker) -> String {
    context().codesize.smt_var(ssa)
}
pub fn gasprice(ssa: &mut SSATracker) -> String {
    context().gasprice.smt_var(ssa)
}
pub fn coinbase(ssa: &mut SSATracker) -> String {
    context().coinbase.smt_var(ssa)
}
pub fn timestamp(ssa: &mut SSATracker) -> String {
    context().timestamp.smt_var(ssa)
}
pub fn number(ssa: &mut SSATracker) -> String {
    context().number.smt_var(ssa)
}
pub fn difficulty(ssa: &mut SSATracker) -> String {
    context().difficulty.smt_var(ssa)
}
pub fn gaslimit(ssa: &mut SSATracker) -> String {
    context().gaslimit.smt_var(ssa)
}
pub fn chainid(ssa: &mut SSATracker) -> String {
    context().chainid.smt_var(ssa)
}
pub fn basefee(ssa: &mut SSATracker) -> String {
    context().basefee.smt_var(ssa)
}

pub fn calldataload(index: &String, ssa: &mut SSATracker) -> String {
    let calldata = context().calldata.smt_var(ssa);
    let arguments = (0..32)
        .map(|i| format!("({} (bvadd {} #x{:064X}))", calldata, index, i))
        .collect::<Vec<_>>()
        .join(" ");
    format!("(concat {})", arguments)
}

pub fn mstore(index: &String, value: &String, ssa: &mut SSATracker) -> String {
    let before = context().memory.smt_var(ssa);
    let after = ssa.allocate_new_ssa_index(&context().memory.identifier);

    let stored = (0..32).fold(before, |acc, i| {
        let sub_index = format!("(bvadd {} #x{:064X})", index, i);
        let byte_value = format!(
            "((_ extract {} {}) {})",
            255 - i * 8,
            256 - (i + 1) * 8,
            value
        );
        format!("(store {} {} {})", acc, sub_index, byte_value,)
    });
    format!(
        "(define-const {} {} {})",
        after.name,
        context().memory.type_,
        stored
    )
}

pub fn mload(index: &String, ssa: &mut SSATracker) -> String {
    let mem = context().memory.smt_var(ssa);

    let arguments = (0..32)
        .map(|i| format!("(select {} (bvadd {} #x{:064X}))", mem, index, i))
        .collect::<Vec<_>>()
        .join(" ");
    format!("(concat {})", arguments)
}

pub fn keccak256(offset: &String, length: &String, ssa: &mut SSATracker) -> String {
    let offset_0 = mload(offset, ssa);
    let offset_32 = mload(&format!("(bvadd {} #x{:064X})", offset, 0x20), ssa);
    smt::ite(
        &smt::eq(length, &0x20),
        &format!("({} {})", context().keccak256_32.smt_var(ssa), offset_0),
        &smt::ite(
            &smt::eq(length, &0x40),
            &format!(
                "({} {} {})",
                context().keccak256_64.smt_var(ssa),
                offset_0,
                offset_32
            ),
            &format!(
                "({} {} {} {})",
                context().keccak256.smt_var(ssa),
                context().memory.smt_var(ssa),
                offset,
                length
            ),
        ),
    )
}

pub fn sstore(index: &String, value: &String, ssa: &mut SSATracker) -> String {
    let before = context().storage.smt_var(ssa);
    let after = ssa.allocate_new_ssa_index(&context().storage.identifier);

    let stored = format!("(store {} {} {})", before, index, value);
    format!(
        "(define-const {} {} {})",
        after.name,
        context().storage.type_,
        stored
    )
}

pub fn sload(index: &String, ssa: &mut SSATracker) -> String {
    format!("(select {} {})", context().storage.smt_var(ssa), index)
}

pub fn encode_revert_unreachable(ssa: &mut SSATracker) -> String {
    format!(
        "(assert (not (= {} #x0000000000000000000000000000000000000000000000000000000000000000)))",
        context().revert_flag.smt_var(ssa)
    )
}

/// Assigns to the variable if we neither stopped nor reverted. Otherwise, the variable keeps
/// its value. Increases the SSA index in any case.
fn assign_variable_if_executing_regularly(
    ssa: &mut SSATracker,
    variable: &Identifier,
    new_value: &str,
) -> String {
    let old_value = ssa.to_smt_variable(variable);
    let update_condition = executing_regularly(ssa);
    let new_var = ssa.allocate_new_ssa_index(variable);
    format!(
        "(define-const {} (_ BitVec 256) (ite {} {} {}))",
        new_var.name, update_condition, new_value, old_value.name
    )
}

pub fn executing_regularly(ssa: &mut SSATracker) -> String {
    format!(
        "(and (= {} #x0000000000000000000000000000000000000000000000000000000000000000) (= {} #x0000000000000000000000000000000000000000000000000000000000000000))",
        context().revert_flag.smt_var(ssa),
        context().stop_flag.smt_var(ssa),
    )
}

fn identifier(name: &str, id: u64) -> Identifier {
    Identifier {
        id: IdentifierID::Reference(id),
        name: name.to_string(),
        location: None,
    }
}

fn as_declaration(identifier: Identifier) -> Identifier {
    if let IdentifierID::Reference(id) = identifier.id {
        Identifier {
            id: IdentifierID::Declaration(id),
            name: identifier.name,
            location: None,
        }
    } else {
        panic!()
    }
}
