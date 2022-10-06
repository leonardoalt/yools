use crate::smt::{self, SMTExpr, SMTSort, SMTStatement, SMTVariable};
use crate::ssa_tracker::SSATracker;
use yultsur::yul::*;

pub fn init(ssa: &mut SSATracker) -> Vec<SMTStatement> {
    let mut output = ContextVariables::all()
        .into_iter()
        .map(|var| {
            let smt_var = ssa.introduce_variable_of_type(
                &as_declaration(var.identifier.clone()),
                var.codomain.clone(),
            );
            if let Some(default) = &var.default_value {
                smt::define_fun(smt_var, var.domain, default.clone())
            } else {
                smt::declare_fun(smt_var, var.domain)
            }
        })
        .collect::<Vec<_>>();

    let address = context().address.smt_var(ssa);
    output.push(smt::assert(smt::eq(
        smt::extract(255, 160, address),
        smt::literal_12_bytes(0),
    )));

    output.push(smt::assert(smt::bvule(calldatasize(ssa), u64::MAX)));

    output
}

struct ContextVariable {
    identifier: Identifier,
    domain: Vec<SMTSort>,
    codomain: SMTSort,
    default_value: Option<SMTExpr>,
}

impl ContextVariable {
    pub fn smt_var(&self, ssa: &mut SSATracker) -> SMTVariable {
        ssa.to_smt_variable(&self.identifier)
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
                        domain: match $type {
                            Type::Default => vec![],
                            Type::Constant(_) => vec![],
                            Type::Function(in_types, _) => in_types
                        },
                        codomain: match $type {
                            Type::Default => smt::bv(256),
                            Type::Constant(t) => t,
                            Type::Function(_, out) => out,
                        },
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
    Constant(SMTSort),
    Function(Vec<SMTSort>, SMTSort),
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
    memory: Type::Constant(smt::array(smt::bv(256), smt::bv(8))); Some(smt::as_const(smt::array(smt::bv(256), smt::bv(8)), smt::literal_1_byte(0))),
    storage: Type::Constant(smt::array(smt::bv(256), smt::bv(256))); None,
    calldata: Type::Function(vec![smt::bv(256)], smt::bv(8)); None,
    keccak256_32: Type::Function(vec![smt::bv(256)], smt::bv(256)); None,
    keccak256_64: Type::Function(vec![smt::bv(256), smt::bv(256)], smt::bv(256)); None,
    keccak256: Type::Function(vec![smt::array(smt::bv(256), smt::bv(8)), smt::bv(256), smt::bv(256)], smt::bv(256)); None,
    revert_flag: Type::Default; Some(0.into()),
    stop_flag: Type::Default; Some(0.into())
}

// TODO can we make this a global variable?
fn context() -> ContextVariables {
    ContextVariables::default()
}

pub struct MemoryRange {
    pub offset: SMTExpr,
    pub length: SMTExpr,
}

pub fn set_reverted(ssa: &mut SSATracker) -> SMTStatement {
    assign_variable_if_executing_regularly(ssa, &context().revert_flag.identifier, 1.into())
}

pub fn set_stopped(ssa: &mut SSATracker) -> SMTStatement {
    assign_variable_if_executing_regularly(ssa, &context().stop_flag.identifier, 1.into())
}

pub fn address(ssa: &mut SSATracker) -> SMTVariable {
    context().address.smt_var(ssa)
}
pub fn origin(ssa: &mut SSATracker) -> SMTVariable {
    context().origin.smt_var(ssa)
}
pub fn caller(ssa: &mut SSATracker) -> SMTVariable {
    context().caller.smt_var(ssa)
}
pub fn callvalue(ssa: &mut SSATracker) -> SMTVariable {
    context().callvalue.smt_var(ssa)
}
pub fn calldatasize(ssa: &mut SSATracker) -> SMTVariable {
    context().calldatasize.smt_var(ssa)
}
pub fn codesize(ssa: &mut SSATracker) -> SMTVariable {
    context().codesize.smt_var(ssa)
}
pub fn gasprice(ssa: &mut SSATracker) -> SMTVariable {
    context().gasprice.smt_var(ssa)
}
pub fn coinbase(ssa: &mut SSATracker) -> SMTVariable {
    context().coinbase.smt_var(ssa)
}
pub fn timestamp(ssa: &mut SSATracker) -> SMTVariable {
    context().timestamp.smt_var(ssa)
}
pub fn number(ssa: &mut SSATracker) -> SMTVariable {
    context().number.smt_var(ssa)
}
pub fn difficulty(ssa: &mut SSATracker) -> SMTVariable {
    context().difficulty.smt_var(ssa)
}
pub fn gaslimit(ssa: &mut SSATracker) -> SMTVariable {
    context().gaslimit.smt_var(ssa)
}
pub fn chainid(ssa: &mut SSATracker) -> SMTVariable {
    context().chainid.smt_var(ssa)
}
pub fn basefee(ssa: &mut SSATracker) -> SMTVariable {
    context().basefee.smt_var(ssa)
}

pub fn calldataload(index: SMTExpr, ssa: &mut SSATracker) -> SMTExpr {
    let calldata = context().calldata.smt_var(ssa);
    let arguments = (0..32)
        .map(|i| {
            // TODO this could benefit from let expressions.
            // We are repeating the expression that computes the index.
            let sub_index = smt::bvadd(index.clone(), i);
            smt::ite(
                smt::bvult(sub_index.clone(), calldatasize(ssa)),
                smt::uf(calldata.clone(), vec![sub_index]),
                smt::literal_1_byte(0),
            )
        })
        .collect::<Vec<_>>();
    smt::concat(arguments)
}

pub fn mstore(index: SMTExpr, value: SMTExpr, ssa: &mut SSATracker) -> SMTStatement {
    let before = context().memory.smt_var(ssa);
    let after = ssa.allocate_new_ssa_index(&context().memory.identifier);

    let stored = (0..32).fold(before.into(), |acc, i| {
        let sub_index = smt::bvadd(index.clone(), i);
        let byte_value = smt::extract(255 - i * 8, 256 - (i + 1) * 8, value.clone());
        smt::store(acc, sub_index, byte_value)
    });
    smt::define_const(after, stored)
}

pub fn mstore8(index: SMTExpr, value: SMTExpr, ssa: &mut SSATracker) -> SMTStatement {
    let before = context().memory.smt_var(ssa);
    let after = ssa.allocate_new_ssa_index(&context().memory.identifier);

    smt::define_const(after, smt::store(before, index, smt::extract(7, 0, value)))
}

pub fn mload(index: SMTExpr, ssa: &mut SSATracker) -> SMTExpr {
    let mem = context().memory.smt_var(ssa);

    let arguments = (0..32)
        .map(|i| smt::select(mem.clone(), smt::bvadd(index.clone(), i)))
        .collect::<Vec<_>>();
    smt::concat(arguments)
}

pub fn keccak256(input: MemoryRange, ssa: &mut SSATracker) -> SMTExpr {
    let offset_0 = mload(input.offset.clone(), ssa);
    let offset_32 = mload(smt::bvadd(input.offset.clone(), 0x20), ssa);
    smt::ite(
        smt::eq(input.length.clone(), 0x20),
        smt::uf(context().keccak256_32.smt_var(ssa), vec![offset_0.clone()]),
        smt::ite(
            smt::eq(input.length.clone(), 0x40),
            smt::uf(
                context().keccak256_64.smt_var(ssa),
                vec![offset_0, offset_32],
            ),
            smt::uf(
                context().keccak256.smt_var(ssa),
                vec![
                    context().memory.smt_var(ssa).into(),
                    input.offset,
                    input.length,
                ],
            ),
        ),
    )
}

pub fn sstore(index: SMTExpr, value: SMTExpr, ssa: &mut SSATracker) -> SMTStatement {
    let before = context().storage.smt_var(ssa);
    let after = ssa.allocate_new_ssa_index(&context().storage.identifier);

    let stored = smt::store(before, index, value);
    smt::define_const(after, stored)
}

pub fn sload(index: SMTExpr, ssa: &mut SSATracker) -> SMTExpr {
    smt::select(context().storage.smt_var(ssa), index)
}

pub fn encode_revert_unreachable(ssa: &mut SSATracker) -> SMTStatement {
    smt::assert(smt::neq(context().revert_flag.smt_var(ssa), 0))
}

/// Assigns to the variable if we neither stopped nor reverted. Otherwise, the variable keeps
/// its value. Increases the SSA index in any case.
fn assign_variable_if_executing_regularly(
    ssa: &mut SSATracker,
    variable: &Identifier,
    new_value: SMTExpr,
) -> SMTStatement {
    let old_value = ssa.to_smt_variable(variable);
    let update_condition = executing_regularly(ssa);
    let new_var = ssa.allocate_new_ssa_index(variable);
    smt::define_const(new_var, smt::ite(update_condition, new_value, old_value))
}

pub fn executing_regularly(ssa: &mut SSATracker) -> SMTExpr {
    smt::and(
        smt::eq(context().revert_flag.smt_var(ssa), 0),
        smt::eq(context().stop_flag.smt_var(ssa), 0),
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
