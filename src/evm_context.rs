use std::collections::BTreeMap;

use crate::ssa_tracker::SSATracker;
use yultsur::yul::*;

pub fn init(ssa: &mut SSATracker) -> String {
    let mut output = [revert_flag(), stop_flag()].into_iter().map(|identifier| {
        let var = ssa.introduce_variable(&as_declaration(identifier));
        format!(
            "(define-const {} (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)\n",
            var.name
        )
    }).collect::<Vec<_>>().join("");
    output.push_str(
        static_vars()
            .into_iter()
            .map(|(_name, identifier)| {
                let var = ssa.introduce_variable(&as_declaration(identifier));
                format!("(declare-const {} (_ BitVec 256))\n", var.name)
            })
            .collect::<Vec<_>>()
            .join("")
            .as_str(),
    );
    let address = ssa.to_smt_variable(&static_vars()["address"]).name;
    format!(
        "{}(assert (= ((_ extract 255 160) {address}) #x000000000000000000000000))\n",
        output,
    )
}

pub fn set_reverted(ssa: &mut SSATracker) -> String {
    assign_variable_if_executing_regularly(
        ssa,
        &revert_flag(),
        "#x0000000000000000000000000000000000000000000000000000000000000001",
    )
}

pub fn set_stopped(ssa: &mut SSATracker) -> String {
    assign_variable_if_executing_regularly(
        ssa,
        &stop_flag(),
        "#x0000000000000000000000000000000000000000000000000000000000000001",
    )
}

fn static_vars() -> BTreeMap<String, Identifier> {
    [
        "address",
        "origin",
        "caller",
        "callvalue",
        "calldatasize",
        "codesize",
        "gasprice",
        "coinbase",
        "timestamp",
        "number",
        "difficulty",
        "gaslimit",
        "chainid",
        "basefee",
    ]
    .iter()
    .enumerate()
    .map(|(i, name)| {
        (
            name.to_string(),
            identifier(format!("_{name}").as_str(), 1026 + i as u64),
        )
    })
    .collect()
}

pub fn address(ssa: &mut SSATracker) -> String {
    ssa.to_smt_variable(&static_vars()["address"]).name
}
pub fn origin(ssa: &mut SSATracker) -> String {
    ssa.to_smt_variable(&static_vars()["origin"]).name
}
pub fn caller(ssa: &mut SSATracker) -> String {
    ssa.to_smt_variable(&static_vars()["caller"]).name
}
pub fn callvalue(ssa: &mut SSATracker) -> String {
    ssa.to_smt_variable(&static_vars()["callvalue"]).name
}
pub fn calldatasize(ssa: &mut SSATracker) -> String {
    ssa.to_smt_variable(&static_vars()["calldatasize"]).name
}
pub fn codesize(ssa: &mut SSATracker) -> String {
    ssa.to_smt_variable(&static_vars()["codesize"]).name
}
pub fn gasprice(ssa: &mut SSATracker) -> String {
    ssa.to_smt_variable(&static_vars()["gasprice"]).name
}
pub fn coinbase(ssa: &mut SSATracker) -> String {
    ssa.to_smt_variable(&static_vars()["coinbase"]).name
}
pub fn timestamp(ssa: &mut SSATracker) -> String {
    ssa.to_smt_variable(&static_vars()["timestamp"]).name
}
pub fn number(ssa: &mut SSATracker) -> String {
    ssa.to_smt_variable(&static_vars()["number"]).name
}
pub fn difficulty(ssa: &mut SSATracker) -> String {
    ssa.to_smt_variable(&static_vars()["difficulty"]).name
}
pub fn gaslimit(ssa: &mut SSATracker) -> String {
    ssa.to_smt_variable(&static_vars()["gaslimit"]).name
}
pub fn chainid(ssa: &mut SSATracker) -> String {
    ssa.to_smt_variable(&static_vars()["chainid"]).name
}
pub fn basefee(ssa: &mut SSATracker) -> String {
    ssa.to_smt_variable(&static_vars()["basefee"]).name
}

pub fn encode_revert_unreachable(ssa: &mut SSATracker) -> String {
    format!(
        "(assert (not (= {} #x0000000000000000000000000000000000000000000000000000000000000000)))",
        ssa.to_smt_variable(&revert_flag()).name
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
        ssa.to_smt_variable(&revert_flag()).name,
        ssa.to_smt_variable(&stop_flag()).name
    )
}

fn revert_flag() -> Identifier {
    identifier("_revert", 1024)
}

fn stop_flag() -> Identifier {
    identifier("_stop", 1025)
}

fn identifier(name: &str, id: u64) -> Identifier {
    Identifier {
        id: IdentifierID::Reference(id),
        name: name.to_string(),
    }
}

fn as_declaration(identifier: Identifier) -> Identifier {
    if let IdentifierID::Reference(id) = identifier.id {
        Identifier {
            id: IdentifierID::Declaration(id),
            name: identifier.name,
        }
    } else {
        panic!()
    }
}
