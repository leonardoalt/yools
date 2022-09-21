use std::collections::BTreeMap;
use std::fmt::Write;

use crate::smt;
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
    let memory_var =
        ssa.introduce_variable_of_type(&as_declaration(memory()), memory_type().to_string());
    // TODO memory is zero initially.
    let _ = writeln!(
        output,
        "(declare-const {} {})",
        memory_var.name,
        memory_type()
    );

    let _ = writeln!(
        output,
        "(declare-fun {} ((_ BitVec 256)) (_ BitVec 8))",
        calldata().name
    );

    let _ = writeln!(
        output,
        "(declare-fun {} ((_ BitVec 256)) (_ BitVec 256))",
        keccak256_32()
    );

    let _ = writeln!(
        output,
        "(declare-fun {} ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))",
        keccak256_64()
    );

    let _ = writeln!(
        output,
        "(declare-fun {} ({} (_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))",
        keccak256_generic(),
        memory_type(),
    );

    // TODO assert that calldata[i] = 0 for i >= calldatasize
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
            identifier(format!("_{name}").as_str(), 2048 + i as u64),
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

pub fn calldataload(index: &String, _ssa: &mut SSATracker) -> String {
    let arguments = (0..32)
        .map(|i| format!("({} (bvadd {} #x{:064X}))", calldata().name, index, i))
        .collect::<Vec<_>>()
        .join(" ");
    format!("(concat {})", arguments)
}

pub fn mstore(index: &String, value: &String, ssa: &mut SSATracker) -> String {
    let before = ssa.to_smt_variable(&memory());
    let after = ssa.allocate_new_ssa_index(&memory());

    let stored = (0..32).fold(before.name, |acc, i| {
        let sub_index = format!("(bvadd {} #x{:064X})", index, i);
        let byte_value = format!(
            "((_ extract {} {}) {})",
            255 - i * 8,
            256 - (i + 1) * 8,
            value
        );
        format!("(store {} {} {})", acc, sub_index, byte_value,)
    });
    format!("(define-const {} {} {})", after.name, memory_type(), stored)
}

pub fn mload(index: &String, ssa: &mut SSATracker) -> String {
    let mem = ssa.to_smt_variable(&memory());

    let arguments = (0..32)
        .map(|i| format!("(select {} (bvadd {} #x{:064X}))", mem.name, index, i))
        .collect::<Vec<_>>()
        .join(" ");
    format!("(concat {})", arguments)
}

pub fn keccak256(offset: &String, length: &String, ssa: &mut SSATracker) -> String {
    let offset_0 = mload(offset, ssa);
    let offset_32 = mload(&format!("(bvadd {} #x{:064X})", offset, 0x20), ssa);
    smt::ite(
        &smt::eq(length, &0x20),
        &format!("({} {})", keccak256_32(), offset_0),
        &smt::ite(
            &smt::eq(length, &0x40),
            &format!("({} {} {})", keccak256_64(), offset_0, offset_32),
            &format!(
                "({} {} {} {})",
                keccak256_generic(),
                ssa.to_smt_variable(&memory()).name,
                offset,
                length
            ),
        ),
    )
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

fn calldata() -> Identifier {
    identifier("_calldata", 1026)
}

fn memory() -> Identifier {
    identifier("_memory", 1027)
}
fn memory_type() -> &'static str {
    "(Array (_ BitVec 256) (_ BitVec 8))"
}

fn keccak256_32() -> String {
    "_keccak256_32".to_string()
}

fn keccak256_64() -> String {
    "_keccak256_64".to_string()
}

fn keccak256_generic() -> String {
    "_keccak256".to_string()
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
