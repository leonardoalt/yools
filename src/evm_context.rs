use crate::ssa_tracker::SSATracker;
use yultsur::yul::*;

pub fn init(ssa: &mut SSATracker) -> String {
    let var = ssa.introduce_variable(&as_declaration(revert_flag()));
    format!(
        "(define-const {} (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)",
        var.name
    )
}

pub fn set_reverted(ssa: &mut SSATracker) -> String {
    let var = ssa.allocate_new_ssa_index(&revert_flag());
    format!(
        "(define-const {} (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000001)",
        var.name
    )
}

pub fn set_stopped(_ssa: &mut SSATracker) -> String {
    // TOODO
    String::new()
}

pub fn encode_revert_unreachable(ssa: &mut SSATracker) -> String {
    format!(
        "(assert (not (= {} #x0000000000000000000000000000000000000000000000000000000000000000)))",
        ssa.to_smt_variable(&revert_flag()).name
    )
}

fn revert_flag() -> Identifier {
    identifier("_revert", 1024)
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
