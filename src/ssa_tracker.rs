use crate::common::SMTVariable;
use std::collections::HashMap;
use std::default::Default;
use yultsur::yul::*;

pub struct SSATracker {
    /// Current SSA index for each variable
    current: HashMap<u64, u64>,
    /// Highest SSA index (used for next assignment) for each variable
    /// TODO "highest" and "names" could be shared by copies of SSATracker...
    highest: HashMap<u64, u64>,
    names: HashMap<u64, String>,
}

impl SSATracker {
    pub fn new() -> Self {
        SSATracker {
            current: Default::default(),
            highest: Default::default(),
            names: Default::default(),
        }
    }

    pub fn copy_current_ssa(&self) -> HashMap<u64, u64> {
        self.current.clone()
    }

    pub fn take_current_ssa(&mut self) -> HashMap<u64, u64> {
        std::mem::take(&mut self.current)
    }

    pub fn set_current_ssa(&mut self, current_ssa: HashMap<u64, u64>) {
        self.current = current_ssa;
    }

    /// This function is to be called after copy_current_ssa.
    /// The SSATracker is used on a branch and then joined again with
    /// the old (stored) ssa values.
    /// The condition should evaluate to "false" for the branch.
    #[must_use]
    pub fn join_branches(
        &mut self,
        skip_condition: String,
        // this is the stored list
        ssa_skipped: HashMap<u64, u64>,
    ) -> String {
        let ssa_branch = std::mem::replace(&mut self.current, ssa_skipped);
        // Now "self.current" are the skipped values - we just update them.

        ssa_branch
            .iter()
            .flat_map(|(key, value)| {
                let skipped_idx = self.current[key];
                if skipped_idx != *value {
                    let new_ssa = self.allocate_new_ssa_index_by_id(*key);
                    Some(format!(
                        "(define-const {} (_ BitVec 256) (ite {} {} {}))\n",
                        self.id_to_smt_variable(*key, new_ssa).name,
                        skip_condition,
                        self.id_to_smt_variable(*key, skipped_idx).name,
                        self.id_to_smt_variable(*key, *value).name,
                    ))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .join("")
    }

    pub fn allocate_new_ssa_index(&mut self, identifier: &Identifier) -> SMTVariable {
        let id = self.identifier_to_id(identifier);
        let index = self.allocate_new_ssa_index_by_id(id);
        self.id_to_smt_variable(id, index)
    }

    /// Creates the variable and allocates the initial SSA index.
    /// Does not generate any SMT code.
    pub fn introduce_variable(&mut self, variable: &Identifier) -> SMTVariable {
        if let IdentifierID::Declaration(id) = variable.id {
            self.names.insert(id, variable.name.clone());
            let ssa_idx = self.allocate_new_ssa_index_by_id(id);
            self.id_to_smt_variable(id, ssa_idx)
        } else {
            panic!();
        }
    }

    pub fn to_smt_variable(&self, identifier: &Identifier) -> SMTVariable {
        let var_id = self.identifier_to_id(identifier);
        self.id_to_smt_variable(var_id, self.current[&var_id])
    }

    pub fn to_smt_variables(&self, identifiers: &[Identifier]) -> Vec<SMTVariable> {
        identifiers
            .iter()
            .map(|i| self.to_smt_variable(i))
            .collect()
    }

    fn allocate_new_ssa_index_by_id(&mut self, var_id: u64) -> u64 {
        let ssa = *self
            .highest
            .entry(var_id)
            .and_modify(|c| *c += 1)
            .or_insert(0);
        self.current.insert(var_id, ssa);
        ssa
    }

    fn id_to_smt_variable(&self, id: u64, ssa_idx: u64) -> SMTVariable {
        SMTVariable {
            name: format!("{}_{}_{}", self.names[&id], id, ssa_idx),
        }
    }

    fn identifier_to_id(&self, identifier: &Identifier) -> u64 {
        match identifier.id {
            IdentifierID::Declaration(id) => id,
            IdentifierID::Reference(id) => id,
            _ => panic!(),
        }
    }
}
