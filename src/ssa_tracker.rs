use crate::smt::{SMTFormat, SMTVariable};
use std::collections::{BTreeMap, HashMap};
use std::default::Default;
use yultsur::yul::*;

#[derive(Default)]
pub struct SSATracker {
    /// Current SSA index for each variable
    current: BTreeMap<u64, u64>,
    /// Highest SSA index (used for next assignment) for each variable
    /// TODO "highest" and "names" could be shared by copies of SSATracker...
    highest: BTreeMap<u64, u64>,
    names: BTreeMap<u64, String>,
    /// Types of variables that are NOT 256 bit bitvectors.
    types: HashMap<u64, String>,
}

impl SSATracker {
    pub fn copy_current_ssa(&self) -> BTreeMap<u64, u64> {
        self.current.clone()
    }

    pub fn take_current_ssa(&mut self) -> BTreeMap<u64, u64> {
        std::mem::take(&mut self.current)
    }

    pub fn set_current_ssa(&mut self, current_ssa: BTreeMap<u64, u64>) {
        self.current = current_ssa;
    }

    /// This function is to be called after copy_current_ssa.
    /// The SSATracker is used on a branch and then joined again with
    /// the old (stored) ssa values.
    /// The condition should evaluate to "false" for the branch.
    #[must_use]
    pub fn join_branches(
        &mut self,
        skip_condition: impl SMTFormat,
        // this is the stored list
        ssa_skipped: BTreeMap<u64, u64>,
    ) -> String {
        let ssa_branch = std::mem::replace(&mut self.current, ssa_skipped);
        // Now "self.current" are the skipped values - we just update them.

        ssa_branch
            .iter()
            .flat_map(|(key, value)| {
                if let Some(&skipped_idx) = self.current.get(key) {
                    if skipped_idx != *value {
                        let new_ssa = self.allocate_new_ssa_index_by_id(*key);
                        Some(format!(
                            "(define-const {} {} (ite {} {} {}))\n",
                            self.id_to_smt_variable(*key, new_ssa).name,
                            self.type_of_id(*key),
                            skip_condition.as_smt(),
                            self.id_to_smt_variable(*key, skipped_idx).name,
                            self.id_to_smt_variable(*key, *value).name,
                        ))
                    } else {
                        None
                    }
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

    pub fn introduce_variable_of_type(
        &mut self,
        variable: &Identifier,
        type_: String,
    ) -> SMTVariable {
        let var = self.introduce_variable(variable);
        self.types.insert(self.identifier_to_id(variable), type_);
        var
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

    fn type_of_id(&self, id: u64) -> String {
        self.types
            .get(&id)
            .unwrap_or(&"(_ BitVec 256)".to_string())
            .clone()
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
