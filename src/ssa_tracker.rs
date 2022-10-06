use crate::smt::{self, SMTExpr, SMTSort, SMTStatement, SMTVariable};
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
    types: HashMap<u64, SMTSort>,
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
        skip_condition: SMTExpr,
        // this is the stored list
        ssa_skipped: BTreeMap<u64, u64>,
    ) -> Vec<SMTStatement> {
        let ssa_branch = std::mem::replace(&mut self.current, ssa_skipped);
        // Now "self.current" are the skipped values - we just update them.

        ssa_branch
            .iter()
            .flat_map(|(key, value)| {
                if let Some(&skipped_idx) = self.current.get(key) {
                    if skipped_idx != *value {
                        let new_ssa = self.allocate_new_ssa_index_by_id(*key);
                        Some(smt::define_const(
                            self.id_to_smt_variable(*key, new_ssa),
                            smt::ite(
                                skip_condition.clone(),
                                self.id_to_smt_variable(*key, skipped_idx),
                                self.id_to_smt_variable(*key, *value),
                            ),
                        ))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
    }

    /// Declares a new SSA index for the given variable and sets it to
    /// "unknown" if the condition is false and to the old value if it is true.
    #[must_use]
    pub fn havoc_unless(&mut self, variable: &Identifier, condition: SMTExpr) -> Vec<SMTStatement> {
        let old = self.to_smt_variable(variable);
        let new = self.allocate_new_ssa_index(variable);
        vec![
            smt::declare_const(new.clone()),
            smt::assert(smt::implies(condition, smt::eq(old, new))),
        ]
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
        type_: SMTSort,
    ) -> SMTVariable {
        self.types.insert(self.identifier_to_id(variable), type_);
        self.introduce_variable(variable)
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

    fn type_of_id(&self, id: u64) -> SMTSort {
        self.types.get(&id).unwrap_or(&SMTSort::BV(256)).clone()
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
            sort: self.type_of_id(id),
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
