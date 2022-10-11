use yultsur::yul::{Identifier, IdentifierID};

use crate::smt::{self, SMTExpr, SMTSort, SMTStatement, SMTVariable};
use crate::ssa_tracker::SSATracker;

pub struct SystemVariable {
    pub identifier: Identifier,
    pub domain: Vec<SMTSort>,
    pub codomain: SMTSort,
    pub default_value: Option<SMTExpr>,
}

impl SystemVariable {
    pub fn smt_var(&self, ssa: &mut SSATracker) -> SMTVariable {
        ssa.to_smt_variable(&self.identifier)
    }

    #[must_use]
    pub fn generate_definition(&self, ssa: &mut SSATracker) -> SMTStatement {
        let smt_var = ssa.introduce_variable_of_type(
            &as_declaration(self.identifier.clone()),
            self.codomain.clone(),
        );
        if let Some(default) = &self.default_value {
            smt::define_fun(smt_var, self.domain.clone(), default.clone())
        } else {
            smt::declare_fun(smt_var, self.domain.clone())
        }
    }

    /// Declares a new SSA index for the given variable and sets it to
    /// "unknown" if the condition is false and to the old value if it is true.
    #[must_use]
    pub fn havoc_unless(&self, ssa: &mut SSATracker, condition: SMTExpr) -> Vec<SMTStatement> {
        let old = self.smt_var(ssa);
        let new = ssa.allocate_new_ssa_index(&self.identifier);
        vec![
            smt::declare_const(new.clone()),
            smt::assert(smt::implies(condition, smt::eq(old, new))),
        ]
    }

    /// Assigns to the variable if the given condition is true. Otherwise, the variable keeps
    /// its value. Increases the SSA index in any case.
    #[must_use]
    pub fn assign_if(
        &self,
        ssa: &mut SSATracker,
        condition: SMTExpr,
        new_value: SMTExpr,
    ) -> SMTStatement {
        let old_value = self.smt_var(ssa);
        let new_var = ssa.allocate_new_ssa_index(&self.identifier);
        smt::define_const(new_var, smt::ite(condition, new_value, old_value))
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
