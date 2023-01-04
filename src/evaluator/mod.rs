use std::fmt;
use std::fmt::Display;

use num_bigint::BigUint;

pub mod engine;
pub mod simplifier;

pub use engine::Evaluator;

/// Symbolic or concrete value
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// A fully known actual number.
    Concrete(BigUint),
    /// The value of a variable.
    Var(String),
    /// A (pure) opcode applied to arguments.
    Op(&'static str, Vec<Value>),
    /// A reference to a Yul sub-object or data item.
    DataRef(String),
    /// The address of a contract created from the
    /// Yul sub-object of the given name and a sequence number.
    KnownContractAddress(String, u64),
}

impl Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Concrete(v) => write!(f, "0x{v:x}"),
            Value::Var(name) => write!(f, "${name}"),
            Value::DataRef(name) => write!(f, "dataref(\"{name}\")"),
            Value::Op(name, args) => write!(
                f,
                "{name}({})",
                args.iter()
                    .map(|a| format!("{a}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Value::KnownContractAddress(name, index) => write!(f, "address<{name},{index}>"),
        }
    }
}
