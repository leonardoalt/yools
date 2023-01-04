use std::collections::HashMap;

use num_bigint::BigUint;
use num_traits::{Num, ToPrimitive};
use yultsur::{dialect::Builtin, yul::Literal};

use crate::smt::SMTVariable;

use super::simplifier::simplify;
use super::Value;

#[derive(Default)]
pub struct Evaluator {
    calldata: Option<Vec<u8>>,
    ssa_values: HashMap<String, Value>,
    storage: HashMap<BigUint, Value>,
    memory: HashMap<BigUint, ValueByte>,
    memory_slices: HashMap<BigUint, Value>,
    unknown_memory_is_zero: bool,
    stopped: bool,
}

#[derive(Clone)]
pub struct EvaluatorState {
    storage: HashMap<BigUint, Value>,
    memory: HashMap<BigUint, ValueByte>,
    memory_slices: HashMap<BigUint, Value>,
    unknown_memory_is_zero: bool,
    stopped: bool,
}

#[derive(PartialEq, Clone)]
struct ValueByte {
    data: Value,
    /// Byte of the data, 0 is most significant byte.
    byte: u32,
}

// TODO
// As soon as we handle side-effecty things, we might have to include
// "executing regularly":
// sstore(0, 1)
// stop()
// sload(0)
//
// Also, storage needs to take branches into account.
// if x { sstore(0, 1) }
// let t := sload(0)
//
// If storage is not changed in a branch, its ssa variable is not updated.
// If all storage writes are to compile-time constant variables,
// then the Evaluator can deal with the branch joins.
// Which means we have to have a mechanism to craete a snapshot of the state (like the SSATracker does)
// and then combine snapshots.
//
// Because of packed storage, the values we store should ideally be byte-wise.
// For now, the following could be OK:
// It's one of the following:
//  - unknown
//  - a symbolic value in the lower 20 bytes (the rest of the bytes are unknown)
//  - a concrete value

impl Evaluator {
    /// Reset all data whose lifetime is tied to a transaction.
    /// Keeps storage but resets memory.
    /// TODO: Change this interface to "push new call" or something.
    /// TODO should also set the current address.
    pub fn new_transaction(&mut self, calldata: Option<Vec<u8>>) {
        self.calldata = calldata;
        self.memory.clear();
        self.memory_slices.clear();
        self.unknown_memory_is_zero = true;
        self.stopped = false;
    }

    /// Returns a copy of the state that can later be joined with.
    pub fn copy_state(&self) -> EvaluatorState {
        EvaluatorState {
            storage: self.storage.clone(),
            memory: self.memory.clone(),
            memory_slices: self.memory_slices.clone(),
            unknown_memory_is_zero: self.unknown_memory_is_zero,
            stopped: self.stopped,
        }
    }
    /// Joins the state with the given old state.
    pub fn join_with_old_state(&mut self, old: EvaluatorState) {
        println!(
            "===> Join: old st: {}, new st: {}",
            self.storage
                .get(&BigUint::from(0u32))
                .unwrap_or(&Value::Var("???".to_string())),
            old.storage
                .get(&BigUint::from(0u32))
                .unwrap_or(&Value::Var("???".to_string())),
        );
        if self.stopped {
            self.storage = old.storage;
            self.memory = old.memory;
            self.memory_slices = old.memory_slices;
            self.unknown_memory_is_zero = old.unknown_memory_is_zero;
            self.stopped = old.stopped;
        } else {
            assert!(!old.stopped);
            self.storage.retain(|k, v| old.storage.get(k) == Some(v));
            self.memory.retain(|k, v| old.memory.get(k) == Some(v));
            self.memory_slices
                .retain(|k, v| old.memory_slices.get(k) == Some(v));
            if self.unknown_memory_is_zero {
                assert!(old.unknown_memory_is_zero);
            }
        }
    }
    /// Returns true if the evaluator can determine that the variable is equal
    /// to the given literal value with the previously set restrictions.
    pub fn variable_known_equal(&self, var: &SMTVariable, value: &String) -> bool {
        println!("Asking if for equal {value}: ");
        if let Some(v) = self.ssa_values.get(&var.name) {
            println!("   - {v}");
        }
        if let Some(Value::Concrete(v)) = self.ssa_values.get(&var.name) {
            if let Some(lit) = literal_value(value) {
                return *v == lit;
            }
        }
        false
    }
    pub fn variable_known_unequal(&self, var: &SMTVariable, value: &str) -> bool {
        if let Some(Value::Concrete(v)) = self.ssa_values.get(&var.name) {
            if let Some(lit) = literal_value(value) {
                return *v != lit;
            }
        }
        false
    }

    pub fn define_from_literal(&mut self, var: &SMTVariable, literal: &Literal) {
        let value = &literal.literal;
        //println!("{} := {literal}", var.name);
        self.ssa_values.insert(
            var.name.clone(),
            if let Some(hex) = value.strip_prefix("0x") {
                Value::Concrete(BigUint::from_str_radix(hex, 16).unwrap())
            } else if let Some(string) = value.strip_prefix('\"') {
                assert!(string.len() >= 2 && string.ends_with('\"'));
                // We assume all strings are references to sub-objects,
                // which is not true but will not harm correctness.
                Value::DataRef(string[1..string.len() - 1].to_string())
            } else {
                Value::Concrete(BigUint::from_str_radix(value, 10).unwrap())
            },
        );
    }
    pub fn define_from_variable(&mut self, var: &SMTVariable, value: &SMTVariable) {
        //println!("{} := {}", var.name, value.name);
        if let Some(value) = self.ssa_values.get(&value.name).cloned() {
            self.ssa_values.insert(var.name.clone(), value);
        }
    }
    pub fn builtin_call(
        &mut self,
        builtin: &Builtin,
        arguments: &[SMTVariable],
        return_vars: &[SMTVariable],
    ) {
        let arg_values = arguments
            .iter()
            .map(|arg| {
                if let Some(val) = self.ssa_values.get(&arg.name) {
                    val.clone()
                } else {
                    Value::Var(arg.name.clone())
                }
            })
            .collect::<Vec<_>>();
        let result = match (builtin.name, &arg_values[..]) {
            (
                "add" | "sub" | "mul" | "div" | "shl" | "shr" | "and" | "or" | "datasize" | "dataoffset" | "not" | "iszero" | "lt" | "gt" | "slt" | "sgt" | "eq" | "callvalue",
                _
                // TODO fewer clones
            ) => Some(Value::Op(builtin.name, arg_values.to_vec())),
            ("datacopy", [Value::Concrete(addr), Value::Op("dataoffset", offset), Value::Op("datasize", size)]) => {
                assert_eq!(offset, size);
                if let Value::DataRef(offset) = &offset[0] {
                    self.memory_slices.insert(addr.clone(), Value::DataRef(offset.clone()));
                }
                self.unknown_memory_write_above(addr);
                None
            }
            ("calldatasize", []) => {
                self.calldata.as_ref().map(|cd| Value::Concrete(BigUint::from(cd.len())))
            }
            ("calldataload", [Value::Concrete(addr)]) => {
                self.calldata.as_ref().map(|cd| {
                    let result = (0..32).map(|i| {
                        cd.get(addr.to_usize().unwrap() + i).copied().unwrap_or_default()
                    }).collect::<Vec<_>>();
                    Value::Concrete(BigUint::from_bytes_be(&result))
                })
            }
            ("create", [_ether_value, Value::Concrete(offset), _size /* TODO check size */]) => {
                if let Some(Value::DataRef(name)) = self.memory_slices.get(offset) {
                    Some(Value::KnownContractAddress(name.clone(), 0)) // TODO increment coutner
                } else {
                    None
                }
            }
            // TODO shoudl be part of simplify
            ("memoryguard", [value]) => Some(value.clone()),
            // TODO unknown mstore?
            ("mstore", [Value::Concrete(addr), value]) => {
                //println!("mstore({}, {})", addr, value);
                self.write_memory(addr.clone(), Some(value.clone()));
                None
            }
            ("mstore", ..) => {
                println!("Unknown memory write!");
                self.unknown_memory_write();
                None
            }
            ("mload", [Value::Concrete(addr)]) => {
                //println!("mload({})", addr);
                self.read_memory(addr)
            }
            ("returndatacopy", ..) => {
                println!("Unknown memory write!");
                // TODO: Problem: If we have an unknown memory write and join this with another
                // branch, we also do need to clear that memory!
                self.unknown_memory_write();
                None
            }
            ("sstore", [Value::Concrete(addr), value]) => {
                println!("sstore({addr}, {value})");
                println!(
                    "===> {}",
                    self.storage
                        .get(&BigUint::from(0u32))
                        .unwrap_or(&Value::Var("???".to_string())),
                );
                self.storage.insert(addr.clone(), value.clone());
                println!(
                    "===> {}",
                    self.storage
                        .get(&BigUint::from(0u32))
                        .unwrap_or(&Value::Var("???".to_string())),
                );
                None
            }
            ("sload", [Value::Concrete(addr)]) => {
                println!("sload({addr})");
                println!(
                    "===> {}",
                    self.storage
                        .get(&BigUint::from(0u32))
                        .unwrap_or(&Value::Var("???".to_string())),
                );
                self.storage.get(addr).cloned()
            }
            ("revert", ..) => {
                self.stopped = true;
                println!("Reverted!");
                None
            }
            ("return" | "stop", ..) => {
                self.stopped = true;
                println!("Returned!");
                None
            }
            (op, ..) => {
                println!("Unhandled opcode: {op}");
                None
            }
        };
        if let Some(result) = result.map(simplify) {
            self.ssa_values.insert(return_vars[0].name.clone(), result);
        }
        if builtin.name == "call" {
            // for i in 0x80..0xc4 {
            //     println!(
            //         "{:x}: {:x?}",
            //         i,
            //         self.read_memory_byte(&BigUint::from(i as u32))
            //     );
            // }
            // if let (Some(Value::Concrete(in_offset)), Some(Value::Concrete(in_len))) = (&arg_values[3], &arg_values[4]) {
            //     println!("{:x?}", &self.get_memory_slice(in_offset.clone(), in_len.clone()).unwrap());

            // }
        }
        match builtin.name {
            "create" | "sstore" | "sload" | "call" | "datacopy" | "mstore" => {
                println!(
                    "{}{}({})",
                    if return_vars.is_empty() {
                        String::new()
                    } else {
                        format!(
                            "{} := ",
                            return_vars
                                .iter()
                                .map(|v| v.name.to_owned())
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    },
                    builtin.name,
                    arguments
                        .iter()
                        .map(|a| {
                            if let Some(v) = self.ssa_values.get(&a.name) {
                                format!("{v}")
                            } else {
                                format!("${}", a.name)
                            }
                        })
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                // for (name, v) in arguments
                //     .iter()
                //     .map(|v| (v.name.clone(), self.ssa_values.get(&v.name)))
                // {
                //     if let Some(v) = v {
                //         println!("   - {name} = {v}");
                //     }
                // }
                for (name, v) in return_vars
                    .iter()
                    .map(|v| (v.name.clone(), self.ssa_values.get(&v.name)))
                {
                    if let Some(v) = v {
                        println!("   - {name} = {v}");
                    }
                }
            }
            _ => {}
        }
    }

    fn read_memory(&self, offset: &BigUint) -> Option<Value> {
        let candidate = self.memory.get(offset);
        if let Some(ValueByte {
            data: candidate, ..
        }) = candidate
        {
            if (0..32u32).all(|i| {
                self.memory.get(&(offset.clone() + BigUint::from(i)))
                    == Some(&ValueByte {
                        data: candidate.clone(),
                        byte: i,
                    })
            }) {
                return Some(candidate.clone());
            }
        }

        let mut result = vec![0u8; 32];
        for (i, item) in result.iter_mut().enumerate() {
            if let Some(v) = self.read_memory_byte(&(offset.clone() + BigUint::from(i))) {
                *item = v;
            } else {
                return None;
            }
        }
        Some(Value::Concrete(BigUint::from_bytes_be(&result)))
    }

    fn read_memory_byte(&self, offset: &BigUint) -> Option<u8> {
        match self.memory.get(offset) {
            Some(ValueByte {
                data: Value::Concrete(v),
                byte: i,
            }) => Some(
                v.to_bytes_le()
                    .get((31 - i) as usize)
                    .copied()
                    .unwrap_or_default(),
            ),
            _ => None,
        }
    }

    fn write_memory(&mut self, offset: BigUint, value: Option<Value>) {
        match value {
            Some(value) => {
                for i in 0..32u32 {
                    self.memory.insert(
                        offset.clone() + BigUint::from(i),
                        ValueByte {
                            data: value.clone(),
                            byte: i,
                        },
                    );
                }
            }
            None => {
                for i in 0..32u32 {
                    self.memory.remove(&(offset.clone() + BigUint::from(i)));
                }
            }
        }
    }

    fn get_memory_slice(&self, offset: BigUint, len: BigUint) -> Option<Vec<u8>> {
        // TODO aliasing?
        (0..(len.to_u64().unwrap()))
            .map(|i| self.read_memory_byte(&(offset.clone() + BigUint::from(i))))
            .fold(Some(Vec::<u8>::new()), |acc, v| {
                if let (Some(mut acc), Some(v)) = (acc, v) {
                    acc.push(v);
                    Some(acc)
                } else {
                    None
                }
            })
    }

    fn unknown_memory_write(&mut self) {
        self.memory.clear();
        self.unknown_memory_is_zero = false;
    }
    fn unknown_memory_write_above(&mut self, offset: &BigUint) {
        self.memory.retain(|addr, _| addr < offset);
        self.unknown_memory_is_zero = false;
    }
}

fn literal_value(value: &str) -> Option<BigUint> {
    if let Some(hex) = value.strip_prefix("0x") {
        Some(BigUint::from_str_radix(hex, 16).unwrap())
    } else if value.chars().next().unwrap().is_ascii_digit() {
        Some(BigUint::from_str_radix(value, 10).unwrap())
    } else {
        None
    }
}
