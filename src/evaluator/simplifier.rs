use num_bigint::BigUint;
use num_traits::ToPrimitive;

use crate::evaluator::Value;

pub fn simplify(input: Value) -> Value {
    if let Value::Op(opcode, mut args) = input {
        let two256: BigUint = BigUint::from(1u64) << 256;
        let mask256 = two256.clone() - BigUint::from(1u64);
        let address_mask = (BigUint::from(1u64) << 160) - BigUint::from(1u64);

        args = args.iter().map(|a| simplify(a.clone())).collect::<Vec<_>>();

        // Swap concrete values to the right for commutative opcodes.
        if matches!(opcode, "and" | "or" | "add")
            && matches!(args[0], Value::Concrete(_))
            && !matches!(args[1], Value::Concrete(_))
        {
            args.reverse();
        }

        match (opcode, &args[..]) {
            ("not", [Value::Concrete(arg)]) => Value::Concrete(arg ^ mask256),
            (
                "add" | "sub" | "mul" | "div" | "shl" | "shr" | "and" | "or" | "eq",
                [Value::Concrete(left), Value::Concrete(right)],
            ) => {
                let result = match opcode {
                    "add" => wrap256(left + right),
                    "sub" => wrap256(left + two256 - right),
                    "mul" => wrap256(left * right),
                    "div" => {
                        if *right == BigUint::from(0u32) {
                            BigUint::from(0u32)
                        } else {
                            wrap256(left / right)
                        }
                    }
                    "shl" => {
                        if *left >= 256u64.into() {
                            BigUint::from(0u64)
                        } else {
                            wrap256(right << left.to_u64().unwrap())
                        }
                    }
                    "shr" => {
                        if *left >= 256u64.into() {
                            BigUint::from(0u64)
                        } else {
                            wrap256(right >> left.to_u64().unwrap())
                        }
                    }
                    "and" => left & right,
                    "or" => left | right,
                    "eq" => {
                        if left == right {
                            BigUint::from(1u32)
                        } else {
                            BigUint::from(0u32)
                        }
                    }
                    _ => panic!(),
                };
                Value::Concrete(result)
            }
            ("lt" | "gt" | "slt" | "sgt", [Value::Concrete(left), Value::Concrete(right)]) => {
                let two255: BigUint = BigUint::from(1u64) << 255;
                Value::Concrete(
                    if match opcode {
                        "lt" => left < right,
                        "gt" => left > right,
                        "slt" => {
                            wrap256(left.clone() + two255.clone()) < wrap256(right.clone() + two255)
                        }
                        "sgt" => {
                            wrap256(left.clone() + two255.clone()) > wrap256(right.clone() + two255)
                        }
                        _ => panic!(),
                    } {
                        BigUint::from(1u32)
                    } else {
                        BigUint::from(0u32)
                    },
                )
            }
            ("shl" | "shr", [Value::Concrete(bits), value]) if *bits == BigUint::from(0u64) => {
                value.clone()
            }
            ("and", [Value::Op("and", inner), Value::Concrete(outer_mask)])
                if matches!(inner[1], Value::Concrete(_)) =>
            {
                if let Value::Concrete(inner_mask) = &inner[1] {
                    simplify(Value::Op(
                        "and",
                        vec![inner[0].clone(), Value::Concrete(inner_mask & outer_mask)],
                    ))
                } else {
                    panic!()
                }
            }
            ("and", [Value::KnownContractAddress(name, idx), Value::Concrete(m)])
                if *m == address_mask =>
            {
                Value::KnownContractAddress(name.clone(), *idx)
            }
            ("and", [_, Value::Concrete(m)]) if *m == BigUint::from(0u32) => {
                Value::Concrete(BigUint::from(0u32))
            }
            ("or", [v, Value::Concrete(m)]) if *m == BigUint::from(0u32) => v.clone(),
            ("iszero", [Value::Concrete(arg)]) => Value::Concrete(if *arg == BigUint::from(0u64) {
                BigUint::from(1u64)
            } else {
                BigUint::from(0u64)
            }),
            ("and", [Value::Op("or", inner), Value::Concrete(mask)])
                if matches!(inner[0], Value::Op("and", _)) =>
            {
                simplify(Value::Op(
                    "or",
                    vec![
                        Value::Op("and", vec![inner[0].clone(), Value::Concrete(mask.clone())]),
                        Value::Op("and", vec![inner[1].clone(), Value::Concrete(mask.clone())]),
                    ],
                ))
            }
            _ => Value::Op(opcode, args),
        }
    } else {
        input
    }
}

fn wrap256(x: BigUint) -> BigUint {
    let mask = (BigUint::from(1u64) << 256) - BigUint::from(1u64);
    // TODO optimization: work directly on limbs
    x & mask
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn simplify_masking() {
        let combined = Value::Op(
            "or",
            vec![
                Value::Op(
                    "and",
                    vec![
                        Value::Var("var".to_string()),
                        Value::Op(
                            "not",
                            vec![Value::Op(
                                "sub",
                                vec![
                                    Value::Op(
                                        "shl",
                                        vec![
                                            Value::Concrete(BigUint::from(160u32)),
                                            Value::Concrete(BigUint::from(1u32)),
                                        ],
                                    ),
                                    Value::Concrete(BigUint::from(1u32)),
                                ],
                            )],
                        ),
                    ],
                ),
                Value::KnownContractAddress("myContract".to_string(), 0),
            ],
        );
        assert_eq!(format!("{}", simplify(combined.clone())), "or(and($var, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000), address<myContract,0>)");
        let extracted = Value::Op(
            "and",
            vec![
                combined,
                Value::Op(
                    "sub",
                    vec![
                        Value::Op(
                            "shl",
                            vec![
                                Value::Concrete(BigUint::from(160u32)),
                                Value::Concrete(BigUint::from(1u32)),
                            ],
                        ),
                        Value::Concrete(BigUint::from(1u32)),
                    ],
                ),
            ],
        );
        assert_eq!(format!("{}", simplify(extracted)), "address<myContract,0>");
    }
}
