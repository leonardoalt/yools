# yools - tools for Yul

Yools is [so far] an experimental symbolic execution engine for Yul.
It translates Yul programs into sets of SMT constraints and queries
an SMT solver to detect reachability of a certain program state.
Currently the only user facing approach is to detect whether a program
may revert or not.

## What's supported

NOT THAT MUCH PLEASE BE PATIENT

Yul's entire syntax is supported, but not all EVM builtin functions are.
The SMT encoding follows the usual BMC-style unrolling of loops up to a
certain constant bound which can be chosen by the user. This means that
results are not always sound in the presence of loops, and in such case
results are always under the assumption that loops do not iterate over
the given bound.

## Usage

Currently there is one subcommand `symbolic` which contains the available
features.

```bash
$ yools symbolic --help
yools-symbolic
Symbolically execute Yul programs checking for revert reachability

USAGE:
    yools symbolic [OPTIONS] --input <FILE.yul>

OPTIONS:
    -h, --help                         Print help information
    -i, --input <FILE.yul>             Yul source file
    -l, --loop-unroll <LOOP_UNROLL>    Loop unrolling limit [default: 10]
    -s, --solver <SOLVER>              SMT solver [default: cvc5]
```

Toy example:

```yul
// switch.yul
{
	let t := 0
	switch calldataload(0)
	case 0 { t := add(t, 10) }
	case 1 { t := add(t, 10) }
	case 2 { t := add(t, 10) }
	default { t := add(t, 10) }

	if iszero(eq(t, 10)) { revert(0, 0) }
}
```

```bash
$ yools symbolic -i switch.yul
All reverts are unreachable.
```

## Why this

Most Formal Verification tools for Ethereum smart contracts focus on EVM
bytecode, understandably.  A few others target Solidity source code. Verifying
Yul instead has some particular advantages over the 2 approaches:

- Writing and maintaining a tool for Yul is much easier than Solidity
due to the high level and complex types and language changes. The Yul
to EVM compiler is also much simpler, so much less trust is required
in the compiler.
- Yul has a lot more structured information than EVM bytecode, such as
functions, loops, ifs, switches, structured storage access for state
variables, structured ABI encoding/decoding and much more. This makes
it much easier to reason about the code and prove/disprove statements.
Tools that reason about bytecode try to infer and lift all this information
up from the bytecode to a higher level, but this process is not always
successful and requires extra effort.

Of course the approach used here also has disadvantages over the 2:

- Solidity has even more structured information and thus can be used
to find contract invariants more easily, for example.
- Analysing bytecode means there is no compiler involved from that point
to deployment, so what you verify is what's deployed.

All approaches are valuable and can/should be used together.

## Features

Please check the open issues to see what features are still not supported
or are planned.

## Research

One of the goals of this project is to allow for highly customizable semantics
when generating the SMT constraints that represent the program. For example,
there are different ways to represent calldata, memory, and storage symbolically.
It is hard to tell in advance which might be better, and ultimately that can be
also highly dependent on the analyzed Yul program as well. It is important
to experiment with different approaches, and this is what we want to achieve.

A few potential directions are given below:

### Calldata/Memory/Storage encoding

There are many different ways one may want to encode these memory regions
symbolically. For example, storage is often encoded as an SMT Array from BV256
to BV256, which is convenient given that `SLOAD` and `STORE` always handle
entire words. Memory, however, requires different handling due to single bytes
being read/written. We would like to eventually experiment with different
approaches to encode the 3 memory regions.


### Function/loop summaries

TODO

### ABI encoding/decoding abstraction

TODO

### Parallelism

TODO

### State variable abstraction

TODO

### Revert data abstraction

TODO

### External calls

TODO

## Contributing

If you're interested in contributing please reach out! There are lots of
exciting thing to do in different levels of Rust/SMT/Yul.
