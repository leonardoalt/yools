{
	let max := calldataload(0)
	if gt(max, 10) { revert(0, 0) }
	let x
	let i
	for {} lt(i, max) { i := add(i, 1) } {
		x := add(x, 1)
	}

	assert(eq(x, max))
}
// loop_unroll:20
// The loop has at most 10 iterations because of the require on `max`.
// We over-unroll 20 iterations, but nevertheless the assertion is still safe.
