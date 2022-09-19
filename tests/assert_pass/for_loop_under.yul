{
	let max := calldataload(0)
	let x
	let i
	for {} lt(i, max) { i := add(i, 1) } {
		x := add(x, 1)
	}

	assert(lt(x, 11))
}
// loop_unroll:10
// The assertion is not always true, but we only unroll 10 times
// so the underapproximation seems safe.
