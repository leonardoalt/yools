{
	let x := calldataload(0)
	if gt(x, 20) {
		assert(gt(x, 10))
	}
}
