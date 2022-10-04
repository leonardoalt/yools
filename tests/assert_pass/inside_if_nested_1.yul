{
	let x := calldataload(0)
	let y := calldataload(32)
	if gt(x, 20) {
		if lt(y, 10) {
			assert(gt(x, y))
		}
	}
}
