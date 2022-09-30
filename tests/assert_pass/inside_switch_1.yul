{
	let x := calldataload(0)
	if gt(x, 0) {
		switch x
		case 10 {
			assert(gt(x, 5))
		}
	}
}
