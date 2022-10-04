{
	let x := calldataload(0)
	if gt(x, 0) {
		switch x
		case 10 {
		}
		case 200 {
		}
		default {
			assert(gt(x, 0))
		}
	}
}
