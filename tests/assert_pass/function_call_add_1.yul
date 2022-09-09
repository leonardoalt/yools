{
	function add2(a, b) -> c {
		if gt(a, 100) { revert(0, 0) }
		if gt(b, 100) { revert(0, 0) }

		c := add(a, b)
	}

	let x := address()
	let y := address()

	assert(iszero(gt(x, add2(x, y))))
}
