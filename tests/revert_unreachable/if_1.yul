{
	let x := 2
	let y := 0
	y := add(x, 42)
	if gt(x, y) {
		revert(0, 0)
	}
}
