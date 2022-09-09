{
	let x := 0
	let y := 3
	for {} lt(x, y) {
		x := add(x, 1)
	} { x := add(x, 0) }

	assert(eq(x, 3))
}
