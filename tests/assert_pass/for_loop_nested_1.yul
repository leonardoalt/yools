{
	let x := 0
	let y := 0
	for {} lt(x, 3) {
		for {} lt(y, 3) {
			y := add(y, 1)
		} { y := add(y, 0) }
		x := add(x, 1)
	} { x := add(x, 0) }

	assert(and(eq(x, 3), eq(y, 3)))
}
