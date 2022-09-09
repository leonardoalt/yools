{
	let x := 0
	let y := 0
	for {} lt(x, 3) {
		for {} lt(y, 3) {
			y := add(y, 2)
		} { y := add(y, 3) }
		x := add(x, 2)
	} { x := add(x, 3) }

	assert(and(eq(x, 5), eq(y, 5)))
}
