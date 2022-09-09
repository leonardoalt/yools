{
	let x := 0
	let y := 3
	for {} lt(x, y) {
		x := add(x, 2)
	} { x := add(x, 3) }

	assert(eq(x, 5))
}
