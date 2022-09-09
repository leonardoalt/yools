{
	let x
	let y := 2
	x := add(x, y)
	y := add(y, 11)
	let a := x
	let b := y

	assert(and(eq(a, 2), eq(b, 13)))
}
