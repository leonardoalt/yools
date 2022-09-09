{
	let x := 2
	let y := add(address(), 1)
	let r := add(x, y)

	assert(and(gt(r, x), gt(r, y)))
}
