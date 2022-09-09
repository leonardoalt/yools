{
	let x := address()
	let t := 20
	if lt(x, 2) { t := 7 }
	if gt(x, 1) { t := 8 }
	let r := lt(t, 9)

	assert(eq(r, 1))
}
