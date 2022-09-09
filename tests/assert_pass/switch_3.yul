{
	let x := 2
	let r := 1
	let t
	switch x
	case 0 { r := 9 t := 7 }
	case 1 { r := t }

	assert(and(eq(r, 1), eq(t, 0)))
}
