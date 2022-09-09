{
	let x := 1
	let r := 1
	let t
	switch x
	case 0 { r := 9 t := 7 }
	case 1 { r := t }

	assert(and(eq(r, 0), eq(t, 0)))
}
