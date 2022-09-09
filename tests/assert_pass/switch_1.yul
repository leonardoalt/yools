{
	let x := 0
	let r := 1
	let t
	switch x
	case 0 { r := 9 t := 7 }
	case 1 { r := t }

	assert(and(eq(r, 9), eq(t, 7)))
}
