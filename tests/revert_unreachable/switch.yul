{
	let x := address()
	let t := 0
	switch address()
	case 0 { t := add(t, 10) }
	case 1 { t := add(t, 10) }
	case 2 { t := add(t, 10) }

	if gt(address(), 2) {
		t := add(t, 10)
	}
	if iszero(eq(t, 10)) { revert(0, 0) }
}
