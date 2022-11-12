{
	let t := 0
	switch calldataload(0)
	case 0 { t := add(t, 10) }
	case 1 { t := add(t, 10) }
	case 2 { t := add(t, 10) }
	default { t := add(t, 10) }

	if iszero(eq(t, 10)) { revert(0, 0) }
}
