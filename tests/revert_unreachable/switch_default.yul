{
    let t := 200
    let c := 0
    switch address()
    case 0 { t := 7 c := add(c, 1) }
    case 1 { t := 8 c := add(c, 1) }
    default { t := 9 c := add(c, 1) }

    if gt(t, 10) { revert(0, 0) }
    if iszero(eq(c, 1)) { revert(0, 0) }
}