{
    let x := calldataload(0)
    switch x
    case 0 { let t := 1 }
    case 2 { let r := 2 }

    assert(eq(x, calldataload(0)))
}
