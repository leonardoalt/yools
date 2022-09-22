{
    let x := calldataload(0)
    if x { let t := 1 }
    assert(eq(x, calldataload(0)))
}
