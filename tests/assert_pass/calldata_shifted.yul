{
    let x := calldataload(0)
    let y := calldataload(1)
    x := shl(8, x)
    y := and(y, not(0xff))
    assert(eq(x, y))
}
