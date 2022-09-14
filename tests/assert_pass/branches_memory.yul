{
    let x := address()
    mstore(0, 20)
    mstore(32, 21)
    if lt(x, 2) { mstore(0, 7) }
    if gt(x, 1) { mstore(0, 8) }
    let r := lt(mload(0), 9)

    assert(eq(r, 1))
    assert(eq(mload(32), 21))
}
