{
    sstore(0, 7)
    let x := call(10000, 0, 0, 0, 0, 0, 0)
    if iszero(x) {
        assert(eq(sload(0), 7))
    }
}