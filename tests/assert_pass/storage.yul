{
    sstore(0, 1)
    sstore(1, 2)
    sstore(2, 1)
    sstore(1, 3)
    assert(eq(sload(0), sload(2)))
    assert(iszero(eq(sload(0), sload(1))))
    assert(eq(sload(1), 3))
}
