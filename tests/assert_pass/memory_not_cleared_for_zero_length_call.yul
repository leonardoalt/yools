{
    mstore(0, 9)
    let x := call(10000, 0, 0, 0, 0, 0, calldataload(0))
    if iszero(calldataload(0)) {
        assert(eq(mload(0), 9))
    }
}