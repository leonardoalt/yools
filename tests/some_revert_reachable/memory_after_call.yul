{
    mstore(0, 7)
    let x := call(10000, 0, 0, 0, 0, 0, 10)
    if x {
        if iszero(mload(0), 7) {
            revert(0, 0)
        }
    }
}