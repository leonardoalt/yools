{
    sstore(0, 7)
    let x := call(10000, 0, 0, 0, 0, 0, 0)
    if x {
        if iszero(sload(0), 7) {
            revert(0, 0)
        }
    }
}