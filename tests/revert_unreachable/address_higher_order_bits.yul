{
    let x := address()
    let t := lt(x, 0x10000000000000000000000000000000000000000)
    if iszero(t) {
        revert(0, 0)
    }
}