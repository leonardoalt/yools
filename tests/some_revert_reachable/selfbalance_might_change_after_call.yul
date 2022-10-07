{
    let b := selfbalance()
    let x := call(10000, 0, 0, 0, 0, 0, 0)
    if iszero(eq(b, selfbalance())) {
        revert(0, 0)
    }
}