{
    let b := selfbalance()
    let x := call(10000, 0, 0, 0, 0, 0, 0)
    if iszero(x) {
        assert(eq(b, selfbalance()))
    }
}