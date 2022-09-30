{
    let x := address()
    if mload(x) {
        revert(0, 0)
    }
}