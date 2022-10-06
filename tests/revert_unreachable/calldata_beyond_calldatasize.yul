{
    let s := calldatasize()
    let t := 0
    if eq(s, 0x10) {
        t := shl(128, calldataload(0))
    }
    if t { revert(0, 0) }
}