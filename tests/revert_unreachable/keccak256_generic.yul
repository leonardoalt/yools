{
    mstore(0, calldataload(0))
    let x := keccak256(0, calldataload(7))
    mstore(0, calldataload(9))
    let y := keccak256(0, calldataload(7))
    if eq(calldataload(0), calldataload(9)) {
        if iszero(eq(x, y)) { revert(0, 0 )}
    }
}
