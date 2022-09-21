{
    mstore(0, calldataload(0))
    mstore(0x20, calldataload(1))
    let x := keccak256(0, 32)
    mstore(64, calldataload(99))
    let y := keccak256(0, 32)
    mstore(0, calldataload(100))
    mstore(0x20, calldataload(200))
    if and(
        eq(calldataload(0), calldataload(100)),
        eq(calldataload(1), calldataload(200))
    ) {
        if iszero(eq(x, y)) { revert(0, 0 )}
    }
}
