{
    switch calldataload(0)
    case 1 { revert(0, 0) }
    case 2 { revert(0, 0x24 )}
    case 3 { revert(0x20, 0x24 )}
}