{
	function panic_error_0x11() {
		mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
		mstore(4, 0x11)
		revert(0, 0x24)
	}

	let a := calldataload(0)
	let b := calldataload(0)
	if iszero(eq(a, b)) {
		panic_error_0x11()
	}
}
