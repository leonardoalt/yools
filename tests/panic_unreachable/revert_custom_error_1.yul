{
	function panic_error_0x11() {
		mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
		mstore(4, 0x11)
		revert(0, 0x24)
	}

	function custom_error() {
		mstore(0, 0xcafe)
		revert(0, 0x04)
	}

	custom_error()
	panic_error_0x11()
}
