{
	let x := calldataload(0)
	let y := calldataload(32)
	for {} lt(x, y) { x := add(x, 1) } {
		if and(lt(x, 100), lt(y, 100)) {
			let a := add(x, 1)
			let b := add(y, 1)
			assert(lt(a, b))
		}
	}
}
// loop_unroll:10
