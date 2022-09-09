{
	function f(a) -> b {
		b := a
	}

	let x := address()
	assert(eq(x, f(x)))
}
