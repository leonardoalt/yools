{
    let x := 0x1234
    assert(eq(byte(0, x), 0))
    assert(eq(byte(29, x), 0))
    assert(eq(byte(30, x), 0x12))
    assert(eq(byte(31, x), 0x34))
    assert(eq(byte(32, x), 0))
    assert(eq(byte(0xffffffffffffffffffffffffff, x), 0))
}
