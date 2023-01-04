{
    /// @src 0:88:299  "contract Test {..."
    mstore(64, memoryguard(128))

    if iszero(lt(calldatasize(), 4))
    {
        let selector := shift_right_224_unsigned(calldataload(0))
        switch selector

        case 0x0a9254e4
        {
            // setUp()

            external_fun_setUp_29()
        }

        case 0x85632895
        {
            // proveA(uint256,uint256)

            external_fun_proveA_63()
        }

        default {}
    }

    revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()

    function shift_right_224_unsigned(value) -> newValue {
        newValue :=

        shr(224, value)

    }

    function allocate_unbounded() -> memPtr {
        memPtr := mload(64)
    }

    function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
        revert(0, 0)
    }

    function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() {
        revert(0, 0)
    }

    function abi_decode_tuple_(headStart, dataEnd)   {
        if slt(sub(dataEnd, headStart), 0) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

    }

    function abi_encode_tuple__to__fromStack(headStart ) -> tail {
        tail := add(headStart, 0)

    }

    function external_fun_setUp_29() {

        if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
        abi_decode_tuple_(4, calldatasize())
        fun_setUp_29()
        let memPos := allocate_unbounded()
        let memEnd := abi_encode_tuple__to__fromStack(memPos  )
        return(memPos, sub(memEnd, memPos))

    }

    function revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db() {
        revert(0, 0)
    }

    function cleanup_t_uint256(value) -> cleaned {
        cleaned := value
    }

    function validator_revert_t_uint256(value) {
        if iszero(eq(value, cleanup_t_uint256(value))) { revert(0, 0) }
    }

    function abi_decode_t_uint256(offset, end) -> value {
        value := calldataload(offset)
        validator_revert_t_uint256(value)
    }

    function abi_decode_tuple_t_uint256t_uint256(headStart, dataEnd) -> value0, value1 {
        if slt(sub(dataEnd, headStart), 64) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

        {

            let offset := 0

            value0 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
        }

        {

            let offset := 32

            value1 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
        }

    }

    function external_fun_proveA_63() {

        if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
        let param_0, param_1 :=  abi_decode_tuple_t_uint256t_uint256(4, calldatasize())
        fun_proveA_63(param_0, param_1)
        let memPos := allocate_unbounded()
        let memEnd := abi_encode_tuple__to__fromStack(memPos  )
        return(memPos, sub(memEnd, memPos))

    }

    function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74() {
        revert(0, 0)
    }

    function panic_error_0x41() {
        mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
        mstore(4, 0x41)
        revert(0, 0x24)
    }

    function revert_forward_1() {
        let pos := allocate_unbounded()
        returndatacopy(pos, 0, returndatasize())
        revert(pos, returndatasize())
    }

    function shift_left_0(value) -> newValue {
        newValue :=

        shl(0, value)

    }

    function update_byte_slice_20_shift_0(value, toInsert) -> result {
        let mask := 0xffffffffffffffffffffffffffffffffffffffff
        toInsert := shift_left_0(toInsert)
        value := and(value, not(mask))
        result := or(value, and(toInsert, mask))
    }

    function cleanup_t_uint160(value) -> cleaned {
        cleaned := and(value, 0xffffffffffffffffffffffffffffffffffffffff)
    }

    function identity(value) -> ret {
        ret := value
    }

    function convert_t_uint160_to_t_uint160(value) -> converted {
        converted := cleanup_t_uint160(identity(cleanup_t_uint160(value)))
    }

    function convert_t_uint160_to_t_contract$_ToTest_$15(value) -> converted {
        converted := convert_t_uint160_to_t_uint160(value)
    }

    function convert_t_contract$_ToTest_$15_to_t_contract$_ToTest_$15(value) -> converted {
        converted := convert_t_uint160_to_t_contract$_ToTest_$15(value)
    }

    function prepare_store_t_contract$_ToTest_$15(value) -> ret {
        ret := value
    }

    function update_storage_value_offset_0t_contract$_ToTest_$15_to_t_contract$_ToTest_$15(slot, value_0) {
        let convertedValue_0 := convert_t_contract$_ToTest_$15_to_t_contract$_ToTest_$15(value_0)
        sstore(slot, update_byte_slice_20_shift_0(sload(slot), prepare_store_t_contract$_ToTest_$15(convertedValue_0)))
    }

    /// @ast-id 29
    /// @src 0:118:169  "function setUp() public {..."
    function fun_setUp_29() {

        /// @src 0:152:164  "new ToTest()"
        let _1 := allocate_unbounded()
        let _2 := add(_1, datasize("ToTest_15"))
        if or(gt(_2, 0xffffffffffffffff), lt(_2, _1)) { panic_error_0x41() }
        datacopy(_1, dataoffset("ToTest_15"), datasize("ToTest_15"))
        _2 := abi_encode_tuple__to__fromStack(_2)

        let expr_25_address := create(0, _1, sub(_2, _1))

        if iszero(expr_25_address) { revert_forward_1() }

        /// @src 0:148:164  "t = new ToTest()"
        update_storage_value_offset_0t_contract$_ToTest_$15_to_t_contract$_ToTest_$15(0x00, expr_25_address)
        let expr_26_address := expr_25_address

    }
    /// @src 0:88:299  "contract Test {..."

    function cleanup_t_rational_10_by_1(value) -> cleaned {
        cleaned := value
    }

    function convert_t_rational_10_by_1_to_t_uint256(value) -> converted {
        converted := cleanup_t_uint256(identity(cleanup_t_rational_10_by_1(value)))
    }

    function require_helper(condition) {
        if iszero(condition) { revert(0, 0) }
    }

    function shift_right_0_unsigned(value) -> newValue {
        newValue :=

        shr(0, value)

    }

    function cleanup_from_storage_t_contract$_ToTest_$15(value) -> cleaned {
        cleaned := and(value, 0xffffffffffffffffffffffffffffffffffffffff)
    }

    function extract_from_storage_value_offset_0t_contract$_ToTest_$15(slot_value) -> value {
        value := cleanup_from_storage_t_contract$_ToTest_$15(shift_right_0_unsigned(slot_value))
    }

    function read_from_storage_split_offset_0_t_contract$_ToTest_$15(slot) -> value {
        value := extract_from_storage_value_offset_0t_contract$_ToTest_$15(sload(slot))

    }

    function convert_t_uint160_to_t_address(value) -> converted {
        converted := convert_t_uint160_to_t_uint160(value)
    }

    function convert_t_contract$_ToTest_$15_to_t_address(value) -> converted {
        converted := convert_t_uint160_to_t_address(value)
    }

    function revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20() {
        revert(0, 0)
    }

    function round_up_to_mul_of_32(value) -> result {
        result := and(add(value, 31), not(31))
    }

    function finalize_allocation(memPtr, size) {
        let newFreePtr := add(memPtr, round_up_to_mul_of_32(size))
        // protect against overflow
        if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
        mstore(64, newFreePtr)
    }

    function shift_left_224(value) -> newValue {
        newValue :=

        shl(224, value)

    }

    function abi_decode_t_uint256_fromMemory(offset, end) -> value {
        value := mload(offset)
        validator_revert_t_uint256(value)
    }

    function abi_decode_tuple_t_uint256_fromMemory(headStart, dataEnd) -> value0 {
        if slt(sub(dataEnd, headStart), 32) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

        {

            let offset := 0

            value0 := abi_decode_t_uint256_fromMemory(add(headStart, offset), dataEnd)
        }

    }

    function abi_encode_t_uint256_to_t_uint256_fromStack(value, pos) {
        mstore(pos, cleanup_t_uint256(value))
    }

    function abi_encode_tuple_t_uint256_t_uint256__to_t_uint256_t_uint256__fromStack(headStart , value0, value1) -> tail {
        tail := add(headStart, 64)

        abi_encode_t_uint256_to_t_uint256_fromStack(value0,  add(headStart, 0))

        abi_encode_t_uint256_to_t_uint256_fromStack(value1,  add(headStart, 32))

    }

    function panic_error_0x11() {
        mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
        mstore(4, 0x11)
        revert(0, 0x24)
    }

    function checked_add_t_uint256(x, y) -> sum {
        x := cleanup_t_uint256(x)
        y := cleanup_t_uint256(y)
        sum := add(x, y)

        if gt(x, sum) { panic_error_0x11() }

    }

    function panic_error_0x01() {
        mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
        mstore(4, 0x01)
        revert(0, 0x24)
    }

    function assert_helper(condition) {
        if iszero(condition) { panic_error_0x01() }
    }

    /// @ast-id 63
    /// @src 0:172:297  "function proveA(uint a, uint b) public {..."
    function fun_proveA_63(var_a_31, var_b_33) {

        /// @src 0:225:226  "a"
        let _3 := var_a_31
        let expr_37 := _3
        /// @src 0:230:232  "10"
        let expr_38 := 0x0a
        /// @src 0:225:232  "a <= 10"
        let expr_39 := iszero(gt(cleanup_t_uint256(expr_37), convert_t_rational_10_by_1_to_t_uint256(expr_38)))
        /// @src 0:225:243  "a <= 10 && b <= 10"
        let expr_43 := expr_39
        if expr_43 {
            /// @src 0:236:237  "b"
            let _4 := var_b_33
            let expr_40 := _4
            /// @src 0:241:243  "10"
            let expr_41 := 0x0a
            /// @src 0:236:243  "b <= 10"
            let expr_42 := iszero(gt(cleanup_t_uint256(expr_40), convert_t_rational_10_by_1_to_t_uint256(expr_41)))
            /// @src 0:225:243  "a <= 10 && b <= 10"
            expr_43 := expr_42
        }
        /// @src 0:217:244  "require(a <= 10 && b <= 10)"
        require_helper(expr_43)
        /// @src 0:259:260  "t"
        let _5_address := read_from_storage_split_offset_0_t_contract$_ToTest_$15(0x00)
        let expr_48_address := _5_address
        /// @src 0:259:262  "t.f"
        let expr_49_address := convert_t_contract$_ToTest_$15_to_t_address(expr_48_address)
        let expr_49_functionSelector := 0x13d1aa2e
        /// @src 0:263:264  "a"
        let _6 := var_a_31
        let expr_50 := _6
        /// @src 0:266:267  "b"
        let _7 := var_b_33
        let expr_51 := _7
        /// @src 0:259:268  "t.f(a, b)"

        // storage for arguments and returned data
        let _8 := allocate_unbounded()
        mstore(_8, shift_left_224(expr_49_functionSelector))
        let _9 := abi_encode_tuple_t_uint256_t_uint256__to_t_uint256_t_uint256__fromStack(add(_8, 4) , expr_50, expr_51)

        let _10 := call(gas(), expr_49_address,  0,  _8, sub(_9, _8), _8, 32)

        if iszero(_10) { revert_forward_1() }

        let expr_52
        if _10 {

            let _11 := 32

            if gt(_11, returndatasize()) {
                _11 := returndatasize()
            }

            // update freeMemoryPointer according to dynamic return size
            finalize_allocation(_8, _11)

            // decode return parameters from external try-call into retVars
            expr_52 :=  abi_decode_tuple_t_uint256_fromMemory(_8, add(_8, _11))
        }
        /// @src 0:250:268  "uint r = t.f(a, b)"
        let var_r_47 := expr_52
        /// @src 0:281:282  "r"
        let _12 := var_r_47
        let expr_55 := _12
        /// @src 0:286:287  "a"
        let _13 := var_a_31
        let expr_56 := _13
        /// @src 0:290:291  "b"
        let _14 := var_b_33
        let expr_57 := _14
        /// @src 0:286:291  "a + b"
        let expr_58 := checked_add_t_uint256(expr_56, expr_57)

        /// @src 0:281:291  "r == a + b"
        let expr_59 := eq(cleanup_t_uint256(expr_55), cleanup_t_uint256(expr_58))
        /// @src 0:274:292  "assert(r == a + b)"
        assert_helper(expr_59)

    }
    /// @src 0:88:299  "contract Test {..."

}
