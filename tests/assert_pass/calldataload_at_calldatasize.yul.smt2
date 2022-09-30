(declare-fun _address_2048_0 () (_ BitVec 256))
(declare-fun _basefee_2049_0 () (_ BitVec 256))
(declare-fun _calldatasize_2050_0 () (_ BitVec 256))
(declare-fun _caller_2051_0 () (_ BitVec 256))
(declare-fun _callvalue_2052_0 () (_ BitVec 256))
(declare-fun _chainid_2053_0 () (_ BitVec 256))
(declare-fun _codesize_2054_0 () (_ BitVec 256))
(declare-fun _coinbase_2055_0 () (_ BitVec 256))
(declare-fun _difficulty_2056_0 () (_ BitVec 256))
(declare-fun _gaslimit_2057_0 () (_ BitVec 256))
(declare-fun _gasprice_2058_0 () (_ BitVec 256))
(declare-fun _number_2059_0 () (_ BitVec 256))
(declare-fun _origin_2060_0 () (_ BitVec 256))
(declare-fun _timestamp_2061_0 () (_ BitVec 256))
(define-fun _memory_2062_0 () (Array (_ BitVec 256) (_ BitVec 8)) ((as const (Array (_ BitVec 256) (_ BitVec 8))) #x00))
(declare-fun _storage_2063_0 () (Array (_ BitVec 256) (_ BitVec 256)))
(declare-fun _calldata_2064_0 ((_ BitVec 256)) (_ BitVec 8))
(declare-fun _keccak256_32_2065_0 ((_ BitVec 256)) (_ BitVec 256))
(declare-fun _keccak256_64_2066_0 ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))
(declare-fun _keccak256_2067_0 ((Array (_ BitVec 256) (_ BitVec 8)) (_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))
(define-fun _revert_flag_2068_0 () (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-fun _stop_flag_2069_0 () (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(assert (= ((_ extract 255 160) _address_2048_0) #x000000000000000000000000))
(assert (bvule _calldatasize_2050_0 #x000000000000000000000000000000000000000000000000ffffffffffffffff))
(define-const _1 (_ BitVec 256) _calldatasize_2050_0)
(define-const _2 (_ BitVec 256) (concat (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000000) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000000)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000001) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000001)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000002) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000002)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000003) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000003)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000004) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000004)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000005) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000005)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000006) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000006)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000007) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000007)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000008) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000008)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000009) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000009)) #x00) (ite (bvult (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000a) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000a)) #x00) (ite (bvult (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000b) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000b)) #x00) (ite (bvult (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000c) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000c)) #x00) (ite (bvult (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000d) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000d)) #x00) (ite (bvult (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000e) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000e)) #x00) (ite (bvult (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000f) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000f)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000010) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000010)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000011) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000011)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000012) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000012)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000013) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000013)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000014) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000014)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000015) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000015)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000016) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000016)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000017) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000017)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000018) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000018)) #x00) (ite (bvult (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000019) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000019)) #x00) (ite (bvult (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001a) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001a)) #x00) (ite (bvult (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001b) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001b)) #x00) (ite (bvult (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001c) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001c)) #x00) (ite (bvult (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001d) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001d)) #x00) (ite (bvult (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001e) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001e)) #x00) (ite (bvult (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001f) _calldatasize_2050_0) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001f)) #x00)))
(define-const x_2_1 (_ BitVec 256) _2)
(define-const _3 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _4 (_ BitVec 256) (ite (= x_2_1 _3) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(assert (and (and (= _revert_flag_2068_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_flag_2069_0 #x0000000000000000000000000000000000000000000000000000000000000000)) true (= _4 #x0000000000000000000000000000000000000000000000000000000000000000)))
(assert (not (= _revert_flag_2068_0 #x0000000000000000000000000000000000000000000000000000000000000000)))