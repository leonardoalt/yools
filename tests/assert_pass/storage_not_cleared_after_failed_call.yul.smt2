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
(declare-fun _selfbalance_2062_0 () (_ BitVec 256))
(define-fun _memory_2063_0 () (Array (_ BitVec 256) (_ BitVec 8)) ((as const (Array (_ BitVec 256) (_ BitVec 8))) #x00))
(declare-fun _storage_2064_0 () (Array (_ BitVec 256) (_ BitVec 256)))
(declare-fun _calldata_2065_0 ((_ BitVec 256)) (_ BitVec 8))
(declare-fun _keccak256_32_2066_0 ((_ BitVec 256)) (_ BitVec 256))
(declare-fun _keccak256_64_2067_0 ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))
(declare-fun _keccak256_2068_0 ((Array (_ BitVec 256) (_ BitVec 8)) (_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))
(define-fun _stop_flag_2069_0 () (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-fun _revert_flag_2070_0 () (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(declare-fun _revert_sig_4_2071_0 () (_ BitVec 32))
(declare-fun _revert_data_32_2072_0 () (_ BitVec 256))
(assert (= ((_ extract 255 160) _address_2048_0) #x000000000000000000000000))
(assert (bvule _calldatasize_2050_0 #x000000000000000000000000000000000000000000000000ffffffffffffffff))
(define-const _1 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _2 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000007)
(define-const _storage_2064_1 (Array (_ BitVec 256) (_ BitVec 256)) (store _storage_2064_0 _1 _2))
(define-const _3 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000002710)
(define-const _4 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _5 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _6 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _7 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _8 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _9 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(declare-const _10 (_ BitVec 256))
(assert (bvult _10 #x0000000000000000000000000000000000000000000000000000000000000002))
(declare-const _selfbalance_2062_1 (_ BitVec 256))
(assert (=> (= _10 #x0000000000000000000000000000000000000000000000000000000000000000) (= _selfbalance_2062_0 _selfbalance_2062_1)))
(declare-const _storage_2064_2 (Array (_ BitVec 256) (_ BitVec 256)))
(assert (=> (= _10 #x0000000000000000000000000000000000000000000000000000000000000000) (= _storage_2064_1 _storage_2064_2)))
(declare-const _memory_2063_1 (Array (_ BitVec 256) (_ BitVec 8)))
(assert (=> (= _9 #x0000000000000000000000000000000000000000000000000000000000000000) (= _memory_2063_0 _memory_2063_1)))
(define-const x_2_1 (_ BitVec 256) _10)
(define-const _11 (_ BitVec 256) (ite (= x_2_1 #x0000000000000000000000000000000000000000000000000000000000000000) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(define-const _12 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _13 (_ BitVec 256) (select _storage_2064_2 _12))
(define-const _14 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000007)
(define-const _15 (_ BitVec 256) (ite (= _13 _14) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(assert (and (and (= _revert_flag_2070_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_flag_2069_0 #x0000000000000000000000000000000000000000000000000000000000000000)) (not (= _11 #x0000000000000000000000000000000000000000000000000000000000000000)) (= _15 #x0000000000000000000000000000000000000000000000000000000000000000)))
(assert (not (= _revert_flag_2070_0 #x0000000000000000000000000000000000000000000000000000000000000000)))