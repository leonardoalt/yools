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
(define-fun _stop_flag_2069_0 () (_ BitVec 256) (_ bv0 256))
(define-fun _revert_flag_2070_0 () (_ BitVec 256) (_ bv0 256))
(declare-fun _revert_sig_4_2071_0 () (_ BitVec 32))
(declare-fun _revert_data_32_2072_0 () (_ BitVec 256))
(assert (= ((_ extract 255 160) _address_2048_0) #x000000000000000000000000))
(assert (bvule _calldatasize_2050_0 #x000000000000000000000000000000000000000000000000ffffffffffffffff))
(define-fun _exe_pos_8128_0 () (_ BitVec 256) (_ bv0 256))
(define-const _1 (_ BitVec 256) (_ bv0 256))
(define-const x_2_1 (_ BitVec 256) _1)
(define-const _2 (_ BitVec 256) (_ bv0 256))
(define-const _3 (_ BitVec 256) (ite (= x_2_1 _2) (_ bv1 256) (_ bv0 256)))
(assert (and (and (= _revert_flag_2070_0 (_ bv0 256)) (= _stop_flag_2069_0 (_ bv0 256))) true (= _3 (_ bv0 256))))
(assert (not (= _revert_flag_2070_0 (_ bv0 256))))