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
(define-const x_2_1 (_ BitVec 256) _1)
(define-const _2 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _3 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _revert_sig_4_2071_1 (_ BitVec 32) (ite (and (= _revert_flag_2070_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_flag_2069_0 #x0000000000000000000000000000000000000000000000000000000000000000)) (ite (bvuge _3 #x0000000000000000000000000000000000000000000000000000000000000004) (concat (select _memory_2063_0 (bvadd #x0000000000000000000000000000000000000000000000000000000000000000 #x0000000000000000000000000000000000000000000000000000000000000000)) (select _memory_2063_0 (bvadd #x0000000000000000000000000000000000000000000000000000000000000000 #x0000000000000000000000000000000000000000000000000000000000000001)) (select _memory_2063_0 (bvadd #x0000000000000000000000000000000000000000000000000000000000000000 #x0000000000000000000000000000000000000000000000000000000000000002)) (select _memory_2063_0 (bvadd #x0000000000000000000000000000000000000000000000000000000000000000 #x0000000000000000000000000000000000000000000000000000000000000003))) #x00000000) _revert_sig_4_2071_0))
(define-const _revert_data_32_2072_1 (_ BitVec 256) (ite (and (= _revert_flag_2070_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_flag_2069_0 #x0000000000000000000000000000000000000000000000000000000000000000)) (ite (= _3 #x0000000000000000000000000000000000000000000000000000000000000024) (concat (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000000)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000001)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000002)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000003)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000004)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000005)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000006)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000007)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000008)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000009)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x000000000000000000000000000000000000000000000000000000000000000a)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x000000000000000000000000000000000000000000000000000000000000000b)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x000000000000000000000000000000000000000000000000000000000000000c)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x000000000000000000000000000000000000000000000000000000000000000d)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x000000000000000000000000000000000000000000000000000000000000000e)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x000000000000000000000000000000000000000000000000000000000000000f)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000010)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000011)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000012)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000013)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000014)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000015)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000016)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000017)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000018)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000000000000000000000000000000000019)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x000000000000000000000000000000000000000000000000000000000000001a)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x000000000000000000000000000000000000000000000000000000000000001b)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x000000000000000000000000000000000000000000000000000000000000001c)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x000000000000000000000000000000000000000000000000000000000000001d)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x000000000000000000000000000000000000000000000000000000000000001e)) (select _memory_2063_0 (bvadd (bvadd _2 #x0000000000000000000000000000000000000000000000000000000000000004) #x000000000000000000000000000000000000000000000000000000000000001f))) #x0000000000000000000000000000000000000000000000000000000000000000) _revert_data_32_2072_0))
(define-const _revert_flag_2070_1 (_ BitVec 256) (ite (and (= _revert_flag_2070_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_flag_2069_0 #x0000000000000000000000000000000000000000000000000000000000000000)) #x0000000000000000000000000000000000000000000000000000000000000001 _revert_flag_2070_0))
(define-const _4 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000001)
(define-const _5 (_ BitVec 256) (ite (= x_2_1 _4) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(assert (and (and (= _revert_flag_2070_1 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_flag_2069_0 #x0000000000000000000000000000000000000000000000000000000000000000)) true (= _5 #x0000000000000000000000000000000000000000000000000000000000000000)))
(assert (not (= _revert_flag_2070_1 #x0000000000000000000000000000000000000000000000000000000000000000)))