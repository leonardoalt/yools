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
(define-const _1 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000002)
(define-const i_2_1 (_ BitVec 256) _1)
(define-const _2 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000001234)
(define-const x_3_1 (_ BitVec 256) _2)
(define-const _memory_2062_1 (Array (_ BitVec 256) (_ BitVec 8)) (store _memory_2062_0 i_2_1 ((_ extract 7 0) x_3_1)))
(define-const _3 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _4 (_ BitVec 256) (concat (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000000)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000001)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000002)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000003)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000004)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000005)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000006)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000007)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000008)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000009)) (select _memory_2062_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000000a)) (select _memory_2062_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000000b)) (select _memory_2062_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000000c)) (select _memory_2062_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000000d)) (select _memory_2062_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000000e)) (select _memory_2062_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000000f)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000010)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000011)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000012)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000013)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000014)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000015)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000016)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000017)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000018)) (select _memory_2062_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000019)) (select _memory_2062_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000001a)) (select _memory_2062_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000001b)) (select _memory_2062_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000001c)) (select _memory_2062_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000001d)) (select _memory_2062_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000001e)) (select _memory_2062_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000001f))))
(define-const t_4_1 (_ BitVec 256) _4)
(define-const _5 (_ BitVec 256) #x0000340000000000000000000000000000000000000000000000000000000000)
(define-const _6 (_ BitVec 256) (ite (= t_4_1 _5) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(assert (and (and (= _revert_flag_2068_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_flag_2069_0 #x0000000000000000000000000000000000000000000000000000000000000000)) (= _6 #x0000000000000000000000000000000000000000000000000000000000000000)))
(assert (not (= _revert_flag_2068_0 #x0000000000000000000000000000000000000000000000000000000000000000)))