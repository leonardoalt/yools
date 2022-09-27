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
(declare-fun _memory_2062_0 () (Array (_ BitVec 256) (_ BitVec 8)))
(declare-fun _storage_2063_0 () (Array (_ BitVec 256) (_ BitVec 256)))
(declare-fun _calldata_2064_0 ((_ BitVec 256)) (_ BitVec 8))
(declare-fun _keccak256_32_2065_0 ((_ BitVec 256)) (_ BitVec 256))
(declare-fun _keccak256_64_2066_0 ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))
(declare-fun _keccak256_2067_0 ((Array (_ BitVec 256) (_ BitVec 8)) (_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))
(define-fun _revert_flag_2068_0 () (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-fun _stop_flag_2069_0 () (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(assert (= ((_ extract 255 160) _address_2048_0) #x000000000000000000000000))

(define-const _1 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _2 (_ BitVec 256) (concat (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000000)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000001)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000002)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000003)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000004)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000005)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000006)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000007)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000008)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000009)) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000A)) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000B)) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000C)) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000D)) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000E)) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000F)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000010)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000011)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000012)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000013)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000014)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000015)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000016)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000017)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000018)) (_calldata_2064_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000019)) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001A)) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001B)) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001C)) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001D)) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001E)) (_calldata_2064_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001F))))
(define-const x_2_1 (_ BitVec 256) _2)
(define-const _3 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000001)
(define-const t_3_1 (_ BitVec 256) _3)

(define-const _4 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000002)
(define-const r_4_1 (_ BitVec 256) _4)

(define-const _5 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _6 (_ BitVec 256) (concat (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000000)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000001)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000002)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000003)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000004)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000005)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000006)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000007)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000008)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000009)) (_calldata_2064_0 (bvadd _5 #x000000000000000000000000000000000000000000000000000000000000000A)) (_calldata_2064_0 (bvadd _5 #x000000000000000000000000000000000000000000000000000000000000000B)) (_calldata_2064_0 (bvadd _5 #x000000000000000000000000000000000000000000000000000000000000000C)) (_calldata_2064_0 (bvadd _5 #x000000000000000000000000000000000000000000000000000000000000000D)) (_calldata_2064_0 (bvadd _5 #x000000000000000000000000000000000000000000000000000000000000000E)) (_calldata_2064_0 (bvadd _5 #x000000000000000000000000000000000000000000000000000000000000000F)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000010)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000011)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000012)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000013)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000014)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000015)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000016)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000017)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000018)) (_calldata_2064_0 (bvadd _5 #x0000000000000000000000000000000000000000000000000000000000000019)) (_calldata_2064_0 (bvadd _5 #x000000000000000000000000000000000000000000000000000000000000001A)) (_calldata_2064_0 (bvadd _5 #x000000000000000000000000000000000000000000000000000000000000001B)) (_calldata_2064_0 (bvadd _5 #x000000000000000000000000000000000000000000000000000000000000001C)) (_calldata_2064_0 (bvadd _5 #x000000000000000000000000000000000000000000000000000000000000001D)) (_calldata_2064_0 (bvadd _5 #x000000000000000000000000000000000000000000000000000000000000001E)) (_calldata_2064_0 (bvadd _5 #x000000000000000000000000000000000000000000000000000000000000001F))))
(define-const _7 (_ BitVec 256) (ite (= x_2_1 _6) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(assert (and (and (= _revert_flag_2068_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_flag_2069_0 #x0000000000000000000000000000000000000000000000000000000000000000)) (= #x0000000000000000000000000000000000000000000000000000000000000000 _7)))
(assert (not (= _revert_flag_2068_0 #x0000000000000000000000000000000000000000000000000000000000000000)))
