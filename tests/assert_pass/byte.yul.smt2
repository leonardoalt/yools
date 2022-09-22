(define-const _revert_1024_0 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _stop_1025_0 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(declare-const _address_2048_0 (_ BitVec 256))
(declare-const _basefee_2061_0 (_ BitVec 256))
(declare-const _calldatasize_2052_0 (_ BitVec 256))
(declare-const _caller_2050_0 (_ BitVec 256))
(declare-const _callvalue_2051_0 (_ BitVec 256))
(declare-const _chainid_2060_0 (_ BitVec 256))
(declare-const _codesize_2053_0 (_ BitVec 256))
(declare-const _coinbase_2055_0 (_ BitVec 256))
(declare-const _difficulty_2058_0 (_ BitVec 256))
(declare-const _gaslimit_2059_0 (_ BitVec 256))
(declare-const _gasprice_2054_0 (_ BitVec 256))
(declare-const _number_2057_0 (_ BitVec 256))
(declare-const _origin_2049_0 (_ BitVec 256))
(declare-const _timestamp_2056_0 (_ BitVec 256))
(declare-const _memory_1027_0 (Array (_ BitVec 256) (_ BitVec 8)))
(declare-fun _calldata ((_ BitVec 256)) (_ BitVec 8))
(declare-fun _keccak256_32 ((_ BitVec 256)) (_ BitVec 256))
(declare-fun _keccak256_64 ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))
(declare-fun _keccak256 ((Array (_ BitVec 256) (_ BitVec 8)) (_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))
(declare-fun _storage_1028_0 () (Array (_ BitVec 256) (_ BitVec 256)))
(assert (= ((_ extract 255 160) _address_2048_0) #x000000000000000000000000))

(define-const _1 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000001234)
(define-const x_2_1 (_ BitVec 256) _1)
(define-const _2 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _3 (_ BitVec 256) (ite (bvugt _2 #x000000000000000000000000000000000000000000000000000000000000001f) #x0000000000000000000000000000000000000000000000000000000000000000 (bvand #x00000000000000000000000000000000000000000000000000000000000000ff (bvlshr x_2_1 (bvsub #x00000000000000000000000000000000000000000000000000000000000000f8 (bvmul #x0000000000000000000000000000000000000000000000000000000000000008 _2))))))
(define-const _4 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _5 (_ BitVec 256) (ite (= _3 _4) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(assert (and (and (= _revert_1024_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_1025_0 #x0000000000000000000000000000000000000000000000000000000000000000)) (= #x0000000000000000000000000000000000000000000000000000000000000000 _5)))
(define-const _6 (_ BitVec 256) #x000000000000000000000000000000000000000000000000000000000000001D)
(define-const _7 (_ BitVec 256) (ite (bvugt _6 #x000000000000000000000000000000000000000000000000000000000000001f) #x0000000000000000000000000000000000000000000000000000000000000000 (bvand #x00000000000000000000000000000000000000000000000000000000000000ff (bvlshr x_2_1 (bvsub #x00000000000000000000000000000000000000000000000000000000000000f8 (bvmul #x0000000000000000000000000000000000000000000000000000000000000008 _6))))))
(define-const _8 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _9 (_ BitVec 256) (ite (= _7 _8) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(assert (and (and (= _revert_1024_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_1025_0 #x0000000000000000000000000000000000000000000000000000000000000000)) (= #x0000000000000000000000000000000000000000000000000000000000000000 _9)))
(define-const _10 (_ BitVec 256) #x000000000000000000000000000000000000000000000000000000000000001E)
(define-const _11 (_ BitVec 256) (ite (bvugt _10 #x000000000000000000000000000000000000000000000000000000000000001f) #x0000000000000000000000000000000000000000000000000000000000000000 (bvand #x00000000000000000000000000000000000000000000000000000000000000ff (bvlshr x_2_1 (bvsub #x00000000000000000000000000000000000000000000000000000000000000f8 (bvmul #x0000000000000000000000000000000000000000000000000000000000000008 _10))))))
(define-const _12 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000012)
(define-const _13 (_ BitVec 256) (ite (= _11 _12) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(assert (and (and (= _revert_1024_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_1025_0 #x0000000000000000000000000000000000000000000000000000000000000000)) (= #x0000000000000000000000000000000000000000000000000000000000000000 _13)))
(define-const _14 (_ BitVec 256) #x000000000000000000000000000000000000000000000000000000000000001F)
(define-const _15 (_ BitVec 256) (ite (bvugt _14 #x000000000000000000000000000000000000000000000000000000000000001f) #x0000000000000000000000000000000000000000000000000000000000000000 (bvand #x00000000000000000000000000000000000000000000000000000000000000ff (bvlshr x_2_1 (bvsub #x00000000000000000000000000000000000000000000000000000000000000f8 (bvmul #x0000000000000000000000000000000000000000000000000000000000000008 _14))))))
(define-const _16 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000034)
(define-const _17 (_ BitVec 256) (ite (= _15 _16) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(assert (and (and (= _revert_1024_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_1025_0 #x0000000000000000000000000000000000000000000000000000000000000000)) (= #x0000000000000000000000000000000000000000000000000000000000000000 _17)))
(define-const _18 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000020)
(define-const _19 (_ BitVec 256) (ite (bvugt _18 #x000000000000000000000000000000000000000000000000000000000000001f) #x0000000000000000000000000000000000000000000000000000000000000000 (bvand #x00000000000000000000000000000000000000000000000000000000000000ff (bvlshr x_2_1 (bvsub #x00000000000000000000000000000000000000000000000000000000000000f8 (bvmul #x0000000000000000000000000000000000000000000000000000000000000008 _18))))))
(define-const _20 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _21 (_ BitVec 256) (ite (= _19 _20) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(assert (and (and (= _revert_1024_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_1025_0 #x0000000000000000000000000000000000000000000000000000000000000000)) (= #x0000000000000000000000000000000000000000000000000000000000000000 _21)))
(define-const _22 (_ BitVec 256) #x00000000000000000000000000000000000000ffffffffffffffffffffffffff)
(define-const _23 (_ BitVec 256) (ite (bvugt _22 #x000000000000000000000000000000000000000000000000000000000000001f) #x0000000000000000000000000000000000000000000000000000000000000000 (bvand #x00000000000000000000000000000000000000000000000000000000000000ff (bvlshr x_2_1 (bvsub #x00000000000000000000000000000000000000000000000000000000000000f8 (bvmul #x0000000000000000000000000000000000000000000000000000000000000008 _22))))))
(define-const _24 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _25 (_ BitVec 256) (ite (= _23 _24) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(assert (and (and (= _revert_1024_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_1025_0 #x0000000000000000000000000000000000000000000000000000000000000000)) (= #x0000000000000000000000000000000000000000000000000000000000000000 _25)))
(assert (not (= _revert_1024_0 #x0000000000000000000000000000000000000000000000000000000000000000)))
