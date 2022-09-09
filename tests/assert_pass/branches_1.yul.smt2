(define-const _revert_1024_0 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _stop_1025_0 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(declare-const _address_1026_0 (_ BitVec 256))
(declare-const _basefee_1039_0 (_ BitVec 256))
(declare-const _calldatasize_1030_0 (_ BitVec 256))
(declare-const _caller_1028_0 (_ BitVec 256))
(declare-const _callvalue_1029_0 (_ BitVec 256))
(declare-const _chainid_1038_0 (_ BitVec 256))
(declare-const _codesize_1031_0 (_ BitVec 256))
(declare-const _coinbase_1033_0 (_ BitVec 256))
(declare-const _difficulty_1036_0 (_ BitVec 256))
(declare-const _gaslimit_1037_0 (_ BitVec 256))
(declare-const _gasprice_1032_0 (_ BitVec 256))
(declare-const _number_1035_0 (_ BitVec 256))
(declare-const _origin_1027_0 (_ BitVec 256))
(declare-const _timestamp_1034_0 (_ BitVec 256))
(assert (= ((_ extract 255 160) _address_1026_0) #x000000000000000000000000))

(define-const _1 (_ BitVec 256) _address_1026_0)
(define-const x_2_1 (_ BitVec 256) _1)
(define-const _2 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000014)
(define-const t_3_1 (_ BitVec 256) _2)
(define-const _3 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000002)
(define-const _4 (_ BitVec 256) (ite (bvult x_2_1 _3) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(define-const _5 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000007)
(define-const t_3_2 (_ BitVec 256) _5)
(define-const t_3_3 (_ BitVec 256) (ite (= _4 #x0000000000000000000000000000000000000000000000000000000000000000) t_3_1 t_3_2))

(define-const _6 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000001)
(define-const _7 (_ BitVec 256) (ite (bvugt x_2_1 _6) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(define-const _8 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000008)
(define-const t_3_4 (_ BitVec 256) _8)
(define-const t_3_5 (_ BitVec 256) (ite (= _7 #x0000000000000000000000000000000000000000000000000000000000000000) t_3_3 t_3_4))

(define-const _9 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000009)
(define-const _10 (_ BitVec 256) (ite (bvult t_3_5 _9) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(define-const r_4_1 (_ BitVec 256) _10)
(define-const _11 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000001)
(define-const _12 (_ BitVec 256) (ite (= r_4_1 _11) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(assert (and (and (= _revert_1024_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_1025_0 #x0000000000000000000000000000000000000000000000000000000000000000)) (= #x0000000000000000000000000000000000000000000000000000000000000000 _12)))
(assert (not (= _revert_1024_0 #x0000000000000000000000000000000000000000000000000000000000000000)))