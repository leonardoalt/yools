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

(define-const _1 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000001)
(define-const _2 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000002)
(declare-const a_3_0 (_ BitVec 256))
(declare-const b_4_0 (_ BitVec 256))
(define-const _3 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const c_5_1 (_ BitVec 256) _3)
(define-const d_6_1 (_ BitVec 256) _3)
(define-const c_5_2 (_ BitVec 256) a_3_0)
(define-const d_6_2 (_ BitVec 256) b_4_0)
(assert (= _1 a_3_0))
(assert (= _2 b_4_0))
(define-const x_7_1 (_ BitVec 256) c_5_2)
(define-const y_8_1 (_ BitVec 256) d_6_2)
(declare-const a_3_1 (_ BitVec 256))
(declare-const b_4_1 (_ BitVec 256))
(define-const _4 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const c_5_4 (_ BitVec 256) _4)
(define-const d_6_4 (_ BitVec 256) _4)
(define-const c_5_5 (_ BitVec 256) a_3_1)
(define-const d_6_5 (_ BitVec 256) b_4_1)
(assert (= x_7_1 a_3_1))
(assert (= y_8_1 b_4_1))
(define-const t_9_1 (_ BitVec 256) c_5_5)
(define-const s_10_1 (_ BitVec 256) d_6_5)
(assert (not (= _revert_1024_0 #x0000000000000000000000000000000000000000000000000000000000000000)))