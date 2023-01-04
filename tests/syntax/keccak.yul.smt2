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
(define-const _1 (_ BitVec 256) _address_2048_0)
(define-const _2 (_ BitVec 256) _number_2059_0)
(define-const _3 (_ BitVec 256) _difficulty_2056_0)
(define-const _4 (_ BitVec 256) (ite (= _2 (_ bv32 256)) (_keccak256_32_2066_0 (concat (select _memory_2063_0 (bvadd _1 (_ bv0 256))) (select _memory_2063_0 (bvadd _1 (_ bv1 256))) (select _memory_2063_0 (bvadd _1 (_ bv2 256))) (select _memory_2063_0 (bvadd _1 (_ bv3 256))) (select _memory_2063_0 (bvadd _1 (_ bv4 256))) (select _memory_2063_0 (bvadd _1 (_ bv5 256))) (select _memory_2063_0 (bvadd _1 (_ bv6 256))) (select _memory_2063_0 (bvadd _1 (_ bv7 256))) (select _memory_2063_0 (bvadd _1 (_ bv8 256))) (select _memory_2063_0 (bvadd _1 (_ bv9 256))) (select _memory_2063_0 (bvadd _1 (_ bv10 256))) (select _memory_2063_0 (bvadd _1 (_ bv11 256))) (select _memory_2063_0 (bvadd _1 (_ bv12 256))) (select _memory_2063_0 (bvadd _1 (_ bv13 256))) (select _memory_2063_0 (bvadd _1 (_ bv14 256))) (select _memory_2063_0 (bvadd _1 (_ bv15 256))) (select _memory_2063_0 (bvadd _1 (_ bv16 256))) (select _memory_2063_0 (bvadd _1 (_ bv17 256))) (select _memory_2063_0 (bvadd _1 (_ bv18 256))) (select _memory_2063_0 (bvadd _1 (_ bv19 256))) (select _memory_2063_0 (bvadd _1 (_ bv20 256))) (select _memory_2063_0 (bvadd _1 (_ bv21 256))) (select _memory_2063_0 (bvadd _1 (_ bv22 256))) (select _memory_2063_0 (bvadd _1 (_ bv23 256))) (select _memory_2063_0 (bvadd _1 (_ bv24 256))) (select _memory_2063_0 (bvadd _1 (_ bv25 256))) (select _memory_2063_0 (bvadd _1 (_ bv26 256))) (select _memory_2063_0 (bvadd _1 (_ bv27 256))) (select _memory_2063_0 (bvadd _1 (_ bv28 256))) (select _memory_2063_0 (bvadd _1 (_ bv29 256))) (select _memory_2063_0 (bvadd _1 (_ bv30 256))) (select _memory_2063_0 (bvadd _1 (_ bv31 256))))) (ite (= _2 (_ bv64 256)) (_keccak256_64_2067_0 (concat (select _memory_2063_0 (bvadd _1 (_ bv0 256))) (select _memory_2063_0 (bvadd _1 (_ bv1 256))) (select _memory_2063_0 (bvadd _1 (_ bv2 256))) (select _memory_2063_0 (bvadd _1 (_ bv3 256))) (select _memory_2063_0 (bvadd _1 (_ bv4 256))) (select _memory_2063_0 (bvadd _1 (_ bv5 256))) (select _memory_2063_0 (bvadd _1 (_ bv6 256))) (select _memory_2063_0 (bvadd _1 (_ bv7 256))) (select _memory_2063_0 (bvadd _1 (_ bv8 256))) (select _memory_2063_0 (bvadd _1 (_ bv9 256))) (select _memory_2063_0 (bvadd _1 (_ bv10 256))) (select _memory_2063_0 (bvadd _1 (_ bv11 256))) (select _memory_2063_0 (bvadd _1 (_ bv12 256))) (select _memory_2063_0 (bvadd _1 (_ bv13 256))) (select _memory_2063_0 (bvadd _1 (_ bv14 256))) (select _memory_2063_0 (bvadd _1 (_ bv15 256))) (select _memory_2063_0 (bvadd _1 (_ bv16 256))) (select _memory_2063_0 (bvadd _1 (_ bv17 256))) (select _memory_2063_0 (bvadd _1 (_ bv18 256))) (select _memory_2063_0 (bvadd _1 (_ bv19 256))) (select _memory_2063_0 (bvadd _1 (_ bv20 256))) (select _memory_2063_0 (bvadd _1 (_ bv21 256))) (select _memory_2063_0 (bvadd _1 (_ bv22 256))) (select _memory_2063_0 (bvadd _1 (_ bv23 256))) (select _memory_2063_0 (bvadd _1 (_ bv24 256))) (select _memory_2063_0 (bvadd _1 (_ bv25 256))) (select _memory_2063_0 (bvadd _1 (_ bv26 256))) (select _memory_2063_0 (bvadd _1 (_ bv27 256))) (select _memory_2063_0 (bvadd _1 (_ bv28 256))) (select _memory_2063_0 (bvadd _1 (_ bv29 256))) (select _memory_2063_0 (bvadd _1 (_ bv30 256))) (select _memory_2063_0 (bvadd _1 (_ bv31 256)))) (concat (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv0 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv1 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv2 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv3 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv4 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv5 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv6 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv7 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv8 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv9 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv10 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv11 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv12 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv13 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv14 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv15 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv16 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv17 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv18 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv19 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv20 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv21 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv22 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv23 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv24 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv25 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv26 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv27 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv28 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv29 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv30 256))) (select _memory_2063_0 (bvadd (bvadd _1 (_ bv32 256)) (_ bv31 256))))) (_keccak256_2068_0 _memory_2063_0 _1 _2))))
(define-const x_2_1 (_ BitVec 256) _4)
(assert (not (= _revert_flag_2070_0 (_ bv0 256))))