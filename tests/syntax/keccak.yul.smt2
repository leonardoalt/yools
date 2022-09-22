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

(define-const _1 (_ BitVec 256) _address_2048_0)
(define-const _2 (_ BitVec 256) _number_2057_0)
(define-const _3 (_ BitVec 256) _difficulty_2058_0)
(define-const _4 (_ BitVec 256) (ite (= _2 #x0000000000000000000000000000000000000000000000000000000000000020) (_keccak256_32 (concat (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000000)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000001)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000002)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000003)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000004)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000005)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000006)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000007)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000008)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000009)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000A)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000B)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000C)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000D)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000E)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000F)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000010)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000011)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000012)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000013)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000014)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000015)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000016)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000017)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000018)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000019)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001A)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001B)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001C)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001D)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001E)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001F)))) (ite (= _2 #x0000000000000000000000000000000000000000000000000000000000000040) (_keccak256_64 (concat (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000000)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000001)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000002)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000003)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000004)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000005)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000006)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000007)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000008)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000009)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000A)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000B)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000C)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000D)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000E)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000F)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000010)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000011)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000012)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000013)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000014)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000015)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000016)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000017)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000018)) (select _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000019)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001A)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001B)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001C)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001D)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001E)) (select _memory_1027_0 (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001F))) (concat (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000000)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000001)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000002)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000003)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000004)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000005)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000006)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000007)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000008)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000009)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x000000000000000000000000000000000000000000000000000000000000000A)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x000000000000000000000000000000000000000000000000000000000000000B)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x000000000000000000000000000000000000000000000000000000000000000C)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x000000000000000000000000000000000000000000000000000000000000000D)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x000000000000000000000000000000000000000000000000000000000000000E)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x000000000000000000000000000000000000000000000000000000000000000F)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000010)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000011)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000012)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000013)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000014)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000015)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000016)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000017)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000018)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x0000000000000000000000000000000000000000000000000000000000000019)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x000000000000000000000000000000000000000000000000000000000000001A)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x000000000000000000000000000000000000000000000000000000000000001B)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x000000000000000000000000000000000000000000000000000000000000001C)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x000000000000000000000000000000000000000000000000000000000000001D)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x000000000000000000000000000000000000000000000000000000000000001E)) (select _memory_1027_0 (bvadd (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000020) #x000000000000000000000000000000000000000000000000000000000000001F)))) (_keccak256 _memory_1027_0 _1 _2))))
(define-const x_2_1 (_ BitVec 256) _4)
(assert (not (= _revert_1024_0 #x0000000000000000000000000000000000000000000000000000000000000000)))
