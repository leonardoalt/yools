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
(assert (= ((_ extract 255 160) _address_2048_0) #x000000000000000000000000))

(define-const _1 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _2 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000008)
(define-const _memory_1027_1 (Array (_ BitVec 256) (_ BitVec 8)) (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store _memory_1027_0 (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000000) ((_ extract 255 248) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000001) ((_ extract 247 240) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000002) ((_ extract 239 232) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000003) ((_ extract 231 224) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000004) ((_ extract 223 216) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000005) ((_ extract 215 208) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000006) ((_ extract 207 200) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000007) ((_ extract 199 192) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000008) ((_ extract 191 184) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000009) ((_ extract 183 176) _2)) (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000A) ((_ extract 175 168) _2)) (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000B) ((_ extract 167 160) _2)) (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000C) ((_ extract 159 152) _2)) (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000D) ((_ extract 151 144) _2)) (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000E) ((_ extract 143 136) _2)) (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000000F) ((_ extract 135 128) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000010) ((_ extract 127 120) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000011) ((_ extract 119 112) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000012) ((_ extract 111 104) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000013) ((_ extract 103 96) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000014) ((_ extract 95 88) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000015) ((_ extract 87 80) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000016) ((_ extract 79 72) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000017) ((_ extract 71 64) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000018) ((_ extract 63 56) _2)) (bvadd _1 #x0000000000000000000000000000000000000000000000000000000000000019) ((_ extract 55 48) _2)) (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001A) ((_ extract 47 40) _2)) (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001B) ((_ extract 39 32) _2)) (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001C) ((_ extract 31 24) _2)) (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001D) ((_ extract 23 16) _2)) (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001E) ((_ extract 15 8) _2)) (bvadd _1 #x000000000000000000000000000000000000000000000000000000000000001F) ((_ extract 7 0) _2)))
(define-const _3 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000000)
(define-const _4 (_ BitVec 256) (concat (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000000)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000001)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000002)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000003)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000004)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000005)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000006)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000007)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000008)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000009)) (select _memory_1027_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000000A)) (select _memory_1027_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000000B)) (select _memory_1027_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000000C)) (select _memory_1027_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000000D)) (select _memory_1027_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000000E)) (select _memory_1027_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000000F)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000010)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000011)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000012)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000013)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000014)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000015)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000016)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000017)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000018)) (select _memory_1027_1 (bvadd _3 #x0000000000000000000000000000000000000000000000000000000000000019)) (select _memory_1027_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000001A)) (select _memory_1027_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000001B)) (select _memory_1027_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000001C)) (select _memory_1027_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000001D)) (select _memory_1027_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000001E)) (select _memory_1027_1 (bvadd _3 #x000000000000000000000000000000000000000000000000000000000000001F))))
(define-const x_2_1 (_ BitVec 256) _4)
(define-const _5 (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000008)
(define-const _6 (_ BitVec 256) (ite (= x_2_1 _5) #x0000000000000000000000000000000000000000000000000000000000000001 #x0000000000000000000000000000000000000000000000000000000000000000))
(assert (and (and (= _revert_1024_0 #x0000000000000000000000000000000000000000000000000000000000000000) (= _stop_1025_0 #x0000000000000000000000000000000000000000000000000000000000000000)) (= #x0000000000000000000000000000000000000000000000000000000000000000 _6)))
(assert (not (= _revert_1024_0 #x0000000000000000000000000000000000000000000000000000000000000000)))
