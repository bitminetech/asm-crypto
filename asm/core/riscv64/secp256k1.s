/*
 * secp256k1 for RISC-V (RISC-V ELF psABI, LP64D): public keys, point
 * decompression, ECDH, and ECDSA signing (RFC 6979 nonces, low s) and
 * verification. Baseline RV64GC instructions only: carries and borrows come
 * from sltu. Values at addresses that may not be 8-byte aligned are read and
 * written one byte at a time.
 * Requirements: docs/reference/secp256k1.md. Layouts: include/secp256k1.inc.
 *
 * Numbers are 4 limbs of 64 bits, least significant first. Products use
 * Montgomery multiplication (CIOS) for both p and n. Points use projective
 * coordinates and the complete formulas of Renes, Costello and Batina
 * (algorithms 7 and 9, a = 0), so no point needs a special case. The scalar
 * multiplication doubles and adds for all 256 bits and picks the sum with a
 * mask. No branch or address depends on a private key or a nonce.
 */
.set ISA_RISCV64, 1
.include "crypto.inc"
.include "secp256k1.inc"
.include "platform.inc"

/* Frame of a non-leaf function: locals at sp, then ra and s0-s11. */
.macro ENTER locals
    addi    sp, sp, -(\locals + 112)
    UNWIND_ALLOC (\locals + 112)
    sd      ra, \locals(sp)
    UNWIND_SAVE ra, \locals
    sd      s0, \locals+8(sp)
    UNWIND_SAVE s0, \locals+8
    sd      s1, \locals+16(sp)
    UNWIND_SAVE s1, \locals+16
    sd      s2, \locals+24(sp)
    UNWIND_SAVE s2, \locals+24
    sd      s3, \locals+32(sp)
    UNWIND_SAVE s3, \locals+32
    sd      s4, \locals+40(sp)
    UNWIND_SAVE s4, \locals+40
    sd      s5, \locals+48(sp)
    UNWIND_SAVE s5, \locals+48
    sd      s6, \locals+56(sp)
    UNWIND_SAVE s6, \locals+56
    sd      s7, \locals+64(sp)
    UNWIND_SAVE s7, \locals+64
    sd      s8, \locals+72(sp)
    UNWIND_SAVE s8, \locals+72
    sd      s9, \locals+80(sp)
    UNWIND_SAVE s9, \locals+80
    sd      s10, \locals+88(sp)
    UNWIND_SAVE s10, \locals+88
    sd      s11, \locals+96(sp)
    UNWIND_SAVE s11, \locals+96
    UNWIND_END_PROLOGUE
.endm

.macro LEAVE locals
    UNWIND_BEGIN_EPILOGUE
    ld      ra, \locals(sp)
    UNWIND_RESTORE ra
    ld      s0, \locals+8(sp)
    UNWIND_RESTORE s0
    ld      s1, \locals+16(sp)
    UNWIND_RESTORE s1
    ld      s2, \locals+24(sp)
    UNWIND_RESTORE s2
    ld      s3, \locals+32(sp)
    UNWIND_RESTORE s3
    ld      s4, \locals+40(sp)
    UNWIND_RESTORE s4
    ld      s5, \locals+48(sp)
    UNWIND_RESTORE s5
    ld      s6, \locals+56(sp)
    UNWIND_RESTORE s6
    ld      s7, \locals+64(sp)
    UNWIND_RESTORE s7
    ld      s8, \locals+72(sp)
    UNWIND_RESTORE s8
    ld      s9, \locals+80(sp)
    UNWIND_RESTORE s9
    ld      s10, \locals+88(sp)
    UNWIND_RESTORE s10
    ld      s11, \locals+96(sp)
    UNWIND_RESTORE s11
    addi    sp, sp, (\locals + 112)
    UNWIND_FREE (\locals + 112)
    UNWIND_END_EPILOGUE
    ret
.endm

/* ---------------------------------------------------------------- Macros */

/* fn(sp + d, sp + a, sp + b, modulus record m). */
.macro OP fn, d, a, b, m
    addi    a0, sp, \d
    addi    a1, sp, \a
    addi    a2, sp, \b
    mv      a3, \m
    call    \fn
.endm

.macro FMUL d, a, b, m=s11
    OP      crypto_secp256k1_mod_mul, \d, \a, \b, \m
.endm

.macro FADD d, a, b, m=s11
    OP      crypto_secp256k1_mod_add, \d, \a, \b, \m
.endm

.macro FSUB d, a, b, m=s11
    OP      crypto_secp256k1_mod_sub, \d, \a, \b, \m
.endm

/* sp + d = b3 * (sp + a) mod p, with b3 = 21 in Montgomery form at s10. */
.macro FMULB3 d, a
    addi    a0, sp, \d
    mv      a1, s10
    addi    a2, sp, \a
    mv      a3, s11
    call    crypto_secp256k1_mod_mul
.endm

/* Copy 32 bytes from soff(src) to doff(dst), both 8-byte aligned. Uses t0. */
.macro COPY dst, doff, src, soff
    .irp i, 0, 8, 16, 24
    ld      t0, \soff+\i(\src)
    sd      t0, \doff+\i(\dst)
    .endr
.endm

/* d = the 8 bytes at off(base) as a big-endian number. Uses tmp. */
.macro LOAD_BE64 d, base, off, tmp
    lbu     \d, \off(\base)
    .irp k, 1, 2, 3, 4, 5, 6, 7
    slli    \d, \d, 8
    lbu     \tmp, \off+\k(\base)
    or      \d, \d, \tmp
    .endr
.endm

/* The 8 bytes at off(base) = s as a big-endian number. Uses tmp. */
.macro STORE_BE64 s, base, off, tmp
    .irp k, 0, 1, 2, 3, 4, 5, 6, 7
    srli    \tmp, \s, 56 - 8 * \k
    sb      \tmp, \off+\k(\base)
    .endr
.endm

/* a4 to a7 = the 32 big-endian bytes at off(src), as limbs. Uses t6. */
.macro LOAD_BE src, off=0
    LOAD_BE64 a7, \src, \off, t6
    LOAD_BE64 a6, \src, \off+8, t6
    LOAD_BE64 a5, \src, \off+16, t6
    LOAD_BE64 a4, \src, \off+24, t6
.endm

/* The limbs a4 to a7 as 32 big-endian bytes at off(dst). Uses t6. */
.macro STORE_BE dst, off=0
    STORE_BE64 a7, \dst, \off, t6
    STORE_BE64 a6, \dst, \off+8, t6
    STORE_BE64 a5, \dst, \off+16, t6
    STORE_BE64 a4, \dst, \off+24, t6
.endm

.macro LOAD_LIMBS src, off=0
    ld      a4, \off(\src)
    ld      a5, \off+8(\src)
    ld      a6, \off+16(\src)
    ld      a7, \off+24(\src)
.endm

.macro STORE_LIMBS dst, off=0
    sd      a4, \off(\dst)
    sd      a5, \off+8(\dst)
    sd      a6, \off+16(\dst)
    sd      a7, \off+24(\dst)
.endm

/* Borrow chain step: t0 = the borrow of limb - (off(m)) - t0. Uses tmp, t2, t3. */
.macro BORROW limb, tmp, off, m
    ld      \tmp, \off(\m)
    sltu    t2, \limb, \tmp
    sub     t3, \limb, \tmp
    sltu    t3, t3, t0
    or      t0, t2, t3
.endm

/* Borrow chain step: t0 = the borrow of (off(m)) - limb - t0. Uses tmp, t2, t3. */
.macro BORROW_REV limb, tmp, off, m
    ld      \tmp, \off(\m)
    sltu    t2, \tmp, \limb
    sub     t3, \tmp, \limb
    sltu    t3, t3, t0
    or      t0, t2, t3
.endm

/* t0 = 1 when the limbs a4 to a7 are below the 4 limbs at m, else 0. Uses t1 to t3. */
.macro BELOW m
    ld      t1, 0(\m)
    sltu    t0, a4, t1
    BORROW  a5, t1, 8, \m
    BORROW  a6, t1, 16, \m
    BORROW  a7, t1, 24, \m
.endm

/* t0 = 1 when the limbs a4 to a7 are above the 4 limbs at m, else 0. Uses t1 to t3. */
.macro ABOVE m
    ld      t1, 0(\m)
    sltu    t0, t1, a4
    BORROW_REV a5, t1, 8, \m
    BORROW_REV a6, t1, 16, \m
    BORROW_REV a7, t1, 24, \m
.endm

/* Jump to label when the limbs a4 to a7 are all zero. Uses t0. */
.macro IF_ZERO label
    or      t0, a4, a5
    or      t0, t0, a6
    or      t0, t0, a7
    beqz    t0, \label
.endm

/* The limbs a4 to a7 minus n when they are n or more (they are below 2n). Uses t0 to t6. */
.macro REDUCE_N m
    ld      t5, 0(\m)
    sltu    t4, a4, t5
    sub     t0, a4, t5
    ld      t5, 8(\m)
    sltu    t6, a5, t5
    sub     t1, a5, t5
    sltu    t5, t1, t4
    sub     t1, t1, t4
    or      t4, t6, t5
    ld      t5, 16(\m)
    sltu    t6, a6, t5
    sub     t2, a6, t5
    sltu    t5, t2, t4
    sub     t2, t2, t4
    or      t4, t6, t5
    ld      t5, 24(\m)
    sltu    t6, a7, t5
    sub     t3, a7, t5
    sltu    t5, t3, t4
    sub     t3, t3, t4
    or      t4, t6, t5
    addi    t4, t4, -1
    xor     t5, t0, a4
    and     t5, t5, t4
    xor     a4, a4, t5
    xor     t5, t1, a5
    and     t5, t5, t4
    xor     a5, a5, t5
    xor     t5, t2, a6
    and     t5, t5, t4
    xor     a6, a6, t5
    xor     t5, t3, a7
    and     t5, t5, t4
    xor     a7, a7, t5
.endm

/* The point G at sp + off: x, y and Z = 1, in Montgomery form. Uses t0, t1. */
.macro LOAD_G off
    lla     t1, 322f
    COPY    sp, \off, t1, 0
    COPY    sp, \off+32, t1, 32
    lla     t1, 320f
    COPY    sp, \off+64, t1, CRYPTO_SECP256K1_MOD_ONE
.endm

/* The 32 bytes at sp + off = the number 1, or 0. */
.macro SET_ONE off
    li      t0, 1
    sd      t0, \off(sp)
    sd      zero, \off+8(sp)
    sd      zero, \off+16(sp)
    sd      zero, \off+24(sp)
.endm

.macro SET_ZERO off
    sd      zero, \off(sp)
    sd      zero, \off+8(sp)
    sd      zero, \off+16(sp)
    sd      zero, \off+24(sp)
.endm

/* Store the compressed point: prefix 2 or 3 from the parity of y, then x, from the affine x, y at sp + off. */
.macro STORE_COMPRESSED dst, off
    ld      t0, \off+32(sp)
    andi    t0, t0, 1
    ori     t0, t0, 2
    sb      t0, 0(\dst)
    LOAD_LIMBS sp, \off
    STORE_BE \dst, 1
.endm

/* ---------------------------------------------------------------- Public keys and ECDH */

.set K_D, 0
.set K_G, 32
.set K_Q, 128
.set K_XY, 224
.set K_FRAME, 288

/*
 * crypto_secp256k1_public_key(private_key, public_key) -> status
 * s1 private_key, s2 public_key.
 */
FUNCTION crypto_secp256k1_public_key
    ENTER   K_FRAME
    mv      s1, a0
    mv      s2, a1
    LOAD_BE s1
    li      a0, CRYPTO_INVALID_PRIVATE_KEY
    IF_ZERO 9f
    lla     t5, 321f
    BELOW   t5
    li      a0, CRYPTO_INVALID_PRIVATE_KEY
    beqz    t0, 9f
    STORE_LIMBS sp, K_D
    LOAD_G  K_G
    addi    a0, sp, K_Q
    addi    a1, sp, K_D
    addi    a2, sp, K_G
    call    crypto_secp256k1_point_mul
    addi    a0, sp, K_XY
    addi    a1, sp, K_Q
    call    crypto_secp256k1_point_affine
    STORE_COMPRESSED s2, K_XY
    li      a0, CRYPTO_OK
9:  LEAVE   K_FRAME
END_FUNCTION crypto_secp256k1_public_key

/*
 * crypto_secp256k1_decompress(public_key, point) -> status
 * s1 public_key, s2 point. The point at sp, x and y at sp + 96.
 */
FUNCTION crypto_secp256k1_decompress
    ENTER   160
    mv      s1, a0
    mv      s2, a1
    mv      a0, sp
    mv      a1, s1
    call    crypto_secp256k1_lift_x
    bnez    a0, 9f
    addi    a0, sp, 96
    mv      a1, sp
    call    crypto_secp256k1_point_affine
    LOAD_LIMBS sp, 96
    STORE_BE s2, 0
    LOAD_LIMBS sp, 128
    STORE_BE s2, 32
    li      a0, CRYPTO_OK
9:  LEAVE   160
END_FUNCTION crypto_secp256k1_decompress

.set E_P, 0
.set E_S, 96
.set E_D, 192
.set E_XY, 224
.set E_FRAME, 288

/*
 * crypto_secp256k1_ecdh(public_key, private_key, shared) -> status
 * s1 public_key, s2 private_key, s3 shared.
 */
FUNCTION crypto_secp256k1_ecdh
    ENTER   E_FRAME
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    addi    a0, sp, E_P
    mv      a1, s1
    call    crypto_secp256k1_lift_x
    bnez    a0, 9f
    LOAD_BE s2
    li      a0, CRYPTO_INVALID_PRIVATE_KEY
    IF_ZERO 9f
    lla     t5, 321f
    BELOW   t5
    li      a0, CRYPTO_INVALID_PRIVATE_KEY
    beqz    t0, 9f
    STORE_LIMBS sp, E_D
    addi    a0, sp, E_S
    addi    a1, sp, E_D
    addi    a2, sp, E_P
    call    crypto_secp256k1_point_mul
    addi    a0, sp, E_XY
    addi    a1, sp, E_S
    call    crypto_secp256k1_point_affine
    STORE_COMPRESSED s3, E_XY
    li      a0, CRYPTO_OK
9:  LEAVE   E_FRAME
END_FUNCTION crypto_secp256k1_ecdh

/* ---------------------------------------------------------------- ECDSA */

.set S_KL, 0            /* K as a ByteList: 24 bytes of header, then K */
.set S_ML, 64           /* the HMAC message as a ByteList: V, a byte, x, h */
.set S_SCR, 192         /* HMAC scratch, 200 bytes */
.set S_OUT, 392         /* HMAC output */
.set S_D, 424           /* the private key d */
.set S_Z, 456           /* the hash, mod n */
.set S_K, 488           /* the nonce k */
.set S_G, 520
.set S_R, 616           /* k * G */
.set S_XY, 712
.set S_RR, 776          /* r */
.set S_S, 808           /* s */
.set S_T1, 840
.set S_T2, 872
.set S_T3, 904
.set S_ONE, 936
.set S_R2, 968          /* 2^512 mod n */
.set S_FRAME, 1008
.set S_V, S_ML + 24
.set S_SEP, S_ML + 56

/* K or V (dst) = HMAC-SHA-256 with key K of the first count bytes of the message. */
.macro HMAC_STEP count, dst
    li      t0, \count
    sd      t0, S_ML+CRYPTO_BYTES_COUNT(sp)
    li      t0, 200
    sd      t0, S_SCR(sp)
    addi    a0, sp, S_KL
    addi    a1, sp, S_ML
    addi    a2, sp, S_SCR
    addi    a3, sp, S_OUT
    CALL_GLOBAL crypto_hmac_sha256
    COPY    sp, \dst, sp, S_OUT
.endm

/* limb = off(s9) - limb - borrow t4, the new borrow in t4. Uses t1, t5, t6. */
.macro NEGATE limb, off
    ld      t1, \off(s9)
    sltu    t5, t1, \limb
    sub     \limb, t1, \limb
    sltu    t6, \limb, t4
    sub     \limb, \limb, t4
    or      t4, t5, t6
.endm

/*
 * crypto_secp256k1_sign(private_key, hash, signature) -> status
 * s1 private_key, s2 hash, s3 signature, s9 n record.
 * The nonce follows RFC 6979 section 3.2 with HMAC-SHA-256, qlen = hlen = 256.
 */
FUNCTION crypto_secp256k1_sign
    ENTER   S_FRAME
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    lla     s9, 321f
    LOAD_BE s1
    li      a0, CRYPTO_INVALID_PRIVATE_KEY
    IF_ZERO 9f
    BELOW   s9
    li      a0, CRYPTO_INVALID_PRIVATE_KEY
    beqz    t0, 9f
    STORE_LIMBS sp, S_D
    LOAD_BE s2
    REDUCE_N s9
    STORE_LIMBS sp, S_Z
    STORE_BE sp, S_ML+24+33+32              # bits2octets(h)
    li      t1, 0                           # int2octets(x): the key bytes
31: add     t2, s1, t1
    lbu     t3, 0(t2)
    add     t2, sp, t1
    sb      t3, S_ML+24+33(t2)
    addi    t1, t1, 1
    li      t4, 32
    bltu    t1, t4, 31b
    SET_ONE S_ONE
    COPY    sp, S_R2, s9, CRYPTO_SECP256K1_MOD_R2
    LOAD_G  S_G
    li      t0, CRYPTO_BYTES_FIXED + 32     # K = 0x00 * 32
    sd      t0, S_KL+CRYPTO_BYTES_SIZE(sp)
    li      t0, CRYPTO_BYTES_FIXED
    sd      t0, S_KL+CRYPTO_BYTES_OFFSET(sp)
    li      t0, 32
    sd      t0, S_KL+CRYPTO_BYTES_COUNT(sp)
    SET_ZERO S_KL+24
    li      t0, 128                         # V = 0x01 * 32
    sd      t0, S_ML+CRYPTO_BYTES_SIZE(sp)
    li      t0, CRYPTO_BYTES_FIXED
    sd      t0, S_ML+CRYPTO_BYTES_OFFSET(sp)
    li      t0, 0x0101010101010101
    sd      t0, S_V(sp)
    sd      t0, S_V+8(sp)
    sd      t0, S_V+16(sp)
    sd      t0, S_V+24(sp)
    sb      zero, S_SEP(sp)                 # K = HMAC_K(V || 0x00 || x || h)
    HMAC_STEP 97, S_KL+24
    HMAC_STEP 32, S_V                       # V = HMAC_K(V)
    li      t0, 1
    sb      t0, S_SEP(sp)                   # K = HMAC_K(V || 0x01 || x || h)
    HMAC_STEP 97, S_KL+24
    HMAC_STEP 32, S_V

    /* T = V = HMAC_K(V); k = bits2int(T), used when 1 <= k < n. */
1:  HMAC_STEP 32, S_V
    LOAD_BE sp, S_V
    IF_ZERO 8f
    BELOW   s9
    beqz    t0, 8f
    STORE_LIMBS sp, S_K
    addi    a0, sp, S_R
    addi    a1, sp, S_K
    addi    a2, sp, S_G
    call    crypto_secp256k1_point_mul
    addi    a0, sp, S_XY
    addi    a1, sp, S_R
    call    crypto_secp256k1_point_affine
    LOAD_LIMBS sp, S_XY                     # r = x mod n
    REDUCE_N s9
    IF_ZERO 8f
    STORE_LIMBS sp, S_RR
    FMUL    S_T1, S_RR, S_R2, s9            # s = k^-1 (z + r d) mod n, Montgomery form
    FMUL    S_T2, S_D, S_R2, s9
    FMUL    S_T1, S_T1, S_T2, s9
    FMUL    S_T2, S_Z, S_R2, s9
    FADD    S_T1, S_T1, S_T2, s9
    FMUL    S_T2, S_K, S_R2, s9
    addi    a0, sp, S_T3
    addi    a1, sp, S_T2
    lla     a2, 327f
    mv      a3, s9
    call    crypto_secp256k1_mod_pow
    FMUL    S_T1, S_T3, S_T1, s9
    FMUL    S_S, S_T1, S_ONE, s9
    LOAD_LIMBS sp, S_S
    IF_ZERO 8f
    lla     t5, 328f                        # low s: s > (n - 1) / 2 becomes n - s
    ABOVE   t5
    beqz    t0, 2f
    ld      t1, 0(s9)
    sltu    t4, t1, a4
    sub     a4, t1, a4
    NEGATE  a5, 8
    NEGATE  a6, 16
    NEGATE  a7, 24
2:  STORE_BE s3, 32
    LOAD_LIMBS sp, S_RR
    STORE_BE s3, 0
    li      a0, CRYPTO_OK
    j       9f

    /* Next candidate: K = HMAC_K(V || 0x00), V = HMAC_K(V). */
8:  sb      zero, S_SEP(sp)
    HMAC_STEP 33, S_KL+24
    HMAC_STEP 32, S_V
    j       1b
9:  LEAVE   S_FRAME
END_FUNCTION crypto_secp256k1_sign

.set V_P, 0
.set V_G, 96
.set V_A, 192
.set V_B, 288
.set V_C, 384
.set V_XY, 480
.set V_RR, 544
.set V_S, 576
.set V_Z, 608
.set V_W, 640
.set V_U1, 672
.set V_U2, 704
.set V_T, 736
.set V_ONE, 768
.set V_R2, 800
.set V_FRAME, 832

/*
 * crypto_secp256k1_verify(public_key, hash, signature, valid) -> status
 * s1 public_key, s2 hash, s3 signature, s4 valid, s5 the result,
 * s9 n record. Valid when 1 <= r, s < n, s <= (n - 1) / 2 and
 * x(u1 G + u2 Q) mod n = r, with u1 = z / s and u2 = r / s.
 */
FUNCTION crypto_secp256k1_verify
    ENTER   V_FRAME
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    lla     s9, 321f
    addi    a0, sp, V_P
    mv      a1, s1
    call    crypto_secp256k1_lift_x
    bnez    a0, 9f
    li      s5, 0
    LOAD_BE s3, 0
    IF_ZERO 7f
    BELOW   s9
    beqz    t0, 7f
    STORE_LIMBS sp, V_RR
    LOAD_BE s3, 32
    IF_ZERO 7f
    lla     t5, 328f
    ABOVE   t5
    bnez    t0, 7f
    STORE_LIMBS sp, V_S
    LOAD_BE s2
    REDUCE_N s9
    STORE_LIMBS sp, V_Z
    SET_ONE V_ONE
    COPY    sp, V_R2, s9, CRYPTO_SECP256K1_MOD_R2
    LOAD_G  V_G
    FMUL    V_T, V_S, V_R2, s9
    addi    a0, sp, V_W
    addi    a1, sp, V_T
    lla     a2, 327f
    mv      a3, s9
    call    crypto_secp256k1_mod_pow
    FMUL    V_T, V_Z, V_R2, s9
    FMUL    V_U1, V_T, V_W, s9
    FMUL    V_U1, V_U1, V_ONE, s9
    FMUL    V_T, V_RR, V_R2, s9
    FMUL    V_U2, V_T, V_W, s9
    FMUL    V_U2, V_U2, V_ONE, s9
    addi    a0, sp, V_A
    addi    a1, sp, V_U1
    addi    a2, sp, V_G
    call    crypto_secp256k1_point_mul
    addi    a0, sp, V_B
    addi    a1, sp, V_U2
    addi    a2, sp, V_P
    call    crypto_secp256k1_point_mul
    addi    a0, sp, V_C
    addi    a1, sp, V_A
    addi    a2, sp, V_B
    call    crypto_secp256k1_point_add
    addi    a0, sp, V_XY
    addi    a1, sp, V_C
    call    crypto_secp256k1_point_affine
    LOAD_LIMBS sp, V_XY
    REDUCE_N s9
    ld      t0, V_RR(sp)
    xor     a4, a4, t0
    ld      t0, V_RR+8(sp)
    xor     a5, a5, t0
    ld      t0, V_RR+16(sp)
    xor     a6, a6, t0
    ld      t0, V_RR+24(sp)
    xor     a7, a7, t0
    or      a4, a4, a5
    or      a6, a6, a7
    or      a4, a4, a6
    seqz    s5, a4
7:  sd      s5, 0(s4)
    li      a0, CRYPTO_OK
9:  LEAVE   V_FRAME
END_FUNCTION crypto_secp256k1_verify

/* ---------------------------------------------------------------- Points */

.set L_X, 0
.set L_RHS, 32
.set L_Y, 64
.set L_T, 96
.set L_ONE, 128
.set L_ZERO, 160
.set L_FRAME, 192

/*
 * crypto_secp256k1_lift_x(point, public_key) -> status: the point of a
 * compressed public key (SEC 1 section 2.3.4), with Z = 1. s1 point,
 * s2 public_key, s3 prefix byte, s11 p record.
 */
LOCAL_FUNCTION crypto_secp256k1_lift_x
    ENTER   L_FRAME
    mv      s1, a0
    mv      s2, a1
    lla     s11, 320f
    li      a0, CRYPTO_INVALID_PUBLIC_KEY
    lbu     s3, 0(s2)
    addi    t0, s3, -2
    li      t1, 1
    bltu    t1, t0, 9f
    LOAD_BE s2, 1
    BELOW   s11
    li      a0, CRYPTO_INVALID_PUBLIC_KEY
    beqz    t0, 9f
    STORE_LIMBS sp, L_X
    mv      a0, s1                          # X = x in Montgomery form
    addi    a1, sp, L_X
    addi    a2, s11, CRYPTO_SECP256K1_MOD_R2
    mv      a3, s11
    call    crypto_secp256k1_mod_mul
    addi    a0, sp, L_RHS                   # x^3 + 7
    mv      a1, s1
    mv      a2, s1
    mv      a3, s11
    call    crypto_secp256k1_mod_mul
    addi    a0, sp, L_RHS
    addi    a1, sp, L_RHS
    mv      a2, s1
    mv      a3, s11
    call    crypto_secp256k1_mod_mul
    addi    a0, sp, L_RHS
    addi    a1, sp, L_RHS
    lla     a2, 324f
    mv      a3, s11
    call    crypto_secp256k1_mod_add
    addi    a0, sp, L_Y                     # y = (x^3 + 7)^((p + 1) / 4)
    addi    a1, sp, L_RHS
    lla     a2, 326f
    mv      a3, s11
    call    crypto_secp256k1_mod_pow
    FMUL    L_T, L_Y, L_Y
    LOAD_LIMBS sp, L_T
    ld      t0, L_RHS(sp)
    xor     a4, a4, t0
    ld      t0, L_RHS+8(sp)
    xor     a5, a5, t0
    ld      t0, L_RHS+16(sp)
    xor     a6, a6, t0
    ld      t0, L_RHS+24(sp)
    xor     a7, a7, t0
    or      a4, a4, a5
    or      a6, a6, a7
    or      a4, a4, a6
    li      a0, CRYPTO_INVALID_PUBLIC_KEY
    bnez    a4, 9f                          # no square root: x is not on the curve
    SET_ONE L_ONE
    FMUL    L_T, L_Y, L_ONE
    ld      t0, L_T(sp)
    xor     t0, t0, s3
    andi    t0, t0, 1
    beqz    t0, 3f
    SET_ZERO L_ZERO                         # the other root, p - y
    FSUB    L_Y, L_ZERO, L_Y
3:  COPY    s1, 32, sp, L_Y
    COPY    s1, 64, s11, CRYPTO_SECP256K1_MOD_ONE
    li      a0, CRYPTO_OK
9:  LEAVE   L_FRAME
END_FUNCTION crypto_secp256k1_lift_x

.set M_R, 0
.set M_T, 96
.set M_P, 192

/*
 * crypto_secp256k1_point_mul(point, scalar, base): point = scalar * base.
 * scalar: 4 limbs. For each bit from 255 down: R = 2R, T = R + base, and R
 * takes T where the bit is 1, through a mask. s1 point, s2 scalar, s3 bit.
 */
LOCAL_FUNCTION crypto_secp256k1_point_mul
    ENTER   288
    mv      s1, a0
    mv      s2, a1
    lla     s11, 320f
    COPY    sp, M_P, a2, 0
    COPY    sp, M_P+32, a2, 32
    COPY    sp, M_P+64, a2, 64
    SET_ZERO M_R                            # R = (0 : 1 : 0), the point at infinity
    COPY    sp, M_R+32, s11, CRYPTO_SECP256K1_MOD_ONE
    SET_ZERO M_R+64
    li      s3, 255
1:  mv      a0, sp
    mv      a1, sp
    call    crypto_secp256k1_point_double
    addi    a0, sp, M_T
    mv      a1, sp
    addi    a2, sp, M_P
    call    crypto_secp256k1_point_add
    srli    t0, s3, 6
    slli    t0, t0, 3
    add     t0, s2, t0
    ld      t0, 0(t0)
    srl     t0, t0, s3
    andi    t0, t0, 1
    neg     t0, t0
    li      t1, 0
2:  add     t2, sp, t1
    ld      t3, 0(t2)
    ld      t4, M_T(t2)
    xor     t4, t4, t3
    and     t4, t4, t0
    xor     t3, t3, t4
    sd      t3, 0(t2)
    addi    t1, t1, 8
    li      t5, 96
    bltu    t1, t5, 2b
    addi    s3, s3, -1
    bgez    s3, 1b
    COPY    s1, 0, sp, M_R
    COPY    s1, 32, sp, M_R+32
    COPY    s1, 64, sp, M_R+64
    LEAVE   288
END_FUNCTION crypto_secp256k1_point_mul

.set A_X1, 0
.set A_Y1, 32
.set A_Z1, 64
.set A_X2, 96
.set A_Y2, 128
.set A_Z2, 160
.set A_T0, 192
.set A_T1, 224
.set A_T2, 256
.set A_T3, 288
.set A_T4, 320
.set A_X3, 352
.set A_Y3, 384
.set A_Z3, 416
.set A_FRAME, 448

/*
 * crypto_secp256k1_point_add(point, first, second): point = first + second,
 * Renes-Costello-Batina algorithm 7 with a = 0 and b3 = 21. Any of the three
 * may be the same. s1 point, s10 b3, s11 p record.
 */
LOCAL_FUNCTION crypto_secp256k1_point_add
    ENTER   A_FRAME
    mv      s1, a0
    lla     s11, 320f
    lla     s10, 323f
    COPY    sp, A_X1, a1, 0
    COPY    sp, A_Y1, a1, 32
    COPY    sp, A_Z1, a1, 64
    COPY    sp, A_X2, a2, 0
    COPY    sp, A_Y2, a2, 32
    COPY    sp, A_Z2, a2, 64
    FMUL    A_T0, A_X1, A_X2                # 1
    FMUL    A_T1, A_Y1, A_Y2                # 2
    FMUL    A_T2, A_Z1, A_Z2                # 3
    FADD    A_T3, A_X1, A_Y1                # 4
    FADD    A_T4, A_X2, A_Y2                # 5
    FMUL    A_T3, A_T3, A_T4                # 6
    FADD    A_T4, A_T0, A_T1                # 7
    FSUB    A_T3, A_T3, A_T4                # 8
    FADD    A_T4, A_Y1, A_Z1                # 9
    FADD    A_X3, A_Y2, A_Z2                # 10
    FMUL    A_T4, A_T4, A_X3                # 11
    FADD    A_X3, A_T1, A_T2                # 12
    FSUB    A_T4, A_T4, A_X3                # 13
    FADD    A_X3, A_X1, A_Z1                # 14
    FADD    A_Y3, A_X2, A_Z2                # 15
    FMUL    A_X3, A_X3, A_Y3                # 16
    FADD    A_Y3, A_T0, A_T2                # 17
    FSUB    A_Y3, A_X3, A_Y3                # 18
    FADD    A_X3, A_T0, A_T0                # 19
    FADD    A_T0, A_X3, A_T0                # 20
    FMULB3  A_T2, A_T2                      # 21
    FADD    A_Z3, A_T1, A_T2                # 22
    FSUB    A_T1, A_T1, A_T2                # 23
    FMULB3  A_Y3, A_Y3                      # 24
    FMUL    A_X3, A_T4, A_Y3                # 25
    FMUL    A_T2, A_T3, A_T1                # 26
    FSUB    A_X3, A_T2, A_X3                # 27
    FMUL    A_Y3, A_Y3, A_T0                # 28
    FMUL    A_T1, A_T1, A_Z3                # 29
    FADD    A_Y3, A_T1, A_Y3                # 30
    FMUL    A_T0, A_T0, A_T3                # 31
    FMUL    A_Z3, A_Z3, A_T4                # 32
    FADD    A_Z3, A_Z3, A_T0                # 33
    COPY    s1, 0, sp, A_X3
    COPY    s1, 32, sp, A_Y3
    COPY    s1, 64, sp, A_Z3
    LEAVE   A_FRAME
END_FUNCTION crypto_secp256k1_point_add

.set D_X, 0
.set D_Y, 32
.set D_Z, 64
.set D_T0, 96
.set D_T1, 128
.set D_T2, 160
.set D_X3, 192
.set D_Y3, 224
.set D_Z3, 256
.set D_FRAME, 288

/*
 * crypto_secp256k1_point_double(point, base): point = 2 * base,
 * Renes-Costello-Batina algorithm 9 with a = 0 and b3 = 21. point may be base.
 * s1 point, s10 b3, s11 p record.
 */
LOCAL_FUNCTION crypto_secp256k1_point_double
    ENTER   D_FRAME
    mv      s1, a0
    lla     s11, 320f
    lla     s10, 323f
    COPY    sp, D_X, a1, 0
    COPY    sp, D_Y, a1, 32
    COPY    sp, D_Z, a1, 64
    FMUL    D_T0, D_Y, D_Y                  # 1
    FADD    D_Z3, D_T0, D_T0                # 2
    FADD    D_Z3, D_Z3, D_Z3                # 3
    FADD    D_Z3, D_Z3, D_Z3                # 4
    FMUL    D_T1, D_Y, D_Z                  # 5
    FMUL    D_T2, D_Z, D_Z                  # 6
    FMULB3  D_T2, D_T2                      # 7
    FMUL    D_X3, D_T2, D_Z3                # 8
    FADD    D_Y3, D_T0, D_T2                # 9
    FMUL    D_Z3, D_T1, D_Z3                # 10
    FADD    D_T1, D_T2, D_T2                # 11
    FADD    D_T2, D_T1, D_T2                # 12
    FSUB    D_T0, D_T0, D_T2                # 13
    FMUL    D_Y3, D_T0, D_Y3                # 14
    FADD    D_Y3, D_X3, D_Y3                # 15
    FMUL    D_T1, D_X, D_Y                  # 16
    FMUL    D_X3, D_T0, D_T1                # 17
    FADD    D_X3, D_X3, D_X3                # 18
    COPY    s1, 0, sp, D_X3
    COPY    s1, 32, sp, D_Y3
    COPY    s1, 64, sp, D_Z3
    LEAVE   D_FRAME
END_FUNCTION crypto_secp256k1_point_double

/*
 * crypto_secp256k1_point_affine(xy, point): x = X / Z and y = Y / Z as plain
 * limbs at xy and xy + 32. The point at infinity gives 0, 0.
 * s1 xy, s2 point, s11 p record. 1 / Z at sp, the number 1 at sp + 32.
 */
LOCAL_FUNCTION crypto_secp256k1_point_affine
    ENTER   64
    mv      s1, a0
    mv      s2, a1
    lla     s11, 320f
    SET_ONE 32
    mv      a0, sp
    addi    a1, s2, 64
    lla     a2, 325f
    mv      a3, s11
    call    crypto_secp256k1_mod_pow
    mv      a0, s1
    mv      a1, s2
    mv      a2, sp
    mv      a3, s11
    call    crypto_secp256k1_mod_mul
    mv      a0, s1
    mv      a1, s1
    addi    a2, sp, 32
    mv      a3, s11
    call    crypto_secp256k1_mod_mul
    addi    a0, s1, 32
    addi    a1, s2, 32
    mv      a2, sp
    mv      a3, s11
    call    crypto_secp256k1_mod_mul
    addi    a0, s1, 32
    addi    a1, s1, 32
    addi    a2, sp, 32
    mv      a3, s11
    call    crypto_secp256k1_mod_mul
    LEAVE   64
END_FUNCTION crypto_secp256k1_point_affine

/* ---------------------------------------------------------------- Modular arithmetic */

/*
 * crypto_secp256k1_mod_pow(result, base, exponent, modulus): base^exponent
 * in Montgomery form, by squaring and multiplying from bit 255 down. The
 * exponent is public. s1 result, s2 exponent, s3 modulus, s4 bit.
 * base at sp, the running value at sp + 32.
 */
LOCAL_FUNCTION crypto_secp256k1_mod_pow
    ENTER   64
    mv      s1, a0
    mv      s2, a2
    mv      s3, a3
    COPY    sp, 0, a1, 0
    COPY    sp, 32, s3, CRYPTO_SECP256K1_MOD_ONE
    li      s4, 255
1:  addi    a0, sp, 32
    addi    a1, sp, 32
    addi    a2, sp, 32
    mv      a3, s3
    call    crypto_secp256k1_mod_mul
    srli    t0, s4, 6
    slli    t0, t0, 3
    add     t0, s2, t0
    ld      t0, 0(t0)
    srl     t0, t0, s4
    andi    t0, t0, 1
    beqz    t0, 2f
    addi    a0, sp, 32
    addi    a1, sp, 32
    mv      a2, sp
    mv      a3, s3
    call    crypto_secp256k1_mod_mul
2:  addi    s4, s4, -1
    bgez    s4, 1b
    COPY    s1, 0, sp, 32
    LEAVE   64
END_FUNCTION crypto_secp256k1_mod_pow

/* T_j += a_j * b_i + c, with b_i in t6, c in s3; lo s1, hi s2. */
.macro MAC tj, aj
    mul     s1, \aj, t6
    mulhu   s2, \aj, t6
    add     \tj, \tj, s1
    sltu    s1, \tj, s1
    add     \tj, \tj, s3
    sltu    s3, \tj, s3
    add     s3, s3, s1
    add     s3, s3, s2
.endm

/* T_j += q * m_j + c, with q in s0, m_j at off(a3), c in s3; lo s1, hi s2. */
.macro MACQ tj, off
    ld      s1, \off(a3)
    mulhu   s2, s0, s1
    mul     s1, s0, s1
    add     \tj, \tj, s1
    sltu    s1, \tj, s1
    add     \tj, \tj, s3
    sltu    s3, \tj, s3
    add     s3, s3, s1
    add     s3, s3, s2
.endm

/* d_j = T_j - m_j at off(a3) - borrow s1, the new borrow in s1. Uses s0, s2, s3. */
.macro SUBM dj, tj, off
    ld      s0, \off(a3)
    sltu    s2, \tj, s0
    sub     \dj, \tj, s0
    sltu    s3, \dj, s1
    sub     \dj, \dj, s1
    or      s1, s2, s3
.endm

/* T_j = d_j when the mask s2 is all ones. Uses s3. */
.macro PICK tj, dj
    xor     s3, \dj, \tj
    and     s3, s3, s2
    xor     \tj, \tj, s3
.endm

/*
 * crypto_secp256k1_mod_mul(result, a, b, modulus): a * b / 2^256 mod m, for
 * a, b < m (CIOS). result may be a or b.
 * a a4 to a7, T t0 to t5, b_i t6, q s0, product s1 and s2, carry s3.
 */
LOCAL_FUNCTION crypto_secp256k1_mod_mul
    addi    sp, sp, -32
    UNWIND_ALLOC 32
    sd      s0, 0(sp)
    UNWIND_SAVE s0, 0
    sd      s1, 8(sp)
    UNWIND_SAVE s1, 8
    sd      s2, 16(sp)
    UNWIND_SAVE s2, 16
    sd      s3, 24(sp)
    UNWIND_SAVE s3, 24
    UNWIND_END_PROLOGUE
    ld      a4, 0(a1)
    ld      a5, 8(a1)
    ld      a6, 16(a1)
    ld      a7, 24(a1)
    li      t0, 0
    li      t1, 0
    li      t2, 0
    li      t3, 0
    li      t4, 0
    .irp off, 0, 8, 16, 24
    ld      t6, \off(a2)                    # T += a * b_i
    li      s3, 0
    MAC     t0, a4
    MAC     t1, a5
    MAC     t2, a6
    MAC     t3, a7
    add     t4, t4, s3
    sltu    t5, t4, s3
    ld      s0, CRYPTO_SECP256K1_MOD_INVERSE(a3)
    mul     s0, t0, s0                      # q = T0 * -m^-1 mod 2^64
    li      s3, 0                           # T = (T + q * m) / 2^64
    MACQ    t0, 0
    MACQ    t1, 8
    MACQ    t2, 16
    MACQ    t3, 24
    add     t4, t4, s3
    sltu    s1, t4, s3
    add     t5, t5, s1
    mv      t0, t1
    mv      t1, t2
    mv      t2, t3
    mv      t3, t4
    mv      t4, t5
    .endr
    li      s1, 0                           # T - m when T >= m
    SUBM    a4, t0, 0
    SUBM    a5, t1, 8
    SUBM    a6, t2, 16
    SUBM    a7, t3, 24
    sltu    s2, t4, s1
    addi    s2, s2, -1
    PICK    t0, a4
    PICK    t1, a5
    PICK    t2, a6
    PICK    t3, a7
    sd      t0, 0(a0)
    sd      t1, 8(a0)
    sd      t2, 16(a0)
    sd      t3, 24(a0)
    UNWIND_BEGIN_EPILOGUE
    ld      s0, 0(sp)
    UNWIND_RESTORE s0
    ld      s1, 8(sp)
    UNWIND_RESTORE s1
    ld      s2, 16(sp)
    UNWIND_RESTORE s2
    ld      s3, 24(sp)
    UNWIND_RESTORE s3
    addi    sp, sp, 32
    UNWIND_FREE 32
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_secp256k1_mod_mul

/* crypto_secp256k1_mod_add(result, a, b, modulus): a + b mod m, for a, b < m. */
LOCAL_FUNCTION crypto_secp256k1_mod_add
    UNWIND_END_PROLOGUE
    ld      t0, 0(a1)                       # the sum in t0 to t3, carry t5
    ld      t4, 0(a2)
    add     t0, t0, t4
    sltu    t5, t0, t4
    ld      t1, 8(a1)
    ld      t4, 8(a2)
    add     t1, t1, t4
    sltu    t6, t1, t4
    add     t1, t1, t5
    sltu    t5, t1, t5
    or      t5, t5, t6
    ld      t2, 16(a1)
    ld      t4, 16(a2)
    add     t2, t2, t4
    sltu    t6, t2, t4
    add     t2, t2, t5
    sltu    t5, t2, t5
    or      t5, t5, t6
    ld      t3, 24(a1)
    ld      t4, 24(a2)
    add     t3, t3, t4
    sltu    t6, t3, t4
    add     t3, t3, t5
    sltu    t5, t3, t5
    or      t5, t5, t6
    ld      t4, 0(a3)                       # the sum - m in a4 to a7, borrow t6
    sltu    t6, t0, t4
    sub     a4, t0, t4
    ld      t4, 8(a3)
    sltu    a1, t1, t4
    sub     a5, t1, t4
    sltu    a2, a5, t6
    sub     a5, a5, t6
    or      t6, a1, a2
    ld      t4, 16(a3)
    sltu    a1, t2, t4
    sub     a6, t2, t4
    sltu    a2, a6, t6
    sub     a6, a6, t6
    or      t6, a1, a2
    ld      t4, 24(a3)
    sltu    a1, t3, t4
    sub     a7, t3, t4
    sltu    a2, a7, t6
    sub     a7, a7, t6
    or      t6, a1, a2
    sltu    a1, t5, t6                      # 1 when the sum is below m
    addi    a1, a1, -1
    xor     a2, a4, t0
    and     a2, a2, a1
    xor     t0, t0, a2
    xor     a2, a5, t1
    and     a2, a2, a1
    xor     t1, t1, a2
    xor     a2, a6, t2
    and     a2, a2, a1
    xor     t2, t2, a2
    xor     a2, a7, t3
    and     a2, a2, a1
    xor     t3, t3, a2
    sd      t0, 0(a0)
    sd      t1, 8(a0)
    sd      t2, 16(a0)
    sd      t3, 24(a0)
    ret
END_FUNCTION crypto_secp256k1_mod_add

/* crypto_secp256k1_mod_sub(result, a, b, modulus): a - b mod m, for a, b < m. */
LOCAL_FUNCTION crypto_secp256k1_mod_sub
    UNWIND_END_PROLOGUE
    ld      t0, 0(a1)                       # the difference in t0 to t3, borrow t5
    ld      t4, 0(a2)
    sltu    t5, t0, t4
    sub     t0, t0, t4
    ld      t1, 8(a1)
    ld      t4, 8(a2)
    sltu    t6, t1, t4
    sub     t1, t1, t4
    sltu    a4, t1, t5
    sub     t1, t1, t5
    or      t5, t6, a4
    ld      t2, 16(a1)
    ld      t4, 16(a2)
    sltu    t6, t2, t4
    sub     t2, t2, t4
    sltu    a4, t2, t5
    sub     t2, t2, t5
    or      t5, t6, a4
    ld      t3, 24(a1)
    ld      t4, 24(a2)
    sltu    t6, t3, t4
    sub     t3, t3, t4
    sltu    a4, t3, t5
    sub     t3, t3, t5
    or      t5, t6, a4
    neg     t5, t5                          # all ones on a borrow: add m
    ld      t4, 0(a3)
    and     t4, t4, t5
    add     t0, t0, t4
    sltu    t6, t0, t4
    ld      t4, 8(a3)
    and     t4, t4, t5
    add     t1, t1, t4
    sltu    a4, t1, t4
    add     t1, t1, t6
    sltu    a5, t1, t6
    or      t6, a4, a5
    ld      t4, 16(a3)
    and     t4, t4, t5
    add     t2, t2, t4
    sltu    a4, t2, t4
    add     t2, t2, t6
    sltu    a5, t2, t6
    or      t6, a4, a5
    ld      t4, 24(a3)
    and     t4, t4, t5
    add     t3, t3, t4
    add     t3, t3, t6
    sd      t0, 0(a0)
    sd      t1, 8(a0)
    sd      t2, 16(a0)
    sd      t3, 24(a0)
    ret
END_FUNCTION crypto_secp256k1_mod_sub

/* ---------------------------------------------------------------- Constants (SEC 2 section 2.4.1) */

    .p2align 3
/* p = 2^256 - 2^32 - 977: p, -p^-1 mod 2^64, 2^256 mod p, 2^512 mod p. */
320:
    .quad   0xFFFFFFFEFFFFFC2F, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF
    .quad   0xD838091DD2253531
    .quad   0x00000001000003D1, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x000007A2000E90A1, 0x0000000000000001, 0x0000000000000000, 0x0000000000000000
/* n, the group order: n, -n^-1 mod 2^64, 2^256 mod n, 2^512 mod n. */
321:
    .quad   0xBFD25E8CD0364141, 0xBAAEDCE6AF48A03B, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF
    .quad   0x4B0DFF665588B13F
    .quad   0x402DA1732FC9BEBF, 0x4551231950B75FC4, 0x0000000000000001, 0x0000000000000000
    .quad   0x896CF21467D7D140, 0x741496C20E7CF878, 0xE697F5E45BCD07C6, 0x9D671CD581C69BC5
/* G: x, then y, in Montgomery form. */
322:
    .quad   0xD7362E5A487E2097, 0x231E295329BC66DB, 0x979F48C033FD129C, 0x9981E643E9089F48
    .quad   0xB15EA6D2D3DBABE2, 0x8DFC5D5D1F1DC64D, 0x70B6B59AAC19C136, 0xCF3F851FD4A582D6
/* b3 = 3 * 7 = 21, in Montgomery form. */
323:
    .quad   0x0000001500005025, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
/* b = 7, in Montgomery form. */
324:
    .quad   0x0000000700001AB7, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
/* p - 2: the exponent of 1 / a mod p. */
325:
    .quad   0xFFFFFFFEFFFFFC2D, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF
/* (p + 1) / 4: the exponent of the square root mod p. */
326:
    .quad   0xFFFFFFFFBFFFFF0C, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x3FFFFFFFFFFFFFFF
/* n - 2: the exponent of 1 / a mod n. */
327:
    .quad   0xBFD25E8CD036413F, 0xBAAEDCE6AF48A03B, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF
/* (n - 1) / 2: the largest low s. */
328:
    .quad   0xDFE92F46681B20A0, 0x5D576E7357A4501D, 0xFFFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF
