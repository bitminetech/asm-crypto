/*
 * P-256 (secp256r1) for ARM64 (AAPCS64): public keys, and ECDSA signing
 * (RFC 6979 nonces) and verification, for the TLS certificates of libp2p.
 * Requirements: docs/reference/p256.md. Layouts: include/p256.inc.
 *
 * The same design as secp256k1.s: numbers are 4 limbs of 64 bits, least
 * significant first; products use Montgomery multiplication (CIOS) for both
 * p and n. Points use projective coordinates and the complete formulas of
 * Renes, Costello and Batina (algorithms 4 and 6, a = -3), so no point needs
 * a special case. The scalar multiplication doubles and adds for all 256
 * bits and picks the sum with a mask. No branch or address depends on a
 * private key or a nonce.
 * x18 is never used. Every function that calls keeps an x29 frame record.
 */
.set ISA_ARM64, 1
.include "crypto.inc"
.include "p256.inc"
.include "platform.inc"

/*
 * Frame of a non-leaf function: x29, x30, x19-x28 at sp + extra, then
 * locals at sp + 96. extra bytes of locals sit below at sp.
 */
.macro ENTER locals, extra=0
    stp     x29, x30, [sp, #-(96 + \locals)]!
    UNWIND_SAVE_FPLR_X (96 + \locals)
    mov     x29, sp
    UNWIND_SET_FP
    stp     x19, x20, [sp, #16]
    UNWIND_SAVE_REGP x19, x20, 16, (96 + \locals)
    stp     x21, x22, [sp, #32]
    UNWIND_SAVE_REGP x21, x22, 32, (96 + \locals)
    stp     x23, x24, [sp, #48]
    UNWIND_SAVE_REGP x23, x24, 48, (96 + \locals)
    stp     x25, x26, [sp, #64]
    UNWIND_SAVE_REGP x25, x26, 64, (96 + \locals)
    stp     x27, x28, [sp, #80]
    UNWIND_SAVE_REGP x27, x28, 80, (96 + \locals)
    .if \extra
    sub     sp, sp, #\extra
    UNWIND_ALLOC \extra
    .endif
    UNWIND_END_PROLOGUE
.endm

.macro LEAVE locals, extra=0
    UNWIND_BEGIN_EPILOGUE
    .if \extra
    add     sp, sp, #\extra
    UNWIND_FREE \extra
    .endif
    ldp     x27, x28, [sp, #80]
    UNWIND_RESTORE_REGP x27, x28, 80
    ldp     x25, x26, [sp, #64]
    UNWIND_RESTORE_REGP x25, x26, 64
    ldp     x23, x24, [sp, #48]
    UNWIND_RESTORE_REGP x23, x24, 48
    ldp     x21, x22, [sp, #32]
    UNWIND_RESTORE_REGP x21, x22, 32
    ldp     x19, x20, [sp, #16]
    UNWIND_RESTORE_REGP x19, x20, 16
    ldp     x29, x30, [sp], #(96 + \locals)
    UNWIND_RESTORE_FPLR_X (96 + \locals)
    UNWIND_END_EPILOGUE
    ret
.endm

/* ---------------------------------------------------------------- Macros */

/* fn(sp + d, sp + a, sp + b, modulus record m). */
.macro OP fn, d, a, b, m
    add     x0, sp, #\d
    add     x1, sp, #\a
    add     x2, sp, #\b
    mov     x3, \m
    bl      \fn
.endm

.macro FMUL d, a, b, m=x28
    OP      crypto_p256_mod_mul, \d, \a, \b, \m
.endm

.macro FADD d, a, b, m=x28
    OP      crypto_p256_mod_add, \d, \a, \b, \m
.endm

.macro FSUB d, a, b, m=x28
    OP      crypto_p256_mod_sub, \d, \a, \b, \m
.endm

/* sp + d = b * (sp + a) mod p, with b in Montgomery form at x27. */
.macro FMULB d, a
    add     x0, sp, #\d
    mov     x1, x27
    add     x2, sp, #\a
    mov     x3, x28
    bl      crypto_p256_mod_mul
.endm

/* Copy 32 bytes from src + soff to dst + doff. Uses x9 to x14. */
.macro COPY dst, doff, src, soff
    add     x13, \src, #\soff
    add     x14, \dst, #\doff
    ldp     x9, x10, [x13]
    ldp     x11, x12, [x13, #16]
    stp     x9, x10, [x14]
    stp     x11, x12, [x14, #16]
.endm

/* x9 to x12 = the 32 big-endian bytes at src, as limbs. */
.macro LOAD_BE src
    ldp     x12, x11, [\src]
    ldp     x10, x9, [\src, #16]
    rev     x9, x9
    rev     x10, x10
    rev     x11, x11
    rev     x12, x12
.endm

/* The limbs x9 to x12 as 32 big-endian bytes at dst. Uses x13, x14. */
.macro STORE_BE dst
    rev     x13, x12
    rev     x14, x11
    stp     x13, x14, [\dst]
    rev     x13, x10
    rev     x14, x9
    stp     x13, x14, [\dst, #16]
.endm

.macro LOAD_LIMBS src
    ldp     x9, x10, [\src]
    ldp     x11, x12, [\src, #16]
.endm

.macro STORE_LIMBS dst
    stp     x9, x10, [\dst]
    stp     x11, x12, [\dst, #16]
.endm

/* Flags: lo when the limbs x9 to x12 are below the 4 limbs at m. Uses x13 to x16. */
.macro BELOW m
    ldp     x13, x14, [\m]
    ldp     x15, x16, [\m, #16]
    cmp     x9, x13
    sbcs    xzr, x10, x14
    sbcs    xzr, x11, x15
    sbcs    xzr, x12, x16
.endm

/* Branch to label when the limbs x9 to x12 are all zero. Uses x13, x14. */
.macro IF_ZERO label
    orr     x13, x9, x10
    orr     x14, x11, x12
    orr     x13, x13, x14
    cbz     x13, \label
.endm

/* The limbs x9 to x12 minus n when they are n or more (they are below 2n). n record at m. Uses x13 to x16. */
.macro REDUCE_N m
    ldp     x13, x14, [\m]
    ldp     x15, x16, [\m, #16]
    subs    x13, x9, x13
    sbcs    x14, x10, x14
    sbcs    x15, x11, x15
    sbcs    x16, x12, x16
    csel    x9, x13, x9, hs
    csel    x10, x14, x10, hs
    csel    x11, x15, x11, hs
    csel    x12, x16, x12, hs
.endm

/* The point G at sp + off: x, y and Z = 1, in Montgomery form. Uses x9 to x14, x17. */
.macro LOAD_G off
    adr     x17, 322f
    COPY    sp, \off, x17, 0
    COPY    sp, (\off + 32), x17, 32
    adr     x17, 320f
    COPY    sp, (\off + 64), x17, CRYPTO_P256_MOD_ONE
.endm

/* The 32 bytes at sp + off = the number 1. */
.macro SET_ONE off
    add     x13, sp, #\off
    mov     x9, #1
    stp     x9, xzr, [x13]
    stp     xzr, xzr, [x13, #16]
.endm

/* ---------------------------------------------------------------- Public keys */

.set K_D, 0
.set K_G, 32
.set K_Q, 128
.set K_XY, 224
.set K_FRAME, 288

/*
 * crypto_p256_public_key(private_key, public_key) -> status
 * x19 private_key, x20 public_key.
 */
FUNCTION crypto_p256_public_key
    ENTER   0, K_FRAME
    mov     x19, x0
    mov     x20, x1
    LOAD_BE x19
    mov     x0, #CRYPTO_INVALID_PRIVATE_KEY
    IF_ZERO 9f
    adr     x17, 321f
    BELOW   x17
    b.hs    9f
    add     x15, sp, #K_D
    STORE_LIMBS x15
    LOAD_G  K_G
    add     x0, sp, #K_Q
    add     x1, sp, #K_D
    add     x2, sp, #K_G
    bl      crypto_p256_point_mul
    add     x0, sp, #K_XY
    add     x1, sp, #K_Q
    bl      crypto_p256_point_affine
    mov     w9, #4                          /* 0x04, x, y */
    strb    w9, [x20]
    add     x15, sp, #K_XY
    LOAD_LIMBS x15
    add     x15, x20, #1
    STORE_BE x15
    add     x15, sp, #(K_XY + 32)
    LOAD_LIMBS x15
    add     x15, x20, #33
    STORE_BE x15
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, K_FRAME
END_FUNCTION crypto_p256_public_key

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
    mov     x9, #\count
    str     x9, [sp, #S_ML + CRYPTO_BYTES_COUNT]
    mov     x9, #200
    str     x9, [sp, #S_SCR]
    add     x0, sp, #S_KL
    add     x1, sp, #S_ML
    add     x2, sp, #S_SCR
    add     x3, sp, #S_OUT
    CALL_GLOBAL crypto_hmac_sha256
    add     x15, sp, #S_OUT
    add     x16, sp, #\dst
    COPY    x16, 0, x15, 0
.endm

/*
 * crypto_p256_sign(private_key, hash, signature) -> status
 * x19 private_key, x20 hash, x21 signature, x25 p record, x26 n record.
 * The nonce follows RFC 6979 section 3.2 with HMAC-SHA-256, qlen = hlen = 256.
 * s is written as computed: P-256 has no low s rule.
 */
FUNCTION crypto_p256_sign
    ENTER   0, S_FRAME
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    adr     x25, 320f
    adr     x26, 321f
    LOAD_BE x19
    mov     x0, #CRYPTO_INVALID_PRIVATE_KEY
    IF_ZERO 9f
    BELOW   x26
    b.hs    9f
    add     x15, sp, #S_D
    STORE_LIMBS x15
    LOAD_BE x20
    REDUCE_N x26
    add     x15, sp, #S_Z
    STORE_LIMBS x15
    add     x15, sp, #(S_ML + 24 + 33 + 32)  /* bits2octets(h) */
    STORE_BE x15
    ldp     x9, x10, [x19]                  /* int2octets(x): the key bytes */
    ldp     x11, x12, [x19, #16]
    add     x15, sp, #(S_ML + 24 + 33)
    stp     x9, x10, [x15]
    stp     x11, x12, [x15, #16]
    SET_ONE S_ONE
    add     x16, sp, #0
    COPY    x16, S_R2, x26, CRYPTO_P256_MOD_R2
    LOAD_G  S_G
    mov     x9, #(CRYPTO_BYTES_FIXED + 32)  /* K = 0x00 * 32 */
    str     x9, [sp, #S_KL + CRYPTO_BYTES_SIZE]
    mov     x9, #CRYPTO_BYTES_FIXED
    str     x9, [sp, #S_KL + CRYPTO_BYTES_OFFSET]
    mov     x9, #32
    str     x9, [sp, #S_KL + CRYPTO_BYTES_COUNT]
    stp     xzr, xzr, [sp, #S_KL + 24]
    stp     xzr, xzr, [sp, #S_KL + 40]
    mov     x9, #128                        /* V = 0x01 * 32 */
    str     x9, [sp, #S_ML + CRYPTO_BYTES_SIZE]
    mov     x9, #CRYPTO_BYTES_FIXED
    str     x9, [sp, #S_ML + CRYPTO_BYTES_OFFSET]
    mov     x9, #0x0101010101010101
    stp     x9, x9, [sp, #S_V]
    stp     x9, x9, [sp, #S_V + 16]
    strb    wzr, [sp, #S_SEP]               /* K = HMAC_K(V || 0x00 || x || h) */
    HMAC_STEP 97, (S_KL + 24)
    HMAC_STEP 32, S_V                       /* V = HMAC_K(V) */
    mov     w9, #1
    strb    w9, [sp, #S_SEP]                /* K = HMAC_K(V || 0x01 || x || h) */
    HMAC_STEP 97, (S_KL + 24)
    HMAC_STEP 32, S_V

    /* T = V = HMAC_K(V); k = bits2int(T), used when 1 <= k < n. */
1:  HMAC_STEP 32, S_V
    add     x15, sp, #S_V
    LOAD_BE x15
    IF_ZERO 8f
    BELOW   x26
    b.hs    8f
    add     x15, sp, #S_K
    STORE_LIMBS x15
    add     x0, sp, #S_R
    add     x1, sp, #S_K
    add     x2, sp, #S_G
    bl      crypto_p256_point_mul
    add     x0, sp, #S_XY
    add     x1, sp, #S_R
    bl      crypto_p256_point_affine
    add     x15, sp, #S_XY                  /* r = x mod n */
    LOAD_LIMBS x15
    REDUCE_N x26
    IF_ZERO 8f
    add     x15, sp, #S_RR
    STORE_LIMBS x15
    FMUL    S_T1, S_RR, S_R2, x26           /* s = k^-1 (z + r d) mod n, Montgomery form */
    FMUL    S_T2, S_D, S_R2, x26
    FMUL    S_T1, S_T1, S_T2, x26
    FMUL    S_T2, S_Z, S_R2, x26
    FADD    S_T1, S_T1, S_T2, x26
    FMUL    S_T2, S_K, S_R2, x26
    add     x0, sp, #S_T3
    add     x1, sp, #S_T2
    adr     x2, 327f
    mov     x3, x26
    bl      crypto_p256_mod_pow
    FMUL    S_T1, S_T3, S_T1, x26
    FMUL    S_S, S_T1, S_ONE, x26
    add     x15, sp, #S_S
    LOAD_LIMBS x15
    IF_ZERO 8f
    add     x15, x21, #32
    STORE_BE x15
    add     x15, sp, #S_RR
    LOAD_LIMBS x15
    STORE_BE x21
    mov     x0, #CRYPTO_OK
    b       9f

    /* Next candidate: K = HMAC_K(V || 0x00), V = HMAC_K(V). */
8:  strb    wzr, [sp, #S_SEP]
    HMAC_STEP 33, (S_KL + 24)
    HMAC_STEP 32, S_V
    b       1b
9:  LEAVE   0, S_FRAME
END_FUNCTION crypto_p256_sign

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
 * crypto_p256_verify(public_key, hash, signature, valid) -> status
 * x19 public_key, x20 hash, x21 signature, x22 valid, x23 the result,
 * x26 n record. Valid when 1 <= r, s < n and x(u1 G + u2 Q) mod n = r,
 * with u1 = z / s and u2 = r / s.
 */
FUNCTION crypto_p256_verify
    ENTER   0, V_FRAME
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    adr     x26, 321f
    add     x0, sp, #V_P
    mov     x1, x19
    bl      crypto_p256_point_load
    cbnz    x0, 9f
    mov     x23, #0
    LOAD_BE x21
    IF_ZERO 7f
    BELOW   x26
    b.hs    7f
    add     x15, sp, #V_RR
    STORE_LIMBS x15
    add     x15, x21, #32
    LOAD_BE x15
    IF_ZERO 7f
    BELOW   x26
    b.hs    7f
    add     x15, sp, #V_S
    STORE_LIMBS x15
    LOAD_BE x20
    REDUCE_N x26
    add     x15, sp, #V_Z
    STORE_LIMBS x15
    SET_ONE V_ONE
    add     x16, sp, #0
    COPY    x16, V_R2, x26, CRYPTO_P256_MOD_R2
    LOAD_G  V_G
    FMUL    V_T, V_S, V_R2, x26
    add     x0, sp, #V_W
    add     x1, sp, #V_T
    adr     x2, 327f
    mov     x3, x26
    bl      crypto_p256_mod_pow
    FMUL    V_T, V_Z, V_R2, x26
    FMUL    V_U1, V_T, V_W, x26
    FMUL    V_U1, V_U1, V_ONE, x26
    FMUL    V_T, V_RR, V_R2, x26
    FMUL    V_U2, V_T, V_W, x26
    FMUL    V_U2, V_U2, V_ONE, x26
    add     x0, sp, #V_A
    add     x1, sp, #V_U1
    add     x2, sp, #V_G
    bl      crypto_p256_point_mul
    add     x0, sp, #V_B
    add     x1, sp, #V_U2
    add     x2, sp, #V_P
    bl      crypto_p256_point_mul
    add     x0, sp, #V_C
    add     x1, sp, #V_A
    add     x2, sp, #V_B
    bl      crypto_p256_point_add
    add     x0, sp, #V_XY
    add     x1, sp, #V_C
    bl      crypto_p256_point_affine
    add     x15, sp, #V_XY
    LOAD_LIMBS x15
    REDUCE_N x26
    add     x15, sp, #V_RR
    ldp     x13, x14, [x15]
    ldp     x15, x16, [x15, #16]
    eor     x9, x9, x13
    eor     x10, x10, x14
    eor     x11, x11, x15
    eor     x12, x12, x16
    orr     x9, x9, x10
    orr     x11, x11, x12
    orr     x9, x9, x11
    cmp     x9, #0
    cset    x23, eq
7:  str     x23, [x22]
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, V_FRAME
END_FUNCTION crypto_p256_verify

/* ---------------------------------------------------------------- Points */

.set L_X, 0
.set L_Y, 32
.set L_RHS, 64
.set L_T, 96
.set L_FRAME, 128

/*
 * crypto_p256_point_load(point, public_key) -> status: the point of an
 * uncompressed public key (SEC 1 section 2.3.4), with Z = 1, after checking
 * that x, y < p and y^2 = x^3 - 3x + b. x19 point, x20 public_key,
 * x28 p record.
 */
LOCAL_FUNCTION crypto_p256_point_load
    ENTER   0, L_FRAME
    mov     x19, x0
    mov     x20, x1
    adr     x28, 320f
    mov     x0, #CRYPTO_INVALID_PUBLIC_KEY
    ldrb    w9, [x20]
    cmp     w9, #4
    b.ne    9f
    add     x15, x20, #1
    LOAD_BE x15
    BELOW   x28
    b.hs    9f
    add     x15, sp, #L_X
    STORE_LIMBS x15
    add     x15, x20, #33
    LOAD_BE x15
    BELOW   x28
    mov     x0, #CRYPTO_INVALID_PUBLIC_KEY
    b.hs    9f
    add     x15, sp, #L_Y
    STORE_LIMBS x15
    mov     x0, x19                         /* X, Y in Montgomery form */
    add     x1, sp, #L_X
    add     x2, x28, #CRYPTO_P256_MOD_R2
    mov     x3, x28
    bl      crypto_p256_mod_mul
    add     x0, x19, #32
    add     x1, sp, #L_Y
    add     x2, x28, #CRYPTO_P256_MOD_R2
    mov     x3, x28
    bl      crypto_p256_mod_mul
    COPY    x19, 64, x28, CRYPTO_P256_MOD_ONE
    add     x0, sp, #L_RHS                  /* x^3 - 3x + b */
    mov     x1, x19
    mov     x2, x19
    mov     x3, x28
    bl      crypto_p256_mod_mul
    add     x0, sp, #L_RHS
    add     x1, sp, #L_RHS
    mov     x2, x19
    mov     x3, x28
    bl      crypto_p256_mod_mul
    add     x0, sp, #L_T
    mov     x1, x19
    mov     x2, x19
    mov     x3, x28
    bl      crypto_p256_mod_add
    add     x0, sp, #L_T
    add     x1, sp, #L_T
    mov     x2, x19
    mov     x3, x28
    bl      crypto_p256_mod_add
    FSUB    L_RHS, L_RHS, L_T
    add     x0, sp, #L_RHS
    add     x1, sp, #L_RHS
    adr     x2, 323f
    mov     x3, x28
    bl      crypto_p256_mod_add
    add     x0, sp, #L_T                    /* y^2 */
    add     x1, x19, #32
    add     x2, x19, #32
    mov     x3, x28
    bl      crypto_p256_mod_mul
    add     x15, sp, #L_T
    LOAD_LIMBS x15
    add     x15, sp, #L_RHS
    ldp     x13, x14, [x15]
    ldp     x15, x16, [x15, #16]
    eor     x9, x9, x13
    eor     x10, x10, x14
    eor     x11, x11, x15
    eor     x12, x12, x16
    orr     x9, x9, x10
    orr     x11, x11, x12
    orr     x9, x9, x11
    mov     x0, #CRYPTO_INVALID_PUBLIC_KEY
    cbnz    x9, 9f                          /* not on the curve */
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, L_FRAME
END_FUNCTION crypto_p256_point_load

.set M_R, 0
.set M_T, 96
.set M_P, 192

/*
 * crypto_p256_point_mul(point, scalar, base): point = scalar * base.
 * scalar: 4 limbs. For each bit from 255 down: R = 2R, T = R + base, and R
 * takes T where the bit is 1, through a mask. x19 point, x20 scalar, x21 bit.
 */
LOCAL_FUNCTION crypto_p256_point_mul
    ENTER   0, 288
    mov     x19, x0
    mov     x20, x1
    adr     x28, 320f
    COPY    sp, M_P, x2, 0
    COPY    sp, (M_P + 32), x2, 32
    COPY    sp, (M_P + 64), x2, 64
    stp     xzr, xzr, [sp, #M_R]            /* R = (0 : 1 : 0), the point at infinity */
    stp     xzr, xzr, [sp, #M_R + 16]
    COPY    sp, (M_R + 32), x28, CRYPTO_P256_MOD_ONE
    stp     xzr, xzr, [sp, #M_R + 64]
    stp     xzr, xzr, [sp, #M_R + 80]
    mov     x21, #255
1:  mov     x0, sp
    mov     x1, sp
    bl      crypto_p256_point_double
    add     x0, sp, #M_T
    mov     x1, sp
    add     x2, sp, #M_P
    bl      crypto_p256_point_add
    lsr     x9, x21, #6
    ldr     x10, [x20, x9, lsl #3]
    lsr     x10, x10, x21
    and     x10, x10, #1
    neg     x10, x10
    mov     x9, #0
    add     x11, sp, #M_T
2:  ldr     x12, [sp, x9]
    ldr     x13, [x11, x9]
    eor     x13, x13, x12
    and     x13, x13, x10
    eor     x12, x12, x13
    str     x12, [sp, x9]
    add     x9, x9, #8
    cmp     x9, #96
    b.lo    2b
    subs    x21, x21, #1
    b.ge    1b
    COPY    x19, 0, sp, M_R
    COPY    x19, 32, sp, (M_R + 32)
    COPY    x19, 64, sp, (M_R + 64)
    LEAVE   0, 288
END_FUNCTION crypto_p256_point_mul

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
 * crypto_p256_point_add(point, first, second): point = first + second,
 * Renes-Costello-Batina algorithm 4 (a = -3). Any of the three may be the
 * same. x19 point, x27 b, x28 p record.
 */
LOCAL_FUNCTION crypto_p256_point_add
    ENTER   0, A_FRAME
    mov     x19, x0
    adr     x28, 320f
    adr     x27, 323f
    COPY    sp, A_X1, x1, 0
    COPY    sp, A_Y1, x1, 32
    COPY    sp, A_Z1, x1, 64
    COPY    sp, A_X2, x2, 0
    COPY    sp, A_Y2, x2, 32
    COPY    sp, A_Z2, x2, 64
    FMUL    A_T0, A_X1, A_X2                /* 1 */
    FMUL    A_T1, A_Y1, A_Y2                /* 2 */
    FMUL    A_T2, A_Z1, A_Z2                /* 3 */
    FADD    A_T3, A_X1, A_Y1                /* 4 */
    FADD    A_T4, A_X2, A_Y2                /* 5 */
    FMUL    A_T3, A_T3, A_T4                /* 6 */
    FADD    A_T4, A_T0, A_T1                /* 7 */
    FSUB    A_T3, A_T3, A_T4                /* 8 */
    FADD    A_T4, A_Y1, A_Z1                /* 9 */
    FADD    A_X3, A_Y2, A_Z2                /* 10 */
    FMUL    A_T4, A_T4, A_X3                /* 11 */
    FADD    A_X3, A_T1, A_T2                /* 12 */
    FSUB    A_T4, A_T4, A_X3                /* 13 */
    FADD    A_X3, A_X1, A_Z1                /* 14 */
    FADD    A_Y3, A_X2, A_Z2                /* 15 */
    FMUL    A_X3, A_X3, A_Y3                /* 16 */
    FADD    A_Y3, A_T0, A_T2                /* 17 */
    FSUB    A_Y3, A_X3, A_Y3                /* 18 */
    FMULB   A_Z3, A_T2                      /* 19 */
    FSUB    A_X3, A_Y3, A_Z3                /* 20 */
    FADD    A_Z3, A_X3, A_X3                /* 21 */
    FADD    A_X3, A_X3, A_Z3                /* 22 */
    FSUB    A_Z3, A_T1, A_X3                /* 23 */
    FADD    A_X3, A_T1, A_X3                /* 24 */
    FMULB   A_Y3, A_Y3                      /* 25 */
    FADD    A_T1, A_T2, A_T2                /* 26 */
    FADD    A_T2, A_T1, A_T2                /* 27 */
    FSUB    A_Y3, A_Y3, A_T2                /* 28 */
    FSUB    A_Y3, A_Y3, A_T0                /* 29 */
    FADD    A_T1, A_Y3, A_Y3                /* 30 */
    FADD    A_Y3, A_T1, A_Y3                /* 31 */
    FADD    A_T1, A_T0, A_T0                /* 32 */
    FADD    A_T0, A_T1, A_T0                /* 33 */
    FSUB    A_T0, A_T0, A_T2                /* 34 */
    FMUL    A_T1, A_T4, A_Y3                /* 35 */
    FMUL    A_T2, A_T0, A_Y3                /* 36 */
    FMUL    A_Y3, A_X3, A_Z3                /* 37 */
    FADD    A_Y3, A_Y3, A_T2                /* 38 */
    FMUL    A_X3, A_T3, A_X3                /* 39 */
    FSUB    A_X3, A_X3, A_T1                /* 40 */
    FMUL    A_Z3, A_T4, A_Z3                /* 41 */
    FMUL    A_T1, A_T3, A_T0                /* 42 */
    FADD    A_Z3, A_Z3, A_T1                /* 43 */
    COPY    x19, 0, sp, A_X3
    COPY    x19, 32, sp, A_Y3
    COPY    x19, 64, sp, A_Z3
    LEAVE   0, A_FRAME
END_FUNCTION crypto_p256_point_add

.set D_X, 0
.set D_Y, 32
.set D_Z, 64
.set D_T0, 96
.set D_T1, 128
.set D_T2, 160
.set D_T3, 192
.set D_X3, 224
.set D_Y3, 256
.set D_Z3, 288
.set D_FRAME, 320

/*
 * crypto_p256_point_double(point, base): point = 2 * base,
 * Renes-Costello-Batina algorithm 6 (a = -3). point may be base.
 * x19 point, x27 b, x28 p record.
 */
LOCAL_FUNCTION crypto_p256_point_double
    ENTER   0, D_FRAME
    mov     x19, x0
    adr     x28, 320f
    adr     x27, 323f
    COPY    sp, D_X, x1, 0
    COPY    sp, D_Y, x1, 32
    COPY    sp, D_Z, x1, 64
    FMUL    D_T0, D_X, D_X                  /* 1 */
    FMUL    D_T1, D_Y, D_Y                  /* 2 */
    FMUL    D_T2, D_Z, D_Z                  /* 3 */
    FMUL    D_T3, D_X, D_Y                  /* 4 */
    FADD    D_T3, D_T3, D_T3                /* 5 */
    FMUL    D_Z3, D_X, D_Z                  /* 6 */
    FADD    D_Z3, D_Z3, D_Z3                /* 7 */
    FMULB   D_Y3, D_T2                      /* 8 */
    FSUB    D_Y3, D_Y3, D_Z3                /* 9 */
    FADD    D_X3, D_Y3, D_Y3                /* 10 */
    FADD    D_Y3, D_X3, D_Y3                /* 11 */
    FSUB    D_X3, D_T1, D_Y3                /* 12 */
    FADD    D_Y3, D_T1, D_Y3                /* 13 */
    FMUL    D_Y3, D_X3, D_Y3                /* 14 */
    FMUL    D_X3, D_X3, D_T3                /* 15 */
    FADD    D_T3, D_T2, D_T2                /* 16 */
    FADD    D_T2, D_T2, D_T3                /* 17 */
    FMULB   D_Z3, D_Z3                      /* 18 */
    FSUB    D_Z3, D_Z3, D_T2                /* 19 */
    FSUB    D_Z3, D_Z3, D_T0                /* 20 */
    FADD    D_T3, D_Z3, D_Z3                /* 21 */
    FADD    D_Z3, D_Z3, D_T3                /* 22 */
    FADD    D_T3, D_T0, D_T0                /* 23 */
    FADD    D_T0, D_T3, D_T0                /* 24 */
    FSUB    D_T0, D_T0, D_T2                /* 25 */
    FMUL    D_T0, D_T0, D_Z3                /* 26 */
    FADD    D_Y3, D_Y3, D_T0                /* 27 */
    FMUL    D_T0, D_Y, D_Z                  /* 28 */
    FADD    D_T0, D_T0, D_T0                /* 29 */
    FMUL    D_Z3, D_T0, D_Z3                /* 30 */
    FSUB    D_X3, D_X3, D_Z3                /* 31 */
    FMUL    D_Z3, D_T0, D_T1                /* 32 */
    FADD    D_Z3, D_Z3, D_Z3                /* 33 */
    FADD    D_Z3, D_Z3, D_Z3                /* 34 */
    COPY    x19, 0, sp, D_X3
    COPY    x19, 32, sp, D_Y3
    COPY    x19, 64, sp, D_Z3
    LEAVE   0, D_FRAME
END_FUNCTION crypto_p256_point_double

/*
 * crypto_p256_point_affine(xy, point): x = X / Z and y = Y / Z as plain
 * limbs at xy and xy + 32. The point at infinity gives 0, 0.
 * x19 xy, x20 point, x28 p record. 1 / Z at sp, the number 1 at sp + 32.
 */
LOCAL_FUNCTION crypto_p256_point_affine
    ENTER   0, 64
    mov     x19, x0
    mov     x20, x1
    adr     x28, 320f
    SET_ONE 32
    mov     x0, sp
    add     x1, x20, #64
    adr     x2, 325f
    mov     x3, x28
    bl      crypto_p256_mod_pow
    mov     x0, x19
    mov     x1, x20
    mov     x2, sp
    mov     x3, x28
    bl      crypto_p256_mod_mul
    mov     x0, x19
    mov     x1, x19
    add     x2, sp, #32
    mov     x3, x28
    bl      crypto_p256_mod_mul
    add     x0, x19, #32
    add     x1, x20, #32
    mov     x2, sp
    mov     x3, x28
    bl      crypto_p256_mod_mul
    add     x0, x19, #32
    add     x1, x19, #32
    add     x2, sp, #32
    mov     x3, x28
    bl      crypto_p256_mod_mul
    LEAVE   0, 64
END_FUNCTION crypto_p256_point_affine

/* ---------------------------------------------------------------- Modular arithmetic */

/*
 * crypto_p256_mod_pow(result, base, exponent, modulus): base^exponent
 * in Montgomery form, by squaring and multiplying from bit 255 down. The
 * exponent is public. x19 result, x20 exponent, x21 modulus, x22 bit.
 * base at sp, the running value at sp + 32.
 */
LOCAL_FUNCTION crypto_p256_mod_pow
    ENTER   0, 64
    mov     x19, x0
    mov     x20, x2
    mov     x21, x3
    COPY    sp, 0, x1, 0
    COPY    sp, 32, x21, CRYPTO_P256_MOD_ONE
    mov     x22, #255
1:  add     x0, sp, #32
    add     x1, sp, #32
    add     x2, sp, #32
    mov     x3, x21
    bl      crypto_p256_mod_mul
    lsr     x9, x22, #6
    ldr     x10, [x20, x9, lsl #3]
    lsr     x10, x10, x22
    tbz     x10, #0, 2f
    add     x0, sp, #32
    add     x1, sp, #32
    mov     x2, sp
    mov     x3, x21
    bl      crypto_p256_mod_mul
2:  subs    x22, x22, #1
    b.ge    1b
    COPY    x19, 0, sp, 32
    LEAVE   0, 64
END_FUNCTION crypto_p256_mod_pow

/*
 * crypto_p256_mod_mul(result, a, b, modulus): a * b / 2^256 mod m, for
 * a, b < m (CIOS). result may be a or b.
 * a x4 to x7, T x8 to x13, b_i x14, q x15, product x16, m_j x17.
 */
LOCAL_FUNCTION crypto_p256_mod_mul
    UNWIND_END_PROLOGUE
    ldp     x4, x5, [x1]
    ldp     x6, x7, [x1, #16]
    mov     x8, #0
    mov     x9, #0
    mov     x10, #0
    mov     x11, #0
    mov     x12, #0
    mov     x13, #0
    .irp off, 0, 8, 16, 24
    ldr     x14, [x2, #\off]                /* T += a * b_i */
    mul     x16, x4, x14
    adds    x8, x8, x16
    mul     x16, x5, x14
    adcs    x9, x9, x16
    mul     x16, x6, x14
    adcs    x10, x10, x16
    mul     x16, x7, x14
    adcs    x11, x11, x16
    adcs    x12, x12, xzr
    adc     x13, xzr, xzr
    umulh   x16, x4, x14
    adds    x9, x9, x16
    umulh   x16, x5, x14
    adcs    x10, x10, x16
    umulh   x16, x6, x14
    adcs    x11, x11, x16
    umulh   x16, x7, x14
    adcs    x12, x12, x16
    adc     x13, x13, xzr
    ldr     x15, [x3, #CRYPTO_P256_MOD_INVERSE]
    mul     x15, x8, x15                    /* q = T0 * -m^-1 mod 2^64 */
    ldr     x17, [x3]                       /* T = (T + q * m) / 2^64 */
    mul     x16, x15, x17
    adds    xzr, x8, x16
    ldr     x17, [x3, #8]
    mul     x16, x15, x17
    adcs    x8, x9, x16
    ldr     x17, [x3, #16]
    mul     x16, x15, x17
    adcs    x9, x10, x16
    ldr     x17, [x3, #24]
    mul     x16, x15, x17
    adcs    x10, x11, x16
    adcs    x11, x12, xzr
    adc     x12, x13, xzr
    ldr     x17, [x3]
    umulh   x16, x15, x17
    adds    x8, x8, x16
    ldr     x17, [x3, #8]
    umulh   x16, x15, x17
    adcs    x9, x9, x16
    ldr     x17, [x3, #16]
    umulh   x16, x15, x17
    adcs    x10, x10, x16
    ldr     x17, [x3, #24]
    umulh   x16, x15, x17
    adcs    x11, x11, x16
    adc     x12, x12, xzr
    .endr
    ldp     x4, x5, [x3]                    /* T - m when T >= m */
    ldp     x6, x7, [x3, #16]
    subs    x4, x8, x4
    sbcs    x5, x9, x5
    sbcs    x6, x10, x6
    sbcs    x7, x11, x7
    sbcs    xzr, x12, xzr
    csel    x8, x4, x8, hs
    csel    x9, x5, x9, hs
    csel    x10, x6, x10, hs
    csel    x11, x7, x11, hs
    stp     x8, x9, [x0]
    stp     x10, x11, [x0, #16]
    ret
END_FUNCTION crypto_p256_mod_mul

/* crypto_p256_mod_add(result, a, b, modulus): a + b mod m, for a, b < m. */
LOCAL_FUNCTION crypto_p256_mod_add
    UNWIND_END_PROLOGUE
    ldp     x4, x5, [x1]
    ldp     x6, x7, [x1, #16]
    ldp     x8, x9, [x2]
    ldp     x10, x11, [x2, #16]
    adds    x4, x4, x8
    adcs    x5, x5, x9
    adcs    x6, x6, x10
    adcs    x7, x7, x11
    adc     x12, xzr, xzr
    ldp     x8, x9, [x3]
    ldp     x10, x11, [x3, #16]
    subs    x8, x4, x8
    sbcs    x9, x5, x9
    sbcs    x10, x6, x10
    sbcs    x11, x7, x11
    sbcs    xzr, x12, xzr
    csel    x4, x8, x4, hs
    csel    x5, x9, x5, hs
    csel    x6, x10, x6, hs
    csel    x7, x11, x7, hs
    stp     x4, x5, [x0]
    stp     x6, x7, [x0, #16]
    ret
END_FUNCTION crypto_p256_mod_add

/* crypto_p256_mod_sub(result, a, b, modulus): a - b mod m, for a, b < m. */
LOCAL_FUNCTION crypto_p256_mod_sub
    UNWIND_END_PROLOGUE
    ldp     x4, x5, [x1]
    ldp     x6, x7, [x1, #16]
    ldp     x8, x9, [x2]
    ldp     x10, x11, [x2, #16]
    subs    x4, x4, x8
    sbcs    x5, x5, x9
    sbcs    x6, x6, x10
    sbcs    x7, x7, x11
    sbc     x12, xzr, xzr                   /* all ones on a borrow */
    ldp     x8, x9, [x3]
    ldp     x10, x11, [x3, #16]
    and     x8, x8, x12
    and     x9, x9, x12
    and     x10, x10, x12
    and     x11, x11, x12
    adds    x4, x4, x8
    adcs    x5, x5, x9
    adcs    x6, x6, x10
    adc     x7, x7, x11
    stp     x4, x5, [x0]
    stp     x6, x7, [x0, #16]
    ret
END_FUNCTION crypto_p256_mod_sub

/* ---------------------------------------------------------------- Constants (SP 800-186 section 3.2.1.3) */

    .p2align 3
/* p = 2^256 - 2^224 + 2^192 + 2^96 - 1: p, -p^-1 mod 2^64, 2^256 mod p, 2^512 mod p. */
320:
    .quad   0xFFFFFFFFFFFFFFFF, 0x00000000FFFFFFFF, 0x0000000000000000, 0xFFFFFFFF00000001
    .quad   0x0000000000000001
    .quad   0x0000000000000001, 0xFFFFFFFF00000000, 0xFFFFFFFFFFFFFFFF, 0x00000000FFFFFFFE
    .quad   0x0000000000000003, 0xFFFFFFFBFFFFFFFF, 0xFFFFFFFFFFFFFFFE, 0x00000004FFFFFFFD
/* n, the group order: n, -n^-1 mod 2^64, 2^256 mod n, 2^512 mod n. */
321:
    .quad   0xF3B9CAC2FC632551, 0xBCE6FAADA7179E84, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF00000000
    .quad   0xCCD1C8AAEE00BC4F
    .quad   0x0C46353D039CDAAF, 0x4319055258E8617B, 0x0000000000000000, 0x00000000FFFFFFFF
    .quad   0x83244C95BE79EEA2, 0x4699799C49BD6FA6, 0x2845B2392B6BEC59, 0x66E12D94F3D95620
/* G: x, then y, in Montgomery form. */
322:
    .quad   0x79E730D418A9143C, 0x75BA95FC5FEDB601, 0x79FB732B77622510, 0x18905F76A53755C6
    .quad   0xDDF25357CE95560A, 0x8B4AB8E4BA19E45C, 0xD2E88688DD21F325, 0x8571FF1825885D85
/* b, in Montgomery form. */
323:
    .quad   0xD89CDF6229C4BDDF, 0xACF005CD78843090, 0xE5A220ABF7212ED6, 0xDC30061D04874834
/* p - 2: the exponent of 1 / a mod p. */
325:
    .quad   0xFFFFFFFFFFFFFFFD, 0x00000000FFFFFFFF, 0x0000000000000000, 0xFFFFFFFF00000001
/* n - 2: the exponent of 1 / a mod n. */
327:
    .quad   0xF3B9CAC2FC63254F, 0xBCE6FAADA7179E84, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF00000000
