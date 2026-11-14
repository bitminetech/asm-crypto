/*
 * Ed25519 (RFC 8032 section 5.1) for ARM64 (AAPCS64).
 * Requirements: docs/reference/ed25519.md. Layouts: include/ed25519.inc.
 *
 * Field elements are 4 limbs of 64 bits below 2^256, mod p = 2^255 - 19,
 * as in x25519.s. Points use extended coordinates and the complete
 * formulas of section 5.1.4. A scalar multiplication doubles and adds for
 * every bit and keeps the sum with a mask, so no branch or address depends
 * on a secret scalar. Numbers mod L use Montgomery multiplication (CIOS).
 * x18 is never used. Every function that calls keeps an x29 frame record.
 */
.set ISA_ARM64, 1
.include "crypto.inc"
.include "sha512.inc"
.include "ed25519.inc"
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

/* fn(sp + d, sp + a, sp + b). */
.macro OP fn, d, a, b
    add     x0, sp, #\d
    add     x1, sp, #\a
    add     x2, sp, #\b
    bl      \fn
.endm

.macro FMUL d, a, b
    OP      crypto_ed25519_fe_mul, \d, \a, \b
.endm

.macro FADD d, a, b
    OP      crypto_ed25519_fe_add, \d, \a, \b
.endm

.macro FSUB d, a, b
    OP      crypto_ed25519_fe_sub, \d, \a, \b
.endm

/* Copy 32 bytes from src + soff to dst + doff. Uses x9 to x14. */
.macro COPY32 dst, doff, src, soff
    add     x13, \src, #\soff
    add     x14, \dst, #\doff
    ldp     x9, x10, [x13]
    ldp     x11, x12, [x13, #16]
    stp     x9, x10, [x14]
    stp     x11, x12, [x14, #16]
.endm

/* Copy a 128-byte point. Uses x9 to x14. */
.macro COPY128 dst, doff, src, soff
    COPY32  \dst, \doff, \src, \soff
    COPY32  \dst, \doff + 32, \src, \soff + 32
    COPY32  \dst, \doff + 64, \src, \soff + 64
    COPY32  \dst, \doff + 96, \src, \soff + 96
.endm

/* Store the small number v as a field element at base + off. Uses x9, x13. */
.macro SETSMALL base, off, v
    add     x13, \base, #\off
    mov     x9, #\v
    stp     x9, xzr, [x13]
    stp     xzr, xzr, [x13, #16]
.endm

/* ---------------------------------------------------------------- Public key */

.set PK_H, 0                        /* SHA-512 of the private key, clamped */
.set PK_P, 64                       /* A */
.set PK_FRAME, 192

/* crypto_ed25519_public_key(private_key, public_key) -> status. x19 public_key. */
FUNCTION crypto_ed25519_public_key
    ENTER   0, PK_FRAME
    mov     x19, x1
    mov     x1, x0
    add     x0, sp, #PK_H
    bl      crypto_ed25519_expand
    add     x0, sp, #PK_P
    add     x1, sp, #PK_H
    adr     x2, 330f
    bl      crypto_ed25519_point_mul
    mov     x0, x19
    add     x1, sp, #PK_P
    bl      crypto_ed25519_point_encode
    mov     x0, #CRYPTO_OK
    LEAVE   0, PK_FRAME
END_FUNCTION crypto_ed25519_public_key

/* ---------------------------------------------------------------- Sign */

.set SG_H, 0                        /* a (clamped), then the prefix */
.set SG_RA, 64                      /* R, then A: encodings */
.set SG_RH, 128                     /* SHA-512(prefix || M) */
.set SG_KH, 192                     /* SHA-512(R || A || M) */
.set SG_R, 256                      /* r mod L */
.set SG_K, 288                      /* k mod L */
.set SG_T, 320                      /* k * a mod L */
.set SG_P, 352                      /* a point */
.set SG_FRAME, 480

/*
 * crypto_ed25519_sign(private_key, message, signature) -> status.
 * x19 message, x20 signature, x21 the modulus record of L.
 */
FUNCTION crypto_ed25519_sign
    ENTER   0, SG_FRAME
    mov     x19, x1
    mov     x20, x2
    adr     x21, 320f
    mov     x1, x0                          /* h = SHA-512(private key), a clamped */
    add     x0, sp, #SG_H
    bl      crypto_ed25519_expand
    add     x0, sp, #SG_P                   /* A = [a]B */
    add     x1, sp, #SG_H
    adr     x2, 330f
    bl      crypto_ed25519_point_mul
    add     x0, sp, #SG_RA + 32
    add     x1, sp, #SG_P
    bl      crypto_ed25519_point_encode
    add     x0, sp, #SG_RH                  /* r = SHA-512(prefix || M) mod L */
    add     x1, sp, #SG_H + 32
    mov     x2, #32
    mov     x3, x19
    bl      crypto_ed25519_hash
    add     x0, sp, #SG_R
    add     x1, sp, #SG_RH
    bl      crypto_ed25519_scalar_reduce
    add     x0, sp, #SG_P                   /* R = [r]B */
    add     x1, sp, #SG_R
    adr     x2, 330f
    bl      crypto_ed25519_point_mul
    add     x0, sp, #SG_RA
    add     x1, sp, #SG_P
    bl      crypto_ed25519_point_encode
    add     x0, sp, #SG_KH                  /* k = SHA-512(R || A || M) mod L */
    add     x1, sp, #SG_RA
    mov     x2, #64
    mov     x3, x19
    bl      crypto_ed25519_hash
    add     x0, sp, #SG_K
    add     x1, sp, #SG_KH
    bl      crypto_ed25519_scalar_reduce
    add     x0, sp, #SG_T                   /* k * a / 2^256, then * 2^512 / 2^256 */
    add     x1, sp, #SG_H
    add     x2, sp, #SG_K
    mov     x3, x21
    bl      crypto_ed25519_scalar_mul
    add     x0, sp, #SG_T
    add     x1, sp, #SG_T
    add     x2, x21, #CRYPTO_ED25519_MOD_R2
    mov     x3, x21
    bl      crypto_ed25519_scalar_mul
    add     x0, x20, #32                    /* S = r + k * a mod L */
    add     x1, sp, #SG_R
    add     x2, sp, #SG_T
    mov     x3, x21
    bl      crypto_ed25519_scalar_add
    mov     x15, sp
    COPY32  x20, 0, x15, SG_RA
    mov     x0, #CRYPTO_OK
    LEAVE   0, SG_FRAME
END_FUNCTION crypto_ed25519_sign

/* ---------------------------------------------------------------- Verify */

.set VF_A, 0                        /* the point A */
.set VF_P1, 128                     /* [S]B */
.set VF_P2, 256                     /* [k]A */
.set VF_KH, 384                     /* SHA-512(R || A || M) */
.set VF_K, 448                      /* k mod L */
.set VF_RA, 480                     /* R, then A: encodings */
.set VF_E, 544                      /* the encoding of [S]B - [k]A */
.set VF_ZERO, 576
.set VF_FRAME, 608

/*
 * crypto_ed25519_verify(public_key, message, signature, valid) -> status.
 * x19 public_key, x20 message, x21 signature, x22 valid.
 */
FUNCTION crypto_ed25519_verify
    ENTER   0, VF_FRAME
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    add     x0, sp, #VF_A
    mov     x1, x19
    bl      crypto_ed25519_point_decode
    cbz     x0, 1f
    mov     x0, #CRYPTO_INVALID_PUBLIC_KEY
    b       9f
1:  ldp     x9, x10, [x21, #32]             /* S < L, compared from the top limb */
    ldp     x11, x12, [x21, #48]
    adr     x13, 320f
    ldp     x14, x15, [x13]
    ldp     x16, x17, [x13, #16]
    subs    xzr, x9, x14
    sbcs    xzr, x10, x15
    sbcs    xzr, x11, x16
    sbcs    xzr, x12, x17
    b.hs    8f                              /* S >= L: not valid */
    mov     x15, sp
    COPY32  x15, VF_RA, x21, 0
    COPY32  x15, VF_RA + 32, x19, 0
    add     x0, sp, #VF_KH
    add     x1, sp, #VF_RA
    mov     x2, #64
    mov     x3, x20
    bl      crypto_ed25519_hash
    add     x0, sp, #VF_K
    add     x1, sp, #VF_KH
    bl      crypto_ed25519_scalar_reduce
    add     x0, sp, #VF_P1                  /* [S]B */
    add     x1, x21, #32
    adr     x2, 330f
    bl      crypto_ed25519_point_mul
    add     x0, sp, #VF_P2                  /* [k]A */
    add     x1, sp, #VF_K
    add     x2, sp, #VF_A
    bl      crypto_ed25519_point_mul
    mov     x15, sp
    SETSMALL x15, VF_ZERO, 0
    FSUB    VF_P2 + CRYPTO_ED25519_POINT_X, VF_ZERO, VF_P2 + CRYPTO_ED25519_POINT_X   /* -[k]A */
    FSUB    VF_P2 + CRYPTO_ED25519_POINT_T, VF_ZERO, VF_P2 + CRYPTO_ED25519_POINT_T
    add     x0, sp, #VF_P1
    add     x1, sp, #VF_P1
    add     x2, sp, #VF_P2
    bl      crypto_ed25519_point_add
    add     x0, sp, #VF_E
    add     x1, sp, #VF_P1
    bl      crypto_ed25519_point_encode
    add     x13, sp, #VF_E                  /* valid when the encoding equals R */
    ldp     x9, x10, [x13]
    ldp     x11, x12, [x13, #16]
    ldp     x14, x15, [x21]
    ldp     x16, x17, [x21, #16]
    eor     x9, x9, x14
    eor     x10, x10, x15
    eor     x11, x11, x16
    eor     x12, x12, x17
    orr     x9, x9, x10
    orr     x11, x11, x12
    orr     x9, x9, x11
    cmp     x9, #0
    cset    x9, eq
    str     x9, [x22]
    mov     x0, #CRYPTO_OK
    b       9f
8:  str     xzr, [x22]
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, VF_FRAME
END_FUNCTION crypto_ed25519_verify

/* ---------------------------------------------------------------- Hashing */

/*
 * crypto_ed25519_expand(h, private_key): h = SHA-512(private_key), then
 * the first half clamped as section 5.1.5 step 2 says. The 32-byte message
 * as a ByteList at sp. x19 h.
 */
LOCAL_FUNCTION crypto_ed25519_expand
    ENTER   0, 64
    mov     x19, x0
    mov     x9, #56                         /* size, offset, count */
    mov     x10, #24
    stp     x9, x10, [sp]
    mov     x9, #32
    str     x9, [sp, #16]
    mov     x15, sp
    COPY32  x15, 24, x1, 0
    mov     x0, sp
    mov     x1, x19
    CALL_GLOBAL crypto_sha512
    ldrb    w9, [x19]
    and     w9, w9, #248
    strb    w9, [x19]
    ldrb    w9, [x19, #31]
    and     w9, w9, #127
    orr     w9, w9, #64
    strb    w9, [x19, #31]
    LEAVE   0, 64
END_FUNCTION crypto_ed25519_expand

/*
 * crypto_ed25519_hash(digest, prefix, prefix_length, message): SHA-512 of
 * the prefix (32 or 64 bytes) followed by the message bytes. The state at
 * sp, the prefix as a ByteList at sp + 208. x19 digest, x20 message.
 */
LOCAL_FUNCTION crypto_ed25519_hash
    ENTER   0, 304
    mov     x19, x0
    mov     x20, x3
    mov     x9, #88                         /* size, offset, count */
    mov     x10, #24
    stp     x9, x10, [sp, #208]
    str     x2, [sp, #224]
    add     x11, sp, #232
1:  ldr     x9, [x1], #8
    str     x9, [x11], #8
    subs    x2, x2, #8
    b.ne    1b
    mov     x0, sp
    CALL_GLOBAL crypto_sha512_init
    mov     x0, sp
    add     x1, sp, #208
    CALL_GLOBAL crypto_sha512_update
    mov     x0, sp
    mov     x1, x20
    CALL_GLOBAL crypto_sha512_update
    mov     x0, sp
    mov     x1, x19
    CALL_GLOBAL crypto_sha512_final
    LEAVE   0, 304
END_FUNCTION crypto_ed25519_hash

/* ---------------------------------------------------------------- Numbers mod L */

/*
 * crypto_ed25519_scalar_reduce(result, h): the 64-byte little-endian h
 * mod L. With lo and hi the halves: lo * 2^256 + hi * 2^512 mod L, from
 * two Montgomery products, then one more by 1 removes the 2^256.
 * x19 result, x20 the modulus record. lo at sp, hi at sp + 32, the sum
 * at sp + 64, 1 at sp + 96.
 */
LOCAL_FUNCTION crypto_ed25519_scalar_reduce
    ENTER   0, 128
    mov     x19, x0
    adr     x20, 320f
    mov     x15, sp
    COPY32  x15, 0, x1, 0
    COPY32  x15, 32, x1, 32
    mov     x0, sp
    mov     x1, sp
    add     x2, x20, #CRYPTO_ED25519_MOD_R2
    mov     x3, x20
    bl      crypto_ed25519_scalar_mul
    add     x0, sp, #32
    add     x1, sp, #32
    add     x2, x20, #CRYPTO_ED25519_MOD_R3
    mov     x3, x20
    bl      crypto_ed25519_scalar_mul
    add     x0, sp, #64
    mov     x1, sp
    add     x2, sp, #32
    mov     x3, x20
    bl      crypto_ed25519_scalar_add
    mov     x15, sp
    SETSMALL x15, 96, 1
    mov     x0, x19
    add     x1, sp, #64
    add     x2, sp, #96
    mov     x3, x20
    bl      crypto_ed25519_scalar_mul
    LEAVE   0, 128
END_FUNCTION crypto_ed25519_scalar_reduce

/*
 * crypto_ed25519_scalar_mul(result, a, b, modulus): a * b / 2^256 mod m,
 * for a below 2^256 and b below m (CIOS). result may be a or b.
 * a x4 to x7, T x8 to x13, b_i x14, q x15, product x16, m_j x17.
 */
LOCAL_FUNCTION crypto_ed25519_scalar_mul
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
    ldr     x15, [x3, #CRYPTO_ED25519_MOD_INVERSE]
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
END_FUNCTION crypto_ed25519_scalar_mul

/* crypto_ed25519_scalar_add(result, a, b, modulus): a + b mod m, for a, b < m. */
LOCAL_FUNCTION crypto_ed25519_scalar_add
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
END_FUNCTION crypto_ed25519_scalar_add

/* ---------------------------------------------------------------- Points */

/*
 * crypto_ed25519_point_mul(result, scalar, point): [scalar]point for a
 * 32-byte little-endian scalar. From bit 255 down: double, add the point,
 * and keep the sum when the bit is 1, through a mask.
 * x19 result, x20 scalar, x21 bit index. The sum at sp, the next sum at
 * sp + 128, the point at sp + 256.
 */
LOCAL_FUNCTION crypto_ed25519_point_mul
    ENTER   0, 384
    mov     x19, x0
    mov     x20, x1
    mov     x15, sp
    COPY128 x15, 256, x2, 0
    SETSMALL x15, 0, 0                      /* the neutral point (0, 1, 1, 0) */
    SETSMALL x15, 32, 1
    SETSMALL x15, 64, 1
    SETSMALL x15, 96, 0
    mov     x21, #255
1:  mov     x0, sp
    mov     x1, sp
    bl      crypto_ed25519_point_double
    add     x0, sp, #128
    mov     x1, sp
    add     x2, sp, #256
    bl      crypto_ed25519_point_add
    lsr     x9, x21, #3                     /* mask = -bit */
    ldrb    w9, [x20, x9]
    and     x10, x21, #7
    lsr     x9, x9, x10
    and     x9, x9, #1
    neg     x9, x9
    mov     x10, #0
2:  ldr     x11, [sp, x10]                  /* sum ^= (sum ^ next) & mask */
    add     x12, x10, #128
    ldr     x12, [sp, x12]
    eor     x12, x12, x11
    and     x12, x12, x9
    eor     x11, x11, x12
    str     x11, [sp, x10]
    add     x10, x10, #8
    cmp     x10, #128
    b.lo    2b
    subs    x21, x21, #1
    b.ge    1b
    mov     x15, sp
    COPY128 x19, 0, x15, 0
    LEAVE   0, 384
END_FUNCTION crypto_ed25519_point_mul

.set PA_P, 0
.set PA_Q, 128
.set PA_A, 256
.set PA_B, 288
.set PA_C, 320
.set PA_D, 352
.set PA_E, 384
.set PA_F, 416
.set PA_G, 448
.set PA_H, 480
.set PA_T1, 512
.set PA_T2, 544
.set PA_FRAME, 576

/*
 * crypto_ed25519_point_add(result, p, q): p + q, with the formulas of
 * section 5.1.4. result may be p or q. x19 result.
 */
LOCAL_FUNCTION crypto_ed25519_point_add
    ENTER   0, PA_FRAME
    mov     x19, x0
    mov     x15, sp
    COPY128 x15, PA_P, x1, 0
    COPY128 x15, PA_Q, x2, 0
    FSUB    PA_T1, PA_P + 32, PA_P          /* A = (Y1 - X1) * (Y2 - X2) */
    FSUB    PA_T2, PA_Q + 32, PA_Q
    FMUL    PA_A, PA_T1, PA_T2
    FADD    PA_T1, PA_P + 32, PA_P          /* B = (Y1 + X1) * (Y2 + X2) */
    FADD    PA_T2, PA_Q + 32, PA_Q
    FMUL    PA_B, PA_T1, PA_T2
    FMUL    PA_C, PA_P + 96, PA_Q + 96      /* C = T1 * 2d * T2 */
    add     x0, sp, #PA_C
    add     x1, sp, #PA_C
    adr     x2, 310f
    bl      crypto_ed25519_fe_mul
    FMUL    PA_D, PA_P + 64, PA_Q + 64      /* D = Z1 * 2 * Z2 */
    FADD    PA_D, PA_D, PA_D
    FSUB    PA_E, PA_B, PA_A
    FSUB    PA_F, PA_D, PA_C
    FADD    PA_G, PA_D, PA_C
    FADD    PA_H, PA_B, PA_A
    mov     x0, x19                         /* X3 = E * F */
    add     x1, sp, #PA_E
    add     x2, sp, #PA_F
    bl      crypto_ed25519_fe_mul
    add     x0, x19, #32                    /* Y3 = G * H */
    add     x1, sp, #PA_G
    add     x2, sp, #PA_H
    bl      crypto_ed25519_fe_mul
    add     x0, x19, #96                    /* T3 = E * H */
    add     x1, sp, #PA_E
    add     x2, sp, #PA_H
    bl      crypto_ed25519_fe_mul
    add     x0, x19, #64                    /* Z3 = F * G */
    add     x1, sp, #PA_F
    add     x2, sp, #PA_G
    bl      crypto_ed25519_fe_mul
    LEAVE   0, PA_FRAME
END_FUNCTION crypto_ed25519_point_add

.set PD_P, 0
.set PD_A, 128
.set PD_B, 160
.set PD_C, 192
.set PD_H, 224
.set PD_E, 256
.set PD_G, 288
.set PD_F, 320
.set PD_T, 352
.set PD_FRAME, 384

/*
 * crypto_ed25519_point_double(result, p): 2p, with the doubling formulas
 * of section 5.1.4. result may be p. x19 result.
 */
LOCAL_FUNCTION crypto_ed25519_point_double
    ENTER   0, PD_FRAME
    mov     x19, x0
    mov     x15, sp
    COPY128 x15, PD_P, x1, 0
    FMUL    PD_A, PD_P, PD_P                /* A = X1^2 */
    FMUL    PD_B, PD_P + 32, PD_P + 32      /* B = Y1^2 */
    FMUL    PD_C, PD_P + 64, PD_P + 64      /* C = 2 * Z1^2 */
    FADD    PD_C, PD_C, PD_C
    FADD    PD_H, PD_A, PD_B                /* H = A + B */
    FADD    PD_T, PD_P, PD_P + 32           /* E = H - (X1 + Y1)^2 */
    FMUL    PD_T, PD_T, PD_T
    FSUB    PD_E, PD_H, PD_T
    FSUB    PD_G, PD_A, PD_B                /* G = A - B */
    FADD    PD_F, PD_C, PD_G                /* F = C + G */
    mov     x0, x19                         /* X3 = E * F */
    add     x1, sp, #PD_E
    add     x2, sp, #PD_F
    bl      crypto_ed25519_fe_mul
    add     x0, x19, #32                    /* Y3 = G * H */
    add     x1, sp, #PD_G
    add     x2, sp, #PD_H
    bl      crypto_ed25519_fe_mul
    add     x0, x19, #96                    /* T3 = E * H */
    add     x1, sp, #PD_E
    add     x2, sp, #PD_H
    bl      crypto_ed25519_fe_mul
    add     x0, x19, #64                    /* Z3 = F * G */
    add     x1, sp, #PD_F
    add     x2, sp, #PD_G
    bl      crypto_ed25519_fe_mul
    LEAVE   0, PD_FRAME
END_FUNCTION crypto_ed25519_point_double

/*
 * crypto_ed25519_point_encode(encoding, p): y = Y / Z with the low bit of
 * x = X / Z in bit 255 (section 5.1.2). x19 encoding, x20 p.
 * 1 / Z at sp, x at sp + 32, y at sp + 64.
 */
LOCAL_FUNCTION crypto_ed25519_point_encode
    ENTER   0, 96
    mov     x19, x0
    mov     x20, x1
    mov     x0, sp
    add     x1, x20, #64
    adr     x2, 300f
    bl      crypto_ed25519_fe_pow
    add     x0, sp, #32
    mov     x1, x20
    mov     x2, sp
    bl      crypto_ed25519_fe_mul
    add     x0, sp, #64
    add     x1, x20, #32
    mov     x2, sp
    bl      crypto_ed25519_fe_mul
    add     x0, sp, #32
    add     x1, sp, #32
    bl      crypto_ed25519_fe_freeze
    add     x0, sp, #64
    add     x1, sp, #64
    bl      crypto_ed25519_fe_freeze
    ldr     x9, [sp, #32]
    ldp     x10, x11, [sp, #64]
    ldp     x12, x13, [sp, #80]
    orr     x13, x13, x9, lsl #63
    stp     x10, x11, [x19]
    stp     x12, x13, [x19, #16]
    LEAVE   0, 96
END_FUNCTION crypto_ed25519_point_encode

.set DC_Y, 0
.set DC_U, 32
.set DC_V, 64
.set DC_V3, 96
.set DC_V7, 128
.set DC_X, 160
.set DC_T, 192
.set DC_W, 224
.set DC_N, 256
.set DC_ZERO, 288
.set DC_ONE, 320
.set DC_FRAME, 352

/* Compare the 32 bytes at sp + a and sp + b: Z set when equal. Uses x9 to x17. */
.macro FEQ a, b
    add     x13, sp, #\a
    add     x14, sp, #\b
    ldp     x9, x10, [x13]
    ldp     x11, x12, [x13, #16]
    ldp     x15, x16, [x14]
    eor     x9, x9, x15
    eor     x10, x10, x16
    ldp     x15, x16, [x14, #16]
    eor     x11, x11, x15
    eor     x12, x12, x16
    orr     x9, x9, x10
    orr     x11, x11, x12
    orr     x9, x9, x11
    cmp     x9, #0
.endm

/*
 * crypto_ed25519_point_decode(result, encoding) -> 0, or 1 when the
 * encoding is not a point: section 5.1.3, with y below p and no x = 0
 * with the sign bit set. Public data: it branches on it.
 * x19 result, x20 the sign bit.
 */
LOCAL_FUNCTION crypto_ed25519_point_decode
    ENTER   0, DC_FRAME
    mov     x19, x0
    ldp     x9, x10, [x1]
    ldp     x11, x12, [x1, #16]
    lsr     x20, x12, #63
    and     x12, x12, #0x7FFFFFFFFFFFFFFF
    stp     x9, x10, [sp, #DC_Y]
    stp     x11, x12, [sp, #DC_Y + 16]
    and     x13, x10, x11                   /* y >= p: the top limbs all ones and y0 >= 2^64 - 19 */
    cmn     x13, #1
    b.ne    1f
    mov     x13, #0x7FFFFFFFFFFFFFFF
    cmp     x12, x13
    b.ne    1f
    cmn     x9, #19
    b.hs    8f
1:  mov     x15, sp
    SETSMALL x15, DC_ZERO, 0
    SETSMALL x15, DC_ONE, 1
    FMUL    DC_U, DC_Y, DC_Y                /* u = y^2 - 1, v = d y^2 + 1 */
    add     x0, sp, #DC_V
    add     x1, sp, #DC_U
    adr     x2, 311f
    bl      crypto_ed25519_fe_mul
    FADD    DC_V, DC_V, DC_ONE
    FSUB    DC_U, DC_U, DC_ONE
    FMUL    DC_V3, DC_V, DC_V               /* v^3, v^7 */
    FMUL    DC_V3, DC_V3, DC_V
    FMUL    DC_V7, DC_V3, DC_V3
    FMUL    DC_V7, DC_V7, DC_V
    FMUL    DC_T, DC_U, DC_V7               /* x = u v^3 (u v^7)^((p - 5) / 8) */
    add     x0, sp, #DC_T
    add     x1, sp, #DC_T
    adr     x2, 301f
    bl      crypto_ed25519_fe_pow
    FMUL    DC_X, DC_U, DC_V3
    FMUL    DC_X, DC_X, DC_T
    FMUL    DC_W, DC_X, DC_X                /* v x^2 against u and -u */
    FMUL    DC_W, DC_W, DC_V
    add     x0, sp, #DC_W
    add     x1, sp, #DC_W
    bl      crypto_ed25519_fe_freeze
    add     x0, sp, #DC_U
    add     x1, sp, #DC_U
    bl      crypto_ed25519_fe_freeze
    FSUB    DC_N, DC_ZERO, DC_U
    add     x0, sp, #DC_N
    add     x1, sp, #DC_N
    bl      crypto_ed25519_fe_freeze
    FEQ     DC_W, DC_U
    b.eq    2f
    FEQ     DC_W, DC_N
    b.ne    8f
    add     x0, sp, #DC_X                   /* x = x * 2^((p - 1) / 4) */
    add     x1, sp, #DC_X
    adr     x2, 312f
    bl      crypto_ed25519_fe_mul
2:  add     x0, sp, #DC_X
    add     x1, sp, #DC_X
    bl      crypto_ed25519_fe_freeze
    FEQ     DC_X, DC_ZERO
    b.ne    3f
    cbnz    x20, 8f                         /* x = 0 with the sign bit set */
3:  ldr     x9, [sp, #DC_X]
    and     x9, x9, #1
    cmp     x9, x20
    b.eq    4f
    FSUB    DC_X, DC_ZERO, DC_X             /* x = p - x */
    add     x0, sp, #DC_X
    add     x1, sp, #DC_X
    bl      crypto_ed25519_fe_freeze
4:  mov     x15, sp
    COPY32  x19, 0, x15, DC_X
    COPY32  x19, 32, x15, DC_Y
    SETSMALL x19, 64, 1
    add     x0, x19, #96
    add     x1, sp, #DC_X
    add     x2, sp, #DC_Y
    bl      crypto_ed25519_fe_mul
    mov     x0, #0
    b       9f
8:  mov     x0, #1
9:  LEAVE   0, DC_FRAME
END_FUNCTION crypto_ed25519_point_decode

/* ---------------------------------------------------------------- Field arithmetic */

/*
 * crypto_ed25519_fe_pow(result, a, exponent): a^exponent for a public
 * exponent below 2^255, by squaring and multiplying from bit 254 down.
 * x19 result, x20 bit, x21 exponent. a at sp, the running value at sp + 32.
 */
LOCAL_FUNCTION crypto_ed25519_fe_pow
    ENTER   0, 64
    mov     x19, x0
    mov     x21, x2
    ldp     x9, x10, [x1]
    ldp     x11, x12, [x1, #16]
    stp     x9, x10, [sp]
    stp     x11, x12, [sp, #16]
    mov     x9, #1
    stp     x9, xzr, [sp, #32]
    stp     xzr, xzr, [sp, #48]
    mov     x20, #254
1:  add     x0, sp, #32
    add     x1, sp, #32
    add     x2, sp, #32
    bl      crypto_ed25519_fe_mul
    lsr     x10, x20, #6
    ldr     x9, [x21, x10, lsl #3]
    lsr     x9, x9, x20
    tbz     x9, #0, 2f
    add     x0, sp, #32
    add     x1, sp, #32
    mov     x2, sp
    bl      crypto_ed25519_fe_mul
2:  subs    x20, x20, #1
    b.ge    1b
    ldp     x9, x10, [sp, #32]
    ldp     x11, x12, [sp, #48]
    stp     x9, x10, [x19]
    stp     x11, x12, [x19, #16]
    LEAVE   0, 64
END_FUNCTION crypto_ed25519_fe_pow

/*
 * crypto_ed25519_fe_freeze(result, a): a mod p, below p. A leaf: folds
 * bit 255 twice, then subtracts p when the value is p or more, by a mask.
 */
LOCAL_FUNCTION crypto_ed25519_fe_freeze
    UNWIND_END_PROLOGUE
    ldp     x9, x10, [x1]
    ldp     x11, x12, [x1, #16]
    mov     x14, #19
    .rept 2
    lsr     x13, x12, #63                   /* 2^255 = 19 */
    and     x12, x12, #0x7FFFFFFFFFFFFFFF
    mul     x13, x13, x14
    adds    x9, x9, x13
    adcs    x10, x10, xzr
    adcs    x11, x11, xzr
    adc     x12, x12, xzr
    .endr
    adds    x13, x9, #19                    /* v + 19 reaches 2^255 when v >= p */
    adcs    x15, x10, xzr
    adcs    x16, x11, xzr
    adc     x17, x12, xzr
    tst     x17, #0x8000000000000000
    and     x17, x17, #0x7FFFFFFFFFFFFFFF
    csel    x9, x13, x9, ne
    csel    x10, x15, x10, ne
    csel    x11, x16, x11, ne
    csel    x12, x17, x12, ne
    stp     x9, x10, [x0]
    stp     x11, x12, [x0, #16]
    ret
END_FUNCTION crypto_ed25519_fe_freeze

/*
 * One column of the product: x11, x12, x13 += a * b, for the limbs a, b.
 * Uses x14, x15.
 */
.macro MULACC a, b
    mul     x14, \a, \b
    umulh   x15, \a, \b
    adds    x11, x11, x14
    adcs    x12, x12, x15
    adc     x13, x13, xzr
.endm

/* Store the low word of the column at sp + off and shift the column down. */
.macro COLUMN off
    str     x11, [sp, #\off]
    mov     x11, x12
    mov     x12, x13
    mov     x13, #0
.endm

/*
 * Store at x0 the low half x3 to x6 plus 38 times the high half x7 to x10,
 * folded below 2^256. Uses x11 to x17.
 */
.macro REDUCE38
    mov     x17, #38
    mul     x11, x7, x17
    umulh   x7, x7, x17
    mul     x12, x8, x17
    umulh   x8, x8, x17
    mul     x13, x9, x17
    umulh   x9, x9, x17
    mul     x14, x10, x17
    umulh   x10, x10, x17
    adds    x3, x3, x11
    adcs    x4, x4, x12
    adcs    x5, x5, x13
    adcs    x6, x6, x14
    adc     x10, x10, xzr
    adds    x4, x4, x7
    adcs    x5, x5, x8
    adcs    x6, x6, x9
    adc     x10, x10, xzr                   /* the top, below 39 */
    mul     x10, x10, x17
    adds    x3, x3, x10
    adcs    x4, x4, xzr
    adcs    x5, x5, xzr
    adcs    x6, x6, xzr
    cset    x10, hs
    mul     x10, x10, x17
    add     x3, x3, x10                     /* no carry: the sum wrapped, so it is small */
    stp     x3, x4, [x0]
    stp     x5, x6, [x0, #16]
.endm

/*
 * crypto_ed25519_fe_mul(result, a, b): a * b mod p, below 2^256, for a, b
 * below 2^256. result may be a or b. A leaf: a x3 to x6, b x7 to x10, the
 * column x11 to x13, products x14, x15. The 8-limb product at sp.
 */
LOCAL_FUNCTION crypto_ed25519_fe_mul
    sub     sp, sp, #64
    UNWIND_ALLOC 64
    UNWIND_END_PROLOGUE
    ldp     x3, x4, [x1]
    ldp     x5, x6, [x1, #16]
    ldp     x7, x8, [x2]
    ldp     x9, x10, [x2, #16]
    mov     x11, #0
    mov     x12, #0
    mov     x13, #0
    MULACC  x3, x7
    COLUMN  0
    MULACC  x3, x8
    MULACC  x4, x7
    COLUMN  8
    MULACC  x3, x9
    MULACC  x4, x8
    MULACC  x5, x7
    COLUMN  16
    MULACC  x3, x10
    MULACC  x4, x9
    MULACC  x5, x8
    MULACC  x6, x7
    COLUMN  24
    MULACC  x4, x10
    MULACC  x5, x9
    MULACC  x6, x8
    COLUMN  32
    MULACC  x5, x10
    MULACC  x6, x9
    COLUMN  40
    MULACC  x6, x10
    stp     x11, x12, [sp, #48]
    ldp     x3, x4, [sp]                    /* low half */
    ldp     x5, x6, [sp, #16]
    ldp     x7, x8, [sp, #32]               /* high half */
    ldp     x9, x10, [sp, #48]
    REDUCE38
    UNWIND_BEGIN_EPILOGUE
    add     sp, sp, #64
    UNWIND_FREE 64
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_ed25519_fe_mul

/*
 * crypto_ed25519_fe_add(result, a, b): a + b mod p, below 2^256. A leaf:
 * the sum x3 to x6, b x7 to x10, the fold x11.
 */
LOCAL_FUNCTION crypto_ed25519_fe_add
    UNWIND_END_PROLOGUE
    ldp     x3, x4, [x1]
    ldp     x5, x6, [x1, #16]
    ldp     x7, x8, [x2]
    ldp     x9, x10, [x2, #16]
    adds    x3, x3, x7
    adcs    x4, x4, x8
    adcs    x5, x5, x9
    adcs    x6, x6, x10
    cset    x11, hs                         /* 2^256 = 38 */
    mov     x12, #38
    mul     x11, x11, x12
    adds    x3, x3, x11
    adcs    x4, x4, xzr
    adcs    x5, x5, xzr
    adcs    x6, x6, xzr
    cset    x11, hs
    mul     x11, x11, x12
    add     x3, x3, x11
    stp     x3, x4, [x0]
    stp     x5, x6, [x0, #16]
    ret
END_FUNCTION crypto_ed25519_fe_add

/*
 * crypto_ed25519_fe_sub(result, a, b): a - b mod p, below 2^256. A leaf:
 * the difference x3 to x6, b x7 to x10, the fold x11.
 */
LOCAL_FUNCTION crypto_ed25519_fe_sub
    UNWIND_END_PROLOGUE
    ldp     x3, x4, [x1]
    ldp     x5, x6, [x1, #16]
    ldp     x7, x8, [x2]
    ldp     x9, x10, [x2, #16]
    subs    x3, x3, x7
    sbcs    x4, x4, x8
    sbcs    x5, x5, x9
    sbcs    x6, x6, x10
    cset    x11, lo                         /* a borrow of 2^256 = 38 */
    mov     x12, #38
    mul     x11, x11, x12
    subs    x3, x3, x11
    sbcs    x4, x4, xzr
    sbcs    x5, x5, xzr
    sbcs    x6, x6, xzr
    cset    x11, lo
    mul     x11, x11, x12
    sub     x3, x3, x11
    stp     x3, x4, [x0]
    stp     x5, x6, [x0, #16]
    ret
END_FUNCTION crypto_ed25519_fe_sub

/* ---------------------------------------------------------------- Constants (RFC 8032 section 5.1) */

    .p2align 3
/* p - 2: the exponent of 1 / a. */
300:
    .quad   0xFFFFFFFFFFFFFFEB, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF
/* (p - 5) / 8: the exponent of the square root candidate. */
301:
    .quad   0xFFFFFFFFFFFFFFFD, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x0FFFFFFFFFFFFFFF
/* 2d. */
310:
    .quad   0xEBD69B9426B2F159, 0x00E0149A8283B156, 0x198E80F2EEF3D130, 0x2406D9DC56DFFCE7
/* d = -121665 / 121666. */
311:
    .quad   0x75EB4DCA135978A3, 0x00700A4D4141D8AB, 0x8CC740797779E898, 0x52036CEE2B6FFE73
/* 2^((p - 1) / 4), a square root of -1. */
312:
    .quad   0xC4EE1B274A0EA0B0, 0x2F431806AD2FE478, 0x2B4D00993DFBD7A7, 0x2B8324804FC1DF0B
/* L, -L^-1 mod 2^64, 2^256 mod L, 2^512 mod L, 2^768 mod L. */
320:
    .quad   0x5812631A5CF5D3ED, 0x14DEF9DEA2F79CD6, 0x0000000000000000, 0x1000000000000000
    .quad   0xD2B51DA312547E1B
    .quad   0xD6EC31748D98951D, 0xC6EF5BF4737DCF70, 0xFFFFFFFFFFFFFFFE, 0x0FFFFFFFFFFFFFFF
    .quad   0xA40611E3449C0F01, 0xD00E1BA768859347, 0xCEEC73D217F5BE65, 0x0399411B7C309A3D
    .quad   0x2A9E49687B83A2DB, 0x278324E6AEF7F3EC, 0x8065DC6C04EC5B65, 0x0E530B773599CEC7
/* B: X, Y, Z = 1, T = X * Y. */
330:
    .quad   0xC9562D608F25D51A, 0x692CC7609525A7B2, 0xC0A4E231FDD6DC5C, 0x216936D3CD6E53FE
    .quad   0x6666666666666658, 0x6666666666666666, 0x6666666666666666, 0x6666666666666666
    .quad   0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x6DDE8AB3A5B7DDA3, 0x20F09F80775152F5, 0x66EA4E8E64ABE37D, 0x67875F0FD78B7665
