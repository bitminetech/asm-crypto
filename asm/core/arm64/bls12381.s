/*
 * BLS12-381 for ARM64 (AAPCS64): the field tower, the groups G1 and G2, the
 * optimal ate pairing, hash to G2 (RFC 9380) and the BLS signatures of the
 * proof of possession scheme, then the KZG commitments of blobs and cells
 * over it, as cryptography-specs v0.3.0 defines them
 * (EthLib/Cryptography/Bls and Kzg). The steps follow the spec. KZG is in
 * this object so that it can call the local helpers of BLS12-381.
 * Requirements: docs/reference/bls12-381.md, docs/reference/hash-to-curve.md,
 * docs/reference/bls-signatures.md, docs/reference/kzg.md,
 * docs/reference/kzg-cells.md. Layouts: include/bls12381.inc,
 * include/kzg.inc.
 *
 * Elements of Fp are 6 limbs of 64 bits, least significant first, in
 * Montgomery form a * 2^384 mod p. Points use Jacobian coordinates (X, Y,
 * Z), with Z = 0 for the point at infinity.
 * x18 is never used. Every function that calls keeps an x29 frame record.
 */
.set ISA_ARM64, 1
.include "crypto.inc"
.include "bls12381.inc"
.include "kzg.inc"
.include "platform.inc"

/*
 * Frame of a non-leaf function: x29, x30, x19-x28 at sp + extra, then
 * locals at sp + extra + 96. extra bytes of locals sit below at sp.
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

/* A leaf that needs x19 to x22: x19-x22 at sp, no frame record (a leaf does not touch x29 or x30). */
.macro LEAF_ENTER
    sub     sp, sp, #32
    UNWIND_ALLOC 32
    stp     x19, x20, [sp]
    UNWIND_SAVE_REGP x19, x20, 0, 32
    stp     x21, x22, [sp, #16]
    UNWIND_SAVE_REGP x21, x22, 16, 32
    UNWIND_END_PROLOGUE
.endm

.macro LEAF_LEAVE
    UNWIND_BEGIN_EPILOGUE
    ldp     x21, x22, [sp, #16]
    UNWIND_RESTORE_REGP x21, x22, 16
    ldp     x19, x20, [sp]
    UNWIND_RESTORE_REGP x19, x20, 0
    add     sp, sp, #32
    UNWIND_FREE 32
    UNWIND_END_EPILOGUE
    ret
.endm

/* ---------------------------------------------------------------- Macros */

/* x0 = ra + oa, x1 = rb + ob, x2 = rc + oc; then bl fn. */
.macro C3 fn, ra, oa, rb, ob, rc, oc
    add     x0, \ra, #\oa
    add     x1, \rb, #\ob
    add     x2, \rc, #\oc
    bl      \fn
.endm

.macro C2 fn, ra, oa, rb, ob
    add     x0, \ra, #\oa
    add     x1, \rb, #\ob
    bl      \fn
.endm

/* The same with a global function of this library. */
.macro G3 fn, ra, oa, rb, ob, rc, oc
    add     x0, \ra, #\oa
    add     x1, \rb, #\ob
    add     x2, \rc, #\oc
    CALL_GLOBAL \fn
.endm

.macro G2 fn, ra, oa, rb, ob
    add     x0, \ra, #\oa
    add     x1, \rb, #\ob
    CALL_GLOBAL \fn
.endm

.macro FMUL ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp_mul, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro FADD ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp_add, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro FSUB ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp_sub, \ra, \oa, \rb, \ob, \rc, \oc
.endm

/* Copy n bytes (a multiple of 16) from rs + os to rd + od. Uses x9 to x12. */
.macro COPY rd, od, rs, os, n
    add     x11, \rs, #\os
    add     x12, \rd, #\od
    .rept   (\n) / 16
    ldp     x9, x10, [x11], #16
    stp     x9, x10, [x12], #16
    .endr
.endm

/* Zero n bytes (a multiple of 16) at rd + od. Uses x12. */
.macro ZERO rd, od, n
    add     x12, \rd, #\od
    .rept   (\n) / 16
    stp     xzr, xzr, [x12], #16
    .endr
.endm

/* Flags eq when the n bytes (a multiple of 16) at rs + os are all zero. Uses x9 to x12. */
.macro IS_ZERO rs, os, n
    add     x12, \rs, #\os
    mov     x9, #0
    .rept   (\n) / 16
    ldp     x10, x11, [x12], #16
    orr     x9, x9, x10
    orr     x9, x9, x11
    .endr
    cmp     x9, #0
.endm

/* Flags eq when the n bytes (a multiple of 16) at ra + oa equal those at rb + ob. Uses x9 to x15. */
.macro EQUAL ra, oa, rb, ob, n
    add     x13, \ra, #\oa
    add     x14, \rb, #\ob
    mov     x15, #0
    .rept   (\n) / 16
    ldp     x9, x10, [x13], #16
    ldp     x11, x12, [x14], #16
    eor     x9, x9, x11
    eor     x10, x10, x12
    orr     x15, x15, x9
    orr     x15, x15, x10
    .endr
    cmp     x15, #0
.endm

/* The Fp element 1 (Montgomery form) at rd + od. Uses x9 to x12. */
.macro SET_ONE rd, od
    adr     x11, 900f
    add     x11, x11, #BLS_FP_RECORD_ONE
    add     x12, \rd, #\od
    .rept   3
    ldp     x9, x10, [x11], #16
    stp     x9, x10, [x12], #16
    .endr
.endm

/* ---------------------------------------------------------------- Fp */

/*
 * crypto_bls_fp_mul(result, a, b): a * b / 2^384 mod p, for a, b < p (CIOS).
 * result may be a or b. a x3 to x8, T x9 to x16, b_i x1, q x17, product
 * x19, p record x20, p_j x21.
 */
LOCAL_FUNCTION crypto_bls_fp_mul
    LEAF_ENTER
    ldp     x3, x4, [x1]
    ldp     x5, x6, [x1, #16]
    ldp     x7, x8, [x1, #32]
    adr     x20, 900f
    mov     x9, #0
    mov     x10, #0
    mov     x11, #0
    mov     x12, #0
    mov     x13, #0
    mov     x14, #0
    mov     x15, #0
    .irp off, 0, 8, 16, 24, 32, 40
    ldr     x1, [x2, #\off]                 /* T += a * b_i */
    mul     x19, x3, x1
    adds    x9, x9, x19
    mul     x19, x4, x1
    adcs    x10, x10, x19
    mul     x19, x5, x1
    adcs    x11, x11, x19
    mul     x19, x6, x1
    adcs    x12, x12, x19
    mul     x19, x7, x1
    adcs    x13, x13, x19
    mul     x19, x8, x1
    adcs    x14, x14, x19
    adcs    x15, x15, xzr
    adc     x16, xzr, xzr
    umulh   x19, x3, x1
    adds    x10, x10, x19
    umulh   x19, x4, x1
    adcs    x11, x11, x19
    umulh   x19, x5, x1
    adcs    x12, x12, x19
    umulh   x19, x6, x1
    adcs    x13, x13, x19
    umulh   x19, x7, x1
    adcs    x14, x14, x19
    umulh   x19, x8, x1
    adcs    x15, x15, x19
    adc     x16, x16, xzr
    ldr     x17, [x20, #BLS_FP_RECORD_INVERSE]
    mul     x17, x9, x17                    /* q = T0 * -p^-1 mod 2^64 */
    ldr     x21, [x20]                      /* T = (T + q * p) / 2^64 */
    mul     x19, x17, x21
    adds    xzr, x9, x19
    ldr     x21, [x20, #8]
    mul     x19, x17, x21
    adcs    x9, x10, x19
    ldr     x21, [x20, #16]
    mul     x19, x17, x21
    adcs    x10, x11, x19
    ldr     x21, [x20, #24]
    mul     x19, x17, x21
    adcs    x11, x12, x19
    ldr     x21, [x20, #32]
    mul     x19, x17, x21
    adcs    x12, x13, x19
    ldr     x21, [x20, #40]
    mul     x19, x17, x21
    adcs    x13, x14, x19
    adcs    x14, x15, xzr
    adc     x15, x16, xzr
    ldr     x21, [x20]
    umulh   x19, x17, x21
    adds    x9, x9, x19
    ldr     x21, [x20, #8]
    umulh   x19, x17, x21
    adcs    x10, x10, x19
    ldr     x21, [x20, #16]
    umulh   x19, x17, x21
    adcs    x11, x11, x19
    ldr     x21, [x20, #24]
    umulh   x19, x17, x21
    adcs    x12, x12, x19
    ldr     x21, [x20, #32]
    umulh   x19, x17, x21
    adcs    x13, x13, x19
    ldr     x21, [x20, #40]
    umulh   x19, x17, x21
    adcs    x14, x14, x19
    adc     x15, x15, xzr
    .endr
    ldp     x3, x4, [x20]                   /* T - p when T >= p */
    ldp     x5, x6, [x20, #16]
    ldp     x7, x8, [x20, #32]
    subs    x3, x9, x3
    sbcs    x4, x10, x4
    sbcs    x5, x11, x5
    sbcs    x6, x12, x6
    sbcs    x7, x13, x7
    sbcs    x8, x14, x8
    sbcs    xzr, x15, xzr
    csel    x9, x3, x9, hs
    csel    x10, x4, x10, hs
    csel    x11, x5, x11, hs
    csel    x12, x6, x12, hs
    csel    x13, x7, x13, hs
    csel    x14, x8, x14, hs
    stp     x9, x10, [x0]
    stp     x11, x12, [x0, #16]
    stp     x13, x14, [x0, #32]
    LEAF_LEAVE
END_FUNCTION crypto_bls_fp_mul

/* crypto_bls_fp_add(result, a, b): a + b mod p, for a, b < p. result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp_add
    UNWIND_END_PROLOGUE
    ldp     x3, x4, [x1]
    ldp     x5, x6, [x1, #16]
    ldp     x7, x8, [x1, #32]
    ldp     x9, x10, [x2]
    ldp     x11, x12, [x2, #16]
    ldp     x13, x14, [x2, #32]
    adds    x3, x3, x9
    adcs    x4, x4, x10
    adcs    x5, x5, x11
    adcs    x6, x6, x12
    adcs    x7, x7, x13
    adcs    x8, x8, x14
    adc     x15, xzr, xzr
    adr     x16, 900f
    ldp     x9, x10, [x16]
    ldp     x11, x12, [x16, #16]
    ldp     x13, x14, [x16, #32]
    subs    x9, x3, x9
    sbcs    x10, x4, x10
    sbcs    x11, x5, x11
    sbcs    x12, x6, x12
    sbcs    x13, x7, x13
    sbcs    x14, x8, x14
    sbcs    xzr, x15, xzr
    csel    x3, x9, x3, hs
    csel    x4, x10, x4, hs
    csel    x5, x11, x5, hs
    csel    x6, x12, x6, hs
    csel    x7, x13, x7, hs
    csel    x8, x14, x8, hs
    stp     x3, x4, [x0]
    stp     x5, x6, [x0, #16]
    stp     x7, x8, [x0, #32]
    ret
END_FUNCTION crypto_bls_fp_add

/* crypto_bls_fp_sub(result, a, b): a - b mod p, for a, b < p. result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp_sub
    UNWIND_END_PROLOGUE
    ldp     x3, x4, [x1]
    ldp     x5, x6, [x1, #16]
    ldp     x7, x8, [x1, #32]
    ldp     x9, x10, [x2]
    ldp     x11, x12, [x2, #16]
    ldp     x13, x14, [x2, #32]
    subs    x3, x3, x9
    sbcs    x4, x4, x10
    sbcs    x5, x5, x11
    sbcs    x6, x6, x12
    sbcs    x7, x7, x13
    sbcs    x8, x8, x14
    sbc     x15, xzr, xzr                   /* all ones on a borrow */
    adr     x16, 900f
    ldp     x9, x10, [x16]
    ldp     x11, x12, [x16, #16]
    ldp     x13, x14, [x16, #32]
    and     x9, x9, x15
    and     x10, x10, x15
    and     x11, x11, x15
    and     x12, x12, x15
    and     x13, x13, x15
    and     x14, x14, x15
    adds    x3, x3, x9
    adcs    x4, x4, x10
    adcs    x5, x5, x11
    adcs    x6, x6, x12
    adcs    x7, x7, x13
    adc     x8, x8, x14
    stp     x3, x4, [x0]
    stp     x5, x6, [x0, #16]
    stp     x7, x8, [x0, #32]
    ret
END_FUNCTION crypto_bls_fp_sub

/* crypto_bls_fp_neg(result, a): -a mod p, for a < p; 0 stays 0. result may be a. */
LOCAL_FUNCTION crypto_bls_fp_neg
    UNWIND_END_PROLOGUE
    ldp     x3, x4, [x1]
    ldp     x5, x6, [x1, #16]
    ldp     x7, x8, [x1, #32]
    orr     x15, x3, x4
    orr     x15, x15, x5
    orr     x15, x15, x6
    orr     x15, x15, x7
    orr     x15, x15, x8
    cmp     x15, #0
    csetm   x15, ne                         /* all ones when a != 0 */
    adr     x16, 900f
    ldp     x9, x10, [x16]
    ldp     x11, x12, [x16, #16]
    ldp     x13, x14, [x16, #32]
    subs    x9, x9, x3
    sbcs    x10, x10, x4
    sbcs    x11, x11, x5
    sbcs    x12, x12, x6
    sbcs    x13, x13, x7
    sbc     x14, x14, x8
    and     x9, x9, x15
    and     x10, x10, x15
    and     x11, x11, x15
    and     x12, x12, x15
    and     x13, x13, x15
    and     x14, x14, x15
    stp     x9, x10, [x0]
    stp     x11, x12, [x0, #16]
    stp     x13, x14, [x0, #32]
    ret
END_FUNCTION crypto_bls_fp_neg

/*
 * crypto_bls_fp_pow(result, base, exponent): base^e (Fp.powNat), with e the
 * 6 little-endian limbs at exponent, a public value. result may be base.
 * Square and multiply from the top set bit of e; e = 0 gives 1.
 */
.set FW_ACC, 0
.set FW_BASE, 48
.set FW_SIZE, 96
LOCAL_FUNCTION crypto_bls_fp_pow
    ENTER   0, FW_SIZE
    mov     x19, x0
    mov     x20, x2
    COPY    sp, FW_BASE, x1, 0, 48
    SET_ONE sp, FW_ACC
    mov     x21, #383                       /* bit index */
1:  lsr     x9, x21, #6                     /* skip the zero bits above the top set bit */
    ldr     x10, [x20, x9, lsl #3]
    lsr     x10, x10, x21
    tbnz    x10, #0, 2f
    subs    x21, x21, #1
    b.ge    1b
    b       4f
2:  FMUL    sp, FW_ACC, sp, FW_ACC, sp, FW_ACC
    lsr     x9, x21, #6
    ldr     x10, [x20, x9, lsl #3]
    lsr     x10, x10, x21
    tbz     x10, #0, 3f
    FMUL    sp, FW_ACC, sp, FW_ACC, sp, FW_BASE
3:  subs    x21, x21, #1
    b.ge    2b
4:  COPY    x19, 0, sp, FW_ACC, 48
    LEAVE   0, FW_SIZE
END_FUNCTION crypto_bls_fp_pow

/*
 * crypto_bls_fp_inverse(result, a): 1 / a (Fp.inverse); 0 gives 0. result
 * may be a. The binary extended Euclid algorithm, in variable time: u = a,
 * v = p, b = R^2, d = 0, with b a = u R^2 and d a = v R^2 mod p kept by each
 * step. It halves u and b (mod p) while u is even, and v and d while v is
 * even, then takes the smaller of u and v from the other, with b and d alike.
 * When u = 1, b = R^2 / a, the Montgomery form of 1 / a for a in Montgomery
 * form; when v = 1, d is. u x2 to x7, v x8 to x13, b x14 to x17, x19, x20,
 * d x21 to x26, p record x1.
 */
LOCAL_FUNCTION crypto_bls_fp_inverse
    sub     sp, sp, #80
    UNWIND_ALLOC 80
    stp     x19, x20, [sp]
    UNWIND_SAVE_REGP x19, x20, 0, 80
    stp     x21, x22, [sp, #16]
    UNWIND_SAVE_REGP x21, x22, 16, 80
    stp     x23, x24, [sp, #32]
    UNWIND_SAVE_REGP x23, x24, 32, 80
    stp     x25, x26, [sp, #48]
    UNWIND_SAVE_REGP x25, x26, 48, 80
    stp     x27, x28, [sp, #64]
    UNWIND_SAVE_REGP x27, x28, 64, 80
    UNWIND_END_PROLOGUE
    ldp     x2, x3, [x1]                    /* u = a */
    ldp     x4, x5, [x1, #16]
    ldp     x6, x7, [x1, #32]
    adr     x1, 900f
    orr     x27, x2, x3
    orr     x27, x27, x4
    orr     x27, x27, x5
    orr     x27, x27, x6
    orr     x27, x27, x7
    cbz     x27, 8f                         /* 0 gives 0 */
    ldp     x8, x9, [x1]                    /* v = p */
    ldp     x10, x11, [x1, #16]
    ldp     x12, x13, [x1, #32]
    ldp     x14, x15, [x1, #BLS_FP_RECORD_R2]       /* b = R^2 */
    ldp     x16, x17, [x1, #BLS_FP_RECORD_R2 + 16]
    ldp     x19, x20, [x1, #BLS_FP_RECORD_R2 + 32]
    mov     x21, #0                         /* d = 0 */
    mov     x22, #0
    mov     x23, #0
    mov     x24, #0
    mov     x25, #0
    mov     x26, #0
1:
    cmp     x2, #1
    orr     x27, x3, x4
    orr     x27, x27, x5
    orr     x27, x27, x6
    orr     x27, x27, x7
    ccmp    x27, #0, #0, eq
    b.eq    6f
    cmp     x8, #1
    orr     x27, x9, x10
    orr     x27, x27, x11
    orr     x27, x27, x12
    orr     x27, x27, x13
    ccmp    x27, #0, #0, eq
    b.eq    7f
    tbnz    x2, #0, 3f
2:                                          /* u even: u / 2, b / 2 mod p */
    extr    x2, x3, x2, #1
    extr    x3, x4, x3, #1
    extr    x4, x5, x4, #1
    extr    x5, x6, x5, #1
    extr    x6, x7, x6, #1
    lsr     x7, x7, #1
    sbfx    x27, x14, #0, #1
    ldr     x28, [x1, #0]
    and     x28, x28, x27
    adds    x14, x14, x28
    ldr     x28, [x1, #8]
    and     x28, x28, x27
    adcs    x15, x15, x28
    ldr     x28, [x1, #16]
    and     x28, x28, x27
    adcs    x16, x16, x28
    ldr     x28, [x1, #24]
    and     x28, x28, x27
    adcs    x17, x17, x28
    ldr     x28, [x1, #32]
    and     x28, x28, x27
    adcs    x19, x19, x28
    ldr     x28, [x1, #40]
    and     x28, x28, x27
    adcs    x20, x20, x28
    extr    x14, x15, x14, #1
    extr    x15, x16, x15, #1
    extr    x16, x17, x16, #1
    extr    x17, x19, x17, #1
    extr    x19, x20, x19, #1
    lsr     x20, x20, #1
    tbz     x2, #0, 2b
3:  tbnz    x8, #0, 5f
4:                                          /* v even: v / 2, d / 2 mod p */
    extr    x8, x9, x8, #1
    extr    x9, x10, x9, #1
    extr    x10, x11, x10, #1
    extr    x11, x12, x11, #1
    extr    x12, x13, x12, #1
    lsr     x13, x13, #1
    sbfx    x27, x21, #0, #1
    ldr     x28, [x1, #0]
    and     x28, x28, x27
    adds    x21, x21, x28
    ldr     x28, [x1, #8]
    and     x28, x28, x27
    adcs    x22, x22, x28
    ldr     x28, [x1, #16]
    and     x28, x28, x27
    adcs    x23, x23, x28
    ldr     x28, [x1, #24]
    and     x28, x28, x27
    adcs    x24, x24, x28
    ldr     x28, [x1, #32]
    and     x28, x28, x27
    adcs    x25, x25, x28
    ldr     x28, [x1, #40]
    and     x28, x28, x27
    adcs    x26, x26, x28
    extr    x21, x22, x21, #1
    extr    x22, x23, x22, #1
    extr    x23, x24, x23, #1
    extr    x24, x25, x24, #1
    extr    x25, x26, x25, #1
    lsr     x26, x26, #1
    tbz     x8, #0, 4b
5:  cmp     x2, x8                          /* u >= v: u - v, b - d; else v - u, d - b */
    sbcs    xzr, x3, x9
    sbcs    xzr, x4, x10
    sbcs    xzr, x5, x11
    sbcs    xzr, x6, x12
    sbcs    xzr, x7, x13
    b.lo    9f
    subs    x2, x2, x8
    sbcs    x3, x3, x9
    sbcs    x4, x4, x10
    sbcs    x5, x5, x11
    sbcs    x6, x6, x12
    sbcs    x7, x7, x13
    subs    x14, x14, x21
    sbcs    x15, x15, x22
    sbcs    x16, x16, x23
    sbcs    x17, x17, x24
    sbcs    x19, x19, x25
    sbcs    x20, x20, x26
    csetm   x27, lo
    ldr     x28, [x1, #0]
    and     x28, x28, x27
    adds    x14, x14, x28
    ldr     x28, [x1, #8]
    and     x28, x28, x27
    adcs    x15, x15, x28
    ldr     x28, [x1, #16]
    and     x28, x28, x27
    adcs    x16, x16, x28
    ldr     x28, [x1, #24]
    and     x28, x28, x27
    adcs    x17, x17, x28
    ldr     x28, [x1, #32]
    and     x28, x28, x27
    adcs    x19, x19, x28
    ldr     x28, [x1, #40]
    and     x28, x28, x27
    adcs    x20, x20, x28
    b       1b
9:
    subs    x8, x8, x2
    sbcs    x9, x9, x3
    sbcs    x10, x10, x4
    sbcs    x11, x11, x5
    sbcs    x12, x12, x6
    sbcs    x13, x13, x7
    subs    x21, x21, x14
    sbcs    x22, x22, x15
    sbcs    x23, x23, x16
    sbcs    x24, x24, x17
    sbcs    x25, x25, x19
    sbcs    x26, x26, x20
    csetm   x27, lo
    ldr     x28, [x1, #0]
    and     x28, x28, x27
    adds    x21, x21, x28
    ldr     x28, [x1, #8]
    and     x28, x28, x27
    adcs    x22, x22, x28
    ldr     x28, [x1, #16]
    and     x28, x28, x27
    adcs    x23, x23, x28
    ldr     x28, [x1, #24]
    and     x28, x28, x27
    adcs    x24, x24, x28
    ldr     x28, [x1, #32]
    and     x28, x28, x27
    adcs    x25, x25, x28
    ldr     x28, [x1, #40]
    and     x28, x28, x27
    adcs    x26, x26, x28
    b       1b
6:
    stp     x14, x15, [x0]
    stp     x16, x17, [x0, #16]
    stp     x19, x20, [x0, #32]
    b       10f
7:
    stp     x21, x22, [x0]
    stp     x23, x24, [x0, #16]
    stp     x25, x26, [x0, #32]
    b       10f
8:  stp     xzr, xzr, [x0]
    stp     xzr, xzr, [x0, #16]
    stp     xzr, xzr, [x0, #32]
10: UNWIND_BEGIN_EPILOGUE
    ldp     x27, x28, [sp, #64]
    UNWIND_RESTORE_REGP x27, x28, 64
    ldp     x25, x26, [sp, #48]
    UNWIND_RESTORE_REGP x25, x26, 48
    ldp     x23, x24, [sp, #32]
    UNWIND_RESTORE_REGP x23, x24, 32
    ldp     x21, x22, [sp, #16]
    UNWIND_RESTORE_REGP x21, x22, 16
    ldp     x19, x20, [sp]
    UNWIND_RESTORE_REGP x19, x20, 0
    add     sp, sp, #80
    UNWIND_FREE 80
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_bls_fp_inverse

/*
 * crypto_bls_fp_sqrt(result, a) -> status: c = a^((p + 1) / 4) (Fp.sqrt).
 * CRYPTO_OK and c when c * c = a; CRYPTO_INVALID_ENCODING when a is not a
 * square, and nothing is written. result may be a.
 */
.set FS_C, 0
.set FS_CC, 48
.set FS_SIZE, 96
LOCAL_FUNCTION crypto_bls_fp_sqrt
    ENTER   0, FS_SIZE
    mov     x19, x0
    mov     x20, x1
    add     x0, sp, #FS_C
    adr     x2, 918f
    bl      crypto_bls_fp_pow
    FMUL    sp, FS_CC, sp, FS_C, sp, FS_C
    EQUAL   sp, FS_CC, x20, 0, 48
    b.ne    9f
    COPY    x19, 0, sp, FS_C, 48
    mov     x0, #CRYPTO_OK
    LEAVE   0, FS_SIZE
9:  mov     x0, #CRYPTO_INVALID_ENCODING
    LEAVE   0, FS_SIZE
END_FUNCTION crypto_bls_fp_sqrt

/*
 * crypto_bls_fp_from_bytes(result, bytes) -> status: the 48 big-endian bytes
 * as an element of Fp, in Montgomery form (Fp.fromBytesBE).
 * CRYPTO_INVALID_ENCODING when the number is p or more; nothing is written.
 */
LOCAL_FUNCTION crypto_bls_fp_from_bytes
    ENTER   0, 48
    mov     x19, x0
    ldp     x14, x13, [x1]
    ldp     x12, x11, [x1, #16]
    ldp     x10, x9, [x1, #32]
    rev     x9, x9
    rev     x10, x10
    rev     x11, x11
    rev     x12, x12
    rev     x13, x13
    rev     x14, x14
    adr     x15, 900f
    ldp     x2, x3, [x15]
    ldp     x4, x5, [x15, #16]
    ldp     x6, x7, [x15, #32]
    cmp     x9, x2                          /* below p? */
    sbcs    xzr, x10, x3
    sbcs    xzr, x11, x4
    sbcs    xzr, x12, x5
    sbcs    xzr, x13, x6
    sbcs    xzr, x14, x7
    b.hs    9f
    stp     x9, x10, [sp]
    stp     x11, x12, [sp, #16]
    stp     x13, x14, [sp, #32]
    mov     x0, x19                         /* result = n * 2^768 / 2^384 */
    mov     x1, sp
    add     x2, x15, #BLS_FP_RECORD_R2
    bl      crypto_bls_fp_mul
    mov     x0, #CRYPTO_OK
    LEAVE   0, 48
9:  mov     x0, #CRYPTO_INVALID_ENCODING
    LEAVE   0, 48
END_FUNCTION crypto_bls_fp_from_bytes

/* crypto_bls_fp_canonical(result, a): the value of a (Montgomery form) as 6 little-endian limbs. */
LOCAL_FUNCTION crypto_bls_fp_canonical
    ENTER   0, 48
    mov     x9, #1
    stp     x9, xzr, [sp]
    stp     xzr, xzr, [sp, #16]
    stp     xzr, xzr, [sp, #32]
    mov     x2, sp                          /* a * 1 / 2^384 */
    bl      crypto_bls_fp_mul
    LEAVE   0, 48
END_FUNCTION crypto_bls_fp_canonical

/* crypto_bls_fp_to_bytes(bytes, a): the 48 big-endian bytes of a (Fp.toBytesBE). */
LOCAL_FUNCTION crypto_bls_fp_to_bytes
    ENTER   0, 48
    mov     x19, x0
    mov     x0, sp
    bl      crypto_bls_fp_canonical
    ldp     x9, x10, [sp]
    ldp     x11, x12, [sp, #16]
    ldp     x13, x14, [sp, #32]
    rev     x9, x9
    rev     x10, x10
    rev     x11, x11
    rev     x12, x12
    rev     x13, x13
    rev     x14, x14
    stp     x14, x13, [x19]
    stp     x12, x11, [x19, #16]
    stp     x10, x9, [x19, #32]
    LEAVE   0, 48
END_FUNCTION crypto_bls_fp_to_bytes

/*
 * crypto_bls_fp_sign_bit(bit, a): the u64 1 when the value y of a satisfies
 * y > p - y (Fp.signBit), else 0.
 */
LOCAL_FUNCTION crypto_bls_fp_sign_bit
    ENTER   0, 48
    mov     x19, x0
    mov     x0, sp
    bl      crypto_bls_fp_canonical
    ldp     x3, x4, [sp]
    ldp     x5, x6, [sp, #16]
    ldp     x7, x8, [sp, #32]
    adr     x16, 900f                       /* d = p - y */
    ldp     x9, x10, [x16]
    ldp     x11, x12, [x16, #16]
    ldp     x13, x14, [x16, #32]
    subs    x9, x9, x3
    sbcs    x10, x10, x4
    sbcs    x11, x11, x5
    sbcs    x12, x12, x6
    sbcs    x13, x13, x7
    sbc     x14, x14, x8
    cmp     x9, x3                          /* d - y borrows when y > d */
    sbcs    xzr, x10, x4
    sbcs    xzr, x11, x5
    sbcs    xzr, x12, x6
    sbcs    xzr, x13, x7
    sbcs    xzr, x14, x8
    cset    x9, lo
    str     x9, [x19]
    LEAVE   0, 48
END_FUNCTION crypto_bls_fp_sign_bit

/* ---------------------------------------------------------------- G1 */

/*
 * crypto_bls_g1_double(result, point): 2 * point (G1.double). result may be
 * point.
 */
.set GD_A, 0
.set GD_B, 48
.set GD_C, 96
.set GD_D, 144
.set GD_E, 192
.set GD_F, 240
.set GD_T, 288
.set GD_X, 336
.set GD_Y, 384
.set GD_Z, 432
.set GD_SIZE, 480
LOCAL_FUNCTION crypto_bls_g1_double
    ENTER   0, GD_SIZE
    mov     x19, x0
    mov     x20, x1
    IS_ZERO x20, 96, 48
    b.ne    1f
    COPY    x19, 0, x20, 0, 144
    LEAVE   0, GD_SIZE
1:  FMUL    sp, GD_A, x20, 0, x20, 0        /* A = X * X */
    FMUL    sp, GD_B, x20, 48, x20, 48      /* B = Y * Y */
    FMUL    sp, GD_C, sp, GD_B, sp, GD_B    /* C = B * B */
    FADD    sp, GD_T, x20, 0, sp, GD_B      /* t = (X + B)^2 - A - C */
    FMUL    sp, GD_T, sp, GD_T, sp, GD_T
    FSUB    sp, GD_T, sp, GD_T, sp, GD_A
    FSUB    sp, GD_T, sp, GD_T, sp, GD_C
    FADD    sp, GD_D, sp, GD_T, sp, GD_T    /* D = t + t */
    FADD    sp, GD_E, sp, GD_A, sp, GD_A    /* E = A + A + A */
    FADD    sp, GD_E, sp, GD_E, sp, GD_A
    FMUL    sp, GD_F, sp, GD_E, sp, GD_E    /* F = E * E */
    FADD    sp, GD_T, sp, GD_D, sp, GD_D    /* x' = F - (D + D) */
    FSUB    sp, GD_X, sp, GD_F, sp, GD_T
    FSUB    sp, GD_T, sp, GD_D, sp, GD_X    /* y' = E (D - x') - (C4 + C4) */
    FMUL    sp, GD_Y, sp, GD_E, sp, GD_T
    FADD    sp, GD_T, sp, GD_C, sp, GD_C
    FADD    sp, GD_T, sp, GD_T, sp, GD_T
    FADD    sp, GD_T, sp, GD_T, sp, GD_T
    FSUB    sp, GD_Y, sp, GD_Y, sp, GD_T
    FADD    sp, GD_T, x20, 48, x20, 48      /* z' = (Y + Y) Z */
    FMUL    sp, GD_Z, sp, GD_T, x20, 96
    COPY    x19, 0, sp, GD_X, 144
    LEAVE   0, GD_SIZE
END_FUNCTION crypto_bls_g1_double

/*
 * crypto_bls_g1_add(first, second, point) -> status: first + second
 * (G1.add). point may be first or second.
 */
.set GA_Z1Z1, 0
.set GA_Z2Z2, 48
.set GA_U1, 96
.set GA_U2, 144
.set GA_S1, 192
.set GA_S2, 240
.set GA_H, 288
.set GA_I, 336
.set GA_J, 384
.set GA_R, 432
.set GA_V, 480
.set GA_T, 528
.set GA_X, 576
.set GA_Y, 624
.set GA_Z, 672
.set GA_SIZE, 720
FUNCTION crypto_bls_g1_add
    ENTER   0, GA_SIZE
    mov     x19, x0                         /* first */
    mov     x20, x1                         /* second */
    mov     x21, x2                         /* point */
    IS_ZERO x19, 96, 48
    b.ne    1f
    COPY    x21, 0, x20, 0, 144             /* first at infinity: second */
    b       9f
1:  IS_ZERO x20, 96, 48
    b.ne    2f
    COPY    x21, 0, x19, 0, 144             /* second at infinity: first */
    b       9f
2:  FMUL    sp, GA_Z1Z1, x19, 96, x19, 96
    FMUL    sp, GA_Z2Z2, x20, 96, x20, 96
    FMUL    sp, GA_U1, x19, 0, sp, GA_Z2Z2
    FMUL    sp, GA_U2, x20, 0, sp, GA_Z1Z1
    FMUL    sp, GA_S1, x19, 48, x20, 96     /* s1 = Y1 Z2 z2z2 */
    FMUL    sp, GA_S1, sp, GA_S1, sp, GA_Z2Z2
    FMUL    sp, GA_S2, x20, 48, x19, 96     /* s2 = Y2 Z1 z1z1 */
    FMUL    sp, GA_S2, sp, GA_S2, sp, GA_Z1Z1
    EQUAL   sp, GA_U1, sp, GA_U2, 48
    b.ne    4f
    EQUAL   sp, GA_S1, sp, GA_S2, 48
    b.ne    3f
    mov     x0, x21                         /* equal points: double */
    mov     x1, x19
    bl      crypto_bls_g1_double
    b       9f
3:  SET_ONE x21, 0                          /* opposite points: infinity */
    SET_ONE x21, 48
    ZERO    x21, 96, 48
    b       9f
4:  FSUB    sp, GA_H, sp, GA_U2, sp, GA_U1  /* h = u2 - u1 */
    FADD    sp, GA_T, sp, GA_H, sp, GA_H    /* i = (2 h)^2 */
    FMUL    sp, GA_I, sp, GA_T, sp, GA_T
    FMUL    sp, GA_J, sp, GA_H, sp, GA_I    /* j = h i */
    FSUB    sp, GA_T, sp, GA_S2, sp, GA_S1  /* r = 2 (s2 - s1) */
    FADD    sp, GA_R, sp, GA_T, sp, GA_T
    FMUL    sp, GA_V, sp, GA_U1, sp, GA_I   /* v = u1 i */
    FMUL    sp, GA_X, sp, GA_R, sp, GA_R    /* x' = r^2 - j - 2 v */
    FSUB    sp, GA_X, sp, GA_X, sp, GA_J
    FSUB    sp, GA_X, sp, GA_X, sp, GA_V
    FSUB    sp, GA_X, sp, GA_X, sp, GA_V
    FSUB    sp, GA_T, sp, GA_V, sp, GA_X    /* y' = r (v - x') - 2 s1 j */
    FMUL    sp, GA_Y, sp, GA_R, sp, GA_T
    FADD    sp, GA_T, sp, GA_S1, sp, GA_S1
    FMUL    sp, GA_T, sp, GA_T, sp, GA_J
    FSUB    sp, GA_Y, sp, GA_Y, sp, GA_T
    FADD    sp, GA_T, x19, 96, x20, 96      /* z' = ((Z1 + Z2)^2 - z1z1 - z2z2) h */
    FMUL    sp, GA_T, sp, GA_T, sp, GA_T
    FSUB    sp, GA_T, sp, GA_T, sp, GA_Z1Z1
    FSUB    sp, GA_T, sp, GA_T, sp, GA_Z2Z2
    FMUL    sp, GA_Z, sp, GA_T, sp, GA_H
    COPY    x21, 0, sp, GA_X, 144
9:  mov     x0, #CRYPTO_OK
    LEAVE   0, GA_SIZE
END_FUNCTION crypto_bls_g1_add

/*
 * crypto_bls_g1_add_affine(result, point, xy): point + (x, y), for the
 * affine (x, y) of a point that is not the point at infinity
 * (madd-2007-bl). Each coordinate is that of crypto_bls_g1_add with second =
 * (x, y, 1): with z1z1 = Z1^2, u2 = x z1z1 and s2 = y Z1 z1z1, h = u2 - X1,
 * hh = h^2, i = 4 hh, j = h i, r = 2 (s2 - Y1), v = X1 i, X3 = r^2 - j - 2 v,
 * Y3 = r (v - X3) - 2 Y1 j, Z3 = (Z1 + h)^2 - z1z1 - hh = 2 Z1 h. result may
 * be point.
 */
.set GB_Z1Z1, 0
.set GB_U2, 48
.set GB_S2, 96
.set GB_H, 144
.set GB_HH, 192
.set GB_I, 240
.set GB_J, 288
.set GB_R, 336
.set GB_V, 384
.set GB_T, 432
.set GB_X, 480
.set GB_Y, 528
.set GB_Z, 576
.set GB_SIZE, 624
LOCAL_FUNCTION crypto_bls_g1_add_affine
    ENTER   0, GB_SIZE
    mov     x19, x0                         /* result */
    mov     x20, x1                         /* point */
    mov     x21, x2                         /* xy */
    IS_ZERO x20, 96, 48
    b.ne    1f
    COPY    x19, 0, x21, 0, 96              /* point at infinity: (x, y, 1) */
    SET_ONE x19, 96
    LEAVE   0, GB_SIZE
1:  FMUL    sp, GB_Z1Z1, x20, 96, x20, 96
    FMUL    sp, GB_U2, x21, 0, sp, GB_Z1Z1
    FMUL    sp, GB_S2, x21, 48, x20, 96
    FMUL    sp, GB_S2, sp, GB_S2, sp, GB_Z1Z1
    EQUAL   x20, 0, sp, GB_U2, 48
    b.ne    4f
    EQUAL   x20, 48, sp, GB_S2, 48
    b.ne    3f
    mov     x0, x19                         /* equal points: double */
    mov     x1, x20
    bl      crypto_bls_g1_double
    LEAVE   0, GB_SIZE
3:  SET_ONE x19, 0                          /* opposite points: infinity */
    SET_ONE x19, 48
    ZERO    x19, 96, 48
    LEAVE   0, GB_SIZE
4:  FSUB    sp, GB_H, sp, GB_U2, x20, 0     /* h = u2 - X1 */
    FMUL    sp, GB_HH, sp, GB_H, sp, GB_H   /* hh = h^2, i = 4 hh, j = h i */
    FADD    sp, GB_I, sp, GB_HH, sp, GB_HH
    FADD    sp, GB_I, sp, GB_I, sp, GB_I
    FMUL    sp, GB_J, sp, GB_H, sp, GB_I
    FSUB    sp, GB_R, sp, GB_S2, x20, 48    /* r = 2 (s2 - Y1) */
    FADD    sp, GB_R, sp, GB_R, sp, GB_R
    FMUL    sp, GB_V, x20, 0, sp, GB_I      /* v = X1 i */
    FMUL    sp, GB_X, sp, GB_R, sp, GB_R    /* X3 = r^2 - j - 2 v */
    FSUB    sp, GB_X, sp, GB_X, sp, GB_J
    FSUB    sp, GB_X, sp, GB_X, sp, GB_V
    FSUB    sp, GB_X, sp, GB_X, sp, GB_V
    FSUB    sp, GB_T, sp, GB_V, sp, GB_X    /* Y3 = r (v - X3) - 2 Y1 j */
    FMUL    sp, GB_Y, sp, GB_R, sp, GB_T
    FMUL    sp, GB_T, x20, 48, sp, GB_J
    FADD    sp, GB_T, sp, GB_T, sp, GB_T
    FSUB    sp, GB_Y, sp, GB_Y, sp, GB_T
    FADD    sp, GB_T, x20, 96, sp, GB_H     /* Z3 = (Z1 + h)^2 - z1z1 - hh */
    FMUL    sp, GB_T, sp, GB_T, sp, GB_T
    FSUB    sp, GB_T, sp, GB_T, sp, GB_Z1Z1
    FSUB    sp, GB_Z, sp, GB_T, sp, GB_HH
    COPY    x19, 0, sp, GB_X, 144
    LEAVE   0, GB_SIZE
END_FUNCTION crypto_bls_g1_add_affine

/* crypto_bls_g1_neg(point, negated) -> status: (X, -Y, Z) (G1.neg). */
FUNCTION crypto_bls_g1_neg
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    COPY    x20, 0, x19, 0, 48
    COPY    x20, 96, x19, 96, 48
    C2      crypto_bls_fp_neg, x20, 48, x19, 48
    mov     x0, #CRYPTO_OK
    LEAVE   0
END_FUNCTION crypto_bls_g1_neg

/*
 * crypto_bls_g1_mul(result, point, scalar): k * point (G1.mulNat), with k
 * the 4 little-endian limbs at scalar. Starts with the point at the highest
 * set bit of k, then doubles and adds down to bit 0. result may be point.
 */
.set GM_ACC, 0
.set GM_P, 144
.set GM_SIZE, 288
LOCAL_FUNCTION crypto_bls_g1_mul
    ENTER   0, GM_SIZE
    mov     x19, x0
    mov     x20, x2
    COPY    sp, GM_P, x1, 0, 144
    mov     x21, #255
0:  lsr     x9, x21, #6                     /* the highest set bit of k */
    ldr     x10, [x20, x9, lsl #3]
    lsr     x10, x10, x21
    tbnz    x10, #0, 3f
    subs    x21, x21, #1
    b.ge    0b
    SET_ONE sp, GM_ACC                      /* k = 0: the point at infinity */
    SET_ONE sp, GM_ACC + 48
    ZERO    sp, GM_ACC + 96, 48
    b       4f
3:  COPY    sp, GM_ACC, sp, GM_P, 144
    subs    x21, x21, #1
    b.lt    4f
1:  C2      crypto_bls_g1_double, sp, GM_ACC, sp, GM_ACC
    lsr     x9, x21, #6
    ldr     x10, [x20, x9, lsl #3]
    lsr     x10, x10, x21
    tbz     x10, #0, 2f
    G3      crypto_bls_g1_add, sp, GM_ACC, sp, GM_P, sp, GM_ACC
2:  subs    x21, x21, #1
    b.ge    1b
4:  COPY    x19, 0, sp, GM_ACC, 144
    LEAVE   0, GM_SIZE
END_FUNCTION crypto_bls_g1_mul

/*
 * crypto_bls_g1_affine(xy, point): x = X / Z^2 and y = Y / Z^3
 * (G1.toAffine); 0 and 0 at infinity.
 */
.set GF_ZI, 0
.set GF_ZI2, 48
.set GF_ZI3, 96
.set GF_SIZE, 144
LOCAL_FUNCTION crypto_bls_g1_affine
    ENTER   0, GF_SIZE
    mov     x19, x0
    mov     x20, x1
    IS_ZERO x20, 96, 48
    b.ne    1f
    ZERO    x19, 0, 96
    LEAVE   0, GF_SIZE
1:  C2      crypto_bls_fp_inverse, sp, GF_ZI, x20, 96
    FMUL    sp, GF_ZI2, sp, GF_ZI, sp, GF_ZI
    FMUL    sp, GF_ZI3, sp, GF_ZI2, sp, GF_ZI
    FMUL    x19, 0, x20, 0, sp, GF_ZI2
    FMUL    x19, 48, x20, 48, sp, GF_ZI3
    LEAVE   0, GF_SIZE
END_FUNCTION crypto_bls_g1_affine

/*
 * crypto_bls_g1_in_subgroup(point, valid): the u64 1 when r * point is the
 * point at infinity, or point is (G1.inSubgroup), else 0. For a point P of
 * E1 this holds exactly when sigma(P) = -x^2 P, with sigma(x, y) = (beta x, y)
 * (docs/reference/bls12-381.md), so it computes x^2 P = |x| (|x| P) and
 * compares: beta X Zt^2 = Xt Z^2 and Y Zt^3 = -Yt Z^3.
 */
.set GS_T, 0
.set GS_A, 144
.set GS_B, 192
.set GS_C, 240
.set GS_D, 288
.set GS_SIZE, 336
LOCAL_FUNCTION crypto_bls_g1_in_subgroup
    ENTER   0, GS_SIZE
    mov     x19, x0
    mov     x20, x1
    IS_ZERO x19, 96, 48
    b.eq    1f
    mov     x0, sp                          /* t = |x| (|x| P) = x^2 P */
    mov     x1, x19
    adr     x2, 926f
    bl      crypto_bls_g1_mul
    mov     x0, sp
    mov     x1, sp
    adr     x2, 926f
    bl      crypto_bls_g1_mul
    IS_ZERO sp, GS_T + 96, 48               /* x^2 P at infinity: sigma(P) is not */
    b.eq    2f
    FMUL    sp, GS_A, sp, GS_T + 96, sp, GS_T + 96  /* a = Zt^2, b = Z^2 */
    FMUL    sp, GS_B, x19, 96, x19, 96
    adr     x2, 928f                        /* c = beta X Zt^2, d = Xt Z^2 */
    add     x0, sp, #GS_C
    mov     x1, x19
    bl      crypto_bls_fp_mul
    FMUL    sp, GS_C, sp, GS_C, sp, GS_A
    FMUL    sp, GS_D, sp, GS_T, sp, GS_B
    EQUAL   sp, GS_C, sp, GS_D, 48
    b.ne    2f
    FMUL    sp, GS_A, sp, GS_A, sp, GS_T + 96  /* c = Y Zt^3, d = Yt Z^3 */
    FMUL    sp, GS_B, sp, GS_B, x19, 96
    FMUL    sp, GS_C, x19, 48, sp, GS_A
    FMUL    sp, GS_D, sp, GS_T + 48, sp, GS_B
    FADD    sp, GS_C, sp, GS_C, sp, GS_D    /* c + d = 0 */
    IS_ZERO sp, GS_C, 48
1:  cset    x9, eq
    str     x9, [x20]
    LEAVE   0, GS_SIZE
2:  str     xzr, [x20]
    LEAVE   0, GS_SIZE
END_FUNCTION crypto_bls_g1_in_subgroup

/*
 * crypto_bls_g1_uncompress(bytes, point) -> status: the point of a
 * compressed form (G1.uncompress), without the subgroup check.
 * CRYPTO_INVALID_ENCODING when the form breaks a rule or x is not the x of a
 * point; nothing is written then.
 */
.set GU_X, 0
.set GU_Y, 48
.set GU_Z, 96
.set GU_RHS, 144
.set GU_BIT, 192
.set GU_SIZE, 208
LOCAL_FUNCTION crypto_bls_g1_uncompress
    ENTER   0, GU_SIZE
    mov     x19, x0
    mov     x20, x1
    ldrb    w21, [x19]
    tbz     w21, #7, 8f                     /* no compression bit */
    tbz     w21, #6, 2f
    cmp     w21, #0xC0                      /* infinity: 0xC0, then zeros */
    b.ne    8f
    ldrb    w9, [x19, #1]                   /* bytes 1 to 47 */
    ldr     x10, [x19, #8]
    orr     x9, x9, x10
    ldp     x10, x11, [x19, #16]
    orr     x9, x9, x10
    orr     x9, x9, x11
    ldr     x10, [x19, #32]
    orr     x9, x9, x10
    ldr     x10, [x19, #40]
    orr     x9, x9, x10
    ldurh   w10, [x19, #2]
    orr     x9, x9, x10
    ldur    w10, [x19, #4]
    orr     x9, x9, x10
    cbnz    x9, 8f
    SET_ONE x20, 0
    SET_ONE x20, 48
    ZERO    x20, 96, 48
    b       9f
2:  COPY    sp, GU_RHS, x19, 0, 48          /* x with the flag bits cleared */
    ldrb    w9, [sp, #GU_RHS]
    and     w9, w9, #0x1F
    strb    w9, [sp, #GU_RHS]
    C2      crypto_bls_fp_from_bytes, sp, GU_X, sp, GU_RHS
    cbnz    x0, 8f
    FMUL    sp, GU_RHS, sp, GU_X, sp, GU_X  /* x^3 + 4 */
    FMUL    sp, GU_RHS, sp, GU_RHS, sp, GU_X
    adr     x9, 923f
    add     x0, sp, #GU_RHS
    add     x1, sp, #GU_RHS
    mov     x2, x9
    bl      crypto_bls_fp_add
    C2      crypto_bls_fp_sqrt, sp, GU_Y, sp, GU_RHS
    cbnz    x0, 8f
    C2      crypto_bls_fp_sign_bit, sp, GU_BIT, sp, GU_Y
    ldr     x9, [sp, #GU_BIT]
    ubfx    w10, w21, #5, #1
    cmp     x9, x10
    b.eq    3f
    C2      crypto_bls_fp_neg, sp, GU_Y, sp, GU_Y
3:  SET_ONE sp, GU_Z
    COPY    x20, 0, sp, GU_X, 144
9:  mov     x0, #CRYPTO_OK
    LEAVE   0, GU_SIZE
8:  mov     x0, #CRYPTO_INVALID_ENCODING
    LEAVE   0, GU_SIZE
END_FUNCTION crypto_bls_g1_uncompress

/*
 * crypto_bls_g1_decode(bytes, point) -> status: G1.uncompress, then the
 * subgroup check (decodeG1Export).
 */
.set GE_P, 0
.set GE_V, 144
.set GE_SIZE, 160
FUNCTION crypto_bls_g1_decode
    ENTER   0, GE_SIZE
    mov     x19, x0
    mov     x20, x1
    mov     x1, sp
    bl      crypto_bls_g1_uncompress
    cbnz    x0, 8f
    C2      crypto_bls_g1_in_subgroup, sp, GE_P, sp, GE_V
    ldr     x9, [sp, #GE_V]
    cbz     x9, 8f
    COPY    x20, 0, sp, GE_P, 144
    mov     x0, #CRYPTO_OK
    LEAVE   0, GE_SIZE
8:  mov     x0, #CRYPTO_INVALID_ENCODING
    LEAVE   0, GE_SIZE
END_FUNCTION crypto_bls_g1_decode

/* crypto_bls_g1_compress(point, bytes) -> status: G1.compress. */
.set GC_XY, 0
.set GC_BIT, 96
.set GC_SIZE, 112
FUNCTION crypto_bls_g1_compress
    ENTER   0, GC_SIZE
    mov     x19, x0
    mov     x20, x1
    IS_ZERO x19, 96, 48
    b.ne    1f
    ZERO    x20, 0, 48
    mov     w9, #0xC0
    strb    w9, [x20]
    b       9f
1:  C2      crypto_bls_g1_affine, sp, GC_XY, x19, 0
    C2      crypto_bls_fp_to_bytes, x20, 0, sp, GC_XY
    C2      crypto_bls_fp_sign_bit, sp, GC_BIT, sp, GC_XY + 48
    ldr     x9, [sp, #GC_BIT]
    ldrb    w10, [x20]
    orr     w10, w10, #0x80
    orr     w10, w10, w9, lsl #5
    strb    w10, [x20]
9:  mov     x0, #CRYPTO_OK
    LEAVE   0, GC_SIZE
END_FUNCTION crypto_bls_g1_compress

/* ---------------------------------------------------------------- Fp2 */

.macro F2MUL ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp2_mul, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro F2ADD ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp2_add, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro F2SUB ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp2_sub, \ra, \oa, \rb, \ob, \rc, \oc
.endm

/* crypto_bls_fp2_add(result, a, b): a + b (Fp2.add). result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp2_add
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    FADD    x19, 0, x20, 0, x21, 0
    FADD    x19, 48, x20, 48, x21, 48
    LEAVE   0
END_FUNCTION crypto_bls_fp2_add

/* crypto_bls_fp2_sub(result, a, b): a - b (Fp2.sub). result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp2_sub
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    FSUB    x19, 0, x20, 0, x21, 0
    FSUB    x19, 48, x20, 48, x21, 48
    LEAVE   0
END_FUNCTION crypto_bls_fp2_sub

/* crypto_bls_fp2_neg(result, a): -a (Fp2.neg). result may be a. */
LOCAL_FUNCTION crypto_bls_fp2_neg
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    C2      crypto_bls_fp_neg, x19, 0, x20, 0
    C2      crypto_bls_fp_neg, x19, 48, x20, 48
    LEAVE   0
END_FUNCTION crypto_bls_fp2_neg

/*
 * crypto_bls_fp2_mul(result, a, b): a * b = (a0 b0 - a1 b1, a0 b1 + a1 b0)
 * (Fp2.mul). result may be a or b.
 */
.set M2_T0, 0
.set M2_T1, 48
.set M2_T2, 96
.set M2_T3, 144
.set M2_SIZE, 192
LOCAL_FUNCTION crypto_bls_fp2_mul
    ENTER   0, M2_SIZE
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    FMUL    sp, M2_T0, x20, 0, x21, 0
    FMUL    sp, M2_T1, x20, 48, x21, 48
    FMUL    sp, M2_T2, x20, 0, x21, 48
    FMUL    sp, M2_T3, x20, 48, x21, 0
    FSUB    x19, 0, sp, M2_T0, sp, M2_T1
    FADD    x19, 48, sp, M2_T2, sp, M2_T3
    LEAVE   0, M2_SIZE
END_FUNCTION crypto_bls_fp2_mul

/* crypto_bls_fp2_mul_fp(result, a, k): (a0 k, a1 k), for k in Fp (Fp2.ofFp k * a). result may be a. */
LOCAL_FUNCTION crypto_bls_fp2_mul_fp
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    FMUL    x19, 0, x20, 0, x21, 0
    FMUL    x19, 48, x20, 48, x21, 0
    LEAVE   0
END_FUNCTION crypto_bls_fp2_mul_fp

/* crypto_bls_fp2_mul_nr(result, a): a (1 + u) = (a0 - a1, a0 + a1) (Fp2.mulByOnePlusI). result may be a. */
.set MN_T, 0
.set MN_SIZE, 48
LOCAL_FUNCTION crypto_bls_fp2_mul_nr
    ENTER   0, MN_SIZE
    mov     x19, x0
    mov     x20, x1
    FSUB    sp, MN_T, x20, 0, x20, 48
    FADD    x19, 48, x20, 0, x20, 48
    COPY    x19, 0, sp, MN_T, 48
    LEAVE   0, MN_SIZE
END_FUNCTION crypto_bls_fp2_mul_nr

/*
 * crypto_bls_fp2_inverse(result, a): (a0 / n, -a1 / n), n = a0^2 + a1^2
 * (Fp2.inverse); 0 gives 0. result may be a.
 */
.set I2_N, 0
.set I2_T, 48
.set I2_SIZE, 96
LOCAL_FUNCTION crypto_bls_fp2_inverse
    ENTER   0, I2_SIZE
    mov     x19, x0
    mov     x20, x1
    FMUL    sp, I2_N, x20, 0, x20, 0
    FMUL    sp, I2_T, x20, 48, x20, 48
    FADD    sp, I2_N, sp, I2_N, sp, I2_T
    C2      crypto_bls_fp_inverse, sp, I2_N, sp, I2_N
    FMUL    x19, 0, x20, 0, sp, I2_N
    FMUL    sp, I2_T, x20, 48, sp, I2_N
    C2      crypto_bls_fp_neg, x19, 48, sp, I2_T
    LEAVE   0, I2_SIZE
END_FUNCTION crypto_bls_fp2_inverse

/*
 * crypto_bls_fp2_sqrt(result, a) -> status: a square root of a, by the steps
 * of Fp2.sqrt. CRYPTO_INVALID_ENCODING when a is not a square; nothing is
 * written then. result may be a.
 */
.set Q2_S, 0
.set Q2_T, 48
.set Q2_C0, 96
.set Q2_C1, 144
.set Q2_SIZE, 192
LOCAL_FUNCTION crypto_bls_fp2_sqrt
    ENTER   0, Q2_SIZE
    mov     x19, x0
    mov     x20, x1
    IS_ZERO x20, 48, 48
    b.ne    3f
    C2      crypto_bls_fp_sqrt, sp, Q2_C0, x20, 0   /* c1 = 0: sqrt(c0), else (0, sqrt(-c0)) */
    cbnz    x0, 1f
    ZERO    sp, Q2_C1, 48
    b       7f
1:  C2      crypto_bls_fp_neg, sp, Q2_T, x20, 0
    C2      crypto_bls_fp_sqrt, sp, Q2_C1, sp, Q2_T
    cbnz    x0, 8f
    ZERO    sp, Q2_C0, 48
    b       7f
3:  FMUL    sp, Q2_S, x20, 0, x20, 0         /* n = c0^2 + c1^2, s = sqrt(n) */
    FMUL    sp, Q2_T, x20, 48, x20, 48
    FADD    sp, Q2_S, sp, Q2_S, sp, Q2_T
    C2      crypto_bls_fp_sqrt, sp, Q2_S, sp, Q2_S
    cbnz    x0, 8f
    FADD    sp, Q2_T, x20, 0, sp, Q2_S       /* sqrt((c0 + s) / 2) */
    adr     x2, 903f
    add     x0, sp, #Q2_T
    add     x1, sp, #Q2_T
    bl      crypto_bls_fp_mul
    C2      crypto_bls_fp_sqrt, sp, Q2_C0, sp, Q2_T
    cbz     x0, 4f
    FSUB    sp, Q2_T, x20, 0, sp, Q2_S       /* else sqrt((c0 - s) / 2) */
    adr     x2, 903f
    add     x0, sp, #Q2_T
    add     x1, sp, #Q2_T
    bl      crypto_bls_fp_mul
    C2      crypto_bls_fp_sqrt, sp, Q2_C0, sp, Q2_T
    cbnz    x0, 8f
4:  FADD    sp, Q2_T, sp, Q2_C0, sp, Q2_C0   /* c1 = a1 / (2 c0) */
    C2      crypto_bls_fp_inverse, sp, Q2_T, sp, Q2_T
    FMUL    sp, Q2_C1, x20, 48, sp, Q2_T
7:  COPY    x19, 0, sp, Q2_C0, 96
    mov     x0, #CRYPTO_OK
    LEAVE   0, Q2_SIZE
8:  mov     x0, #CRYPTO_INVALID_ENCODING
    LEAVE   0, Q2_SIZE
END_FUNCTION crypto_bls_fp2_sqrt

/*
 * crypto_bls_fp2_sign_bit(bit, a): Fp2.signBit: the sign bit of c1 when c1
 * is not 0, else that of c0, as the u64 1 or 0.
 */
LOCAL_FUNCTION crypto_bls_fp2_sign_bit
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    IS_ZERO x20, 48, 48
    b.eq    1f
    C2      crypto_bls_fp_sign_bit, x19, 0, x20, 48
    LEAVE   0
1:  C2      crypto_bls_fp_sign_bit, x19, 0, x20, 0
    LEAVE   0
END_FUNCTION crypto_bls_fp2_sign_bit

/* ---------------------------------------------------------------- G2 */

/* crypto_bls_g2_double(result, point): 2 * point (G2.double). result may be point. */
.set HD_A, 0
.set HD_B, 96
.set HD_C, 192
.set HD_D, 288
.set HD_E, 384
.set HD_F, 480
.set HD_T, 576
.set HD_X, 672
.set HD_Y, 768
.set HD_Z, 864
.set HD_SIZE, 960
LOCAL_FUNCTION crypto_bls_g2_double
    ENTER   0, HD_SIZE
    mov     x19, x0
    mov     x20, x1
    IS_ZERO x20, 192, 96
    b.ne    1f
    COPY    x19, 0, x20, 0, 288
    LEAVE   0, HD_SIZE
1:  F2MUL   sp, HD_A, x20, 0, x20, 0        /* A = X * X */
    F2MUL   sp, HD_B, x20, 96, x20, 96      /* B = Y * Y */
    F2MUL   sp, HD_C, sp, HD_B, sp, HD_B    /* C = B * B */
    F2ADD   sp, HD_T, x20, 0, sp, HD_B      /* D = 2 ((X + B)^2 - A - C) */
    F2MUL   sp, HD_T, sp, HD_T, sp, HD_T
    F2SUB   sp, HD_T, sp, HD_T, sp, HD_A
    F2SUB   sp, HD_T, sp, HD_T, sp, HD_C
    F2ADD   sp, HD_D, sp, HD_T, sp, HD_T
    F2ADD   sp, HD_E, sp, HD_A, sp, HD_A    /* E = 3 A */
    F2ADD   sp, HD_E, sp, HD_E, sp, HD_A
    F2MUL   sp, HD_F, sp, HD_E, sp, HD_E    /* F = E * E */
    F2ADD   sp, HD_T, sp, HD_D, sp, HD_D    /* x' = F - 2 D */
    F2SUB   sp, HD_X, sp, HD_F, sp, HD_T
    F2SUB   sp, HD_T, sp, HD_D, sp, HD_X    /* y' = E (D - x') - 8 C */
    F2MUL   sp, HD_Y, sp, HD_E, sp, HD_T
    F2ADD   sp, HD_T, sp, HD_C, sp, HD_C
    F2ADD   sp, HD_T, sp, HD_T, sp, HD_T
    F2ADD   sp, HD_T, sp, HD_T, sp, HD_T
    F2SUB   sp, HD_Y, sp, HD_Y, sp, HD_T
    F2ADD   sp, HD_T, x20, 96, x20, 96      /* z' = 2 Y Z */
    F2MUL   sp, HD_Z, sp, HD_T, x20, 192
    COPY    x19, 0, sp, HD_X, 288
    LEAVE   0, HD_SIZE
END_FUNCTION crypto_bls_g2_double

/*
 * crypto_bls_g2_add(result, first, second): first + second (G2.add). result
 * may be first or second. The temporaries are reused: h replaces u2, r
 * replaces s2, v replaces u1.
 */
.set HA_Z1Z1, 0
.set HA_Z2Z2, 96
.set HA_U1, 192
.set HA_U2, 288
.set HA_S1, 384
.set HA_S2, 480
.set HA_I, 576
.set HA_J, 672
.set HA_X, 768
.set HA_Y, 864
.set HA_Z, 960
.set HA_SIZE, 1056
LOCAL_FUNCTION crypto_bls_g2_add
    ENTER   0, HA_SIZE
    mov     x21, x0                         /* result */
    mov     x19, x1                         /* first */
    mov     x20, x2                         /* second */
    IS_ZERO x19, 192, 96
    b.ne    1f
    COPY    x21, 0, x20, 0, 288
    b       9f
1:  IS_ZERO x20, 192, 96
    b.ne    2f
    COPY    x21, 0, x19, 0, 288
    b       9f
2:  F2MUL   sp, HA_Z1Z1, x19, 192, x19, 192
    F2MUL   sp, HA_Z2Z2, x20, 192, x20, 192
    F2MUL   sp, HA_U1, x19, 0, sp, HA_Z2Z2
    F2MUL   sp, HA_U2, x20, 0, sp, HA_Z1Z1
    F2MUL   sp, HA_S1, x19, 96, x20, 192
    F2MUL   sp, HA_S1, sp, HA_S1, sp, HA_Z2Z2
    F2MUL   sp, HA_S2, x20, 96, x19, 192
    F2MUL   sp, HA_S2, sp, HA_S2, sp, HA_Z1Z1
    EQUAL   sp, HA_U1, sp, HA_U2, 96
    b.ne    4f
    EQUAL   sp, HA_S1, sp, HA_S2, 96
    b.ne    3f
    mov     x0, x21
    mov     x1, x19
    bl      crypto_bls_g2_double
    b       9f
3:  SET_ONE x21, 0                          /* the point at infinity: (1, 1, 0) */
    ZERO    x21, 48, 48
    SET_ONE x21, 96
    ZERO    x21, 144, 144
    b       9f
4:  F2SUB   sp, HA_U2, sp, HA_U2, sp, HA_U1 /* h = u2 - u1 */
    F2ADD   sp, HA_I, sp, HA_U2, sp, HA_U2  /* i = (2 h)^2 */
    F2MUL   sp, HA_I, sp, HA_I, sp, HA_I
    F2MUL   sp, HA_J, sp, HA_U2, sp, HA_I   /* j = h i */
    F2SUB   sp, HA_S2, sp, HA_S2, sp, HA_S1 /* r = 2 (s2 - s1) */
    F2ADD   sp, HA_S2, sp, HA_S2, sp, HA_S2
    F2MUL   sp, HA_U1, sp, HA_U1, sp, HA_I  /* v = u1 i */
    F2MUL   sp, HA_X, sp, HA_S2, sp, HA_S2  /* x' = r^2 - j - 2 v */
    F2SUB   sp, HA_X, sp, HA_X, sp, HA_J
    F2SUB   sp, HA_X, sp, HA_X, sp, HA_U1
    F2SUB   sp, HA_X, sp, HA_X, sp, HA_U1
    F2SUB   sp, HA_I, sp, HA_U1, sp, HA_X   /* y' = r (v - x') - 2 s1 j */
    F2MUL   sp, HA_Y, sp, HA_S2, sp, HA_I
    F2ADD   sp, HA_S1, sp, HA_S1, sp, HA_S1
    F2MUL   sp, HA_S1, sp, HA_S1, sp, HA_J
    F2SUB   sp, HA_Y, sp, HA_Y, sp, HA_S1
    F2ADD   sp, HA_I, x19, 192, x20, 192    /* z' = ((Z1 + Z2)^2 - z1z1 - z2z2) h */
    F2MUL   sp, HA_I, sp, HA_I, sp, HA_I
    F2SUB   sp, HA_I, sp, HA_I, sp, HA_Z1Z1
    F2SUB   sp, HA_I, sp, HA_I, sp, HA_Z2Z2
    F2MUL   sp, HA_Z, sp, HA_I, sp, HA_U2
    COPY    x21, 0, sp, HA_X, 288
9:  LEAVE   0, HA_SIZE
END_FUNCTION crypto_bls_g2_add

/* crypto_bls_g2_neg(result, point): (X, -Y, Z) (G2.neg). result may be point. */
LOCAL_FUNCTION crypto_bls_g2_neg
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    COPY    x19, 0, x20, 0, 96
    COPY    x19, 192, x20, 192, 96
    C2      crypto_bls_fp2_neg, x19, 96, x20, 96
    LEAVE   0
END_FUNCTION crypto_bls_g2_neg

/*
 * crypto_bls_g2_mul(result, point, scalar): k * point (G2.mulNat), with k
 * the 4 little-endian limbs at scalar. Starts with the point at the highest
 * set bit of k, then doubles and adds down to bit 0. result may be point.
 */
.set HM_ACC, 0
.set HM_P, 288
.set HM_SIZE, 576
LOCAL_FUNCTION crypto_bls_g2_mul
    ENTER   0, HM_SIZE
    mov     x19, x0
    mov     x20, x2
    COPY    sp, HM_P, x1, 0, 288
    mov     x21, #255
0:  lsr     x9, x21, #6                     /* the highest set bit of k */
    ldr     x10, [x20, x9, lsl #3]
    lsr     x10, x10, x21
    tbnz    x10, #0, 3f
    subs    x21, x21, #1
    b.ge    0b
    SET_ONE sp, HM_ACC                      /* k = 0: the point at infinity */
    ZERO    sp, HM_ACC + 48, 48
    SET_ONE sp, HM_ACC + 96
    ZERO    sp, HM_ACC + 144, 144
    b       4f
3:  COPY    sp, HM_ACC, sp, HM_P, 288
    subs    x21, x21, #1
    b.lt    4f
1:  C2      crypto_bls_g2_double, sp, HM_ACC, sp, HM_ACC
    lsr     x9, x21, #6
    ldr     x10, [x20, x9, lsl #3]
    lsr     x10, x10, x21
    tbz     x10, #0, 2f
    C3      crypto_bls_g2_add, sp, HM_ACC, sp, HM_ACC, sp, HM_P
2:  subs    x21, x21, #1
    b.ge    1b
4:  COPY    x19, 0, sp, HM_ACC, 288
    LEAVE   0, HM_SIZE
END_FUNCTION crypto_bls_g2_mul

/* crypto_bls_g2_affine(xy, point): x = X / Z^2, y = Y / Z^3 (G2.toAffine); 0 and 0 at infinity. */
.set HF_ZI, 0
.set HF_ZI2, 96
.set HF_ZI3, 192
.set HF_SIZE, 288
LOCAL_FUNCTION crypto_bls_g2_affine
    ENTER   0, HF_SIZE
    mov     x19, x0
    mov     x20, x1
    IS_ZERO x20, 192, 96
    b.ne    1f
    ZERO    x19, 0, 192
    LEAVE   0, HF_SIZE
1:  C2      crypto_bls_fp2_inverse, sp, HF_ZI, x20, 192
    F2MUL   sp, HF_ZI2, sp, HF_ZI, sp, HF_ZI
    F2MUL   sp, HF_ZI3, sp, HF_ZI2, sp, HF_ZI
    F2MUL   x19, 0, x20, 0, sp, HF_ZI2
    F2MUL   x19, 96, x20, 96, sp, HF_ZI3
    LEAVE   0, HF_SIZE
END_FUNCTION crypto_bls_g2_affine

/*
 * crypto_bls_g2_in_subgroup(point, valid): the u64 1 when r * point is the
 * point at infinity, or point is (G2.inSubgroup), else 0. For a point P of
 * E2 this holds exactly when psi(P) = x P (docs/reference/bls12-381.md), with
 * psi(X, Y, Z) = (c1Psi conj(X), c2Psi conj(Y), conj(Z)). So it computes
 * t = |x| P = -x P and compares psi(P) with -t: Xs Zt^2 = Xt Zs^2 and
 * Ys Zt^3 = -Yt Zs^3.
 */
.set HS_T, 0
.set HS_A, 288
.set HS_B, 384
.set HS_C, 480
.set HS_D, 576
.set HS_E, 672
.set HS_SIZE, 768
LOCAL_FUNCTION crypto_bls_g2_in_subgroup
    ENTER   0, HS_SIZE
    mov     x19, x0
    mov     x20, x1
    IS_ZERO x19, 192, 96
    b.eq    1f
    mov     x0, sp                          /* t = |x| P */
    mov     x1, x19
    adr     x2, 926f
    bl      crypto_bls_g2_mul
    IS_ZERO sp, HS_T + 192, 96              /* x P at infinity: psi(P) is not */
    b.eq    2f
    adr     x21, 907f                       /* c1Psi, then c2Psi */
    COPY    sp, HS_E, x19, 192, 48          /* e = Zs = conj(Z) */
    C2      crypto_bls_fp_neg, sp, HS_E + 48, x19, 240
    F2MUL   sp, HS_A, sp, HS_T + 192, sp, HS_T + 192    /* a = Zt^2, b = Zs^2 */
    F2MUL   sp, HS_B, sp, HS_E, sp, HS_E
    COPY    sp, HS_C, x19, 0, 48            /* c = c1Psi conj(X) Zt^2, d = Xt Zs^2 */
    C2      crypto_bls_fp_neg, sp, HS_C + 48, x19, 48
    F2MUL   sp, HS_C, x21, 0, sp, HS_C
    F2MUL   sp, HS_C, sp, HS_C, sp, HS_A
    F2MUL   sp, HS_D, sp, HS_T, sp, HS_B
    EQUAL   sp, HS_C, sp, HS_D, 96
    b.ne    2f
    F2MUL   sp, HS_A, sp, HS_A, sp, HS_T + 192  /* a = Zt^3, b = Zs^3 */
    F2MUL   sp, HS_B, sp, HS_B, sp, HS_E
    COPY    sp, HS_C, x19, 96, 48           /* c = c2Psi conj(Y) Zt^3, d = Yt Zs^3 */
    C2      crypto_bls_fp_neg, sp, HS_C + 48, x19, 144
    F2MUL   sp, HS_C, x21, 96, sp, HS_C
    F2MUL   sp, HS_C, sp, HS_C, sp, HS_A
    F2MUL   sp, HS_D, sp, HS_T + 96, sp, HS_B
    F2ADD   sp, HS_C, sp, HS_C, sp, HS_D    /* c + d = 0 */
    IS_ZERO sp, HS_C, 96
1:  cset    x9, eq
    str     x9, [x20]
    LEAVE   0, HS_SIZE
2:  str     xzr, [x20]
    LEAVE   0, HS_SIZE
END_FUNCTION crypto_bls_g2_in_subgroup

/*
 * crypto_bls_g2_uncompress(bytes, point) -> status: the point of a
 * compressed form (G2.uncompress), without the subgroup check.
 * CRYPTO_INVALID_ENCODING when the form breaks a rule or x is not the x of a
 * point; nothing is written then.
 */
.set HU_X, 0
.set HU_Y, 96
.set HU_Z, 192
.set HU_RHS, 288
.set HU_BIT, 384
.set HU_SIZE, 400
LOCAL_FUNCTION crypto_bls_g2_uncompress
    ENTER   0, HU_SIZE
    mov     x19, x0
    mov     x20, x1
    ldrb    w21, [x19]
    tbz     w21, #7, 8f
    tbz     w21, #6, 2f
    cmp     w21, #0xC0                      /* infinity: 0xC0, then 95 zero bytes */
    b.ne    8f
    ldrb    w9, [x19, #1]
    ldurh   w10, [x19, #2]
    orr     x9, x9, x10
    ldur    w10, [x19, #4]
    orr     x9, x9, x10
    add     x11, x19, #8
    .rept   11
    ldr     x10, [x11], #8
    orr     x9, x9, x10
    .endr
    cbnz    x9, 8f
    SET_ONE x20, 0
    ZERO    x20, 48, 48
    SET_ONE x20, 96
    ZERO    x20, 144, 144
    b       9f
2:  COPY    sp, HU_RHS, x19, 0, 96          /* x1 with the flag bits cleared, then x0 */
    ldrb    w9, [sp, #HU_RHS]
    and     w9, w9, #0x1F
    strb    w9, [sp, #HU_RHS]
    C2      crypto_bls_fp_from_bytes, sp, HU_X + 48, sp, HU_RHS
    cbnz    x0, 8f
    C2      crypto_bls_fp_from_bytes, sp, HU_X, sp, HU_RHS + 48
    cbnz    x0, 8f
    F2MUL   sp, HU_RHS, sp, HU_X, sp, HU_X  /* x^3 + 4 (1 + u) */
    F2MUL   sp, HU_RHS, sp, HU_RHS, sp, HU_X
    adr     x9, 901f
    add     x0, sp, #HU_RHS
    add     x1, sp, #HU_RHS
    mov     x2, x9
    bl      crypto_bls_fp2_add
    C2      crypto_bls_fp2_sqrt, sp, HU_Y, sp, HU_RHS
    cbnz    x0, 8f
    C2      crypto_bls_fp2_sign_bit, sp, HU_BIT, sp, HU_Y
    ldr     x9, [sp, #HU_BIT]
    ubfx    w10, w21, #5, #1
    cmp     x9, x10
    b.eq    3f
    C2      crypto_bls_fp2_neg, sp, HU_Y, sp, HU_Y
3:  SET_ONE sp, HU_Z
    ZERO    sp, HU_Z + 48, 48
    COPY    x20, 0, sp, HU_X, 288
9:  mov     x0, #CRYPTO_OK
    LEAVE   0, HU_SIZE
8:  mov     x0, #CRYPTO_INVALID_ENCODING
    LEAVE   0, HU_SIZE
END_FUNCTION crypto_bls_g2_uncompress

/* crypto_bls_g2_decode(bytes, point) -> status: G2.uncompress, then the subgroup check (decodeG2Export). */
.set HE_P, 0
.set HE_V, 288
.set HE_SIZE, 304
FUNCTION crypto_bls_g2_decode
    ENTER   0, HE_SIZE
    mov     x19, x0
    mov     x20, x1
    mov     x1, sp
    bl      crypto_bls_g2_uncompress
    cbnz    x0, 8f
    C2      crypto_bls_g2_in_subgroup, sp, HE_P, sp, HE_V
    ldr     x9, [sp, #HE_V]
    cbz     x9, 8f
    COPY    x20, 0, sp, HE_P, 288
    mov     x0, #CRYPTO_OK
    LEAVE   0, HE_SIZE
8:  mov     x0, #CRYPTO_INVALID_ENCODING
    LEAVE   0, HE_SIZE
END_FUNCTION crypto_bls_g2_decode

/* crypto_bls_g2_compress(point, bytes) -> status: G2.compress. */
.set HC_XY, 0
.set HC_BIT, 192
.set HC_SIZE, 208
FUNCTION crypto_bls_g2_compress
    ENTER   0, HC_SIZE
    mov     x19, x0
    mov     x20, x1
    IS_ZERO x19, 192, 96
    b.ne    1f
    ZERO    x20, 0, 96
    mov     w9, #0xC0
    strb    w9, [x20]
    b       9f
1:  C2      crypto_bls_g2_affine, sp, HC_XY, x19, 0
    C2      crypto_bls_fp_to_bytes, x20, 0, sp, HC_XY + 48     /* c1 */
    C2      crypto_bls_fp_to_bytes, x20, 48, sp, HC_XY          /* c0 */
    C2      crypto_bls_fp2_sign_bit, sp, HC_BIT, sp, HC_XY + 96
    ldr     x9, [sp, #HC_BIT]
    ldrb    w10, [x20]
    orr     w10, w10, #0x80
    orr     w10, w10, w9, lsl #5
    strb    w10, [x20]
9:  mov     x0, #CRYPTO_OK
    LEAVE   0, HC_SIZE
END_FUNCTION crypto_bls_g2_compress

/* ---------------------------------------------------------------- Hash to G2 (HashToCurve.lean) */

/* Copy the bytes [rs, rs + rn) to rd; rd and rs end past the bytes, rn ends at 0. Uses w9. */
.macro COPYB rd, rs, rn
    cbz     \rn, 82f
81: ldrb    w9, [\rs], #1
    strb    w9, [\rd], #1
    subs    \rn, \rn, #1
    b.ne    81b
82:
.endm

/*
 * crypto_bls_xmd(message, dst, length, work, uniform): the first length
 * bytes of expand_message_xmd (expandMessageXmd), for length at most 8160,
 * written at uniform. work holds at least 360 + max(323 + count of
 * message, 17 + count of dst) bytes.
 */
.set XW_B0, 0
.set XW_BI, 32
.set XW_DSTP, 64
.set XW_DPLEN, 328
.set XW_BUF, 336
.set XW_DATA, 360
/* SHA-256 of the nreg bytes of the BUF data of work x22, digest at x22 + dig. */
.macro XHASH nreg, dig
    add     x0, x22, #XW_BUF
    mov     x10, #24
    add     x11, \nreg, #24
    stp     x11, x10, [x0]                  /* size, offset */
    str     \nreg, [x0, #16]                /* count */
    add     x1, x22, #\dig
    CALL_GLOBAL crypto_sha256
.endm

LOCAL_FUNCTION crypto_bls_xmd
    ENTER   0
    mov     x19, x0                         /* message */
    mov     x20, x1                         /* dst */
    ldr     x21, [x2]                       /* length */
    mov     x22, x3                         /* work */
    mov     x23, x4                         /* uniform */
    ldp     x24, x25, [x20, #8]             /* dst offset, count */
    add     x24, x20, x24
    add     x26, x22, #XW_DATA
    cmp     x25, #255
    b.ls    1f
    adr     x9, 930f                        /* a long DST: SHA-256("H2C-OVERSIZE-DST-" || DST) */
    ldp     x10, x11, [x9]
    stp     x10, x11, [x26]
    ldrb    w10, [x9, #16]
    strb    w10, [x26, #16]
    add     x10, x26, #17
    mov     x11, x24
    mov     x12, x25
    COPYB   x10, x11, x12
    add     x13, x25, #17
    XHASH   x13, XW_DSTP
    mov     x25, #32
    b       2f
1:  add     x10, x22, #XW_DSTP
    mov     x11, x24
    mov     x12, x25
    COPYB   x10, x11, x12
2:  add     x9, x22, #XW_DSTP               /* DST' = DST || I2OSP(len(DST), 1) */
    strb    w25, [x9, x25]
    add     x25, x25, #1
    str     x25, [x22, #XW_DPLEN]
    /* b_0 = H(Z_pad || msg || I2OSP(length, 2) || I2OSP(0, 1) || DST') */
    ZERO    x26, 0, 64
    add     x10, x26, #64
    ldp     x11, x12, [x19, #8]
    add     x11, x19, x11
    COPYB   x10, x11, x12
    lsr     w9, w21, #8
    strb    w9, [x10], #1
    strb    w21, [x10], #1
    strb    wzr, [x10], #1
    add     x11, x22, #XW_DSTP
    ldr     x12, [x22, #XW_DPLEN]
    COPYB   x10, x11, x12
    sub     x13, x10, x26
    XHASH   x13, XW_B0
    /* b_1 = H(b_0 || I2OSP(1, 1) || DST'); b_i = H((b_0 xor b_(i-1)) || I2OSP(i, 1) || DST') */
    COPY    x22, XW_DATA, x22, XW_B0, 32
    mov     x27, #1                         /* i */
    mov     x28, #0                         /* bytes written */
3:  add     x10, x26, #32
    strb    w27, [x10], #1
    add     x11, x22, #XW_DSTP
    ldr     x12, [x22, #XW_DPLEN]
    COPYB   x10, x11, x12
    sub     x13, x10, x26
    XHASH   x13, XW_BI
    sub     x12, x21, x28                   /* copy min(32, length - written) bytes */
    mov     x9, #32
    cmp     x12, x9
    csel    x12, x12, x9, lo
    add     x10, x23, x28
    add     x11, x22, #XW_BI
    add     x28, x28, x12
    COPYB   x10, x11, x12
    cmp     x28, x21
    b.hs    9f
    add     x27, x27, #1
    .irp off, 0, 8, 16, 24
    ldr     x9, [x22, #XW_B0 + \off]
    ldr     x10, [x22, #XW_BI + \off]
    eor     x9, x9, x10
    str     x9, [x26, #\off]
    .endr
    b       3b
9:  mov     x0, #CRYPTO_OK
    LEAVE   0
END_FUNCTION crypto_bls_xmd

/*
 * crypto_bls_fp_from_bytes64(result, bytes): the 64 big-endian bytes, a
 * number n below 2^512, as n mod p in Montgomery form (fpFromBytesL).
 * n = hi 2^384 + lo: result = lo * R^2 / R + hi * R^3 / R, with R = 2^384.
 */
.set F64_LO, 0
.set F64_HI, 48
.set F64_A, 96
.set F64_SIZE, 144
LOCAL_FUNCTION crypto_bls_fp_from_bytes64
    ENTER   0, F64_SIZE
    mov     x19, x0
    mov     x20, x1
    ldp     x10, x9, [x20, #48]             /* lo: bytes 16 to 63, least significant last */
    rev     x9, x9
    rev     x10, x10
    stp     x9, x10, [sp, #F64_LO]
    ldp     x10, x9, [x20, #32]
    rev     x9, x9
    rev     x10, x10
    stp     x9, x10, [sp, #F64_LO + 16]
    ldp     x10, x9, [x20, #16]
    rev     x9, x9
    rev     x10, x10
    stp     x9, x10, [sp, #F64_LO + 32]
    ldp     x10, x9, [x20]                  /* hi: bytes 0 to 15 */
    rev     x9, x9
    rev     x10, x10
    stp     x9, x10, [sp, #F64_HI]
    ZERO    sp, F64_HI + 16, 32
    adr     x2, 900f
    add     x2, x2, #BLS_FP_RECORD_R2
    add     x0, sp, #F64_A
    add     x1, sp, #F64_LO
    bl      crypto_bls_fp_mul
    adr     x2, 925f
    add     x0, sp, #F64_LO
    add     x1, sp, #F64_HI
    bl      crypto_bls_fp_mul
    FADD    x19, 0, sp, F64_A, sp, F64_LO
    LEAVE   0, F64_SIZE
END_FUNCTION crypto_bls_fp_from_bytes64

/*
 * crypto_bls_fp2_sgn0(bit, a): sgn0 of RFC 9380 section 4.1 for Fp2
 * (sgn0Fp2): s0 or (c0 = 0 and s1), with si the parity of ci, as the u64 1 or 0.
 */
.set SG_C, 0
.set SG_SIZE, 48
LOCAL_FUNCTION crypto_bls_fp2_sgn0
    ENTER   0, SG_SIZE
    mov     x19, x0
    mov     x20, x1
    C2      crypto_bls_fp_canonical, sp, SG_C, x20, 0
    ldr     x21, [sp, #SG_C]
    and     x21, x21, #1                    /* s0 */
    IS_ZERO sp, SG_C, 48
    cset    x22, eq                         /* z0 */
    C2      crypto_bls_fp_canonical, sp, SG_C, x20, 48
    ldr     x9, [sp, #SG_C]
    and     x9, x9, x22                     /* z0 and s1 */
    orr     x9, x9, x21
    str     x9, [x19]
    LEAVE   0, SG_SIZE
END_FUNCTION crypto_bls_fp2_sgn0

/*
 * crypto_bls_simple_swu(xy, u) -> status: the point (x, y) of E2' for u, by
 * the steps of simpleSwu (RFC 9380 section 6.6.2). CRYPTO_INVALID_ENCODING
 * when neither g(x1) nor g(x2) is a square, which the RFC excludes.
 */
.set SW_U2, 0
.set SW_ZU2, 96
.set SW_DEN, 192
.set SW_X1, 288
.set SW_GX, 384
.set SW_X, 480
.set SW_Y, 576
.set SW_T, 672
.set SW_S, 768
.set SW_BIT, 864
.set SW_SIZE, 880
LOCAL_FUNCTION crypto_bls_simple_swu
    ENTER   0, SW_SIZE
    mov     x19, x0
    mov     x20, x1
    adr     x21, 910f                       /* A', then B', then Z */
    F2MUL   sp, SW_U2, x20, 0, x20, 0       /* u2 = u u */
    F2MUL   sp, SW_ZU2, x21, 192, sp, SW_U2 /* zu2 = Z u2 */
    F2MUL   sp, SW_DEN, sp, SW_ZU2, sp, SW_ZU2
    F2ADD   sp, SW_DEN, sp, SW_DEN, sp, SW_ZU2
    IS_ZERO sp, SW_DEN, 96
    b.ne    1f
    F2MUL   sp, SW_T, x21, 192, x21, 0      /* x1 = B' / (Z A') */
    C2      crypto_bls_fp2_inverse, sp, SW_T, sp, SW_T
    F2MUL   sp, SW_X1, x21, 96, sp, SW_T
    b       2f
1:  C2      crypto_bls_fp2_neg, sp, SW_S, x21, 96      /* x1 = (-B' / A') (1 + 1 / denom) */
    C2      crypto_bls_fp2_inverse, sp, SW_T, x21, 0
    F2MUL   sp, SW_S, sp, SW_S, sp, SW_T
    C2      crypto_bls_fp2_inverse, sp, SW_T, sp, SW_DEN
    adr     x9, 900f
    add     x9, x9, #BLS_FP_RECORD_ONE
    add     x0, sp, #SW_T
    add     x1, sp, #SW_T
    mov     x2, x9
    bl      crypto_bls_fp_add               /* 1 + c0; c1 unchanged */
    F2MUL   sp, SW_X1, sp, SW_S, sp, SW_T
2:  COPY    sp, SW_X, sp, SW_X1, 96
    C2      crypto_bls_swu_g, sp, SW_GX, sp, SW_X   /* gx1 = x1^3 + A' x1 + B' */
    C2      crypto_bls_fp2_sqrt, sp, SW_Y, sp, SW_GX
    cbz     x0, 3f
    F2MUL   sp, SW_X, sp, SW_ZU2, sp, SW_X1 /* x2 = zu2 x1 */
    C2      crypto_bls_swu_g, sp, SW_GX, sp, SW_X
    C2      crypto_bls_fp2_sqrt, sp, SW_Y, sp, SW_GX
    cbnz    x0, 8f
3:  C2      crypto_bls_fp2_sgn0, sp, SW_BIT, x20, 0
    C2      crypto_bls_fp2_sgn0, sp, SW_BIT + 8, sp, SW_Y
    add     x11, sp, #SW_BIT
    ldp     x9, x10, [x11]
    cmp     x9, x10
    b.eq    4f
    C2      crypto_bls_fp2_neg, sp, SW_Y, sp, SW_Y
4:  COPY    x19, 0, sp, SW_X, 192
    mov     x0, #CRYPTO_OK
    LEAVE   0, SW_SIZE
8:  mov     x0, #CRYPTO_INVALID_ENCODING
    LEAVE   0, SW_SIZE
END_FUNCTION crypto_bls_simple_swu

/* crypto_bls_swu_g(result, x): x^3 + A' x + B' on E2'. */
.set SV_T, 0
.set SV_SIZE, 96
LOCAL_FUNCTION crypto_bls_swu_g
    ENTER   0, SV_SIZE
    mov     x19, x0
    mov     x20, x1
    adr     x21, 910f
    F2MUL   x19, 0, x20, 0, x20, 0
    F2MUL   x19, 0, x19, 0, x20, 0
    F2MUL   sp, SV_T, x21, 0, x20, 0
    F2ADD   x19, 0, x19, 0, sp, SV_T
    F2ADD   x19, 0, x19, 0, x21, 96
    LEAVE   0, SV_SIZE
END_FUNCTION crypto_bls_swu_g

/*
 * crypto_bls_iso_map_g2(point, xy): the 3-isogeny of RFC 9380 appendix E.3
 * (isoMapG2): (x_num / x_den, y' y_num / y_den, 1), or the point at
 * infinity when a denominator is 0.
 */
.set IM_X2, 0
.set IM_X3, 96
.set IM_XN, 192
.set IM_XD, 288
.set IM_YN, 384
.set IM_YD, 480
.set IM_T, 576
.set IM_SIZE, 672
LOCAL_FUNCTION crypto_bls_iso_map_g2
    ENTER   0, IM_SIZE
    mov     x19, x0
    mov     x20, x1
    adr     x21, 913f                       /* k10..k13, then k20, k21, then k30..k33, then k40..k42 */
    F2MUL   sp, IM_X2, x20, 0, x20, 0
    F2MUL   sp, IM_X3, sp, IM_X2, x20, 0
    F2MUL   sp, IM_XN, x21, 288, sp, IM_X3  /* x_num = k13 x^3 + k12 x^2 + k11 x + k10 */
    F2MUL   sp, IM_T, x21, 192, sp, IM_X2
    F2ADD   sp, IM_XN, sp, IM_XN, sp, IM_T
    F2MUL   sp, IM_T, x21, 96, x20, 0
    F2ADD   sp, IM_XN, sp, IM_XN, sp, IM_T
    F2ADD   sp, IM_XN, sp, IM_XN, x21, 0
    F2MUL   sp, IM_T, x21, 480, x20, 0      /* x_den = x^2 + k21 x + k20 */
    F2ADD   sp, IM_XD, sp, IM_X2, sp, IM_T
    F2ADD   sp, IM_XD, sp, IM_XD, x21, 384
    add     x22, x21, #576
    F2MUL   sp, IM_YN, x22, 288, sp, IM_X3  /* y_num = k33 x^3 + k32 x^2 + k31 x + k30 */
    F2MUL   sp, IM_T, x22, 192, sp, IM_X2
    F2ADD   sp, IM_YN, sp, IM_YN, sp, IM_T
    F2MUL   sp, IM_T, x22, 96, x20, 0
    F2ADD   sp, IM_YN, sp, IM_YN, sp, IM_T
    F2ADD   sp, IM_YN, sp, IM_YN, x22, 0
    add     x22, x21, #960
    F2MUL   sp, IM_T, x22, 192, sp, IM_X2   /* y_den = x^3 + k42 x^2 + k41 x + k40 */
    F2ADD   sp, IM_YD, sp, IM_X3, sp, IM_T
    F2MUL   sp, IM_T, x22, 96, x20, 0
    F2ADD   sp, IM_YD, sp, IM_YD, sp, IM_T
    F2ADD   sp, IM_YD, sp, IM_YD, x22, 0
    IS_ZERO sp, IM_XD, 96
    b.eq    1f
    IS_ZERO sp, IM_YD, 96
    b.eq    1f
    C2      crypto_bls_fp2_inverse, sp, IM_T, sp, IM_XD
    F2MUL   x19, 0, sp, IM_XN, sp, IM_T
    F2MUL   sp, IM_YN, x20, 96, sp, IM_YN
    C2      crypto_bls_fp2_inverse, sp, IM_T, sp, IM_YD
    F2MUL   x19, 96, sp, IM_YN, sp, IM_T
    SET_ONE x19, 192
    ZERO    x19, 240, 48
    LEAVE   0, IM_SIZE
1:  SET_ONE x19, 0                          /* the point at infinity */
    ZERO    x19, 48, 48
    SET_ONE x19, 96
    ZERO    x19, 144, 144
    LEAVE   0, IM_SIZE
END_FUNCTION crypto_bls_iso_map_g2

/*
 * crypto_bls_psi(result, point): psi of RFC 9380 appendix G.3 (psi): the
 * affine (c1Psi conj(x), c2Psi conj(y), 1); the point at infinity stays.
 * result may be point.
 */
.set PS_XY, 0
.set PS_T, 192
.set PS_SIZE, 288
LOCAL_FUNCTION crypto_bls_psi
    ENTER   0, PS_SIZE
    mov     x19, x0
    mov     x20, x1
    IS_ZERO x20, 192, 96
    b.ne    1f
    COPY    x19, 0, x20, 0, 288
    LEAVE   0, PS_SIZE
1:  C2      crypto_bls_g2_affine, sp, PS_XY, x20, 0
    adr     x21, 907f                       /* c1Psi, then c2Psi */
    COPY    sp, PS_T, sp, PS_XY, 48         /* conj(x) */
    C2      crypto_bls_fp_neg, sp, PS_T + 48, sp, PS_XY + 48
    F2MUL   x19, 0, x21, 0, sp, PS_T
    COPY    sp, PS_T, sp, PS_XY + 96, 48    /* conj(y) */
    C2      crypto_bls_fp_neg, sp, PS_T + 48, sp, PS_XY + 144
    F2MUL   x19, 96, x21, 96, sp, PS_T
    SET_ONE x19, 192
    ZERO    x19, 240, 48
    LEAVE   0, PS_SIZE
END_FUNCTION crypto_bls_psi

/*
 * crypto_bls_psi2(result, point): psi2 of RFC 9380 appendix G.3 (psi2):
 * the affine (c1Psi2 x, -y, 1); the point at infinity stays. result may be
 * point.
 */
.set P2_XY, 0
.set P2_SIZE, 192
LOCAL_FUNCTION crypto_bls_psi2
    ENTER   0, P2_SIZE
    mov     x19, x0
    mov     x20, x1
    IS_ZERO x20, 192, 96
    b.ne    1f
    COPY    x19, 0, x20, 0, 288
    LEAVE   0, P2_SIZE
1:  C2      crypto_bls_g2_affine, sp, P2_XY, x20, 0
    adr     x2, 908f                        /* c1Psi2, in Fp */
    add     x0, x19, #0
    add     x1, sp, #P2_XY
    bl      crypto_bls_fp2_mul_fp
    C2      crypto_bls_fp2_neg, x19, 96, sp, P2_XY + 96
    SET_ONE x19, 192
    ZERO    x19, 240, 48
    LEAVE   0, P2_SIZE
END_FUNCTION crypto_bls_psi2

/* crypto_bls_g2_mul_neg_x(result, point): x * point, with the negative BLS parameter x = -|x| (mulNegX). */
LOCAL_FUNCTION crypto_bls_g2_mul_neg_x
    ENTER   0
    mov     x19, x0
    adr     x2, 926f
    bl      crypto_bls_g2_mul
    C2      crypto_bls_g2_neg, x19, 0, x19, 0
    LEAVE   0
END_FUNCTION crypto_bls_g2_mul_neg_x

/*
 * crypto_bls_clear_cofactor(result, point, work): clear_cofactor of RFC 9380
 * appendix G.3 (clearCofactor). work holds 1152 bytes: t1, t2, t3 and t4.
 * result may be point.
 */
.set CC_T1, 0
.set CC_T2, 288
.set CC_T3, 576
.set CC_T4, 864
LOCAL_FUNCTION crypto_bls_clear_cofactor
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    C2      crypto_bls_g2_mul_neg_x, x21, CC_T1, x20, 0     /* t1 = x P */
    C2      crypto_bls_psi, x21, CC_T2, x20, 0              /* t2 = psi(P) */
    C2      crypto_bls_g2_double, x21, CC_T3, x20, 0        /* t3 = psi2(2 P) */
    C2      crypto_bls_psi2, x21, CC_T3, x21, CC_T3
    C2      crypto_bls_g2_neg, x21, CC_T4, x21, CC_T2       /* t3 = t3 - t2 */
    C3      crypto_bls_g2_add, x21, CC_T3, x21, CC_T3, x21, CC_T4
    C3      crypto_bls_g2_add, x21, CC_T2, x21, CC_T1, x21, CC_T2    /* t2 = t1 + t2 */
    C2      crypto_bls_g2_mul_neg_x, x21, CC_T2, x21, CC_T2 /* t2 = x t2 */
    C3      crypto_bls_g2_add, x21, CC_T3, x21, CC_T3, x21, CC_T2    /* t3 = t3 + t2 */
    C2      crypto_bls_g2_neg, x21, CC_T1, x21, CC_T1       /* t3 = t3 - t1 */
    C3      crypto_bls_g2_add, x21, CC_T3, x21, CC_T3, x21, CC_T1
    C2      crypto_bls_g2_neg, x21, CC_T4, x20, 0           /* result = t3 - P */
    C3      crypto_bls_g2_add, x19, 0, x21, CC_T3, x21, CC_T4
    LEAVE   0
END_FUNCTION crypto_bls_clear_cofactor

/*
 * crypto_bls_hash_to_g2_point(message, dst, work, point): hashToG2 into a
 * point of G2. work holds the H2C work area of include/bls12381.inc.
 */
.set HW_U, 0
.set HW_U0, 256
.set HW_U1, 352
.set HW_XY0, 448
.set HW_XY1, 640
.set HW_Q0, 832
.set HW_Q1, 1120
.set HW_LEN, 1408
.set HW_P, 1416
.set HW_CC, 1704
.set HW_XMD, 2856
LOCAL_FUNCTION crypto_bls_hash_to_g2_point
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2                         /* work */
    mov     x22, x3                         /* point */
    mov     x9, #256
    str     x9, [x21, #HW_LEN]
    mov     x0, x19                         /* uniform = expand_message_xmd(msg, DST, 256) */
    mov     x1, x20
    add     x2, x21, #HW_LEN
    add     x3, x21, #HW_XMD
    add     x4, x21, #HW_U
    bl      crypto_bls_xmd
    C2      crypto_bls_fp_from_bytes64, x21, HW_U0, x21, HW_U        /* hash_to_field: u0, u1 */
    C2      crypto_bls_fp_from_bytes64, x21, HW_U0 + 48, x21, HW_U + 64
    C2      crypto_bls_fp_from_bytes64, x21, HW_U1, x21, HW_U + 128
    C2      crypto_bls_fp_from_bytes64, x21, HW_U1 + 48, x21, HW_U + 192
    C2      crypto_bls_simple_swu, x21, HW_XY0, x21, HW_U0
    cbnz    x0, 9f
    C2      crypto_bls_simple_swu, x21, HW_XY1, x21, HW_U1
    cbnz    x0, 9f
    C2      crypto_bls_iso_map_g2, x21, HW_Q0, x21, HW_XY0
    C2      crypto_bls_iso_map_g2, x21, HW_Q1, x21, HW_XY1
    C3      crypto_bls_g2_add, x21, HW_Q0, x21, HW_Q0, x21, HW_Q1
    C3      crypto_bls_clear_cofactor, x22, 0, x21, HW_Q0, x21, HW_CC
    mov     x0, #CRYPTO_OK
9:  LEAVE   0
END_FUNCTION crypto_bls_hash_to_g2_point

/*
 * crypto_bls_expand_message_xmd(message, dst, length, scratch, uniform) ->
 * status: checks length, scratch and uniform, then crypto_bls_xmd.
 */
FUNCTION crypto_bls_expand_message_xmd
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x23, x4
    ldr     x24, [x21]                      /* length */
    mov     x9, #CRYPTO_BLS_XMD_MAX_LENGTH
    cmp     x24, x9
    b.hi    7f
    ldr     x9, [x19, #CRYPTO_BYTES_COUNT]  /* scratch: CRYPTO_BLS_H2C_SCRATCH + message + dst */
    ldr     x10, [x20, #CRYPTO_BYTES_COUNT]
    add     x9, x9, x10
    add     x9, x9, #CRYPTO_BLS_H2C_SCRATCH
    ldr     x10, [x22]
    cmp     x10, x9
    b.lo    8f
    add     x9, x24, #CRYPTO_BYTES_FIXED    /* uniform: 24 + length */
    ldr     x10, [x23]
    cmp     x10, x9
    b.lo    8f
    mov     x0, x19
    mov     x1, x20
    mov     x2, x21
    add     x3, x22, #8
    add     x4, x23, #CRYPTO_BYTES_FIXED
    bl      crypto_bls_xmd
    mov     x9, #CRYPTO_BYTES_FIXED
    stp     x9, x24, [x23, #CRYPTO_BYTES_OFFSET]
    mov     x0, #CRYPTO_OK
    LEAVE   0
7:  mov     x0, #CRYPTO_BLS_XMD_LENGTH
    LEAVE   0
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
END_FUNCTION crypto_bls_expand_message_xmd

/*
 * crypto_bls_hash_to_g2(message, dst, scratch, point) -> status: checks
 * scratch, hashes, and writes the affine coordinates (hashToG2Export).
 */
.set HG_XY, 0
.set HG_SIZE, 192
FUNCTION crypto_bls_hash_to_g2
    ENTER   0, HG_SIZE
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    ldr     x9, [x19, #CRYPTO_BYTES_COUNT]
    ldr     x10, [x20, #CRYPTO_BYTES_COUNT]
    add     x9, x9, x10
    add     x9, x9, #CRYPTO_BLS_H2C_SCRATCH
    ldr     x10, [x21]
    cmp     x10, x9
    b.lo    8f
    add     x23, x21, #8                    /* work */
    mov     x0, x19
    mov     x1, x20
    mov     x2, x23
    add     x3, x23, #HW_P
    bl      crypto_bls_hash_to_g2_point
    cbnz    x0, 9f
    IS_ZERO x23, HW_P + 192, 96
    b.eq    7f
    C2      crypto_bls_g2_affine, sp, HG_XY, x23, HW_P
    C2      crypto_bls_fp_to_bytes, x22, 0, sp, HG_XY
    C2      crypto_bls_fp_to_bytes, x22, 48, sp, HG_XY + 48
    C2      crypto_bls_fp_to_bytes, x22, 96, sp, HG_XY + 96
    C2      crypto_bls_fp_to_bytes, x22, 144, sp, HG_XY + 144
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, HG_SIZE
7:  mov     x0, #CRYPTO_BLS_POINT_AT_INFINITY
    LEAVE   0, HG_SIZE
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0, HG_SIZE
END_FUNCTION crypto_bls_hash_to_g2

/* ---------------------------------------------------------------- Signatures (Signatures.lean) */

/*
 * crypto_bls_secret_key(scalar, secret_key) -> status: the 32 big-endian
 * bytes as 4 little-endian limbs (SecretKey.fromBytes).
 * CRYPTO_INVALID_PRIVATE_KEY when the key is 0, or r or more; nothing is
 * written then.
 */
LOCAL_FUNCTION crypto_bls_secret_key
    UNWIND_END_PROLOGUE
    ldp     x12, x11, [x1]
    ldp     x10, x9, [x1, #16]
    rev     x9, x9
    rev     x10, x10
    rev     x11, x11
    rev     x12, x12
    orr     x13, x9, x10
    orr     x14, x11, x12
    orr     x13, x13, x14
    cbz     x13, 8f
    adr     x15, 924f
    ldp     x13, x14, [x15]
    ldp     x15, x16, [x15, #16]
    cmp     x9, x13                         /* below r? */
    sbcs    xzr, x10, x14
    sbcs    xzr, x11, x15
    sbcs    xzr, x12, x16
    b.hs    8f
    stp     x9, x10, [x0]
    stp     x11, x12, [x0, #16]
    mov     x0, #CRYPTO_OK
    ret
8:  mov     x0, #CRYPTO_INVALID_PRIVATE_KEY
    ret
END_FUNCTION crypto_bls_secret_key

/* crypto_bls_sk_to_pk(secret_key, public_key) -> status: skToPk. */
.set SP_K, 0
.set SP_P, 32
.set SP_SIZE, 176
FUNCTION crypto_bls_sk_to_pk
    ENTER   0, SP_SIZE
    mov     x19, x0
    mov     x20, x1
    add     x0, sp, #SP_K
    mov     x1, x19
    bl      crypto_bls_secret_key
    cbnz    x0, 9f
    adr     x9, 904f                        /* the generator of G1: (x, y, 1) */
    COPY    sp, SP_P, x9, 0, 96
    SET_ONE sp, SP_P + 96
    C3      crypto_bls_g1_mul, sp, SP_P, sp, SP_P, sp, SP_K
    G2      crypto_bls_g1_compress, sp, SP_P, x20, 0
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, SP_SIZE
END_FUNCTION crypto_bls_sk_to_pk

/*
 * crypto_bls_sign(secret_key, message, scratch, signature) -> status: sign:
 * the compressed SK * H(message), H the hash to G2 under the DST.
 * scratch: Q at work + 0, the hash work at work + 288.
 */
.set SN_K, 0
.set SN_SIZE, 32
FUNCTION crypto_bls_sign
    ENTER   0, SN_SIZE
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x0, sp
    mov     x1, x19
    bl      crypto_bls_secret_key
    cbnz    x0, 9f
    ldr     x9, [x20, #CRYPTO_BYTES_COUNT]
    add     x9, x9, #(CRYPTO_BLS_SCRATCH & 0xFFF)
    add     x9, x9, #(CRYPTO_BLS_SCRATCH & 0xFFF000)
    ldr     x10, [x21]
    cmp     x10, x9
    b.lo    8f
    add     x23, x21, #8                    /* work */
    mov     x0, x20
    adr     x1, 931f                        /* the DST, as a ByteList */
    add     x2, x23, #288
    mov     x3, x23
    bl      crypto_bls_hash_to_g2_point
    cbnz    x0, 9f
    mov     x0, x23
    mov     x1, x23
    mov     x2, sp
    bl      crypto_bls_g2_mul
    G2      crypto_bls_g2_compress, x23, 0, x22, 0
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, SN_SIZE
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0, SN_SIZE
END_FUNCTION crypto_bls_sign

/*
 * crypto_bls_key_validate_point(public_key, point) -> status: G1.keyValidatePoint:
 * decompression, not the point at infinity, in the subgroup.
 * CRYPTO_INVALID_PUBLIC_KEY otherwise; nothing is written then.
 */
.set KV_P, 0
.set KV_V, 144
.set KV_SIZE, 160
LOCAL_FUNCTION crypto_bls_key_validate_point
    ENTER   0, KV_SIZE
    mov     x19, x0
    mov     x20, x1
    mov     x1, sp
    bl      crypto_bls_g1_uncompress
    cbnz    x0, 8f
    IS_ZERO sp, KV_P + 96, 48
    b.eq    8f
    C2      crypto_bls_g1_in_subgroup, sp, KV_P, sp, KV_V
    ldr     x9, [sp, #KV_V]
    cbz     x9, 8f
    COPY    x20, 0, sp, KV_P, 144
    mov     x0, #CRYPTO_OK
    LEAVE   0, KV_SIZE
8:  mov     x0, #CRYPTO_INVALID_PUBLIC_KEY
    LEAVE   0, KV_SIZE
END_FUNCTION crypto_bls_key_validate_point

/* crypto_bls_key_validate(public_key, valid) -> status: keyValidate, as 1 or 0. */
.set KW_P, 0
.set KW_SIZE, 144
FUNCTION crypto_bls_key_validate
    ENTER   0, KW_SIZE
    mov     x20, x1
    mov     x1, sp
    bl      crypto_bls_key_validate_point
    cmp     x0, #CRYPTO_OK
    cset    x9, eq
    str     x9, [x20]
    mov     x0, #CRYPTO_OK
    LEAVE   0, KW_SIZE
END_FUNCTION crypto_bls_key_validate

/* crypto_bls_aggregate(signatures, signature) -> status: aggregate. */
.set AG_ACC, 0
.set AG_P, 288
.set AG_SIZE, 576
FUNCTION crypto_bls_aggregate
    ENTER   0, AG_SIZE
    mov     x19, x0
    mov     x20, x1
    ldp     x21, x22, [x19, #CRYPTO_BLS_LIST_OFFSET]   /* offset, count */
    cbz     x22, 7f
    add     x21, x19, x21
    SET_ONE sp, AG_ACC                      /* the point at infinity */
    ZERO    sp, AG_ACC + 48, 48
    SET_ONE sp, AG_ACC + 96
    ZERO    sp, AG_ACC + 144, 144
1:  mov     x0, x21
    add     x1, sp, #AG_P
    bl      crypto_bls_g2_uncompress
    cbnz    x0, 8f
    C3      crypto_bls_g2_add, sp, AG_ACC, sp, AG_ACC, sp, AG_P
    add     x21, x21, #96
    subs    x22, x22, #1
    b.ne    1b
    G2      crypto_bls_g2_compress, sp, AG_ACC, x20, 0
    mov     x0, #CRYPTO_OK
    LEAVE   0, AG_SIZE
7:  mov     x0, #CRYPTO_EMPTY_LIST
    LEAVE   0, AG_SIZE
8:  mov     x0, #CRYPTO_INVALID_SIGNATURE
    LEAVE   0, AG_SIZE
END_FUNCTION crypto_bls_aggregate

/*
 * crypto_bls_aggregate_keys(public_keys, point) -> status: the sum of the
 * keys, each through crypto_bls_key_validate_point, from the point at
 * infinity. CRYPTO_EMPTY_LIST or CRYPTO_INVALID_PUBLIC_KEY otherwise.
 */
.set AK_ACC, 0
.set AK_P, 144
.set AK_SIZE, 288
LOCAL_FUNCTION crypto_bls_aggregate_keys
    ENTER   0, AK_SIZE
    mov     x19, x0
    mov     x20, x1
    ldp     x21, x22, [x19, #CRYPTO_BLS_LIST_OFFSET]
    cbz     x22, 7f
    add     x21, x19, x21
    SET_ONE sp, AK_ACC
    SET_ONE sp, AK_ACC + 48
    ZERO    sp, AK_ACC + 96, 48
1:  mov     x0, x21
    add     x1, sp, #AK_P
    bl      crypto_bls_key_validate_point
    cbnz    x0, 9f
    C3      crypto_bls_g1_add_affine, sp, AK_ACC, sp, AK_ACC, sp, AK_P  /* the key has Z = 1 */
    add     x21, x21, #48
    subs    x22, x22, #1
    b.ne    1b
    COPY    x20, 0, sp, AK_ACC, 144
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, AK_SIZE
7:  mov     x0, #CRYPTO_EMPTY_LIST
    LEAVE   0, AK_SIZE
END_FUNCTION crypto_bls_aggregate_keys

/* crypto_bls_eth_aggregate_pubkeys(public_keys, public_key) -> status: ethAggregatePubkeys. */
.set EA_P, 0
.set EA_SIZE, 144
FUNCTION crypto_bls_eth_aggregate_pubkeys
    ENTER   0, EA_SIZE
    mov     x20, x1
    mov     x1, sp
    bl      crypto_bls_aggregate_keys
    cbnz    x0, 9f
    G2      crypto_bls_g1_compress, sp, EA_P, x20, 0
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, EA_SIZE
END_FUNCTION crypto_bls_eth_aggregate_pubkeys

/* ---------------------------------------------------------------- Fp6 (Fp6.lean) */

.macro F2NR ra, oa, rb, ob
    C2      crypto_bls_fp2_mul_nr, \ra, \oa, \rb, \ob
.endm
.macro F6MUL ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp6_mul, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro F6ADD ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp6_add, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro F6SUB ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp6_sub, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro F12MUL ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp12_mul, \ra, \oa, \rb, \ob, \rc, \oc
.endm

/* crypto_bls_fp6_add(result, a, b): a + b (Fp6.add). result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp6_add
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    F2ADD   x19, 0, x20, 0, x21, 0
    F2ADD   x19, 96, x20, 96, x21, 96
    F2ADD   x19, 192, x20, 192, x21, 192
    LEAVE   0
END_FUNCTION crypto_bls_fp6_add

/* crypto_bls_fp6_sub(result, a, b): a - b (Fp6.sub). result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp6_sub
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    F2SUB   x19, 0, x20, 0, x21, 0
    F2SUB   x19, 96, x20, 96, x21, 96
    F2SUB   x19, 192, x20, 192, x21, 192
    LEAVE   0
END_FUNCTION crypto_bls_fp6_sub

/* crypto_bls_fp6_neg(result, a): -a (Fp6.neg). result may be a. */
LOCAL_FUNCTION crypto_bls_fp6_neg
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    C2      crypto_bls_fp2_neg, x19, 0, x20, 0
    C2      crypto_bls_fp2_neg, x19, 96, x20, 96
    C2      crypto_bls_fp2_neg, x19, 192, x20, 192
    LEAVE   0
END_FUNCTION crypto_bls_fp6_neg

/*
 * crypto_bls_fp6_mul(result, a, b): a * b (Fp6.mul): with t_i = a_i b_i,
 * c0 = xi ((a1 + a2)(b1 + b2) - t1 - t2) + t0, c1 = (a0 + a1)(b0 + b1) - t0
 * - t1 + xi t2, c2 = (a0 + a2)(b0 + b2) - t0 - t2 + t1. result may be a or b.
 */
.set M6_T0, 0
.set M6_T1, 96
.set M6_T2, 192
.set M6_S, 288
.set M6_U, 384
.set M6_C0, 480
.set M6_C1, 576
.set M6_C2, 672
.set M6_SIZE, 768
LOCAL_FUNCTION crypto_bls_fp6_mul
    ENTER   0, M6_SIZE
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    F2MUL   sp, M6_T0, x20, 0, x21, 0
    F2MUL   sp, M6_T1, x20, 96, x21, 96
    F2MUL   sp, M6_T2, x20, 192, x21, 192
    F2ADD   sp, M6_S, x20, 96, x20, 192     /* c0 */
    F2ADD   sp, M6_U, x21, 96, x21, 192
    F2MUL   sp, M6_C0, sp, M6_S, sp, M6_U
    F2SUB   sp, M6_C0, sp, M6_C0, sp, M6_T1
    F2SUB   sp, M6_C0, sp, M6_C0, sp, M6_T2
    F2NR    sp, M6_C0, sp, M6_C0
    F2ADD   sp, M6_C0, sp, M6_C0, sp, M6_T0
    F2ADD   sp, M6_S, x20, 0, x20, 96       /* c1 */
    F2ADD   sp, M6_U, x21, 0, x21, 96
    F2MUL   sp, M6_C1, sp, M6_S, sp, M6_U
    F2SUB   sp, M6_C1, sp, M6_C1, sp, M6_T0
    F2SUB   sp, M6_C1, sp, M6_C1, sp, M6_T1
    F2NR    sp, M6_U, sp, M6_T2
    F2ADD   sp, M6_C1, sp, M6_C1, sp, M6_U
    F2ADD   sp, M6_S, x20, 0, x20, 192      /* c2 */
    F2ADD   sp, M6_U, x21, 0, x21, 192
    F2MUL   sp, M6_C2, sp, M6_S, sp, M6_U
    F2SUB   sp, M6_C2, sp, M6_C2, sp, M6_T0
    F2SUB   sp, M6_C2, sp, M6_C2, sp, M6_T2
    F2ADD   sp, M6_C2, sp, M6_C2, sp, M6_T1
    COPY    x19, 0, sp, M6_C0, 288
    LEAVE   0, M6_SIZE
END_FUNCTION crypto_bls_fp6_mul

/* crypto_bls_fp6_mul_v(result, a): a v = (xi a2, a0, a1) (Fp6.mulByV). result may be a. */
.set MV_T, 0
.set MV_SIZE, 96
LOCAL_FUNCTION crypto_bls_fp6_mul_v
    ENTER   0, MV_SIZE
    mov     x19, x0
    mov     x20, x1
    F2NR    sp, MV_T, x20, 192
    COPY    x19, 192, x20, 96, 96
    COPY    x19, 96, x20, 0, 96
    COPY    x19, 0, sp, MV_T, 96
    LEAVE   0, MV_SIZE
END_FUNCTION crypto_bls_fp6_mul_v

/*
 * crypto_bls_fp6_inverse(result, a): 1 / a (Fp6.inverse): t0 = a0^2 - xi
 * a1 a2, t1 = xi a2^2 - a0 a1, t2 = a1^2 - a0 a2, det = a0 t0 + xi a2 t1 +
 * xi a1 t2, and (t0, t1, t2) / det. result may be a.
 */
.set N6_T0, 0
.set N6_T1, 96
.set N6_T2, 192
.set N6_D, 288
.set N6_U, 384
.set N6_SIZE, 480
LOCAL_FUNCTION crypto_bls_fp6_inverse
    ENTER   0, N6_SIZE
    mov     x19, x0
    mov     x20, x1
    F2MUL   sp, N6_T0, x20, 0, x20, 0       /* t0 */
    F2MUL   sp, N6_U, x20, 96, x20, 192
    F2NR    sp, N6_U, sp, N6_U
    F2SUB   sp, N6_T0, sp, N6_T0, sp, N6_U
    F2MUL   sp, N6_T1, x20, 192, x20, 192   /* t1 */
    F2NR    sp, N6_T1, sp, N6_T1
    F2MUL   sp, N6_U, x20, 0, x20, 96
    F2SUB   sp, N6_T1, sp, N6_T1, sp, N6_U
    F2MUL   sp, N6_T2, x20, 96, x20, 96     /* t2 */
    F2MUL   sp, N6_U, x20, 0, x20, 192
    F2SUB   sp, N6_T2, sp, N6_T2, sp, N6_U
    F2MUL   sp, N6_D, x20, 0, sp, N6_T0     /* det */
    F2MUL   sp, N6_U, x20, 192, sp, N6_T1
    F2NR    sp, N6_U, sp, N6_U
    F2ADD   sp, N6_D, sp, N6_D, sp, N6_U
    F2MUL   sp, N6_U, x20, 96, sp, N6_T2
    F2NR    sp, N6_U, sp, N6_U
    F2ADD   sp, N6_D, sp, N6_D, sp, N6_U
    C2      crypto_bls_fp2_inverse, sp, N6_D, sp, N6_D
    F2MUL   x19, 0, sp, N6_T0, sp, N6_D
    F2MUL   x19, 96, sp, N6_T1, sp, N6_D
    F2MUL   x19, 192, sp, N6_T2, sp, N6_D
    LEAVE   0, N6_SIZE
END_FUNCTION crypto_bls_fp6_inverse

/* ---------------------------------------------------------------- Fp12 (Fp12.lean) */

/*
 * crypto_bls_fp12_mul(result, a, b): a * b (Fp12.mul): t0 = a0 b0, t1 = a1
 * b1, c0 = t0 + v t1, c1 = (a0 + a1)(b0 + b1) - t0 - t1. result may be a or b.
 */
.set M12_T0, 0
.set M12_T1, 288
.set M12_SA, 576
.set M12_SB, 864
.set M12_SIZE, 1152
LOCAL_FUNCTION crypto_bls_fp12_mul
    ENTER   0, M12_SIZE
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    F6MUL   sp, M12_T0, x20, 0, x21, 0
    F6MUL   sp, M12_T1, x20, 288, x21, 288
    F6ADD   sp, M12_SA, x20, 0, x20, 288
    F6ADD   sp, M12_SB, x21, 0, x21, 288
    F6MUL   sp, M12_SA, sp, M12_SA, sp, M12_SB
    F6SUB   sp, M12_SA, sp, M12_SA, sp, M12_T0
    F6SUB   sp, M12_SA, sp, M12_SA, sp, M12_T1
    C2      crypto_bls_fp6_mul_v, sp, M12_T1, sp, M12_T1
    F6ADD   x19, 0, sp, M12_T0, sp, M12_T1
    COPY    x19, 288, sp, M12_SA, 288
    LEAVE   0, M12_SIZE
END_FUNCTION crypto_bls_fp12_mul

/* crypto_bls_fp12_conjugate(result, a): (a0, -a1) (Fp12.conjugate). result may be a. */
LOCAL_FUNCTION crypto_bls_fp12_conjugate
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    COPY    x19, 0, x20, 0, 288
    C2      crypto_bls_fp6_neg, x19, 288, x20, 288
    LEAVE   0
END_FUNCTION crypto_bls_fp12_conjugate

/*
 * crypto_bls_fp12_inverse(result, a): (a0 / n, -a1 / n), n = a0^2 - v a1^2
 * (Fp12.inverse). result may be a.
 */
.set N12_N, 0
.set N12_U, 288
.set N12_SIZE, 576
LOCAL_FUNCTION crypto_bls_fp12_inverse
    ENTER   0, N12_SIZE
    mov     x19, x0
    mov     x20, x1
    F6MUL   sp, N12_N, x20, 0, x20, 0
    F6MUL   sp, N12_U, x20, 288, x20, 288
    C2      crypto_bls_fp6_mul_v, sp, N12_U, sp, N12_U
    F6SUB   sp, N12_N, sp, N12_N, sp, N12_U
    C2      crypto_bls_fp6_inverse, sp, N12_N, sp, N12_N
    F6MUL   sp, N12_U, x20, 288, sp, N12_N
    C2      crypto_bls_fp6_neg, x19, 288, sp, N12_U
    F6MUL   x19, 0, x20, 0, sp, N12_N
    LEAVE   0, N12_SIZE
END_FUNCTION crypto_bls_fp12_inverse

/*
 * crypto_bls_fp12_frobenius(result, a): a^p (Fp12.frobenius): conj(a_k)
 * g^k, with a_k the coefficient of w^k and g the frobeniusCoeff. result may
 * be a.
 */
.set FR_T, 0
.set FR_SIZE, 96
LOCAL_FUNCTION crypto_bls_fp12_frobenius
    ENTER   0, FR_SIZE
    mov     x19, x0
    mov     x20, x1
    adr     x21, 909f                       /* g^0, ..., g^5 */
    mov     x22, #0                         /* component: offset in a, then power of g */
1:  adr     x9, 932f
    add     x9, x9, x22, lsl #2
    ldrh    w23, [x9]                       /* offset of a_k in a */
    ldrh    w24, [x9, #2]                   /* k */
    add     x10, x20, x23
    add     x11, sp, #FR_T
    ldp     x12, x13, [x10]                 /* conj: c0, then -c1 */
    stp     x12, x13, [x11]
    ldp     x12, x13, [x10, #16]
    stp     x12, x13, [x11, #16]
    ldp     x12, x13, [x10, #32]
    stp     x12, x13, [x11, #32]
    add     x0, sp, #FR_T + 48
    add     x1, x10, #48
    bl      crypto_bls_fp_neg
    mov     x9, #96
    madd    x2, x24, x9, x21
    add     x0, x19, x23
    add     x1, sp, #FR_T
    bl      crypto_bls_fp2_mul
    add     x22, x22, #1
    cmp     x22, #6
    b.lo    1b
    LEAVE   0, FR_SIZE
END_FUNCTION crypto_bls_fp12_frobenius

/*
 * crypto_bls_fp12_cyclotomic_square(result, a): a^2 for a in the cyclotomic
 * subgroup (Granger and Scott). With a = (r0, r4, r3) + (r2, r1, r5) w:
 * (t0, t1), (t2, t3), (t4, t5) are the squares of r0 + r1 y, r2 + r3 y and
 * r4 + r5 y with y^2 = xi: t = a0 b, a0^2 + xi b^2 = (a0 + b)(xi b + a0) - t
 * - xi t, 2 t. Then r0' = 3 t0 - 2 r0, r1' = 3 t1 + 2 r1, r2' = 3 xi t5 +
 * 2 r2, r3' = 3 t4 - 2 r3, r4' = 3 t2 - 2 r4, r5' = 3 t3 + 2 r5. result may
 * be a.
 */
.set CS_T0, 0
.set CS_T1, 96
.set CS_T2, 192
.set CS_T3, 288
.set CS_T4, 384
.set CS_T5, 480
.set CS_A, 576
.set CS_B, 672
.set CS_SIZE, 768
/* (t0, t1) = (a0^2 + xi b^2, 2 a0 b) for a0 at x20 + a, b at x20 + b. */
.macro CYC_SQ4 a, b, t0, t1
    F2MUL   sp, \t1, x20, \a, x20, \b
    F2ADD   sp, CS_A, x20, \a, x20, \b
    F2NR    sp, CS_B, x20, \b
    F2ADD   sp, CS_B, sp, CS_B, x20, \a
    F2MUL   sp, CS_A, sp, CS_A, sp, CS_B
    F2SUB   sp, CS_A, sp, CS_A, sp, \t1
    F2NR    sp, CS_B, sp, \t1
    F2SUB   sp, \t0, sp, CS_A, sp, CS_B
    F2ADD   sp, \t1, sp, \t1, sp, \t1
.endm
/* x19 + z = 3 t - 2 z (CYC_MINUS) or 3 t + 2 z (CYC_PLUS), t at sp + t, z at x20 + z. */
.macro CYC_MINUS z, t
    F2SUB   sp, CS_A, sp, \t, x20, \z
    F2ADD   sp, CS_A, sp, CS_A, sp, CS_A
    F2ADD   x19, \z, sp, CS_A, sp, \t
.endm
.macro CYC_PLUS z, t
    F2ADD   sp, CS_A, sp, \t, x20, \z
    F2ADD   sp, CS_A, sp, CS_A, sp, CS_A
    F2ADD   x19, \z, sp, CS_A, sp, \t
.endm
LOCAL_FUNCTION crypto_bls_fp12_cyclotomic_square
    ENTER   0, CS_SIZE
    mov     x19, x0
    mov     x20, x1
    CYC_SQ4 0, 384, CS_T0, CS_T1            /* r0 + r1 y */
    CYC_SQ4 288, 192, CS_T2, CS_T3          /* r2 + r3 y */
    CYC_SQ4 96, 480, CS_T4, CS_T5           /* r4 + r5 y */
    CYC_MINUS 0, CS_T0
    CYC_PLUS 384, CS_T1
    F2NR    sp, CS_B, sp, CS_T5             /* r2' = 3 xi t5 + 2 r2 */
    CYC_PLUS 288, CS_B
    CYC_MINUS 192, CS_T4
    CYC_MINUS 96, CS_T2
    CYC_PLUS 480, CS_T3
    LEAVE   0, CS_SIZE
END_FUNCTION crypto_bls_fp12_cyclotomic_square

/*
 * crypto_bls_fp12_cyclotomic_pow(result, base, exponent): base^e
 * (Fp12.powNat) for base in the cyclotomic subgroup, with e the u64 at
 * exponent, a public value. Starts with base at the top set bit of e, then
 * squares with crypto_bls_fp12_cyclotomic_square, and multiplies by base where
 * a bit of e is 1. result must not be base.
 */
LOCAL_FUNCTION crypto_bls_fp12_cyclotomic_pow
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    ldr     x21, [x2]
    cbnz    x21, 1f
    SET_ONE x19, 0                          /* e = 0: 1 */
    ZERO    x19, 48, 528
    LEAVE   0
1:  COPY    x19, 0, x20, 0, 576
    clz     x22, x21
    mov     x9, #62
    subs    x22, x9, x22                    /* the bit below the top set bit */
    b.lt    9f
2:  C2      crypto_bls_fp12_cyclotomic_square, x19, 0, x19, 0
    lsr     x9, x21, x22
    tbz     x9, #0, 3f
    F12MUL  x19, 0, x19, 0, x20, 0
3:  subs    x22, x22, #1
    b.ge    2b
9:  LEAVE   0
END_FUNCTION crypto_bls_fp12_cyclotomic_pow

/* ---------------------------------------------------------------- Pairing (Pairing.lean) */

/*
 * A line value c0 + c2 w^2 + c3 w^3 (lineValue) is kept as its three Fp2
 * values: c0 at 0, c2 at 96, c3 at 192 (288 bytes). In Fp12 = Fp6[w] it is
 * (c0 + c2 v) + (c3 v) w.
 */

/*
 * crypto_bls_fp12_square(result, a): a^2: with a = a0 + a1 w and t = a0 a1,
 * c0 = (a0 + a1)(a0 + a1 v) - t - t v, c1 = 2 t. result may be a.
 */
.set SQ_T, 0
.set SQ_A, 288
.set SQ_B, 576
.set SQ_SIZE, 864
LOCAL_FUNCTION crypto_bls_fp12_square
    ENTER   0, SQ_SIZE
    mov     x19, x0
    mov     x20, x1
    F6MUL   sp, SQ_T, x20, 0, x20, 288      /* t = a0 a1 */
    F6ADD   sp, SQ_A, x20, 0, x20, 288      /* (a0 + a1)(a0 + a1 v) */
    C2      crypto_bls_fp6_mul_v, sp, SQ_B, x20, 288
    F6ADD   sp, SQ_B, sp, SQ_B, x20, 0
    F6MUL   sp, SQ_A, sp, SQ_A, sp, SQ_B
    F6SUB   sp, SQ_A, sp, SQ_A, sp, SQ_T
    C2      crypto_bls_fp6_mul_v, sp, SQ_B, sp, SQ_T
    F6SUB   x19, 0, sp, SQ_A, sp, SQ_B      /* c0 */
    F6ADD   x19, 288, sp, SQ_T, sp, SQ_T    /* c1 = 2 t */
    LEAVE   0, SQ_SIZE
END_FUNCTION crypto_bls_fp12_square

/*
 * crypto_bls_fp12_mul_line(f, line): f = f l, with l = (c0 + c2 v) + (c3 v) w
 * the line value at line. With f = a + b w: t0 = a (c0 + c2 v), t1 = b c3 v,
 * c1 = (a + b)(c0 + (c2 + c3) v) - t0 - t1, c0 = t0 + t1 v. Each product by
 * x0 + x1 v takes 5 Fp2 products: with v0 = a0 x0 and v1 = a1 x1, it is
 * (v0 + xi a2 x1) + ((a0 + a1)(x0 + x1) - v0 - v1) v + (a2 x0 + v1) v^2.
 */
.set LM_T0, 0
.set LM_T1, 288
.set LM_S, 576
.set LM_X, 864
.set LM_V0, 960
.set LM_V1, 1056
.set LM_U, 1152
.set LM_W, 1248
.set LM_SIZE, 1344
/* rd + od = (ra + oa) (x0 + x1 v), x0 at rx + ox, x1 at ry + oy; rd + od apart from ra + oa. */
.macro MUL01 rd, od, ra, oa, rx, ox, ry, oy
    F2MUL   sp, LM_V0, \ra, \oa, \rx, \ox
    F2MUL   sp, LM_V1, \ra, \oa + 96, \ry, \oy
    F2ADD   sp, LM_U, \ra, \oa, \ra, \oa + 96
    F2ADD   sp, LM_W, \rx, \ox, \ry, \oy
    F2MUL   sp, LM_U, sp, LM_U, sp, LM_W
    F2SUB   sp, LM_U, sp, LM_U, sp, LM_V0
    F2SUB   \rd, \od + 96, sp, LM_U, sp, LM_V1
    F2MUL   sp, LM_W, \ra, \oa + 192, \ry, \oy
    F2NR    sp, LM_W, sp, LM_W
    F2ADD   \rd, \od, sp, LM_V0, sp, LM_W
    F2MUL   sp, LM_W, \ra, \oa + 192, \rx, \ox
    F2ADD   \rd, \od + 192, sp, LM_W, sp, LM_V1
.endm
LOCAL_FUNCTION crypto_bls_fp12_mul_line
    ENTER   0, LM_SIZE
    mov     x19, x0                         /* f */
    mov     x20, x1                         /* line */
    MUL01   sp, LM_T0, x19, 0, x20, 0, x20, 96      /* t0 = a (c0 + c2 v) */
    F2MUL   sp, LM_T1 + 96, x19, 288, x20, 192      /* t1 = b c3 v = (xi b2 c3, b0 c3, b1 c3) */
    F2MUL   sp, LM_T1 + 192, x19, 384, x20, 192
    F2MUL   sp, LM_T1, x19, 480, x20, 192
    F2NR    sp, LM_T1, sp, LM_T1
    F6ADD   sp, LM_S, x19, 0, x19, 288      /* c1 = (a + b)(c0 + (c2 + c3) v) - t0 - t1 */
    F2ADD   sp, LM_X, x20, 96, x20, 192
    MUL01   x19, 288, sp, LM_S, x20, 0, sp, LM_X
    F6SUB   x19, 288, x19, 288, sp, LM_T0
    F6SUB   x19, 288, x19, 288, sp, LM_T1
    C2      crypto_bls_fp6_mul_v, sp, LM_T1, sp, LM_T1  /* c0 = t0 + t1 v */
    F6ADD   x19, 0, sp, LM_T0, sp, LM_T1
    LEAVE   0, LM_SIZE
END_FUNCTION crypto_bls_fp12_mul_line

/*
 * crypto_bls_miller_double(line, t, p, work): the line of millerDouble: with
 * T the G2 point at t and P = (xp, yp) at p, the tangent line at T, valued
 * at P, then T = 2 T. work holds 384 bytes of temporaries.
 */
.set MD_XX, 0
.set MD_ZZ, 96
.set MD_A, 192
.set MD_U, 288
LOCAL_FUNCTION crypto_bls_miller_double
    ENTER   0
    mov     x19, x0                         /* line */
    mov     x20, x1                         /* T */
    mov     x21, x2                         /* P */
    mov     x22, x3                         /* work */
    F2MUL   x22, MD_XX, x20, 0, x20, 0       /* xx = X^2, zz = Z^2 */
    F2MUL   x22, MD_ZZ, x20, 192, x20, 192
    F2ADD   x22, MD_A, x22, MD_XX, x22, MD_XX  /* 3 xx */
    F2ADD   x22, MD_A, x22, MD_A, x22, MD_XX
    F2MUL   x19, 0, x22, MD_A, x20, 0        /* c0 = 3 xx X - 2 Y^2 */
    F2MUL   x22, MD_U, x20, 96, x20, 96
    F2ADD   x22, MD_U, x22, MD_U, x22, MD_U
    F2SUB   x19, 0, x19, 0, x22, MD_U
    F2MUL   x19, 96, x22, MD_A, x22, MD_ZZ    /* c2 = -(3 xx zz xp) */
    C3      crypto_bls_fp2_mul_fp, x19, 96, x19, 96, x21, 0
    C2      crypto_bls_fp2_neg, x19, 96, x19, 96
    F2ADD   x19, 192, x20, 96, x20, 96       /* c3 = 2 Y zz Z yp */
    F2MUL   x19, 192, x19, 192, x22, MD_ZZ
    F2MUL   x19, 192, x19, 192, x20, 192
    C3      crypto_bls_fp2_mul_fp, x19, 192, x19, 192, x21, 48
    C2      crypto_bls_g2_double, x20, 0, x20, 0
    LEAVE   0
END_FUNCTION crypto_bls_miller_double

/*
 * crypto_bls_miller_add(line, t, q, p, work): the line of millerAdd: with
 * Q = (xq, yq) at q, the line through T and Q, valued at P, then T = T + Q.
 * work holds 672 bytes: Q in Jacobian coordinates, then the temporaries.
 */
.set MA_ZZ, 288
.set MA_N, 384
.set MA_D, 480
.set MA_U, 576
LOCAL_FUNCTION crypto_bls_miller_add
    ENTER   0
    mov     x19, x0                         /* line */
    mov     x20, x1                         /* T */
    mov     x21, x2                         /* Q */
    mov     x22, x3                         /* P */
    mov     x23, x4                         /* work */
    F2MUL   x23, MA_ZZ, x20, 192, x20, 192   /* zz = Z^2 */
    F2MUL   x23, MA_N, x21, 96, x23, MA_ZZ    /* n = yq zz Z - Y */
    F2MUL   x23, MA_N, x23, MA_N, x20, 192
    F2SUB   x23, MA_N, x23, MA_N, x20, 96
    F2MUL   x23, MA_D, x21, 0, x23, MA_ZZ     /* d = (xq zz - X) Z */
    F2SUB   x23, MA_D, x23, MA_D, x20, 0
    F2MUL   x23, MA_D, x23, MA_D, x20, 192
    F2MUL   x19, 0, x23, MA_N, x21, 0        /* c0 = n xq - d yq */
    F2MUL   x23, MA_U, x23, MA_D, x21, 96
    F2SUB   x19, 0, x19, 0, x23, MA_U
    C3      crypto_bls_fp2_mul_fp, x19, 96, x23, MA_N, x22, 0  /* c2 = -(n xp) */
    C2      crypto_bls_fp2_neg, x19, 96, x19, 96
    C3      crypto_bls_fp2_mul_fp, x19, 192, x23, MA_D, x22, 48  /* c3 = d yp */
    COPY    x23, 0, x21, 0, 192             /* Q = (xq, yq, 1) */
    SET_ONE x23, 192
    ZERO    x23, 240, 48
    C3      crypto_bls_g2_add, x20, 0, x20, 0, x23, 0
    LEAVE   0
END_FUNCTION crypto_bls_miller_add

/*
 * crypto_bls_miller_loop(f, pairs, count, work): the product of
 * millerLoop(Q_i, P_i) for the count pairs, in one loop: each pair entry
 * (576 bytes) holds Q = (xq, yq) at 0, P = (xp, yp) at 192 and its T at 288.
 * T_i = Q_i and f = 1; then for each bit of |x| below its top bit, f = f^2
 * (not for the first bit, where f = 1), then for each pair the double step,
 * f = f l, and on a set bit for each pair the add step, f = f l. work holds
 * 960 bytes: the line, then the work of the steps.
 */
.set ML_LINE, 0
.set ML_STEP, 288
LOCAL_FUNCTION crypto_bls_miller_loop
    ENTER   0
    mov     x19, x0                         /* f */
    mov     x20, x1                         /* the pairs */
    mov     x21, x2                         /* count */
    mov     x22, x3                         /* work */
    mov     x25, x20                        /* T_i = (xq, yq, 1) */
    mov     x26, x21
0:  COPY    x25, 288, x25, 0, 192
    SET_ONE x25, 480
    ZERO    x25, 528, 48
    add     x25, x25, #576
    subs    x26, x26, #1
    b.ne    0b
    SET_ONE x19, 0                          /* f = 1 */
    ZERO    x19, 48, 528
    adr     x9, 927f
    ldr     x23, [x9]                       /* |x| */
    mov     x24, #62                        /* bits 62 to 0; bit 63 is the top bit */
1:  cmp     x24, #62
    b.eq    2f
    C2      crypto_bls_fp12_square, x19, 0, x19, 0
2:  mov     x25, x20
    mov     x26, x21
3:  add     x0, x22, #ML_LINE               /* the double step of each pair */
    add     x1, x25, #288
    add     x2, x25, #192
    add     x3, x22, #ML_STEP
    bl      crypto_bls_miller_double
    C2      crypto_bls_fp12_mul_line, x19, 0, x22, ML_LINE
    add     x25, x25, #576
    subs    x26, x26, #1
    b.ne    3b
    lsr     x9, x23, x24
    tbz     x9, #0, 5f
    mov     x25, x20
    mov     x26, x21
4:  add     x0, x22, #ML_LINE               /* the add step of each pair */
    add     x1, x25, #288
    mov     x2, x25
    add     x3, x25, #192
    add     x4, x22, #ML_STEP
    bl      crypto_bls_miller_add
    C2      crypto_bls_fp12_mul_line, x19, 0, x22, ML_LINE
    add     x25, x25, #576
    subs    x26, x26, #1
    b.ne    4b
5:  subs    x24, x24, #1
    b.ge    1b
    LEAVE   0
END_FUNCTION crypto_bls_miller_loop

/*
 * crypto_bls_final_exponentiation(result, f, work): f^((p^12 - 1) / r) by
 * the steps of finalExponentiation. work holds 3456 bytes. result is not in
 * work.
 */
.set FE_T, 0
.set FE_M, 576
.set FE_A, 1152
.set FE_B, 1728
.set FE_C, 2304
.set FE_U, 2880
LOCAL_FUNCTION crypto_bls_final_exponentiation
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2                         /* work */
    adr     x22, 927f                       /* |x|, |x| + 1, (|x| + 1) / 3 */
    C2      crypto_bls_fp12_inverse, x21, FE_U, x20, 0          /* t = conj(f) / f */
    C2      crypto_bls_fp12_conjugate, x21, FE_T, x20, 0
    F12MUL  x21, FE_T, x21, FE_T, x21, FE_U
    C2      crypto_bls_fp12_frobenius, x21, FE_M, x21, FE_T     /* m = frob(frob(t)) t */
    C2      crypto_bls_fp12_frobenius, x21, FE_M, x21, FE_M
    F12MUL  x21, FE_M, x21, FE_M, x21, FE_T
    C3      crypto_bls_fp12_cyclotomic_pow, x21, FE_U, x21, FE_M, x22, 16  /* a = (m^((|x| + 1) / 3))^(|x| + 1) */
    C3      crypto_bls_fp12_cyclotomic_pow, x21, FE_A, x21, FE_U, x22, 8
    C3      crypto_bls_fp12_cyclotomic_pow, x21, FE_U, x21, FE_A, x22, 0   /* b = frob(a) conj(a^|x|) */
    C2      crypto_bls_fp12_conjugate, x21, FE_U, x21, FE_U
    C2      crypto_bls_fp12_frobenius, x21, FE_B, x21, FE_A
    F12MUL  x21, FE_B, x21, FE_B, x21, FE_U
    C3      crypto_bls_fp12_cyclotomic_pow, x21, FE_U, x21, FE_B, x22, 0   /* c = (b^|x|)^|x| frob(frob(b)) conj(b) */
    C3      crypto_bls_fp12_cyclotomic_pow, x21, FE_C, x21, FE_U, x22, 0
    C2      crypto_bls_fp12_frobenius, x21, FE_U, x21, FE_B
    C2      crypto_bls_fp12_frobenius, x21, FE_U, x21, FE_U
    F12MUL  x21, FE_C, x21, FE_C, x21, FE_U
    C2      crypto_bls_fp12_conjugate, x21, FE_U, x21, FE_B
    F12MUL  x21, FE_C, x21, FE_C, x21, FE_U
    F12MUL  x19, 0, x21, FE_C, x21, FE_M    /* c m */
    LEAVE   0
END_FUNCTION crypto_bls_final_exponentiation


/*
 * crypto_bls_pairing_check(pairs, work, valid): pairingCheck: the u64 1 when
 * the product of e(P_i, Q_i) is 1, else 0. pairs holds a u64 count, then the
 * pairs, each a G1 point and a G2 point (432 bytes). A pair with a point at
 * infinity counts as 1. The other pairs go in groups of up to PC_GROUP to
 * crypto_bls_miller_loop, in affine coordinates; it multiplies the conj of
 * each group's product. work holds 4608 bytes.
 */
.set PC_GROUP, 4
.set PC_ACC, 0
.set PC_F, 576
.set PC_E, 1152
.set PC_ML, PC_E + 576 * PC_GROUP
.set PC_R, 576
.set PC_FE, 1152
.if PC_ML + 960 > 4608
.error "pairing_check work"
.endif
/* The group of x24 pairs: acc = acc conj(their product); x24 = 0. */
.macro PC_FLUSH
    add     x0, x20, #PC_F
    add     x1, x20, #PC_E
    mov     x2, x24
    add     x3, x20, #PC_ML
    bl      crypto_bls_miller_loop
    C2      crypto_bls_fp12_conjugate, x20, PC_F, x20, PC_F
    F12MUL  x20, PC_ACC, x20, PC_ACC, x20, PC_F
    mov     x24, #0
.endm
LOCAL_FUNCTION crypto_bls_pairing_check
    ENTER   0
    mov     x19, x0
    mov     x20, x1                         /* work */
    mov     x21, x2                         /* valid */
    ldr     x22, [x19]                      /* count */
    add     x23, x19, #8                    /* the first pair */
    mov     x24, #0                         /* pairs in the group */
    SET_ONE x20, PC_ACC
    ZERO    x20, PC_ACC + 48, 528
    cbz     x22, 5f
1:  IS_ZERO x23, 96, 48                     /* skip a point at infinity */
    b.eq    2f
    IS_ZERO x23, 144 + 192, 96
    b.eq    2f
    mov     x9, #576                        /* the entry: Q, then P */
    madd    x25, x24, x9, x20
    add     x25, x25, #PC_E
    C2      crypto_bls_g2_affine, x25, 0, x23, 144
    C2      crypto_bls_g1_affine, x25, 192, x23, 0
    add     x24, x24, #1
    cmp     x24, #PC_GROUP
    b.ne    2f
    PC_FLUSH
2:  add     x23, x23, #432
    subs    x22, x22, #1
    b.ne    1b
    cbz     x24, 5f
    PC_FLUSH
5:  C3      crypto_bls_final_exponentiation, x20, PC_R, x20, PC_ACC, x20, PC_FE
    adr     x9, 900f                        /* is it 1? */
    add     x9, x9, #BLS_FP_RECORD_ONE
    EQUAL   x20, PC_R, x9, 0, 48
    b.ne    6f
    IS_ZERO x20, PC_R + 48, 528
6:  cset    x9, eq
    str     x9, [x21]
    LEAVE   0
END_FUNCTION crypto_bls_pairing_check

/* ---------------------------------------------------------------- Verification (Signatures.lean) */

/*
 * crypto_bls_core_verify(public_key, message, signature, work, valid):
 * coreVerify with the DST: the u64 1 when the signature decompresses into
 * G2, the key passes KeyValidate, and e(P, R) e(-PK, H(message)) = 1, else
 * 0. work: the 2 pairs (880 bytes), then the hash work or the pairing work.
 */
.set CV_PAIRS, 0
.set CV_G1A, 8
.set CV_G2A, 152
.set CV_G1B, 440
.set CV_G2B, 584
.set CV_AREA, 880
.set CV_V, 0
.set CV_SIZE, 16
LOCAL_FUNCTION crypto_bls_core_verify
    ENTER   0, CV_SIZE
    mov     x19, x0                         /* public_key */
    mov     x20, x1                         /* message */
    mov     x21, x2                         /* signature */
    mov     x22, x3                         /* work */
    mov     x23, x4                         /* valid */
    str     xzr, [x23]
    mov     x0, x21                         /* R: decompress, subgroup check */
    add     x1, x22, #CV_G2A
    bl      crypto_bls_g2_uncompress
    cbnz    x0, 9f
    C2      crypto_bls_g2_in_subgroup, x22, CV_G2A, sp, CV_V
    ldr     x9, [sp, #CV_V]
    cbz     x9, 9f
    mov     x0, x19                         /* PK: KeyValidate */
    add     x1, x22, #CV_G1B
    bl      crypto_bls_key_validate_point
    cbnz    x0, 9f
    G2      crypto_bls_g1_neg, x22, CV_G1B, x22, CV_G1B
    mov     x0, x20                         /* Q = H(message) */
    adr     x1, 931f
    add     x2, x22, #CV_AREA
    add     x3, x22, #CV_G2B
    bl      crypto_bls_hash_to_g2_point
    cbnz    x0, 9f
    adr     x9, 904f                        /* P: the generator of G1 */
    COPY    x22, CV_G1A, x9, 0, 96
    SET_ONE x22, CV_G1A + 96
    mov     x9, #2
    str     x9, [x22, #CV_PAIRS]
    mov     x0, x22
    add     x1, x22, #CV_AREA
    mov     x2, x23
    bl      crypto_bls_pairing_check
9:  LEAVE   0, CV_SIZE
END_FUNCTION crypto_bls_core_verify

/* Branch to label when the scratch at rs is smaller than CRYPTO_BLS_SCRATCH + count of the message at rm. Uses x9, x10. */
.macro SCRATCH_CHECK rs, rm, label
    ldr     x9, [\rm, #CRYPTO_BYTES_COUNT]
    add     x9, x9, #(CRYPTO_BLS_SCRATCH & 0xFFF)
    add     x9, x9, #(CRYPTO_BLS_SCRATCH & 0xFFF000)
    ldr     x10, [\rs]
    cmp     x10, x9
    b.lo    \label
.endm

/* crypto_bls_verify(public_key, message, signature, scratch, valid) -> status: verify. */
FUNCTION crypto_bls_verify
    ENTER   0
    SCRATCH_CHECK x3, x1, 8f
    add     x3, x3, #8
    bl      crypto_bls_core_verify
    mov     x0, #CRYPTO_OK
    LEAVE   0
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
END_FUNCTION crypto_bls_verify

/*
 * crypto_bls_fast_verify(public_keys, message, signature, work, valid):
 * fastAggregateVerify: 0 for an empty list or a key that fails KeyValidate,
 * else crypto_bls_core_verify of the compressed sum of the keys. The sum
 * and its compressed form sit in work at 5488, after the area of
 * crypto_bls_core_verify.
 */
.set FV_AREA, 5488
.set FV_P, 0
.set FV_K, 144
LOCAL_FUNCTION crypto_bls_fast_verify
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x23, x4
    str     xzr, [x23]
    add     x24, x22, #4096                 /* the sum, in work after the area of core_verify */
    add     x24, x24, #(FV_AREA - 4096)
    mov     x0, x19
    add     x1, x24, #FV_P
    bl      crypto_bls_aggregate_keys
    cbnz    x0, 9f
    G2      crypto_bls_g1_compress, x24, FV_P, x24, FV_K
    add     x0, x24, #FV_K
    mov     x1, x20
    mov     x2, x21
    mov     x3, x22
    mov     x4, x23
    bl      crypto_bls_core_verify
9:  LEAVE   0
END_FUNCTION crypto_bls_fast_verify

/* crypto_bls_fast_aggregate_verify(public_keys, message, signature, scratch, valid) -> status: fastAggregateVerify. */
FUNCTION crypto_bls_fast_aggregate_verify
    ENTER   0
    SCRATCH_CHECK x3, x1, 8f
    add     x3, x3, #8
    bl      crypto_bls_fast_verify
    mov     x0, #CRYPTO_OK
    LEAVE   0
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
END_FUNCTION crypto_bls_fast_aggregate_verify

/*
 * crypto_bls_eth_fast_aggregate_verify(public_keys, message, signature,
 * scratch, valid) -> status: ethFastAggregateVerify.
 */
FUNCTION crypto_bls_eth_fast_aggregate_verify
    ENTER   0
    SCRATCH_CHECK x3, x1, 8f
    ldr     x9, [x0, #CRYPTO_BLS_LIST_COUNT]
    cbz     x9, 1f
    add     x3, x3, #8
    bl      crypto_bls_fast_verify
    mov     x0, #CRYPTO_OK
    LEAVE   0
1:  ldrb    w9, [x2]                        /* no key: 1 exactly for 0xC0 then 95 zero bytes */
    eor     x9, x9, #0xC0
    ldrb    w10, [x2, #1]
    orr     x9, x9, x10
    ldurh   w10, [x2, #2]
    orr     x9, x9, x10
    ldur    w10, [x2, #4]
    orr     x9, x9, x10
    add     x11, x2, #8
    .rept   11
    ldr     x10, [x11], #8
    orr     x9, x9, x10
    .endr
    cmp     x9, #0
    cset    x9, eq
    str     x9, [x4]
    mov     x0, #CRYPTO_OK
    LEAVE   0
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
END_FUNCTION crypto_bls_eth_fast_aggregate_verify

/*
 * crypto_bls_core_verify_point(point, message, signature, work, valid):
 * crypto_bls_core_verify with the key as a point of G1 that is not the point
 * at infinity: the u64 1 when the signature decompresses into G2 and
 * e(P, R) e(-point, H(message)) = 1, else 0. work as for crypto_bls_core_verify.
 */
LOCAL_FUNCTION crypto_bls_core_verify_point
    ENTER   0, CV_SIZE
    mov     x19, x0                         /* point */
    mov     x20, x1                         /* message */
    mov     x21, x2                         /* signature */
    mov     x22, x3                         /* work */
    mov     x23, x4                         /* valid */
    str     xzr, [x23]
    mov     x0, x21                         /* R: decompress, subgroup check */
    add     x1, x22, #CV_G2A
    bl      crypto_bls_g2_uncompress
    cbnz    x0, 9f
    C2      crypto_bls_g2_in_subgroup, x22, CV_G2A, sp, CV_V
    ldr     x9, [sp, #CV_V]
    cbz     x9, 9f
    COPY    x22, CV_G1B, x19, 0, 144        /* -point */
    G2      crypto_bls_g1_neg, x22, CV_G1B, x22, CV_G1B
    mov     x0, x20                         /* Q = H(message) */
    adr     x1, 931f
    add     x2, x22, #CV_AREA
    add     x3, x22, #CV_G2B
    bl      crypto_bls_hash_to_g2_point
    cbnz    x0, 9f
    adr     x9, 904f                        /* P: the generator of G1 */
    COPY    x22, CV_G1A, x9, 0, 96
    SET_ONE x22, CV_G1A + 96
    mov     x9, #2
    str     x9, [x22, #CV_PAIRS]
    mov     x0, x22
    add     x1, x22, #CV_AREA
    mov     x2, x23
    bl      crypto_bls_pairing_check
9:  LEAVE   0, CV_SIZE
END_FUNCTION crypto_bls_core_verify_point

/*
 * crypto_bls_fast_aggregate_verify_cached(keys, indices, cache, message,
 * signature, scratch, valid) -> status: fastAggregateVerify of the keys at
 * the indices, each key checked once through its cache entry.
 * x19 keys, x20 the next index, x21 cache, x22 message, x23 signature,
 * x24 work, x25 valid, x26 indices left, x27 key i, x28 entry i.
 * Stack: the sum (G1Point) at 0, a point (G1Point) at 144.
 */
.set FC_ACC, 0
.set FC_P, 144
.set FC_SIZE, 288
FUNCTION crypto_bls_fast_aggregate_verify_cached
    ENTER   0, FC_SIZE
    SCRATCH_CHECK x5, x3, 8f
    mov     x19, x0
    mov     x21, x2
    mov     x22, x3
    mov     x23, x4
    add     x24, x5, #8
    mov     x25, x6
    str     xzr, [x25]
    ldp     x9, x26, [x1, #CRYPTO_BLS_LIST_OFFSET]   /* offset, count */
    cbz     x26, 9f                         /* no index: 0 */
    add     x20, x1, x9
    SET_ONE sp, FC_ACC                      /* the sum: the point at infinity */
    SET_ONE sp, FC_ACC + 48
    ZERO    sp, FC_ACC + 96, 48
1:  ldr     x9, [x20], #8                   /* index i */
    ldr     x10, [x21, #CRYPTO_BLS_CACHE_COUNT]
    cmp     x9, x10
    b.hs    9f                              /* at or past count: 0 */
    ldr     x10, [x21, #CRYPTO_BLS_CACHE_KEY_STRIDE]
    madd    x27, x9, x10, x19
    ldr     x10, [x21, #CRYPTO_BLS_CACHE_OFFSET]
    add     x10, x21, x10
    mov     x11, #CRYPTO_BLS_ENTRY_BYTES
    madd    x28, x9, x11, x10
    ldr     x9, [x28, #CRYPTO_BLS_ENTRY_STATUS]
    cbz     x9, 3f                          /* empty: check the key */
    EQUAL   x28, CRYPTO_BLS_ENTRY_KEY, x27, 0, 48
    b.ne    3f                              /* the entry of another key: check this one */
    ldr     x9, [x28, #CRYPTO_BLS_ENTRY_STATUS]
    cmp     x9, #2
    b.eq    9f                              /* a key that fails KeyValidate: 0 */
    COPY    sp, FC_P, x28, CRYPTO_BLS_ENTRY_POINT, 96
    b       4f
3:  mov     x0, x27                         /* KeyValidate, then the entry */
    add     x1, sp, #FC_P
    bl      crypto_bls_key_validate_point
    mov     x9, #2
    cbnz    x0, 31f
    COPY    x28, CRYPTO_BLS_ENTRY_POINT, sp, FC_P, 96
    mov     x9, #1
31: str     x9, [x28, #CRYPTO_BLS_ENTRY_STATUS]
    COPY    x28, CRYPTO_BLS_ENTRY_KEY, x27, 0, 48
    ldr     x9, [x28, #CRYPTO_BLS_ENTRY_STATUS]
    cmp     x9, #2
    b.eq    9f
4:  C3      crypto_bls_g1_add_affine, sp, FC_ACC, sp, FC_ACC, sp, FC_P  /* the affine point */
    subs    x26, x26, #1
    b.ne    1b
    IS_ZERO sp, FC_ACC + 96, 48             /* the sum at infinity: 0 */
    b.eq    9f
    add     x0, sp, #FC_ACC
    mov     x1, x22
    mov     x2, x23
    mov     x3, x24
    mov     x4, x25
    bl      crypto_bls_core_verify_point
9:  mov     x0, #CRYPTO_OK
    LEAVE   0, FC_SIZE
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0, FC_SIZE
END_FUNCTION crypto_bls_fast_aggregate_verify_cached


/* ---------------------------------------------------------------- Fr (Bls/Fr.lean), for KZG */

.macro RMUL ra, oa, rb, ob, rc, oc
    C3      crypto_kzg_fr_mul, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro RADD ra, oa, rb, ob, rc, oc
    C3      crypto_kzg_fr_add, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro RSUB ra, oa, rb, ob, rc, oc
    C3      crypto_kzg_fr_sub, \ra, \oa, \rb, \ob, \rc, \oc
.endm

/* The Fr element 1 (Montgomery form) at rd + od. Uses x9 to x12. */
.macro SET_FR_ONE rd, od
    adr     x11, 940f
    add     x11, x11, #KZG_FR_RECORD_ONE
    add     x12, \rd, #\od
    ldp     x9, x10, [x11]
    stp     x9, x10, [x12]
    ldp     x9, x10, [x11, #16]
    stp     x9, x10, [x12, #16]
.endm

/* The point at infinity of G1, (1, 1, 0), at rd + od. Uses x9 to x12. */
.macro G1_ZERO rd, od
    SET_ONE \rd, \od
    SET_ONE \rd, \od + 48
    ZERO    \rd, \od + 96, 48
.endm

/*
 * crypto_kzg_fr_mul(result, a, b): a * b / 2^256 mod r, for a < 2^256 and
 * b < r (CIOS). result may be a or b. a x3 to x6, T x7 to x12, b_i x1, q
 * x15, product x13, r record x14, r_j x16. A leaf.
 */
LOCAL_FUNCTION crypto_kzg_fr_mul
    UNWIND_END_PROLOGUE
    ldp     x3, x4, [x1]
    ldp     x5, x6, [x1, #16]
    adr     x14, 940f
    mov     x7, #0
    mov     x8, #0
    mov     x9, #0
    mov     x10, #0
    mov     x11, #0
    .irp off, 0, 8, 16, 24
    ldr     x1, [x2, #\off]                 /* T += a * b_i */
    mul     x13, x3, x1
    adds    x7, x7, x13
    mul     x13, x4, x1
    adcs    x8, x8, x13
    mul     x13, x5, x1
    adcs    x9, x9, x13
    mul     x13, x6, x1
    adcs    x10, x10, x13
    adcs    x11, x11, xzr
    adc     x12, xzr, xzr
    umulh   x13, x3, x1
    adds    x8, x8, x13
    umulh   x13, x4, x1
    adcs    x9, x9, x13
    umulh   x13, x5, x1
    adcs    x10, x10, x13
    umulh   x13, x6, x1
    adcs    x11, x11, x13
    adc     x12, x12, xzr
    ldr     x15, [x14, #KZG_FR_RECORD_INVERSE]
    mul     x15, x7, x15                    /* q = T0 * -r^-1 mod 2^64 */
    ldr     x16, [x14]                      /* T = (T + q * r) / 2^64 */
    mul     x13, x15, x16
    adds    xzr, x7, x13
    ldr     x16, [x14, #8]
    mul     x13, x15, x16
    adcs    x7, x8, x13
    ldr     x16, [x14, #16]
    mul     x13, x15, x16
    adcs    x8, x9, x13
    ldr     x16, [x14, #24]
    mul     x13, x15, x16
    adcs    x9, x10, x13
    adcs    x10, x11, xzr
    adc     x11, x12, xzr
    ldr     x16, [x14]
    umulh   x13, x15, x16
    adds    x7, x7, x13
    ldr     x16, [x14, #8]
    umulh   x13, x15, x16
    adcs    x8, x8, x13
    ldr     x16, [x14, #16]
    umulh   x13, x15, x16
    adcs    x9, x9, x13
    ldr     x16, [x14, #24]
    umulh   x13, x15, x16
    adcs    x10, x10, x13
    adc     x11, x11, xzr
    .endr
    ldp     x3, x4, [x14]                   /* T - r when T >= r */
    ldp     x5, x6, [x14, #16]
    subs    x3, x7, x3
    sbcs    x4, x8, x4
    sbcs    x5, x9, x5
    sbcs    x6, x10, x6
    sbcs    xzr, x11, xzr
    csel    x7, x3, x7, hs
    csel    x8, x4, x8, hs
    csel    x9, x5, x9, hs
    csel    x10, x6, x10, hs
    stp     x7, x8, [x0]
    stp     x9, x10, [x0, #16]
    ret
END_FUNCTION crypto_kzg_fr_mul

/* crypto_kzg_fr_add(result, a, b): a + b mod r, for a, b < r. result may be a or b. A leaf. */
LOCAL_FUNCTION crypto_kzg_fr_add
    UNWIND_END_PROLOGUE
    ldp     x3, x4, [x1]
    ldp     x5, x6, [x1, #16]
    ldp     x7, x8, [x2]
    ldp     x9, x10, [x2, #16]
    adds    x3, x3, x7
    adcs    x4, x4, x8
    adcs    x5, x5, x9
    adcs    x6, x6, x10
    adc     x11, xzr, xzr
    adr     x12, 940f
    ldp     x7, x8, [x12]
    ldp     x9, x10, [x12, #16]
    subs    x7, x3, x7
    sbcs    x8, x4, x8
    sbcs    x9, x5, x9
    sbcs    x10, x6, x10
    sbcs    xzr, x11, xzr
    csel    x3, x7, x3, hs
    csel    x4, x8, x4, hs
    csel    x5, x9, x5, hs
    csel    x6, x10, x6, hs
    stp     x3, x4, [x0]
    stp     x5, x6, [x0, #16]
    ret
END_FUNCTION crypto_kzg_fr_add

/* crypto_kzg_fr_sub(result, a, b): a - b mod r, for a, b < r. result may be a or b. A leaf. */
LOCAL_FUNCTION crypto_kzg_fr_sub
    UNWIND_END_PROLOGUE
    ldp     x3, x4, [x1]
    ldp     x5, x6, [x1, #16]
    ldp     x7, x8, [x2]
    ldp     x9, x10, [x2, #16]
    subs    x3, x3, x7
    sbcs    x4, x4, x8
    sbcs    x5, x5, x9
    sbcs    x6, x6, x10
    sbc     x11, xzr, xzr                   /* all ones on a borrow */
    adr     x12, 940f
    ldp     x7, x8, [x12]
    ldp     x9, x10, [x12, #16]
    and     x7, x7, x11
    and     x8, x8, x11
    and     x9, x9, x11
    and     x10, x10, x11
    adds    x3, x3, x7
    adcs    x4, x4, x8
    adcs    x5, x5, x9
    adc     x6, x6, x10
    stp     x3, x4, [x0]
    stp     x5, x6, [x0, #16]
    ret
END_FUNCTION crypto_kzg_fr_sub

/* crypto_kzg_fr_neg(result, a): -a mod r, for a < r; 0 stays 0. result may be a. A leaf. */
LOCAL_FUNCTION crypto_kzg_fr_neg
    UNWIND_END_PROLOGUE
    ldp     x3, x4, [x1]
    ldp     x5, x6, [x1, #16]
    orr     x11, x3, x4
    orr     x11, x11, x5
    orr     x11, x11, x6
    cmp     x11, #0
    csetm   x11, ne                         /* all ones when a != 0 */
    adr     x12, 940f
    ldp     x7, x8, [x12]
    ldp     x9, x10, [x12, #16]
    subs    x7, x7, x3
    sbcs    x8, x8, x4
    sbcs    x9, x9, x5
    sbc     x10, x10, x6
    and     x7, x7, x11
    and     x8, x8, x11
    and     x9, x9, x11
    and     x10, x10, x11
    stp     x7, x8, [x0]
    stp     x9, x10, [x0, #16]
    ret
END_FUNCTION crypto_kzg_fr_neg

/*
 * crypto_kzg_fr_pow(result, base, exponent): base^e (Fr.powNat), with e the
 * 4 little-endian limbs at exponent, a public value. result may be base.
 * Square and multiply from the top set bit of e; e = 0 gives 1.
 */
.set RW_ACC, 0
.set RW_BASE, 32
.set RW_SIZE, 64
LOCAL_FUNCTION crypto_kzg_fr_pow
    ENTER   0, RW_SIZE
    mov     x19, x0
    mov     x20, x2
    COPY    sp, RW_BASE, x1, 0, 32
    SET_FR_ONE sp, RW_ACC
    mov     x21, #255                       /* bit index */
1:  lsr     x9, x21, #6                     /* skip the zero bits above the top set bit */
    ldr     x10, [x20, x9, lsl #3]
    lsr     x10, x10, x21
    tbnz    x10, #0, 2f
    subs    x21, x21, #1
    b.ge    1b
    b       4f
2:  RMUL    sp, RW_ACC, sp, RW_ACC, sp, RW_ACC
    lsr     x9, x21, #6
    ldr     x10, [x20, x9, lsl #3]
    lsr     x10, x10, x21
    tbz     x10, #0, 3f
    RMUL    sp, RW_ACC, sp, RW_ACC, sp, RW_BASE
3:  subs    x21, x21, #1
    b.ge    2b
4:  COPY    x19, 0, sp, RW_ACC, 32
    LEAVE   0, RW_SIZE
END_FUNCTION crypto_kzg_fr_pow

/* crypto_kzg_fr_inverse(result, a): a^(r - 2) (Fr.inverse); 0 gives 0. result may be a. */
LOCAL_FUNCTION crypto_kzg_fr_inverse
    ENTER   0
    adr     x2, 941f
    bl      crypto_kzg_fr_pow
    LEAVE   0
END_FUNCTION crypto_kzg_fr_inverse

/*
 * crypto_kzg_fr_from_bytes(result, bytes) -> status: the 32 big-endian bytes
 * as an element of Fr (Fr.fromBytesBE, bytesToBlsField).
 * CRYPTO_INVALID_ENCODING when the number is r or more; nothing is written.
 */
LOCAL_FUNCTION crypto_kzg_fr_from_bytes
    ENTER   0, 32
    mov     x19, x0
    ldp     x12, x11, [x1]
    ldp     x10, x9, [x1, #16]
    rev     x9, x9
    rev     x10, x10
    rev     x11, x11
    rev     x12, x12
    adr     x15, 940f
    ldp     x2, x3, [x15]
    ldp     x4, x5, [x15, #16]
    cmp     x9, x2                          /* below r? */
    sbcs    xzr, x10, x3
    sbcs    xzr, x11, x4
    sbcs    xzr, x12, x5
    b.hs    9f
    stp     x9, x10, [sp]
    stp     x11, x12, [sp, #16]
    mov     x0, x19                         /* result = n * 2^512 / 2^256 */
    mov     x1, sp
    add     x2, x15, #KZG_FR_RECORD_R2
    bl      crypto_kzg_fr_mul
    mov     x0, #CRYPTO_OK
    LEAVE   0, 32
9:  mov     x0, #CRYPTO_INVALID_ENCODING
    LEAVE   0, 32
END_FUNCTION crypto_kzg_fr_from_bytes

/*
 * crypto_kzg_fr_from_digest(result, bytes): the 32 big-endian bytes, a
 * number n below 2^256, as n mod r (Fr.ofNat in hashToBlsField).
 */
LOCAL_FUNCTION crypto_kzg_fr_from_digest
    ENTER   0, 32
    ldp     x12, x11, [x1]
    ldp     x10, x9, [x1, #16]
    rev     x9, x9
    rev     x10, x10
    rev     x11, x11
    rev     x12, x12
    stp     x9, x10, [sp]
    stp     x11, x12, [sp, #16]
    mov     x1, sp                          /* n * 2^512 / 2^256, with n < 2^256 */
    adr     x2, 940f
    add     x2, x2, #KZG_FR_RECORD_R2
    bl      crypto_kzg_fr_mul
    LEAVE   0, 32
END_FUNCTION crypto_kzg_fr_from_digest

/* crypto_kzg_fr_from_u64(result, value): the u64 value in x1 as an element of Fr (Fr.ofNat). */
LOCAL_FUNCTION crypto_kzg_fr_from_u64
    ENTER   0, 32
    stp     x1, xzr, [sp]
    stp     xzr, xzr, [sp, #16]
    mov     x1, sp
    adr     x2, 940f
    add     x2, x2, #KZG_FR_RECORD_R2
    bl      crypto_kzg_fr_mul
    LEAVE   0, 32
END_FUNCTION crypto_kzg_fr_from_u64

/* crypto_kzg_fr_canonical(result, a): the value of a (Fr.val) as 4 little-endian limbs. result may be a. */
LOCAL_FUNCTION crypto_kzg_fr_canonical
    ENTER   0, 32
    mov     x9, #1
    stp     x9, xzr, [sp]
    stp     xzr, xzr, [sp, #16]
    mov     x2, sp                          /* a * 1 / 2^256 */
    bl      crypto_kzg_fr_mul
    LEAVE   0, 32
END_FUNCTION crypto_kzg_fr_canonical

/* crypto_kzg_fr_to_bytes(bytes, a): the 32 big-endian bytes of a (blsFieldToBytes). */
LOCAL_FUNCTION crypto_kzg_fr_to_bytes
    ENTER   0, 32
    mov     x19, x0
    mov     x0, sp
    bl      crypto_kzg_fr_canonical
    ldp     x9, x10, [sp]
    ldp     x11, x12, [sp, #16]
    rev     x9, x9
    rev     x10, x10
    rev     x11, x11
    rev     x12, x12
    stp     x12, x11, [x19]
    stp     x10, x9, [x19, #16]
    LEAVE   0, 32
END_FUNCTION crypto_kzg_fr_to_bytes

/* ---------------------------------------------------------------- Roots of unity, bit reversal, FFT (Kzg) */

/*
 * crypto_kzg_roots_of_unity(roots, order): the powers 1, w, ..., w^(order - 1)
 * of w = 7^((r - 1) / order) (computeRootsOfUnity), for order a power of two
 * from 2 to 2^32, in x1.
 */
.set RU_E, 0
.set RU_W, 32
.set RU_SIZE, 64
LOCAL_FUNCTION crypto_kzg_roots_of_unity
    ENTER   0, RU_SIZE
    mov     x19, x0
    mov     x20, x1
    clz     x9, x20                         /* k = log2 order */
    mov     x10, #63
    sub     x9, x10, x9
    neg     x10, x9                         /* 64 - k, mod 64 */
    adr     x11, 942f                       /* e = (r - 1) >> k */
    ldp     x12, x13, [x11]
    ldp     x14, x15, [x11, #16]
    lsr     x12, x12, x9
    lsl     x16, x13, x10
    orr     x12, x12, x16
    lsr     x13, x13, x9
    lsl     x16, x14, x10
    orr     x13, x13, x16
    lsr     x14, x14, x9
    lsl     x16, x15, x10
    orr     x14, x14, x16
    lsr     x15, x15, x9
    stp     x12, x13, [sp, #RU_E]
    stp     x14, x15, [sp, #RU_E + 16]
    add     x0, sp, #RU_W                   /* w = 7^e */
    mov     x1, #7
    bl      crypto_kzg_fr_from_u64
    C3      crypto_kzg_fr_pow, sp, RU_W, sp, RU_W, sp, RU_E
    SET_FR_ONE x19, 0                       /* computePowers */
    mov     x21, #1
1:  cmp     x21, x20
    b.hs    9f
    add     x0, x19, x21, lsl #5
    sub     x1, x0, #32
    add     x2, sp, #RU_W
    bl      crypto_kzg_fr_mul
    add     x21, x21, #1
    b       1b
9:  LEAVE   0, RU_SIZE
END_FUNCTION crypto_kzg_roots_of_unity

/*
 * crypto_kzg_bit_reversal(array, n, size): the bit-reversal permutation
 * (bitReversalPermutation) of the n entries of size bytes at array, in
 * place: entry i swaps with entry rev(i), with rev the reversal of log2 n
 * bits (reverseBits). n is a power of two from 2 up, in x1; size is a
 * multiple of 16, in x2. A leaf.
 */
LOCAL_FUNCTION crypto_kzg_bit_reversal
    UNWIND_END_PROLOGUE
    clz     x9, x1                          /* 64 - log2 n */
    add     x9, x9, #1
    mov     x10, #0                         /* i */
1:  rbit    x11, x10                        /* j = rev(i) */
    lsr     x11, x11, x9
    cmp     x10, x11
    b.hs    3f
    mul     x12, x10, x2
    add     x12, x0, x12
    mul     x13, x11, x2
    add     x13, x0, x13
    mov     x14, x2
2:  ldp     x3, x4, [x12]
    ldp     x5, x6, [x13]
    stp     x5, x6, [x12], #16
    stp     x3, x4, [x13], #16
    subs    x14, x14, #16
    b.ne    2b
3:  add     x10, x10, #1
    cmp     x10, x1
    b.lo    1b
    ret
END_FUNCTION crypto_kzg_bit_reversal

/*
 * crypto_kzg_fft(vals, n, roots, inverse): the FFT of the n values at vals,
 * in place (fftField): the bit-reversal permutation, then the stages of
 * fftStages, each pair r < h of a block of 2 h values with the root at m r,
 * for m = n / (2 h). With inverse 1, root i is root (n - i) mod n and each
 * value is divided by n. n (a power of two) and inverse are in x1 and x3;
 * roots holds the n-th roots of unity.
 */
.set KF_T, 0
.set KF_SIZE, 32
LOCAL_FUNCTION crypto_kzg_fft
    ENTER   0, KF_SIZE
    mov     x19, x0                         /* vals */
    mov     x20, x1                         /* n */
    mov     x21, x2                         /* roots */
    mov     x22, x3                         /* inverse */
    mov     x2, #32
    bl      crypto_kzg_bit_reversal
    mov     x23, #0                         /* log2 h */
    lsr     x24, x20, #1                    /* m */
1:  cbz     x24, 5f
    mov     x25, #0                         /* pair j < n / 2 */
2:  lsr     x9, x25, x23                    /* block b = j / h, r = j mod h */
    mov     x10, #1
    lsl     x10, x10, x23
    sub     x10, x10, #1
    and     x10, x25, x10
    add     x11, x23, #1
    lsl     x9, x9, x11
    add     x26, x9, x10                    /* i1 = 2 h b + r */
    mov     x11, #1
    lsl     x11, x11, x23
    add     x27, x26, x11                   /* i2 = i1 + h */
    mul     x12, x24, x10                   /* root index m r, or (n - m r) mod n */
    cbz     x22, 3f
    sub     x13, x20, #1
    sub     x12, x20, x12
    and     x12, x12, x13
3:  add     x0, sp, #KF_T                   /* t = x[i2] * root */
    add     x1, x19, x27, lsl #5
    add     x2, x21, x12, lsl #5
    bl      crypto_kzg_fr_mul
    add     x0, x19, x27, lsl #5            /* x[i2] = x[i1] - t */
    add     x1, x19, x26, lsl #5
    add     x2, sp, #KF_T
    bl      crypto_kzg_fr_sub
    add     x0, x19, x26, lsl #5            /* x[i1] = x[i1] + t */
    mov     x1, x0
    add     x2, sp, #KF_T
    bl      crypto_kzg_fr_add
    add     x25, x25, #1
    cmp     x25, x20, lsr #1
    b.lo    2b
    add     x23, x23, #1
    lsr     x24, x24, #1
    b       1b
5:  cbz     x22, 9f                         /* inverse: times 1 / n */
    add     x0, sp, #KF_T
    mov     x1, x20
    bl      crypto_kzg_fr_from_u64
    C2      crypto_kzg_fr_inverse, sp, KF_T, sp, KF_T
    mov     x25, #0
6:  add     x0, x19, x25, lsl #5
    mov     x1, x0
    add     x2, sp, #KF_T
    bl      crypto_kzg_fr_mul
    add     x25, x25, #1
    cmp     x25, x20
    b.lo    6b
9:  LEAVE   0, KF_SIZE
END_FUNCTION crypto_kzg_fft

/* crypto_kzg_shift_vals(vals, n, factor): vals[i] times factor^i, in place (shiftVals); n in x1. */
.set SH_S, 0
.set SH_SIZE, 32
LOCAL_FUNCTION crypto_kzg_shift_vals
    ENTER   0, SH_SIZE
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    SET_FR_ONE sp, SH_S
    mov     x22, #0
1:  cmp     x22, x20
    b.hs    9f
    add     x0, x19, x22, lsl #5
    mov     x1, x0
    add     x2, sp, #SH_S
    bl      crypto_kzg_fr_mul
    C3      crypto_kzg_fr_mul, sp, SH_S, sp, SH_S, x21, 0
    add     x22, x22, #1
    b       1b
9:  LEAVE   0, SH_SIZE
END_FUNCTION crypto_kzg_shift_vals

/*
 * crypto_kzg_coset_fft(vals, n, roots, inverse): cosetFftField with the shift
 * 7: shiftVals by 7 then the FFT; or the inverse FFT then shiftVals by 1 / 7.
 * n and inverse are in x1 and x3.
 */
.set CF_F, 0
.set CF_SIZE, 32
LOCAL_FUNCTION crypto_kzg_coset_fft
    ENTER   0, CF_SIZE
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    add     x0, sp, #CF_F
    mov     x1, #7
    bl      crypto_kzg_fr_from_u64
    cbnz    x22, 1f
    mov     x0, x19
    mov     x1, x20
    add     x2, sp, #CF_F
    bl      crypto_kzg_shift_vals
    mov     x0, x19
    mov     x1, x20
    mov     x2, x21
    mov     x3, #0
    bl      crypto_kzg_fft
    LEAVE   0, CF_SIZE
1:  mov     x0, x19
    mov     x1, x20
    mov     x2, x21
    mov     x3, #1
    bl      crypto_kzg_fft
    C2      crypto_kzg_fr_inverse, sp, CF_F, sp, CF_F
    mov     x0, x19
    mov     x1, x20
    add     x2, sp, #CF_F
    bl      crypto_kzg_shift_vals
    LEAVE   0, CF_SIZE
END_FUNCTION crypto_kzg_coset_fft

/*
 * crypto_kzg_batch_inverse(out, in, n): out[i] = 1 / in[i], and 0 for 0
 * (Fr.batchInverse): the products of the nonzero values before each one, one
 * inversion, then the walk back. out must not be in. n in x2.
 */
.set BI_P, 0
.set BI_S, 32
.set BI_SIZE, 64
LOCAL_FUNCTION crypto_kzg_batch_inverse
    ENTER   0, BI_SIZE
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    SET_FR_ONE sp, BI_P
    mov     x22, #0
1:  cmp     x22, x21                        /* out[i] = pre, the product of the nonzero values before i */
    b.hs    3f
    add     x23, x20, x22, lsl #5
    add     x9, x19, x22, lsl #5
    add     x10, sp, #BI_P
    ldp     x11, x12, [x10]
    stp     x11, x12, [x9]
    ldp     x11, x12, [x10, #16]
    stp     x11, x12, [x9, #16]
    IS_ZERO x23, 0, 32
    b.eq    2f
    C3      crypto_kzg_fr_mul, sp, BI_P, sp, BI_P, x23, 0
2:  add     x22, x22, #1
    b       1b
3:  C2      crypto_kzg_fr_inverse, sp, BI_S, sp, BI_P      /* s = 1 / the product */
4:  cbz     x22, 9f
    sub     x22, x22, #1
    add     x23, x20, x22, lsl #5
    add     x24, x19, x22, lsl #5
    IS_ZERO x23, 0, 32
    b.ne    5f
    ZERO    x24, 0, 32
    b       4b
5:  C3      crypto_kzg_fr_mul, x24, 0, x24, 0, sp, BI_S    /* out[i] = pre s; s = s in[i] */
    C3      crypto_kzg_fr_mul, sp, BI_S, sp, BI_S, x23, 0
    b       4b
9:  LEAVE   0, BI_SIZE
END_FUNCTION crypto_kzg_batch_inverse

/*
 * crypto_kzg_blob_to_poly(poly, bytes, count) -> status: count field
 * elements of 32 big-endian bytes (bytesToBlsFields). CRYPTO_INVALID_ENCODING
 * when one is r or more. count in x2.
 */
LOCAL_FUNCTION crypto_kzg_blob_to_poly
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, #0
1:  cmp     x22, x21
    b.hs    8f
    add     x0, x19, x22, lsl #5
    add     x1, x20, x22, lsl #5
    bl      crypto_kzg_fr_from_bytes
    cbnz    x0, 9f
    add     x22, x22, #1
    b       1b
8:  mov     x0, #CRYPTO_OK
9:  LEAVE   0
END_FUNCTION crypto_kzg_blob_to_poly

/*
 * crypto_kzg_eval_to_coeff(poly, roots): the 4096 coefficients of the
 * polynomial of 4096 values, in place (polynomialEvalToCoeff): the inverse
 * FFT of the bit-reversed values. roots receives the 4096-th roots of unity.
 */
LOCAL_FUNCTION crypto_kzg_eval_to_coeff
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x0, x20
    mov     x1, #4096
    bl      crypto_kzg_roots_of_unity
    mov     x0, x19
    mov     x1, #4096
    mov     x2, #32
    bl      crypto_kzg_bit_reversal
    mov     x0, x19
    mov     x1, #4096
    mov     x2, x20
    mov     x3, #1
    bl      crypto_kzg_fft
    LEAVE   0
END_FUNCTION crypto_kzg_eval_to_coeff

/*
 * crypto_kzg_extended_cells(cells, coeff, work): the cells of the 4096
 * coefficients at coeff (cellsOfExtendedEvaluations of extendedEvaluations):
 * zero padding to 8192, the FFT over the 8192-th roots of unity, the
 * bit-reversal permutation, then 32 big-endian bytes per value. work holds
 * 524288 bytes: the values, then the roots.
 */
LOCAL_FUNCTION crypto_kzg_extended_cells
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2                         /* values */
    add     x22, x21, #(262144 >> 12), lsl #12      /* roots */
    mov     x9, x20
    mov     x10, x21
    mov     x11, #4096
1:  ldp     x12, x13, [x9], #16
    stp     x12, x13, [x10], #16
    ldp     x12, x13, [x9], #16
    stp     x12, x13, [x10], #16
    subs    x11, x11, #1
    b.ne    1b
    mov     x11, #4096
2:  stp     xzr, xzr, [x10], #16
    stp     xzr, xzr, [x10], #16
    subs    x11, x11, #1
    b.ne    2b
    mov     x0, x22
    mov     x1, #8192
    bl      crypto_kzg_roots_of_unity
    mov     x0, x21
    mov     x1, #8192
    mov     x2, x22
    mov     x3, #0
    bl      crypto_kzg_fft
    mov     x0, x21
    mov     x1, #8192
    mov     x2, #32
    bl      crypto_kzg_bit_reversal
    mov     x23, #0
3:  add     x0, x19, x23, lsl #5
    add     x1, x21, x23, lsl #5
    bl      crypto_kzg_fr_to_bytes
    add     x23, x23, #1
    cmp     x23, #8192
    b.lo    3b
    LEAVE   0
END_FUNCTION crypto_kzg_extended_cells

/* Branch to label when the scratch at rs holds fewer than CRYPTO_KZG_SCRATCH + rn * CRYPTO_KZG_SCRATCH_PER_ENTRY bytes. Uses x9, x10. */
.macro KZG_SCRATCH_CHECK rs, rn, label
    lsl     x9, \rn, #13
    add     x9, x9, #(CRYPTO_KZG_SCRATCH >> 12), lsl #12
    ldr     x10, [\rs]
    cmp     x10, x9
    b.lo    \label
.endm

/* crypto_kzg_compute_cells(blob, scratch, cells) -> status: computeCells. work: the polynomial, then 524288 bytes. */
FUNCTION crypto_kzg_compute_cells
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    KZG_SCRATCH_CHECK x20, xzr, 8f
    add     x22, x20, #8                    /* the polynomial */
    mov     x0, x22
    mov     x1, x19
    mov     x2, #4096
    bl      crypto_kzg_blob_to_poly
    cbnz    x0, 9f
    add     x23, x22, #(131072 >> 12), lsl #12
    mov     x0, x22
    mov     x1, x23
    bl      crypto_kzg_eval_to_coeff
    mov     x0, x21
    mov     x1, x22
    mov     x2, x23
    bl      crypto_kzg_extended_cells
    mov     x0, #CRYPTO_OK
9:  LEAVE   0
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
END_FUNCTION crypto_kzg_compute_cells

/* ---------------------------------------------------------------- Trusted setup (TrustedSetup.lean) */

/* crypto_kzg_trusted_setup_of_bytes(g1_lagrange, g1_monomial, g2_monomial, settings) -> status: TrustedSetup.ofBytes. */
FUNCTION crypto_kzg_trusted_setup_of_bytes
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    ldr     x9, [x19, #CRYPTO_BYTES_COUNT]  /* the counts */
    mov     x10, #CRYPTO_KZG_SETUP_G1_SIZE
    cmp     x9, x10
    b.ne    8f
    ldr     x9, [x20, #CRYPTO_BYTES_COUNT]
    cmp     x9, x10
    b.ne    8f
    ldr     x9, [x21, #CRYPTO_BYTES_COUNT]
    mov     x10, #CRYPTO_KZG_SETUP_G2_SIZE
    cmp     x9, x10
    b.ne    8f
    ldr     x23, [x19, #CRYPTO_BYTES_OFFSET]  /* Lagrange point i at rev(i) */
    add     x23, x19, x23
    mov     x24, #0
1:  rbit    x9, x24
    lsr     x9, x9, #52
    mov     x10, #BLS_G1
    madd    x1, x9, x10, x22
    mov     x10, #48
    madd    x0, x24, x10, x23
    bl      crypto_bls_g1_uncompress
    cbnz    x0, 8f
    add     x24, x24, #1
    cmp     x24, #4096
    b.lo    1b
    ldr     x23, [x20, #CRYPTO_BYTES_OFFSET]  /* the monomial points */
    add     x23, x20, x23
    add     x25, x22, #(CRYPTO_KZG_SETTINGS_G1_MONOMIAL >> 12), lsl #12
    mov     x24, #0
2:  mov     x10, #BLS_G1
    madd    x1, x24, x10, x25
    mov     x10, #48
    madd    x0, x24, x10, x23
    bl      crypto_bls_g1_uncompress
    cbnz    x0, 8f
    add     x24, x24, #1
    cmp     x24, #4096
    b.lo    2b
    ldr     x23, [x21, #CRYPTO_BYTES_OFFSET]  /* the G2 points */
    add     x23, x21, x23
    add     x25, x22, #(CRYPTO_KZG_SETTINGS_G2_MONOMIAL >> 12), lsl #12
    mov     x24, #0
3:  mov     x10, #BLS_G2
    madd    x1, x24, x10, x25
    mov     x10, #96
    madd    x0, x24, x10, x23
    bl      crypto_bls_g2_uncompress
    cbnz    x0, 8f
    add     x24, x24, #1
    cmp     x24, #65
    b.lo    3b
    mov     x0, #CRYPTO_OK
    LEAVE   0
8:  mov     x0, #CRYPTO_KZG_INVALID_TRUSTED_SETUP
    LEAVE   0
END_FUNCTION crypto_kzg_trusted_setup_of_bytes

/* ---------------------------------------------------------------- Challenges and point checks (Core.lean) */

/*
 * crypto_kzg_validate_g1(bytes, point) -> status: validateKzgG1Point: the
 * point at infinity for 0xC0 followed by 47 zero bytes, else
 * crypto_bls_key_validate_point. CRYPTO_INVALID_PUBLIC_KEY otherwise.
 */
LOCAL_FUNCTION crypto_kzg_validate_g1
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    ldrb    w9, [x19]
    eor     x9, x9, #0xC0
    ldrb    w10, [x19, #1]
    orr     x9, x9, x10
    ldurh   w10, [x19, #2]
    orr     x9, x9, x10
    ldur    w10, [x19, #4]
    orr     x9, x9, x10
    add     x11, x19, #8
    .rept   5
    ldr     x10, [x11], #8
    orr     x9, x9, x10
    .endr
    cbnz    x9, 1f
    G1_ZERO x20, 0
    mov     x0, #CRYPTO_OK
    LEAVE   0
1:  mov     x0, x19
    mov     x1, x20
    bl      crypto_bls_key_validate_point
    LEAVE   0
END_FUNCTION crypto_kzg_validate_g1

/*
 * crypto_kzg_challenge(result, blob, commitment, work): computeChallenge:
 * SHA-256 of "FSBLOBVERIFY_V1_" || I2OSP(4096, 16) || blob || commitment, as
 * a number mod r. work holds 131232 bytes: the data as a ByteList, then the
 * digest.
 */
.set CH_DATA, 0
.set CH_DIGEST, 131200
LOCAL_FUNCTION crypto_kzg_challenge
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x9, #(CH_DIGEST & 0xFFFF)       /* size, offset 24, count 131152 */
    movk    x9, #(CH_DIGEST >> 16), lsl #16
    mov     x10, #24
    stp     x9, x10, [x22]
    mov     x9, #(131152 & 0xFFFF)
    movk    x9, #(131152 >> 16), lsl #16
    str     x9, [x22, #16]
    adr     x9, 945f
    ldp     x10, x11, [x9]
    stp     x10, x11, [x22, #24]
    movz    x10, #0x10, lsl #48             /* I2OSP(4096, 16): byte 14 is 0x10 */
    stp     xzr, x10, [x22, #40]
    add     x10, x22, #56                   /* the blob */
    mov     x11, x20
    mov     x12, #8192
1:  ldp     x13, x14, [x11], #16
    stp     x13, x14, [x10], #16
    subs    x12, x12, #1
    b.ne    1b
    ldp     x13, x14, [x21]                 /* the commitment */
    stp     x13, x14, [x10]
    ldp     x13, x14, [x21, #16]
    stp     x13, x14, [x10, #16]
    ldp     x13, x14, [x21, #32]
    stp     x13, x14, [x10, #32]
    mov     x0, x22
    add     x1, x22, #(CH_DIGEST >> 12), lsl #12
    add     x1, x1, #(CH_DIGEST & 0xFFF)
    CALL_GLOBAL crypto_sha256
    mov     x0, x19
    add     x1, x22, #(CH_DIGEST >> 12), lsl #12
    add     x1, x1, #(CH_DIGEST & 0xFFF)
    bl      crypto_kzg_fr_from_digest
    LEAVE   0
END_FUNCTION crypto_kzg_challenge

/*
 * crypto_kzg_compute_challenge(blob, commitment, scratch, challenge) ->
 * status: computeChallengeExport. work: the polynomial, then the point, then
 * the challenge work.
 */
.set CC_POLY, 0
.set CC_POINT, 131072
.set CC_FR, 131216
.set CC_WORK, 131248
FUNCTION crypto_kzg_compute_challenge
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    KZG_SCRATCH_CHECK x21, xzr, 7f
    add     x23, x21, #8                    /* work */
    mov     x0, x23
    mov     x1, x19
    mov     x2, #4096
    bl      crypto_kzg_blob_to_poly
    cbnz    x0, 9f
    add     x24, x23, #(CC_POINT >> 12), lsl #12
    mov     x0, x20
    mov     x1, x24
    bl      crypto_kzg_validate_g1
    cbnz    x0, 8f
    mov     x0, x24                         /* the result, at CC_FR */
    add     x0, x0, #(CC_FR - CC_POINT)
    mov     x1, x19
    mov     x2, x20
    add     x3, x24, #(CC_WORK - CC_POINT)
    bl      crypto_kzg_challenge
    mov     x0, x22
    add     x1, x24, #(CC_FR - CC_POINT)
    bl      crypto_kzg_fr_to_bytes
    mov     x0, #CRYPTO_OK
9:  LEAVE   0
7:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
8:  mov     x0, #CRYPTO_KZG_INVALID_COMMITMENT
    LEAVE   0
END_FUNCTION crypto_kzg_compute_challenge

/* ---------------------------------------------------------------- Linear combinations and evaluation (Core.lean, Polynomials.lean) */

/* The generator of G1 as a G1 point at rd + od. Uses x9 to x12. */
.macro G1_GEN rd, od
    adr     x9, 904f
    COPY    \rd, \od, x9, 0, 96
    SET_ONE \rd, \od + 96
.endm

/* The generator of G2 as a G2 point at rd + od. Uses x9 to x12. */
.macro G2_GEN rd, od
    adr     x9, 905f
    COPY    \rd, \od, x9, 0, 192
    SET_ONE \rd, \od + 192
    ZERO    \rd, \od + 240, 48
.endm

/*
 * crypto_kzg_g1_lincomb(result, points, scalars, n, work): the sum of
 * scalars[j] times points[j] (g1LincombPoints), by the steps of G1.msm:
 * Pippenger's method with windows of 8 bits, from the top window down, the
 * point at infinity for n = 0 or all scalars 0. n in x3. work holds 32 n +
 * 37296 bytes: the values of the scalars, the 256 buckets, then the sum,
 * the running sum and the partial sum.
 */
LOCAL_FUNCTION crypto_kzg_g1_lincomb
    ENTER   0
    mov     x19, x0                         /* result */
    mov     x20, x1                         /* points */
    mov     x21, x2                         /* scalars */
    mov     x22, x3                         /* n */
    mov     x23, x4                         /* work: the values */
    cbz     x22, 8f
    mov     x24, #0                         /* vals = the values of the scalars */
1:  add     x0, x23, x24, lsl #5
    add     x1, x21, x24, lsl #5
    bl      crypto_kzg_fr_canonical
    add     x24, x24, #1
    cmp     x24, x22
    b.lo    1b
    mov     x25, #0                         /* msmMaxBits */
    mov     x24, #0
2:  add     x9, x23, x24, lsl #5
    ldp     x10, x11, [x9]
    ldp     x12, x13, [x9, #16]
    mov     x14, #256
    cbnz    x13, 3f
    mov     x13, x12
    mov     x14, #192
    cbnz    x13, 3f
    mov     x13, x11
    mov     x14, #128
    cbnz    x13, 3f
    mov     x13, x10
    mov     x14, #64
    cbz     x13, 4f
3:  clz     x15, x13
    sub     x14, x14, x15
    cmp     x14, x25
    csel    x25, x14, x25, hi
4:  add     x24, x24, #1
    cmp     x24, x22
    b.lo    2b
    cbz     x25, 8f
    add     x25, x25, #7                    /* nW */
    lsr     x25, x25, #3
    add     x24, x23, x22, lsl #5           /* the buckets */
    add     x28, x24, #(256 * BLS_G1)       /* the sum, then the running and partial sums */
    G1_ZERO x28, 0
    mov     x26, #0                         /* kk */
5:  mov     x27, #1                         /* buckets 1 to 255 at infinity */
6:  mov     x9, #BLS_G1
    madd    x13, x27, x9, x24
    G1_ZERO x13, 0
    add     x27, x27, #1
    cmp     x27, #256
    b.lo    6b
    mov     x27, #0                         /* msmBuckets */
7:  sub     x9, x25, x26                    /* k = nW - 1 - kk */
    sub     x9, x9, #1
    add     x10, x23, x27, lsl #5
    ldrb    w10, [x10, x9]                  /* digit k of vals[j] */
    cbz     x10, 70f
    mov     x9, #BLS_G1
    madd    x0, x10, x9, x24
    mov     x9, #BLS_G1
    madd    x1, x27, x9, x20
    mov     x2, x0
    CALL_GLOBAL crypto_bls_g1_add
70: add     x27, x27, #1
    cmp     x27, x22
    b.lo    7b
    G1_ZERO x28, BLS_G1                     /* msmRunning: from bucket 255 down to 1 */
    G1_ZERO x28, 2 * BLS_G1
    mov     x27, #255
71: mov     x9, #BLS_G1
    madd    x1, x27, x9, x24
    add     x0, x28, #BLS_G1
    add     x2, x28, #BLS_G1
    CALL_GLOBAL crypto_bls_g1_add           /* running += B_v */
    add     x0, x28, #(2 * BLS_G1)
    add     x1, x28, #BLS_G1
    add     x2, x28, #(2 * BLS_G1)
    CALL_GLOBAL crypto_bls_g1_add           /* partial += running */
    subs    x27, x27, #1
    b.ne    71b
    cbz     x26, 73f                        /* msmCombine: 8 doublings, except for the first window */
    mov     x27, #8
72: mov     x0, x28
    mov     x1, x28
    bl      crypto_bls_g1_double
    subs    x27, x27, #1
    b.ne    72b
73: mov     x0, x28
    add     x1, x28, #(2 * BLS_G1)
    mov     x2, x28
    CALL_GLOBAL crypto_bls_g1_add
    add     x26, x26, #1
    cmp     x26, x25
    b.lo    5b
    COPY    x19, 0, x28, 0, BLS_G1
    LEAVE   0
8:  G1_ZERO x19, 0
    LEAVE   0
END_FUNCTION crypto_kzg_g1_lincomb

/* crypto_kzg_domain(domain): the bit-reversed 4096-th roots of unity (rootsOfUnityBrp 4096). */
LOCAL_FUNCTION crypto_kzg_domain
    ENTER   0
    mov     x19, x0
    mov     x1, #4096
    bl      crypto_kzg_roots_of_unity
    mov     x0, x19
    mov     x1, #4096
    mov     x2, #32
    bl      crypto_kzg_bit_reversal
    LEAVE   0
END_FUNCTION crypto_kzg_domain

/*
 * crypto_kzg_evaluate(result, poly, z, work): p(z) for the 4096 values at
 * poly (evaluatePolynomialInEvaluationForm): value i when z is point i of
 * the domain, else (z^4096 - 1) / 4096 times the sum of p_i d_i / (z - d_i).
 * work holds 393216 bytes: the domain, z - d_i, then the inverses. z is not
 * in work.
 */
.set EV_ACC, 0
.set EV_T, 32
.set EV_E, 64
.set EV_SIZE, 96
LOCAL_FUNCTION crypto_kzg_evaluate
    ENTER   0, EV_SIZE
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3                         /* the domain */
    add     x23, x22, #(131072 >> 12), lsl #12      /* z - d_i */
    add     x24, x22, #(262144 >> 12), lsl #12      /* the inverses */
    mov     x0, x22
    bl      crypto_kzg_domain
    mov     x25, #0                         /* z in the domain: its value */
1:  add     x26, x22, x25, lsl #5
    EQUAL   x26, 0, x21, 0, 32
    b.ne    2f
    add     x9, x20, x25, lsl #5
    COPY    x19, 0, x9, 0, 32
    LEAVE   0, EV_SIZE
2:  add     x25, x25, #1
    cmp     x25, #4096
    b.lo    1b
    mov     x25, #0
3:  add     x0, x23, x25, lsl #5
    mov     x1, x21
    add     x2, x22, x25, lsl #5
    bl      crypto_kzg_fr_sub
    add     x25, x25, #1
    cmp     x25, #4096
    b.lo    3b
    mov     x0, x24
    mov     x1, x23
    mov     x2, #4096
    bl      crypto_kzg_batch_inverse
    ZERO    sp, EV_ACC, 32
    mov     x25, #0
4:  add     x0, sp, #EV_T                   /* acc += p_i d_i inv_i */
    add     x1, x20, x25, lsl #5
    add     x2, x22, x25, lsl #5
    bl      crypto_kzg_fr_mul
    add     x0, sp, #EV_T
    add     x1, sp, #EV_T
    add     x2, x24, x25, lsl #5
    bl      crypto_kzg_fr_mul
    RADD    sp, EV_ACC, sp, EV_ACC, sp, EV_T
    add     x25, x25, #1
    cmp     x25, #4096
    b.lo    4b
    mov     x9, #4096                       /* r = z^4096 - 1 */
    stp     x9, xzr, [sp, #EV_E]
    stp     xzr, xzr, [sp, #EV_E + 16]
    C3      crypto_kzg_fr_pow, sp, EV_T, x21, 0, sp, EV_E
    SET_FR_ONE sp, EV_E
    RSUB    sp, EV_T, sp, EV_T, sp, EV_E
    RMUL    sp, EV_ACC, sp, EV_ACC, sp, EV_T        /* acc r / 4096 */
    add     x0, sp, #EV_T
    mov     x1, #4096
    bl      crypto_kzg_fr_from_u64
    C2      crypto_kzg_fr_inverse, sp, EV_T, sp, EV_T
    RMUL    x19, 0, sp, EV_ACC, sp, EV_T
    LEAVE   0, EV_SIZE
END_FUNCTION crypto_kzg_evaluate

/*
 * crypto_kzg_quotient_in_domain(result, z, poly, y, work): the quotient at the
 * domain point z (computeQuotientEvalWithinDomain): the sum over the points
 * d_i != z of (p_i - y) d_i / (z (z - d_i)). work holds 393216 bytes. z and
 * y are not in work.
 */
.set QD_T, 0
.set QD_SIZE, 32
LOCAL_FUNCTION crypto_kzg_quotient_in_domain
    ENTER   0, QD_SIZE
    mov     x19, x0
    mov     x20, x1                         /* z */
    mov     x21, x2                         /* poly */
    mov     x22, x3                         /* y */
    mov     x23, x4                         /* the domain */
    add     x24, x23, #(131072 >> 12), lsl #12      /* z (z - d_i) */
    add     x25, x23, #(262144 >> 12), lsl #12      /* the inverses */
    mov     x0, x23
    bl      crypto_kzg_domain
    mov     x26, #0
1:  add     x0, x24, x26, lsl #5
    mov     x1, x20
    add     x2, x23, x26, lsl #5
    bl      crypto_kzg_fr_sub
    add     x0, x24, x26, lsl #5
    mov     x1, x20
    mov     x2, x0
    bl      crypto_kzg_fr_mul
    add     x26, x26, #1
    cmp     x26, #4096
    b.lo    1b
    mov     x0, x25
    mov     x1, x24
    mov     x2, #4096
    bl      crypto_kzg_batch_inverse
    ZERO    x19, 0, 32
    mov     x26, #0
2:  add     x27, x23, x26, lsl #5
    EQUAL   x27, 0, x20, 0, 32              /* skip d_i = z */
    b.eq    3f
    add     x0, sp, #QD_T
    add     x1, x21, x26, lsl #5
    mov     x2, x22
    bl      crypto_kzg_fr_sub
    RMUL    sp, QD_T, sp, QD_T, x27, 0
    add     x0, sp, #QD_T
    add     x1, sp, #QD_T
    add     x2, x25, x26, lsl #5
    bl      crypto_kzg_fr_mul
    RADD    x19, 0, x19, 0, sp, QD_T
3:  add     x26, x26, #1
    cmp     x26, #4096
    b.lo    2b
    LEAVE   0, QD_SIZE
END_FUNCTION crypto_kzg_quotient_in_domain

/*
 * crypto_kzg_proof_impl(settings, poly, z, work, proof, y): computeKzgProofImpl:
 * y = p(z), the quotient q_i = (p_i - y) / (d_i - z), or the quotient in the
 * domain where d_i = z, and the proof, the sum of q_i times Lagrange point i.
 * proof is a G1 point, y an element of Fr. work holds 1310720 bytes. z, the
 * outputs and poly are not in work.
 */
.set PI_DOMAIN, 0
.set PI_SHIFT, 131072
.set PI_DEN, 262144
.set PI_INV, 393216
.set PI_Q, 524288
.set PI_WORK, 655360
LOCAL_FUNCTION crypto_kzg_proof_impl
    ENTER   0
    mov     x19, x0                         /* settings */
    mov     x20, x1                         /* poly */
    mov     x21, x2                         /* z */
    mov     x22, x3                         /* work */
    mov     x23, x4                         /* proof */
    mov     x24, x5                         /* y */
    mov     x0, x24
    mov     x1, x20
    mov     x2, x21
    add     x3, x22, #(PI_WORK >> 12), lsl #12
    bl      crypto_kzg_evaluate
    mov     x0, x22
    bl      crypto_kzg_domain
    mov     x25, #0
1:  add     x9, x22, #(PI_SHIFT >> 12), lsl #12     /* p_i - y, and d_i - z */
    add     x0, x9, x25, lsl #5
    add     x1, x20, x25, lsl #5
    mov     x2, x24
    bl      crypto_kzg_fr_sub
    add     x9, x22, #(PI_DEN >> 12), lsl #12
    add     x0, x9, x25, lsl #5
    add     x1, x22, x25, lsl #5
    mov     x2, x21
    bl      crypto_kzg_fr_sub
    add     x25, x25, #1
    cmp     x25, #4096
    b.lo    1b
    add     x0, x22, #(PI_INV >> 12), lsl #12
    add     x1, x22, #(PI_DEN >> 12), lsl #12
    mov     x2, #4096
    bl      crypto_kzg_batch_inverse
    mov     x25, #0
2:  add     x9, x22, #(PI_DEN >> 12), lsl #12
    add     x26, x9, x25, lsl #5
    add     x9, x22, #(PI_Q >> 12), lsl #12
    add     x27, x9, x25, lsl #5
    IS_ZERO x26, 0, 32
    b.ne    3f
    mov     x0, x27                         /* z is the domain point d_i */
    add     x1, x22, x25, lsl #5
    mov     x2, x20
    mov     x3, x24
    add     x4, x22, #(PI_WORK >> 12), lsl #12
    bl      crypto_kzg_quotient_in_domain
    b       4f
3:  mov     x0, x27
    add     x9, x22, #(PI_SHIFT >> 12), lsl #12
    add     x1, x9, x25, lsl #5
    add     x9, x22, #(PI_INV >> 12), lsl #12
    add     x2, x9, x25, lsl #5
    bl      crypto_kzg_fr_mul
4:  add     x25, x25, #1
    cmp     x25, #4096
    b.lo    2b
    mov     x0, x23
    add     x1, x19, #CRYPTO_KZG_SETTINGS_G1_LAGRANGE
    add     x2, x22, #(PI_Q >> 12), lsl #12
    mov     x3, #4096
    add     x4, x22, #(PI_WORK >> 12), lsl #12
    bl      crypto_kzg_g1_lincomb
    LEAVE   0
END_FUNCTION crypto_kzg_proof_impl

/*
 * crypto_kzg_verify_impl(s, area, valid): verifyKzgProofWith: the u64 1 when
 * e(C - [y], -[1]) e(proof, [s] - [z]) = 1, else 0. s is a G2 point. area
 * holds C, the proof (G1 points), z and y, then 5872 bytes of work.
 */
.set VI_C, 0
.set VI_P, 144
.set VI_Z, 288
.set VI_Y, 320
.set VI_K, 352
.set VI_PAIRS, 384
.set VI_WORK, 1256
LOCAL_FUNCTION crypto_kzg_verify_impl
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    add     x22, x20, #VI_PAIRS             /* pair 1: (C - [y], -[1]) */
    C2      crypto_kzg_fr_neg, x20, VI_K, x20, VI_Y
    C2      crypto_kzg_fr_canonical, x20, VI_K, x20, VI_K
    G1_GEN  x22, 8
    C3      crypto_bls_g1_mul, x22, 8, x22, 8, x20, VI_K
    G3      crypto_bls_g1_add, x20, VI_C, x22, 8, x22, 8
    G2_GEN  x22, 152
    C2      crypto_bls_g2_neg, x22, 152, x22, 152
    COPY    x22, 440, x20, VI_P, BLS_G1      /* pair 2: (proof, [s] - [z]) */
    C2      crypto_kzg_fr_neg, x20, VI_K, x20, VI_Z
    C2      crypto_kzg_fr_canonical, x20, VI_K, x20, VI_K
    G2_GEN  x22, 584
    C3      crypto_bls_g2_mul, x22, 584, x22, 584, x20, VI_K
    C3      crypto_bls_g2_add, x22, 584, x19, 0, x22, 584
    mov     x9, #2
    str     x9, [x22]
    mov     x0, x22
    add     x1, x20, #VI_WORK
    mov     x2, x21
    bl      crypto_bls_pairing_check
    LEAVE   0
END_FUNCTION crypto_kzg_verify_impl

/* ---------------------------------------------------------------- Blob functions (Core.lean) */

/* crypto_kzg_blob_to_kzg_commitment(settings, blob, scratch, commitment) -> status: blobToKzgCommitment. */
.set BC_POLY, 0
.set BC_POINT, 131072
.set BC_WORK, 131216
FUNCTION crypto_kzg_blob_to_kzg_commitment
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    KZG_SCRATCH_CHECK x21, xzr, 8f
    add     x23, x21, #8
    mov     x0, x23
    mov     x1, x20
    mov     x2, #4096
    bl      crypto_kzg_blob_to_poly
    cbnz    x0, 9f
    add     x24, x23, #(BC_POINT >> 12), lsl #12
    mov     x0, x24
    add     x1, x19, #CRYPTO_KZG_SETTINGS_G1_LAGRANGE
    mov     x2, x23
    mov     x3, #4096
    add     x4, x24, #(BC_WORK - BC_POINT)
    bl      crypto_kzg_g1_lincomb
    G2      crypto_bls_g1_compress, x24, 0, x22, 0
    mov     x0, #CRYPTO_OK
9:  LEAVE   0
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
END_FUNCTION crypto_kzg_blob_to_kzg_commitment

/* crypto_kzg_compute_kzg_proof(settings, blob, z, scratch, proof, y) -> status: computeKzgProof. */
.set KP_POLY, 0
.set KP_Z, 131072
.set KP_Y, 131104
.set KP_POINT, 131136
.set KP_WORK, 131280
FUNCTION crypto_kzg_compute_kzg_proof
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x23, x4
    mov     x24, x5
    KZG_SCRATCH_CHECK x22, xzr, 8f
    add     x25, x22, #8
    mov     x0, x25
    mov     x1, x20
    mov     x2, #4096
    bl      crypto_kzg_blob_to_poly
    cbnz    x0, 9f
    add     x26, x25, #(KP_Z >> 12), lsl #12
    mov     x0, x26
    mov     x1, x21
    bl      crypto_kzg_fr_from_bytes
    cbnz    x0, 9f
    mov     x0, x19
    mov     x1, x25
    mov     x2, x26
    add     x3, x26, #(KP_WORK - KP_Z)
    add     x4, x26, #(KP_POINT - KP_Z)
    add     x5, x26, #(KP_Y - KP_Z)
    bl      crypto_kzg_proof_impl
    G2      crypto_bls_g1_compress, x26, (KP_POINT - KP_Z), x23, 0
    C2      crypto_kzg_fr_to_bytes, x24, 0, x26, (KP_Y - KP_Z)
    mov     x0, #CRYPTO_OK
9:  LEAVE   0
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
END_FUNCTION crypto_kzg_compute_kzg_proof

/* crypto_kzg_verify_kzg_proof(settings, commitment, z, y, proof, scratch, valid) -> status: verifyKzgProof. */
FUNCTION crypto_kzg_verify_kzg_proof
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x23, x4
    mov     x24, x5
    mov     x25, x6
    KZG_SCRATCH_CHECK x24, xzr, 8f
    add     x26, x24, #8                    /* the area of crypto_kzg_verify_impl */
    C2      crypto_kzg_validate_g1, x20, 0, x26, VI_C
    cbnz    x0, 5f
    C2      crypto_kzg_validate_g1, x23, 0, x26, VI_P
    cbnz    x0, 6f
    C2      crypto_kzg_fr_from_bytes, x26, VI_Z, x21, 0
    cbnz    x0, 9f
    C2      crypto_kzg_fr_from_bytes, x26, VI_Y, x22, 0
    cbnz    x0, 9f
    add     x0, x19, #(CRYPTO_KZG_SETTINGS_G2_MONOMIAL >> 12), lsl #12
    add     x0, x0, #BLS_G2                 /* [s] */
    mov     x1, x26
    mov     x2, x25
    bl      crypto_kzg_verify_impl
    mov     x0, #CRYPTO_OK
9:  LEAVE   0
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
5:  mov     x0, #CRYPTO_KZG_INVALID_COMMITMENT
    LEAVE   0
6:  mov     x0, #CRYPTO_KZG_INVALID_PROOF
    LEAVE   0
END_FUNCTION crypto_kzg_verify_kzg_proof

/* crypto_kzg_compute_blob_kzg_proof(settings, blob, commitment, scratch, proof) -> status: computeBlobKzgProof. */
FUNCTION crypto_kzg_compute_blob_kzg_proof
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x23, x4
    KZG_SCRATCH_CHECK x22, xzr, 8f
    add     x24, x22, #8
    add     x25, x24, #(KP_Z >> 12), lsl #12
    mov     x0, x21                         /* bytesToKzgCommitment */
    add     x1, x25, #(KP_POINT - KP_Z)
    bl      crypto_kzg_validate_g1
    cbnz    x0, 7f
    mov     x0, x24
    mov     x1, x20
    mov     x2, #4096
    bl      crypto_kzg_blob_to_poly
    cbnz    x0, 9f
    mov     x0, x25                         /* z = the challenge */
    mov     x1, x20
    mov     x2, x21
    add     x3, x25, #(KP_WORK - KP_Z)
    bl      crypto_kzg_challenge
    mov     x0, x19
    mov     x1, x24
    mov     x2, x25
    add     x3, x25, #(KP_WORK - KP_Z)
    add     x4, x25, #(KP_POINT - KP_Z)
    add     x5, x25, #(KP_Y - KP_Z)
    bl      crypto_kzg_proof_impl
    G2      crypto_bls_g1_compress, x25, (KP_POINT - KP_Z), x23, 0
    mov     x0, #CRYPTO_OK
9:  LEAVE   0
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
7:  mov     x0, #CRYPTO_KZG_INVALID_COMMITMENT
    LEAVE   0
END_FUNCTION crypto_kzg_compute_blob_kzg_proof

/* crypto_kzg_verify_blob_kzg_proof(settings, blob, commitment, proof, scratch, valid) -> status: verifyBlobKzgProof. */
.set VB_POLY, 0
.set VB_AREA, 131072
.set VB_WORK, 138240
FUNCTION crypto_kzg_verify_blob_kzg_proof
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x23, x4
    mov     x24, x5
    KZG_SCRATCH_CHECK x23, xzr, 8f
    add     x25, x23, #8
    add     x26, x25, #(VB_AREA >> 12), lsl #12
    C2      crypto_kzg_validate_g1, x21, 0, x26, VI_C
    cbnz    x0, 5f
    mov     x0, x25
    mov     x1, x20
    mov     x2, #4096
    bl      crypto_kzg_blob_to_poly
    cbnz    x0, 9f
    add     x0, x26, #VI_Z                  /* z = the challenge, y = p(z) */
    mov     x1, x20
    mov     x2, x21
    add     x3, x25, #(VB_WORK >> 12), lsl #12
    add     x3, x3, #(VB_WORK & 0xFFF)
    bl      crypto_kzg_challenge
    add     x0, x26, #VI_Y
    mov     x1, x25
    add     x2, x26, #VI_Z
    add     x3, x25, #(VB_WORK >> 12), lsl #12
    add     x3, x3, #(VB_WORK & 0xFFF)
    bl      crypto_kzg_evaluate
    C2      crypto_kzg_validate_g1, x22, 0, x26, VI_P
    cbnz    x0, 6f
    add     x0, x19, #(CRYPTO_KZG_SETTINGS_G2_MONOMIAL >> 12), lsl #12
    add     x0, x0, #BLS_G2
    mov     x1, x26
    mov     x2, x24
    bl      crypto_kzg_verify_impl
    mov     x0, #CRYPTO_OK
9:  LEAVE   0
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
5:  mov     x0, #CRYPTO_KZG_INVALID_COMMITMENT
    LEAVE   0
6:  mov     x0, #CRYPTO_KZG_INVALID_PROOF
    LEAVE   0
END_FUNCTION crypto_kzg_verify_blob_kzg_proof

/*
 * crypto_kzg_verify_blob_kzg_proof_batch(settings, blobs, commitments, proofs,
 * scratch, valid) -> status: verifyBlobKzgProofBatch, then verifyKzgProofBatch.
 * work: the polynomial, the work of the evaluation and the challenges, the
 * fixed points, then the arrays of the n entries and the work of the sums.
 */
.set VBB_POLY, 0
.set VBB_EVAL, 131072
.set VBB_R, 524288
.set VBB_K, 524320
.set VBB_L1, 524352
.set VBB_L2, 524496
.set VBB_L3, 524640
.set VBB_TMP, 524784
.set VBB_PAIRS, 524928
.set VBB_PW, 525800
.set VBB_ARR, 532480
/* stack: the arrays */
.set VBS_CG, 0
.set VBS_PG, 8
.set VBS_ZS, 16
.set VBS_YS, 24
.set VBS_RP, 32
.set VBS_ZR, 40
.set VBS_CM, 48
.set VBS_DATA, 56
.set VBS_MSM, 64
.set VBS_SIZE, 80
FUNCTION crypto_kzg_verify_blob_kzg_proof_batch
    ENTER   0, VBS_SIZE
    mov     x19, x0                         /* settings */
    mov     x23, x4                         /* scratch, then work */
    mov     x24, x5                         /* valid */
    ldr     x25, [x1, #CRYPTO_KZG_LIST_COUNT]       /* n */
    KZG_SCRATCH_CHECK x23, x25, 8f
    ldr     x9, [x2, #CRYPTO_KZG_LIST_COUNT]
    cmp     x9, x25
    b.ne    4f
    ldr     x9, [x3, #CRYPTO_KZG_LIST_COUNT]
    cmp     x9, x25
    b.ne    4f
    ldr     x9, [x1, #CRYPTO_KZG_LIST_OFFSET]
    add     x20, x1, x9                     /* the blobs */
    ldr     x9, [x2, #CRYPTO_KZG_LIST_OFFSET]
    add     x21, x2, x9                     /* the commitments */
    ldr     x9, [x3, #CRYPTO_KZG_LIST_OFFSET]
    add     x22, x3, x9                     /* the proofs */
    add     x23, x23, #8
    add     x9, x23, #(VBB_ARR >> 12), lsl #12      /* the arrays */
    mov     x10, #BLS_G1
    mul     x10, x10, x25                   /* 144 n */
    lsl     x11, x25, #5                    /* 32 n */
    str     x9, [sp, #VBS_CG]
    add     x9, x9, x10
    str     x9, [sp, #VBS_PG]
    add     x9, x9, x10
    str     x9, [sp, #VBS_ZS]
    add     x9, x9, x11
    str     x9, [sp, #VBS_YS]
    add     x9, x9, x11
    str     x9, [sp, #VBS_RP]
    add     x9, x9, x11
    str     x9, [sp, #VBS_ZR]
    add     x9, x9, x11
    str     x9, [sp, #VBS_CM]
    add     x9, x9, x10
    str     x9, [sp, #VBS_DATA]
    mov     x12, #160                       /* the data: 24 + 32 + 160 n, then the digest */
    madd    x9, x12, x25, x9
    add     x9, x9, #(24 + 32 + 32)
    str     x9, [sp, #VBS_MSM]
    mov     x26, #0                         /* each triple: commitment, blob, proof */
1:  cmp     x26, x25
    b.hs    2f
    mov     x9, #48
    madd    x0, x26, x9, x21
    ldr     x9, [sp, #VBS_CG]
    mov     x10, #BLS_G1
    madd    x1, x26, x10, x9
    bl      crypto_kzg_validate_g1
    cbnz    x0, 5f
    mov     x0, x23
    add     x1, x20, x26, lsl #17
    mov     x2, #4096
    bl      crypto_kzg_blob_to_poly
    cbnz    x0, 9f
    ldr     x9, [sp, #VBS_ZS]               /* z_i = the challenge */
    add     x0, x9, x26, lsl #5
    add     x1, x20, x26, lsl #17
    mov     x9, #48
    madd    x2, x26, x9, x21
    add     x3, x23, #(VBB_EVAL >> 12), lsl #12
    bl      crypto_kzg_challenge
    ldr     x9, [sp, #VBS_YS]               /* y_i = p_i(z_i) */
    add     x0, x9, x26, lsl #5
    mov     x1, x23
    ldr     x9, [sp, #VBS_ZS]
    add     x2, x9, x26, lsl #5
    add     x3, x23, #(VBB_EVAL >> 12), lsl #12
    bl      crypto_kzg_evaluate
    mov     x9, #48
    madd    x0, x26, x9, x22
    ldr     x9, [sp, #VBS_PG]
    mov     x10, #BLS_G1
    madd    x1, x26, x10, x9
    bl      crypto_kzg_validate_g1
    cbnz    x0, 6f
    add     x26, x26, #1
    b       1b
2:  ldr     x27, [sp, #VBS_DATA]            /* r: computeVerifyKzgProofBatchChallenge */
    mov     x9, #160
    madd    x9, x9, x25, xzr
    add     x10, x9, #32                    /* count */
    add     x9, x9, #(24 + 32 + 32)         /* size */
    mov     x11, #24
    stp     x9, x11, [x27]
    str     x10, [x27, #16]
    adr     x9, 946f
    ldp     x10, x11, [x9]
    stp     x10, x11, [x27, #24]
    movz    x10, #0x10, lsl #48             /* I2OSP(4096, 8) */
    rev     x11, x25                        /* I2OSP(n, 8) */
    stp     x10, x11, [x27, #40]
    add     x28, x27, #56
    mov     x26, #0
3:  cmp     x26, x25
    b.hs    30f
    mov     x9, #48
    madd    x9, x26, x9, x21                /* commitment, z, y, proof */
    ldp     x10, x11, [x9]
    stp     x10, x11, [x28]
    ldp     x10, x11, [x9, #16]
    stp     x10, x11, [x28, #16]
    ldp     x10, x11, [x9, #32]
    stp     x10, x11, [x28, #32]
    add     x0, x28, #48
    ldr     x9, [sp, #VBS_ZS]
    add     x1, x9, x26, lsl #5
    bl      crypto_kzg_fr_to_bytes
    add     x0, x28, #80
    ldr     x9, [sp, #VBS_YS]
    add     x1, x9, x26, lsl #5
    bl      crypto_kzg_fr_to_bytes
    mov     x9, #48
    madd    x9, x26, x9, x22
    ldp     x10, x11, [x9]
    stp     x10, x11, [x28, #112]
    ldp     x10, x11, [x9, #16]
    stp     x10, x11, [x28, #128]
    ldp     x10, x11, [x9, #32]
    stp     x10, x11, [x28, #144]
    add     x28, x28, #160
    add     x26, x26, #1
    b       3b
30: mov     x0, x27
    mov     x1, x28                         /* the digest, after the data */
    CALL_GLOBAL crypto_sha256
    add     x0, x23, #(VBB_R >> 12), lsl #12
    mov     x1, x28
    bl      crypto_kzg_fr_from_digest
    ldr     x27, [sp, #VBS_RP]              /* r^i: computePowers */
    cbz     x25, 32f
    SET_FR_ONE x27, 0
    mov     x26, #1
31: cmp     x26, x25
    b.hs    32f
    add     x0, x27, x26, lsl #5
    sub     x1, x0, #32
    add     x2, x23, #(VBB_R >> 12), lsl #12
    bl      crypto_kzg_fr_mul
    add     x26, x26, #1
    b       31b
32: add     x0, x23, #(VBB_L1 >> 12), lsl #12       /* the sum of r^i proof_i */
    add     x0, x0, #(VBB_L1 & 0xFFF)
    ldr     x1, [sp, #VBS_PG]
    ldr     x2, [sp, #VBS_RP]
    mov     x3, x25
    ldr     x4, [sp, #VBS_MSM]
    bl      crypto_kzg_g1_lincomb
    mov     x26, #0                         /* z_i r^i */
33: cmp     x26, x25
    b.hs    34f
    ldr     x9, [sp, #VBS_ZR]
    add     x0, x9, x26, lsl #5
    ldr     x9, [sp, #VBS_ZS]
    add     x1, x9, x26, lsl #5
    ldr     x9, [sp, #VBS_RP]
    add     x2, x9, x26, lsl #5
    bl      crypto_kzg_fr_mul
    add     x26, x26, #1
    b       33b
34: add     x0, x23, #(VBB_L2 >> 12), lsl #12       /* the sum of z_i r^i proof_i */
    add     x0, x0, #(VBB_L2 & 0xFFF)
    ldr     x1, [sp, #VBS_PG]
    ldr     x2, [sp, #VBS_ZR]
    mov     x3, x25
    ldr     x4, [sp, #VBS_MSM]
    bl      crypto_kzg_g1_lincomb
    add     x28, x23, #(VBB_K >> 12), lsl #12       /* C_i - [y_i] */
    add     x28, x28, #(VBB_K & 0xFFF)
    mov     x26, #0
35: cmp     x26, x25
    b.hs    36f
    ldr     x9, [sp, #VBS_YS]
    add     x1, x9, x26, lsl #5
    mov     x0, x28
    bl      crypto_kzg_fr_neg
    C2      crypto_kzg_fr_canonical, x28, 0, x28, 0
    G1_GEN  x28, (VBB_TMP - VBB_K)
    C3      crypto_bls_g1_mul, x28, (VBB_TMP - VBB_K), x28, (VBB_TMP - VBB_K), x28, 0
    ldr     x9, [sp, #VBS_CG]
    mov     x10, #BLS_G1
    madd    x0, x26, x10, x9
    add     x1, x28, #(VBB_TMP - VBB_K)
    ldr     x9, [sp, #VBS_CM]
    madd    x2, x26, x10, x9
    CALL_GLOBAL crypto_bls_g1_add
    add     x26, x26, #1
    b       35b
36: add     x0, x23, #(VBB_L3 >> 12), lsl #12       /* the sum of r^i (C_i - [y_i]) */
    add     x0, x0, #(VBB_L3 & 0xFFF)
    ldr     x1, [sp, #VBS_CM]
    ldr     x2, [sp, #VBS_RP]
    mov     x3, x25
    ldr     x4, [sp, #VBS_MSM]
    bl      crypto_kzg_g1_lincomb
    add     x28, x23, #(VBB_PAIRS >> 12), lsl #12   /* the pairs */
    add     x28, x28, #(VBB_PAIRS & 0xFFF)
    mov     x9, #2
    str     x9, [x28]
    add     x9, x23, #(VBB_L1 >> 12), lsl #12
    add     x9, x9, #(VBB_L1 & 0xFFF)
    COPY    x28, 8, x9, 0, BLS_G1
    add     x0, x28, #152                   /* -[s] */
    add     x1, x19, #(CRYPTO_KZG_SETTINGS_G2_MONOMIAL >> 12), lsl #12
    add     x1, x1, #BLS_G2
    bl      crypto_bls_g2_neg
    add     x0, x23, #(VBB_L3 >> 12), lsl #12
    add     x0, x0, #(VBB_L3 & 0xFFF)
    add     x1, x23, #(VBB_L2 >> 12), lsl #12
    add     x1, x1, #(VBB_L2 & 0xFFF)
    add     x2, x28, #440
    CALL_GLOBAL crypto_bls_g1_add
    G2_GEN  x28, 584
    mov     x0, x28
    add     x1, x23, #(VBB_PW >> 12), lsl #12
    add     x1, x1, #(VBB_PW & 0xFFF)
    mov     x2, x24
    bl      crypto_bls_pairing_check
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, VBS_SIZE
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0, VBS_SIZE
4:  mov     x0, #CRYPTO_KZG_LENGTH_MISMATCH
    LEAVE   0, VBS_SIZE
5:  mov     x0, #CRYPTO_KZG_INVALID_COMMITMENT
    LEAVE   0, VBS_SIZE
6:  mov     x0, #CRYPTO_KZG_INVALID_PROOF
    LEAVE   0, VBS_SIZE
END_FUNCTION crypto_kzg_verify_blob_kzg_proof_batch

/* ---------------------------------------------------------------- Cells (Cells.lean, Fft.lean) */

/*
 * crypto_kzg_g1_fft(vals, n, roots, work): the FFT in G1 of the n points at
 * vals, in place (fftG1): the butterflies of fftG1Vector, in the order of
 * fftFieldIter: the bit-reversal permutation, then for each pair the
 * product t of the second point by its root, and the pair (l + t, l - t).
 * n (a power of two) in x1; roots holds the n-th roots of unity. work holds
 * 320 bytes.
 */
.set GF_T, 0
.set GF_N, 144
.set GF_K, 288
LOCAL_FUNCTION crypto_kzg_g1_fft
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x2, #BLS_G1
    bl      crypto_kzg_bit_reversal
    mov     x23, #0                         /* log2 h */
    lsr     x24, x20, #1                    /* m */
1:  cbz     x24, 9f
    mov     x25, #0                         /* pair j < n / 2 */
2:  lsr     x9, x25, x23
    mov     x10, #1
    lsl     x10, x10, x23
    sub     x10, x10, #1
    and     x10, x25, x10                   /* r = j mod h */
    add     x11, x23, #1
    lsl     x9, x9, x11
    add     x26, x9, x10                    /* i1 */
    mov     x11, #1
    lsl     x11, x11, x23
    add     x27, x26, x11                   /* i2 = i1 + h */
    mul     x12, x24, x10                   /* root m r */
    add     x0, x22, #GF_K
    add     x1, x21, x12, lsl #5
    bl      crypto_kzg_fr_canonical
    mov     x9, #BLS_G1
    madd    x26, x26, x9, x19               /* the points */
    madd    x27, x27, x9, x19
    C3      crypto_bls_g1_mul, x22, GF_T, x27, 0, x22, GF_K
    G2      crypto_bls_g1_neg, x22, GF_T, x22, GF_N
    G3      crypto_bls_g1_add, x26, 0, x22, GF_N, x27, 0     /* l - t */
    G3      crypto_bls_g1_add, x26, 0, x22, GF_T, x26, 0     /* l + t */
    add     x25, x25, #1
    cmp     x25, x20, lsr #1
    b.lo    2b
    add     x23, x23, #1
    lsr     x24, x24, #1
    b       1b
9:  LEAVE   0
END_FUNCTION crypto_kzg_g1_fft

/*
 * crypto_kzg_fk20(settings, coeff, work, cells, proofs): the cells and the
 * proofs of the 4096 coefficients at coeff
 * (computeCellsAndKzgProofsPolynomialcoeff): H_d = the sum of
 * coeff[i + 64 d] [s^i] for d = 1 to 63, then the FFT in G1 of the H_d,
 * padded to 128 with the point at infinity, in bit-reversed order. work
 * holds 720896 bytes; coeff is not in work.
 */
.set FK_EXT, 0
.set FK_H, 524288
.set FK_R, 542720
.set FK_FW, 546816
.set FK_MSM, 548864
LOCAL_FUNCTION crypto_kzg_fk20
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x23, x4
    mov     x0, x22                         /* the cells */
    mov     x1, x20
    add     x2, x21, #FK_EXT
    bl      crypto_kzg_extended_cells
    add     x24, x21, #(FK_H >> 12), lsl #12
    add     x24, x24, #(FK_H & 0xFFF)
    mov     x25, #1                         /* d */
1:  mov     x9, #BLS_G1                     /* H_d, in entry d - 1 */
    sub     x10, x25, #1
    madd    x0, x10, x9, x24
    add     x1, x19, #(CRYPTO_KZG_SETTINGS_G1_MONOMIAL >> 12), lsl #12
    add     x2, x20, x25, lsl #11           /* coeff[64 d] */
    mov     x3, #4096
    sub     x3, x3, x25, lsl #6             /* 4096 - 64 d points */
    add     x4, x21, #(FK_MSM >> 12), lsl #12
    bl      crypto_kzg_g1_lincomb
    add     x25, x25, #1
    cmp     x25, #64
    b.lo    1b
    mov     x25, #63                        /* padding */
2:  mov     x9, #BLS_G1
    madd    x13, x25, x9, x24
    G1_ZERO x13, 0
    add     x25, x25, #1
    cmp     x25, #128
    b.lo    2b
    add     x0, x21, #(FK_R >> 12), lsl #12
    add     x0, x0, #(FK_R & 0xFFF)
    mov     x1, #128
    bl      crypto_kzg_roots_of_unity
    mov     x0, x24
    mov     x1, #128
    add     x2, x21, #(FK_R >> 12), lsl #12
    add     x2, x2, #(FK_R & 0xFFF)
    add     x3, x21, #(FK_FW >> 12), lsl #12
    add     x3, x3, #(FK_FW & 0xFFF)
    bl      crypto_kzg_g1_fft
    mov     x0, x24
    mov     x1, #128
    mov     x2, #BLS_G1
    bl      crypto_kzg_bit_reversal
    mov     x25, #0
3:  mov     x9, #BLS_G1
    madd    x0, x25, x9, x24
    mov     x9, #48
    madd    x1, x25, x9, x23
    CALL_GLOBAL crypto_bls_g1_compress
    add     x25, x25, #1
    cmp     x25, #128
    b.lo    3b
    LEAVE   0
END_FUNCTION crypto_kzg_fk20

/* crypto_kzg_compute_cells_and_kzg_proofs(settings, blob, scratch, cells, proofs) -> status: computeCellsAndKzgProofs. */
FUNCTION crypto_kzg_compute_cells_and_kzg_proofs
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x23, x4
    KZG_SCRATCH_CHECK x21, xzr, 8f
    add     x24, x21, #8                    /* the polynomial, then the roots, then the work of crypto_kzg_fk20 */
    mov     x0, x24
    mov     x1, x20
    mov     x2, #4096
    bl      crypto_kzg_blob_to_poly
    cbnz    x0, 9f
    mov     x0, x24
    add     x1, x24, #(131072 >> 12), lsl #12
    bl      crypto_kzg_eval_to_coeff
    mov     x0, x19
    mov     x1, x24
    add     x2, x24, #(262144 >> 12), lsl #12
    mov     x3, x22
    mov     x4, x23
    bl      crypto_kzg_fk20
    mov     x0, #CRYPTO_OK
9:  LEAVE   0
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
END_FUNCTION crypto_kzg_compute_cells_and_kzg_proofs

/*
 * crypto_kzg_cell_challenge(result, request, work): computeVerifyCellKzgProofBatchChallenge:
 * SHA-256 of "RCKZGCBATCH__V1_" || I2OSP(4096, 8) || I2OSP(64, 8) ||
 * I2OSP(m, 8) || I2OSP(n, 8) || the m commitments || for each cell k:
 * I2OSP(commitment index, 8) || I2OSP(cell index, 8) || its 64 values ||
 * proof k, as a number mod r. request holds m, the address of an array of
 * m commitment addresses, n, then the addresses of the n commitment
 * indices, cell indices (u64 each), cells and proofs. The cells hold
 * canonical values, so their bytes are those of blsFieldToBytes. work holds
 * 136 + 48 m + 2112 n bytes.
 */
.set CQ_M, 0
.set CQ_COMMITMENTS, 8
.set CQ_N, 16
.set CQ_CIDX, 24
.set CQ_IDX, 32
.set CQ_CELLS, 40
.set CQ_PROOFS, 48
LOCAL_FUNCTION crypto_kzg_cell_challenge
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    ldr     x22, [x20, #CQ_M]
    ldr     x23, [x20, #CQ_N]
    mov     x9, #48                         /* count = 48 + 48 m + 2112 n */
    mul     x10, x22, x9
    mov     x9, #2112
    madd    x10, x23, x9, x10
    add     x10, x10, #48
    add     x9, x10, #(24 + 32)             /* size, with room for the digest */
    mov     x11, #24
    stp     x9, x11, [x21]
    str     x10, [x21, #16]
    adr     x9, 947f
    ldp     x10, x11, [x9]
    stp     x10, x11, [x21, #24]
    movz    x10, #0x10, lsl #48             /* I2OSP(4096, 8) */
    movz    x11, #0x4000, lsl #48           /* I2OSP(64, 8) */
    stp     x10, x11, [x21, #40]
    rev     x10, x22
    rev     x11, x23
    stp     x10, x11, [x21, #56]
    add     x24, x21, #72
    mov     x25, #0                         /* the commitments */
1:  cmp     x25, x22
    b.hs    2f
    ldr     x9, [x20, #CQ_COMMITMENTS]
    ldr     x9, [x9, x25, lsl #3]
    ldp     x10, x11, [x9]
    stp     x10, x11, [x24]
    ldp     x10, x11, [x9, #16]
    stp     x10, x11, [x24, #16]
    ldp     x10, x11, [x9, #32]
    stp     x10, x11, [x24, #32]
    add     x24, x24, #48
    add     x25, x25, #1
    b       1b
2:  mov     x25, #0                         /* the cells */
3:  cmp     x25, x23
    b.hs    5f
    ldr     x9, [x20, #CQ_CIDX]
    ldr     x10, [x9, x25, lsl #3]
    rev     x10, x10
    ldr     x9, [x20, #CQ_IDX]
    ldr     x11, [x9, x25, lsl #3]
    rev     x11, x11
    stp     x10, x11, [x24], #16
    ldr     x9, [x20, #CQ_CELLS]
    add     x9, x9, x25, lsl #11
    mov     x12, #128
4:  ldp     x10, x11, [x9], #16
    stp     x10, x11, [x24], #16
    subs    x12, x12, #1
    b.ne    4b
    ldr     x9, [x20, #CQ_PROOFS]
    mov     x10, #48
    madd    x9, x25, x10, x9
    ldp     x10, x11, [x9]
    stp     x10, x11, [x24]
    ldp     x10, x11, [x9, #16]
    stp     x10, x11, [x24, #16]
    ldp     x10, x11, [x9, #32]
    stp     x10, x11, [x24, #32]
    add     x24, x24, #48
    add     x25, x25, #1
    b       3b
5:  mov     x0, x21
    mov     x1, x24                         /* the digest, after the data */
    CALL_GLOBAL crypto_sha256
    mov     x0, x19
    mov     x1, x24
    bl      crypto_kzg_fr_from_digest
    LEAVE   0
END_FUNCTION crypto_kzg_cell_challenge

/*
 * crypto_kzg_check_cell_indices(indices, n) -> status: CRYPTO_KZG_CELL_INDEX
 * when one of the n u64 values is 128 or more. A leaf.
 */
LOCAL_FUNCTION crypto_kzg_check_cell_indices
    UNWIND_END_PROLOGUE
    cbz     x1, 2f
1:  ldr     x9, [x0], #8
    cmp     x9, #CRYPTO_KZG_CELLS_PER_EXT_BLOB
    b.hs    8f
    subs    x1, x1, #1
    b.ne    1b
2:  mov     x0, #CRYPTO_OK
    ret
8:  mov     x0, #CRYPTO_KZG_CELL_INDEX
    ret
END_FUNCTION crypto_kzg_check_cell_indices

/*
 * crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge(commitments,
 * commitment_indices, cell_indices, cells, proofs, scratch, challenge) ->
 * status: computeVerifyCellKzgProofBatchChallengeExport.
 */
.set VQ_REQ, 0
.set VQ_FR, 64
.set VQ_POINT, 96
.set VQ_EVALS, 240
.set VQ_PTRS, 2288
FUNCTION crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge
    ENTER   0
    mov     x19, x0                         /* commitments */
    mov     x20, x1                         /* commitment indices */
    mov     x21, x2                         /* cell indices */
    mov     x22, x3                         /* cells */
    mov     x23, x4                         /* proofs */
    mov     x24, x5                         /* scratch, then work */
    mov     x25, x6                         /* challenge */
    ldr     x26, [x19, #CRYPTO_KZG_LIST_COUNT]      /* m */
    ldr     x27, [x20, #CRYPTO_KZG_LIST_COUNT]      /* n */
    add     x9, x26, x27
    KZG_SCRATCH_CHECK x24, x9, 8f
    add     x24, x24, #8
    ldr     x9, [x21, #CRYPTO_KZG_LIST_COUNT]
    cmp     x9, x27
    b.ne    4f
    ldr     x9, [x22, #CRYPTO_KZG_LIST_COUNT]
    cmp     x9, x27
    b.ne    4f
    ldr     x9, [x23, #CRYPTO_KZG_LIST_COUNT]
    cmp     x9, x27
    b.ne    4f
    ldr     x9, [x19, #CRYPTO_KZG_LIST_OFFSET]      /* the request: m, the commitment addresses, n, the lists */
    add     x19, x19, x9
    ldr     x9, [x20, #CRYPTO_KZG_LIST_OFFSET]
    add     x20, x20, x9
    ldr     x9, [x21, #CRYPTO_KZG_LIST_OFFSET]
    add     x21, x21, x9
    ldr     x9, [x22, #CRYPTO_KZG_LIST_OFFSET]
    add     x22, x22, x9
    ldr     x9, [x23, #CRYPTO_KZG_LIST_OFFSET]
    add     x23, x23, x9
    add     x9, x24, #VQ_PTRS
    stp     x26, x9, [x24, #VQ_REQ + CQ_M]
    stp     x27, x20, [x24, #VQ_REQ + CQ_N]
    stp     x21, x22, [x24, #VQ_REQ + CQ_IDX]
    str     x23, [x24, #VQ_REQ + CQ_PROOFS]
    mov     x28, #0                         /* each commitment */
1:  cmp     x28, x26
    b.hs    2f
    mov     x9, #48
    madd    x0, x28, x9, x19
    add     x9, x24, #VQ_PTRS
    str     x0, [x9, x28, lsl #3]
    add     x1, x24, #VQ_POINT
    bl      crypto_kzg_validate_g1
    cbnz    x0, 5f
    add     x28, x28, #1
    b       1b
2:  mov     x28, #0                         /* each commitment index */
21: cmp     x28, x27
    b.hs    22f
    ldr     x9, [x20, x28, lsl #3]
    cmp     x9, x26
    b.hs    6f
    add     x28, x28, #1
    b       21b
22: mov     x0, x21                         /* the cell indices */
    mov     x1, x27
    bl      crypto_kzg_check_cell_indices
    cbnz    x0, 9f
    mov     x28, #0                         /* each proof */
3:  cmp     x28, x27
    b.hs    31f
    mov     x9, #48
    madd    x0, x28, x9, x23
    add     x1, x24, #VQ_POINT
    bl      crypto_kzg_validate_g1
    cbnz    x0, 7f
    add     x28, x28, #1
    b       3b
31: mov     x28, #0                         /* each cell */
32: cmp     x28, x27
    b.hs    33f
    add     x0, x24, #VQ_EVALS
    add     x1, x22, x28, lsl #11
    mov     x2, #64
    bl      crypto_kzg_blob_to_poly
    cbnz    x0, 9f
    add     x28, x28, #1
    b       32b
33: add     x0, x24, #VQ_FR
    add     x1, x24, #VQ_REQ
    add     x2, x24, #VQ_PTRS               /* the data, after the m addresses */
    add     x2, x2, x26, lsl #3
    bl      crypto_kzg_cell_challenge
    C2      crypto_kzg_fr_to_bytes, x25, 0, x24, VQ_FR
    mov     x0, #CRYPTO_OK
9:  LEAVE   0
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
4:  mov     x0, #CRYPTO_KZG_LENGTH_MISMATCH
    LEAVE   0
5:  mov     x0, #CRYPTO_KZG_INVALID_COMMITMENT
    LEAVE   0
6:  mov     x0, #CRYPTO_KZG_COMMITMENT_INDEX
    LEAVE   0
7:  mov     x0, #CRYPTO_KZG_INVALID_PROOF
    LEAVE   0
END_FUNCTION crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge

/*
 * crypto_kzg_interpolate(interp, shift, evals, work): the 64 coefficients of
 * the polynomial with the 64 values evals on the coset of shift
 * (interpolateCosetEvals): the inverse FFT of the bit-reversed values over
 * the 64-th roots of unity, then shiftVals by 1 / shift. work holds 2080
 * bytes; interp is not evals.
 */
.set IP_R, 0
.set IP_H, 2048
LOCAL_FUNCTION crypto_kzg_interpolate
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    COPY    x19, 0, x21, 0, 2048
    mov     x0, x19
    mov     x1, #64
    mov     x2, #32
    bl      crypto_kzg_bit_reversal
    mov     x0, x22
    mov     x1, #64
    bl      crypto_kzg_roots_of_unity
    mov     x0, x19
    mov     x1, #64
    mov     x2, x22
    mov     x3, #1
    bl      crypto_kzg_fft
    C2      crypto_kzg_fr_inverse, x22, IP_H, x20, 0
    mov     x0, x19
    mov     x1, #64
    add     x2, x22, #IP_H
    bl      crypto_kzg_shift_vals
    LEAVE   0
END_FUNCTION crypto_kzg_interpolate

/*
 * crypto_kzg_verify_cell_kzg_proof_batch(settings, commitments, cell_indices,
 * cells, proofs, scratch, valid) -> status: verifyCellKzgProofBatch, then
 * verifyCellKzgProofBatchImpl.
 */
.set VC_DOMAIN, 0
.set VC_R, 262144
.set VC_K, 262176
.set VC_E, 262208
.set VC_SUM, 262240
.set VC_INTERP, 264288
.set VC_IW, 266336
.set VC_LL, 268416
.set VC_RLC, 268560
.set VC_RLI, 268704
.set VC_RLP, 268848
.set VC_PAIRS, 268992
.set VC_PW, 269864
.set VC_REQ, 274472
.set VC_ARR, 278528
/* stack: the arrays of the n entries */
.set VCS_CPTR, 0
.set VCS_CIDX, 8
.set VCS_CG, 16
.set VCS_PG, 24
.set VCS_EV, 32
.set VCS_RP, 40
.set VCS_WT, 48
.set VCS_SH, 56
.set VCS_WR, 64
.set VCS_DATA, 72
.set VCS_MSM, 80
.set VCS_M, 88
.set VCS_J, 96
.set VCS_SIZE, 112
FUNCTION crypto_kzg_verify_cell_kzg_proof_batch
    ENTER   0, VCS_SIZE
    mov     x19, x0                         /* settings */
    mov     x20, x1                         /* commitments */
    mov     x21, x2                         /* cell indices */
    mov     x22, x3                         /* cells */
    mov     x23, x4                         /* proofs */
    mov     x24, x5                         /* scratch, then work */
    mov     x25, x6                         /* valid */
    ldr     x26, [x20, #CRYPTO_KZG_LIST_COUNT]      /* n */
    KZG_SCRATCH_CHECK x24, x26, 8f
    add     x24, x24, #8
    ldr     x9, [x22, #CRYPTO_KZG_LIST_COUNT]
    cmp     x9, x26
    b.ne    4f
    ldr     x9, [x23, #CRYPTO_KZG_LIST_COUNT]
    cmp     x9, x26
    b.ne    4f
    ldr     x9, [x21, #CRYPTO_KZG_LIST_COUNT]
    cmp     x9, x26
    b.ne    4f
    ldr     x9, [x20, #CRYPTO_KZG_LIST_OFFSET]
    add     x20, x20, x9
    ldr     x9, [x21, #CRYPTO_KZG_LIST_OFFSET]
    add     x21, x21, x9
    ldr     x9, [x22, #CRYPTO_KZG_LIST_OFFSET]
    add     x22, x22, x9
    ldr     x9, [x23, #CRYPTO_KZG_LIST_OFFSET]
    add     x23, x23, x9
    mov     x0, x21
    mov     x1, x26
    bl      crypto_kzg_check_cell_indices
    cbnz    x0, 9f
    add     x9, x24, #(VC_ARR >> 12), lsl #12       /* the arrays */
    lsl     x10, x26, #3                    /* 8 n */
    lsl     x11, x26, #5                    /* 32 n */
    mov     x12, #BLS_G1
    mul     x12, x12, x26                   /* 144 n */
    str     x9, [sp, #VCS_CPTR]
    add     x9, x9, x10
    str     x9, [sp, #VCS_CIDX]
    add     x9, x9, x10
    str     x9, [sp, #VCS_CG]
    add     x9, x9, x12
    str     x9, [sp, #VCS_PG]
    add     x9, x9, x12
    str     x9, [sp, #VCS_EV]
    add     x9, x9, x26, lsl #11
    str     x9, [sp, #VCS_RP]
    add     x9, x9, x11
    str     x9, [sp, #VCS_WT]
    add     x9, x9, x11
    str     x9, [sp, #VCS_SH]
    add     x9, x9, x11
    str     x9, [sp, #VCS_WR]
    add     x9, x9, x11
    str     x9, [sp, #VCS_DATA]
    mov     x13, #2160                      /* the data: 104 + 48 m + 2112 n bytes, m <= n */
    madd    x9, x26, x13, x9
    add     x9, x9, #104
    str     x9, [sp, #VCS_MSM]
    mov     x27, #0                         /* each commitment: check, and keep the first of equal ones */
    str     xzr, [sp, #VCS_M]
1:  cmp     x27, x26
    b.hs    20f
    mov     x9, #48
    madd    x28, x27, x9, x20               /* commitment k */
    ldr     x9, [sp, #VCS_M]
    ldr     x10, [sp, #VCS_CG]
    mov     x11, #BLS_G1
    madd    x1, x9, x11, x10
    mov     x0, x28
    bl      crypto_kzg_validate_g1
    cbnz    x0, 5f
    str     xzr, [sp, #VCS_J]               /* j: the kept commitment with these bytes */
10: ldr     x13, [sp, #VCS_J]
    ldr     x9, [sp, #VCS_M]
    cmp     x13, x9
    b.hs    12f
    ldr     x10, [sp, #VCS_CPTR]
    ldr     x10, [x10, x13, lsl #3]
    EQUAL   x10, 0, x28, 0, 48
    b.eq    13f
    ldr     x13, [sp, #VCS_J]
    add     x13, x13, #1
    str     x13, [sp, #VCS_J]
    b       10b
12: ldr     x10, [sp, #VCS_CPTR]            /* a new one: j = m, m + 1 */
    str     x28, [x10, x13, lsl #3]
    add     x9, x13, #1
    str     x9, [sp, #VCS_M]
13: ldr     x13, [sp, #VCS_J]
    ldr     x10, [sp, #VCS_CIDX]
    str     x13, [x10, x27, lsl #3]
    add     x27, x27, #1
    b       1b
20: mov     x27, #0                         /* each cell: cellToCosetEvals */
2:  cmp     x27, x26
    b.hs    3f
    ldr     x9, [sp, #VCS_EV]
    add     x0, x9, x27, lsl #11
    add     x1, x22, x27, lsl #11
    mov     x2, #64
    bl      crypto_kzg_blob_to_poly
    cbnz    x0, 9f
    add     x27, x27, #1
    b       2b
3:  mov     x27, #0                         /* each proof */
30: cmp     x27, x26
    b.hs    31f
    mov     x9, #48
    madd    x0, x27, x9, x23
    ldr     x9, [sp, #VCS_PG]
    mov     x10, #BLS_G1
    madd    x1, x27, x10, x9
    bl      crypto_kzg_validate_g1
    cbnz    x0, 6f
    add     x27, x27, #1
    b       30b
31: add     x28, x24, #(VC_REQ >> 12), lsl #12      /* r */
    add     x28, x28, #(VC_REQ & 0xFFF)
    ldr     x9, [sp, #VCS_M]
    ldr     x10, [sp, #VCS_CPTR]
    stp     x9, x10, [x28, #CQ_M]
    ldr     x10, [sp, #VCS_CIDX]
    stp     x26, x10, [x28, #CQ_N]
    stp     x21, x22, [x28, #CQ_IDX]
    str     x23, [x28, #CQ_PROOFS]
    add     x0, x24, #(VC_R >> 12), lsl #12
    add     x0, x0, #(VC_R & 0xFFF)
    mov     x1, x28
    ldr     x2, [sp, #VCS_DATA]
    bl      crypto_kzg_cell_challenge
    cbz     x26, 41f                        /* r^k */
    ldr     x27, [sp, #VCS_RP]
    SET_FR_ONE x27, 0
    mov     x28, #1
40: cmp     x28, x26
    b.hs    41f
    add     x0, x27, x28, lsl #5
    sub     x1, x0, #32
    add     x2, x24, #(VC_R >> 12), lsl #12
    add     x2, x2, #(VC_R & 0xFFF)
    bl      crypto_kzg_fr_mul
    add     x28, x28, #1
    b       40b
41: add     x0, x24, #(VC_LL >> 12), lsl #12        /* LL = the sum of r^k proof_k */
    add     x0, x0, #(VC_LL & 0xFFF)
    ldr     x1, [sp, #VCS_PG]
    ldr     x2, [sp, #VCS_RP]
    mov     x3, x26
    ldr     x4, [sp, #VCS_MSM]
    bl      crypto_kzg_g1_lincomb
    ldr     x9, [sp, #VCS_M]                /* weights[i] = the sum of r^k over the cells of commitment i */
    ldr     x0, [sp, #VCS_WT]
    lsl     x9, x9, #5
    cbz     x9, 43f
42: str     xzr, [x0], #8
    subs    x9, x9, #8
    b.ne    42b
43: mov     x27, #0
44: cmp     x27, x26
    b.hs    45f
    ldr     x9, [sp, #VCS_CIDX]
    ldr     x9, [x9, x27, lsl #3]
    ldr     x10, [sp, #VCS_WT]
    add     x0, x10, x9, lsl #5
    mov     x1, x0
    ldr     x10, [sp, #VCS_RP]
    add     x2, x10, x27, lsl #5
    bl      crypto_kzg_fr_add
    add     x27, x27, #1
    b       44b
45: add     x0, x24, #(VC_RLC >> 12), lsl #12       /* RLC = the sum of weights[i] C_i */
    add     x0, x0, #(VC_RLC & 0xFFF)
    ldr     x1, [sp, #VCS_CG]
    ldr     x2, [sp, #VCS_WT]
    ldr     x3, [sp, #VCS_M]
    ldr     x4, [sp, #VCS_MSM]
    bl      crypto_kzg_g1_lincomb
    mov     x0, x24                         /* the domain: rootsOfUnityBrp 8192 */
    mov     x1, #8192
    bl      crypto_kzg_roots_of_unity
    mov     x0, x24
    mov     x1, #8192
    mov     x2, #32
    bl      crypto_kzg_bit_reversal
    mov     x27, #0                         /* shift_k = domain[64 cell index] */
46: cmp     x27, x26
    b.hs    47f
    ldr     x9, [x21, x27, lsl #3]
    add     x9, x24, x9, lsl #11
    ldr     x10, [sp, #VCS_SH]
    add     x10, x10, x27, lsl #5
    COPY    x10, 0, x9, 0, 32
    add     x27, x27, #1
    b       46b
47: add     x28, x24, #(VC_SUM >> 12), lsl #12      /* the sum of r^k I_k */
    add     x28, x28, #(VC_SUM & 0xFFF)
    ZERO    x28, 0, 2048
    mov     x27, #0
48: cmp     x27, x26
    b.hs    49f
    add     x0, x28, #(VC_INTERP - VC_SUM)
    ldr     x9, [sp, #VCS_SH]
    add     x1, x9, x27, lsl #5
    ldr     x9, [sp, #VCS_EV]
    add     x2, x9, x27, lsl #11
    add     x3, x28, #(VC_IW - VC_SUM)
    bl      crypto_kzg_interpolate
    mov     x13, #0                         /* sum += r^k interp */
480: add    x0, x28, #(VC_INTERP - VC_SUM)
    add     x0, x0, x13, lsl #5
    mov     x1, x0
    ldr     x9, [sp, #VCS_RP]
    add     x2, x9, x27, lsl #5
    str     x13, [sp, #VCS_J]
    bl      crypto_kzg_fr_mul
    ldr     x13, [sp, #VCS_J]
    add     x0, x28, x13, lsl #5
    mov     x1, x0
    add     x2, x28, #(VC_INTERP - VC_SUM)
    add     x2, x2, x13, lsl #5
    bl      crypto_kzg_fr_add
    ldr     x13, [sp, #VCS_J]
    add     x13, x13, #1
    cmp     x13, #64
    b.lo    480b
    add     x27, x27, #1
    b       48b
49: add     x0, x24, #(VC_RLI >> 12), lsl #12       /* RLI = [the sum at s] */
    add     x0, x0, #(VC_RLI & 0xFFF)
    add     x1, x19, #(CRYPTO_KZG_SETTINGS_G1_MONOMIAL >> 12), lsl #12
    mov     x2, x28
    mov     x3, #64
    ldr     x4, [sp, #VCS_MSM]
    bl      crypto_kzg_g1_lincomb
    add     x28, x24, #(VC_K >> 12), lsl #12        /* r^k shift_k^64 */
    add     x28, x28, #(VC_K & 0xFFF)
    mov     x9, #64
    stp     x9, xzr, [x28, #(VC_E - VC_K)]
    stp     xzr, xzr, [x28, #(VC_E - VC_K + 16)]
    mov     x27, #0
50: cmp     x27, x26
    b.hs    51f
    mov     x0, x28
    ldr     x9, [sp, #VCS_SH]
    add     x1, x9, x27, lsl #5
    add     x2, x28, #(VC_E - VC_K)
    bl      crypto_kzg_fr_pow
    ldr     x9, [sp, #VCS_WR]
    add     x0, x9, x27, lsl #5
    ldr     x9, [sp, #VCS_RP]
    add     x1, x9, x27, lsl #5
    mov     x2, x28
    bl      crypto_kzg_fr_mul
    add     x27, x27, #1
    b       50b
51: add     x0, x24, #(VC_RLP >> 12), lsl #12       /* RLP = the sum of r^k shift_k^64 proof_k */
    add     x0, x0, #(VC_RLP & 0xFFF)
    ldr     x1, [sp, #VCS_PG]
    ldr     x2, [sp, #VCS_WR]
    mov     x3, x26
    ldr     x4, [sp, #VCS_MSM]
    bl      crypto_kzg_g1_lincomb
    add     x28, x24, #(VC_PAIRS >> 12), lsl #12    /* the pairs: (LL, [s^64]), (RLC - RLI + RLP, -[1]) */
    add     x28, x28, #(VC_PAIRS & 0xFFF)
    mov     x9, #2
    str     x9, [x28]
    add     x9, x24, #(VC_LL >> 12), lsl #12
    add     x9, x9, #(VC_LL & 0xFFF)
    COPY    x28, 8, x9, 0, BLS_G1
    add     x9, x19, #(CRYPTO_KZG_SETTINGS_G2_MONOMIAL >> 12), lsl #12
    add     x9, x9, #((64 * BLS_G2) >> 12), lsl #12     /* [s^64] */
    add     x9, x9, #((64 * BLS_G2) & 0xFFF)
    COPY    x28, 152, x9, 0, BLS_G2
    add     x0, x24, #(VC_RLI >> 12), lsl #12
    add     x0, x0, #(VC_RLI & 0xFFF)
    mov     x1, x0
    CALL_GLOBAL crypto_bls_g1_neg
    add     x0, x24, #(VC_RLC >> 12), lsl #12
    add     x0, x0, #(VC_RLC & 0xFFF)
    add     x1, x24, #(VC_RLI >> 12), lsl #12
    add     x1, x1, #(VC_RLI & 0xFFF)
    add     x2, x28, #440
    CALL_GLOBAL crypto_bls_g1_add
    add     x0, x28, #440
    add     x1, x24, #(VC_RLP >> 12), lsl #12
    add     x1, x1, #(VC_RLP & 0xFFF)
    add     x2, x28, #440
    CALL_GLOBAL crypto_bls_g1_add
    add     x0, x28, #584
    add     x1, x19, #(CRYPTO_KZG_SETTINGS_G2_MONOMIAL >> 12), lsl #12
    bl      crypto_bls_g2_neg
    mov     x0, x28
    add     x1, x24, #(VC_PW >> 12), lsl #12
    add     x1, x1, #(VC_PW & 0xFFF)
    mov     x2, x25
    bl      crypto_bls_pairing_check
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, VCS_SIZE
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0, VCS_SIZE
4:  mov     x0, #CRYPTO_KZG_LENGTH_MISMATCH
    LEAVE   0, VCS_SIZE
5:  mov     x0, #CRYPTO_KZG_INVALID_COMMITMENT
    LEAVE   0, VCS_SIZE
6:  mov     x0, #CRYPTO_KZG_INVALID_PROOF
    LEAVE   0, VCS_SIZE
END_FUNCTION crypto_kzg_verify_cell_kzg_proof_batch

/*
 * crypto_kzg_recover_cells_and_kzg_proofs(settings, cell_indices, cells,
 * scratch, recovered_cells, recovered_proofs) -> status:
 * recoverCellsAndKzgProofs: the checks, recoverPolynomialcoeff, then the
 * cells and proofs of crypto_kzg_fk20.
 */
.set RC_EVALS, 0
.set RC_EXT, 262144
.set RC_ROU, 524288
.set RC_ZC, 786432
.set RC_ZE, 1048576
.set RC_ZI, 1310720
.set RC_R128, 1572864
.set RC_SHORT, 1576960
.set RC_MISS, 1581056
.set RC_X, 1582080
.set RC_T, 1582112
FUNCTION crypto_kzg_recover_cells_and_kzg_proofs
    ENTER   0
    mov     x19, x0                         /* settings */
    mov     x20, x1                         /* cell indices */
    mov     x21, x2                         /* cells */
    mov     x22, x3                         /* scratch, then work */
    mov     x23, x4
    mov     x24, x5
    KZG_SCRATCH_CHECK x22, xzr, 8f
    add     x22, x22, #8
    ldr     x25, [x20, #CRYPTO_KZG_LIST_COUNT]      /* n */
    ldr     x9, [x21, #CRYPTO_KZG_LIST_COUNT]
    cmp     x9, x25
    b.ne    4f
    cmp     x25, #(CRYPTO_KZG_CELLS_PER_EXT_BLOB / 2)
    b.lo    5f
    cmp     x25, #CRYPTO_KZG_CELLS_PER_EXT_BLOB
    b.hi    6f
    ldr     x9, [x20, #CRYPTO_KZG_LIST_OFFSET]
    add     x20, x20, x9
    ldr     x9, [x21, #CRYPTO_KZG_LIST_OFFSET]
    add     x21, x21, x9
    mov     x0, x20
    mov     x1, x25
    bl      crypto_kzg_check_cell_indices
    cbnz    x0, 9f
    mov     x26, #1                         /* strictly ascending */
1:  cmp     x26, x25
    b.hs    2f
    add     x9, x20, x26, lsl #3
    ldur    x10, [x9, #-8]
    ldr     x11, [x9]
    cmp     x11, x10
    b.ls    7f
    add     x26, x26, #1
    b       1b
2:  mov     x26, #0                         /* cellToCosetEvals */
3:  cmp     x26, x25
    b.hs    10f
    add     x0, x22, x26, lsl #11
    add     x1, x21, x26, lsl #11
    mov     x2, #64
    bl      crypto_kzg_blob_to_poly
    cbnz    x0, 9f
    add     x26, x26, #1
    b       3b
10: add     x27, x22, #(RC_ROU >> 12), lsl #12      /* the 8192-th roots of unity */
    mov     x0, x27
    mov     x1, #8192
    bl      crypto_kzg_roots_of_unity
    add     x28, x22, #(RC_EXT >> 12), lsl #12      /* E: the values in their places, zeros elsewhere */
    mov     x9, x28
    mov     x10, #16384
11: stp     xzr, xzr, [x9], #16
    subs    x10, x10, #1
    b.ne    11b
    mov     x26, #0
12: cmp     x26, x25
    b.hs    14f
    ldr     x9, [x20, x26, lsl #3]
    add     x10, x28, x9, lsl #11
    add     x11, x22, x26, lsl #11
    mov     x12, #128
13: ldp     x13, x14, [x11], #16
    stp     x13, x14, [x10], #16
    subs    x12, x12, #1
    b.ne    13b
    add     x26, x26, #1
    b       12b
14: mov     x0, x28
    mov     x1, #8192
    mov     x2, #32
    bl      crypto_kzg_bit_reversal
    add     x0, x22, #(RC_R128 >> 12), lsl #12      /* the missing cells, and their roots */
    mov     x1, #128
    bl      crypto_kzg_roots_of_unity
    mov     x26, #0                         /* cell index ci */
    mov     x15, #0                         /* missing count */
15: mov     x9, #0
16: cmp     x9, x25
    b.hs    17f
    ldr     x10, [x20, x9, lsl #3]
    cmp     x10, x26
    b.eq    18f
    add     x9, x9, #1
    b       16b
17: add     x10, x22, #(RC_MISS >> 12), lsl #12
    str     x26, [x10, x15, lsl #3]
    add     x15, x15, #1
18: add     x26, x26, #1
    cmp     x26, #128
    b.lo    15b
    add     x10, x22, #(RC_MISS >> 12), lsl #12     /* keep the count after the list */
    str     x15, [x10, #1016]
    add     x28, x22, #(RC_SHORT >> 12), lsl #12    /* the short polynomial: 1, then times (X - x) for each */
    SET_FR_ONE x28, 0
    mov     x26, #0                         /* missing cells done; also the length - 1 */
20: add     x10, x22, #(RC_MISS >> 12), lsl #12
    ldr     x15, [x10, #1016]
    cmp     x26, x15
    b.hs    25f
    ldr     x9, [x10, x26, lsl #3]          /* x = root rev(mci) of 128 */
    rbit    x9, x9
    lsr     x9, x9, #57
    add     x10, x22, #(RC_R128 >> 12), lsl #12
    add     x9, x10, x9, lsl #5
    add     x10, x22, #(RC_X >> 12), lsl #12
    add     x10, x10, #(RC_X & 0xFFF)
    COPY    x10, 0, x9, 0, 32
    add     x9, x28, x26, lsl #5            /* p[L] = p[L - 1], L = count + 1 */
    COPY    x9, 32, x9, 0, 32
    mov     x27, x26                        /* k from L - 1 down to 1: p[k] = p[k - 1] - x p[k] */
21: cbz     x27, 22f
    add     x0, x22, #(RC_T >> 12), lsl #12
    add     x0, x0, #(RC_T & 0xFFF)
    add     x1, x28, x27, lsl #5
    add     x2, x22, #(RC_X >> 12), lsl #12
    add     x2, x2, #(RC_X & 0xFFF)
    bl      crypto_kzg_fr_mul
    add     x0, x28, x27, lsl #5
    sub     x1, x0, #32
    add     x2, x22, #(RC_T >> 12), lsl #12
    add     x2, x2, #(RC_T & 0xFFF)
    bl      crypto_kzg_fr_sub
    sub     x27, x27, #1
    b       21b
22: mov     x0, x28                         /* p[0] = -(x p[0]) */
    mov     x1, x28
    add     x2, x22, #(RC_X >> 12), lsl #12
    add     x2, x2, #(RC_X & 0xFFF)
    bl      crypto_kzg_fr_mul
    mov     x0, x28
    mov     x1, x28
    bl      crypto_kzg_fr_neg
    add     x26, x26, #1
    b       20b
25: add     x27, x22, #(RC_ZC >> 12), lsl #12       /* Z: coefficient i of the short one at 64 i */
    mov     x9, x27
    mov     x10, #16384
26: stp     xzr, xzr, [x9], #16
    subs    x10, x10, #1
    b.ne    26b
    mov     x9, #0
27: cmp     x9, x26
    b.hi    28f
    add     x10, x28, x9, lsl #5
    add     x11, x27, x9, lsl #11
    ldp     x12, x13, [x10]
    stp     x12, x13, [x11]
    ldp     x12, x13, [x10, #16]
    stp     x12, x13, [x11, #16]
    add     x9, x9, #1
    b       27b
28: add     x28, x22, #(RC_ZE >> 12), lsl #12       /* the FFT of Z */
    mov     x9, x28
    mov     x10, x27
    mov     x11, #16384
281: ldp    x12, x13, [x10], #16
    stp     x12, x13, [x9], #16
    subs    x11, x11, #1
    b.ne    281b
    mov     x0, x28
    mov     x1, #8192
    add     x2, x22, #(RC_ROU >> 12), lsl #12
    mov     x3, #0
    bl      crypto_kzg_fft
    add     x26, x22, #(RC_EXT >> 12), lsl #12      /* E Z, then P Z = its inverse FFT */
    mov     x25, #0
29: add     x0, x26, x25, lsl #5
    add     x1, x28, x25, lsl #5
    mov     x2, x0
    bl      crypto_kzg_fr_mul
    add     x25, x25, #1
    cmp     x25, #8192
    b.lo    29b
    mov     x0, x26
    mov     x1, #8192
    add     x2, x22, #(RC_ROU >> 12), lsl #12
    mov     x3, #1
    bl      crypto_kzg_fft
    mov     x0, x26                         /* P Z and Z over the coset */
    mov     x1, #8192
    add     x2, x22, #(RC_ROU >> 12), lsl #12
    mov     x3, #0
    bl      crypto_kzg_coset_fft
    mov     x9, x28
    mov     x10, x27
    mov     x11, #16384
282: ldp    x12, x13, [x10], #16
    stp     x12, x13, [x9], #16
    subs    x11, x11, #1
    b.ne    282b
    mov     x0, x28
    mov     x1, #8192
    add     x2, x22, #(RC_ROU >> 12), lsl #12
    mov     x3, #0
    bl      crypto_kzg_coset_fft
    add     x0, x22, #(RC_ZI >> 12), lsl #12        /* P = P Z / Z over the coset */
    mov     x1, x28
    mov     x2, #8192
    bl      crypto_kzg_batch_inverse
    add     x27, x22, #(RC_ZI >> 12), lsl #12
    mov     x25, #0
30: add     x0, x26, x25, lsl #5
    mov     x1, x0
    add     x2, x27, x25, lsl #5
    bl      crypto_kzg_fr_mul
    add     x25, x25, #1
    cmp     x25, #8192
    b.lo    30b
    mov     x0, x26
    mov     x1, #8192
    add     x2, x22, #(RC_ROU >> 12), lsl #12
    mov     x3, #1
    bl      crypto_kzg_coset_fft
    mov     x0, x19                         /* the cells and proofs of the first 4096 coefficients */
    mov     x1, x26
    add     x2, x22, #(RC_ROU >> 12), lsl #12
    mov     x3, x23
    mov     x4, x24
    bl      crypto_kzg_fk20
    mov     x0, #CRYPTO_OK
9:  LEAVE   0
8:  mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
4:  mov     x0, #CRYPTO_KZG_LENGTH_MISMATCH
    LEAVE   0
5:  mov     x0, #CRYPTO_KZG_NOT_ENOUGH_CELLS
    LEAVE   0
6:  mov     x0, #CRYPTO_KZG_TOO_MANY_CELLS
    LEAVE   0
7:  mov     x0, #CRYPTO_KZG_INDICES_NOT_ASCENDING
    LEAVE   0
END_FUNCTION crypto_kzg_recover_cells_and_kzg_proofs


/* ---------------------------------------------------------------- Constants */

    .p2align 3
/* p, -p^-1 mod 2^64, 2^384 mod p, 2^768 mod p (Fp.lean) */
900:
    .quad   0xB9FEFFFFFFFFAAAB, 0x1EABFFFEB153FFFF, 0x6730D2A0F6B0F624, 0x64774B84F38512BF, 0x4B1BA7B6434BACD7, 0x1A0111EA397FE69A
    .quad   0x89F3FFFCFFFCFFFD
    .quad   0x760900000002FFFD, 0xEBF4000BC40C0002, 0x5F48985753C758BA, 0x77CE585370525745, 0x5C071A97A256EC6D, 0x15F65EC3FA80E493
    .quad   0xF4DF1F341C341746, 0x0A76E6A609D104F1, 0x8DE5476C4C95B6D5, 0x67EB88A9939D83C0, 0x9A793E85B519952D, 0x11988FE592CAE3AA
/* b' = 4 (1 + u) of E2, Montgomery form */
901:
    .quad   0xAA270000000CFFF3, 0x53CC0032FC34000A, 0x478FE97A6B0A807F, 0xB1D37EBEE6BA24D7, 0x8EC9733BBF78AB2F, 0x09D645513D83DE7E
    .quad   0xAA270000000CFFF3, 0x53CC0032FC34000A, 0x478FE97A6B0A807F, 0xB1D37EBEE6BA24D7, 0x8EC9733BBF78AB2F, 0x09D645513D83DE7E
/* 1 / 2, Montgomery form (Fp2.sqrt: BaseField.inverse 2) */
903:
    .quad   0x1804000000015554, 0x855000053AB00001, 0x633CB57C253C276F, 0x6E22D1EC31EBB502, 0xD3916126F2D14CA2, 0x17FBB8571A006596
/* the generator of G2, x.c0, x.c1, y.c0, y.c1, Montgomery form (G2.lean) */
905:
    .quad   0xF5F28FA202940A10, 0xB3F5FB2687B4961A, 0xA1A893B53E2AE580, 0x9894999D1A3CAEE9, 0x6F67B7631863366B, 0x058191924350BCD7
    .quad   0xA5A9C0759E23F606, 0xAAA0C59DBCCD60C3, 0x3BB17E18E2867806, 0x1B1AB6CC8541B367, 0xC2B6ED0EF2158547, 0x11922A097360EDF3
    .quad   0x4C730AF860494C4A, 0x597CFA1F5E369C5A, 0xE7E6856CAA0A635A, 0xBBEFB5E96E0D495F, 0x07D3A975F0EF25A2, 0x0083FD8E7E80DAE5
    .quad   0xADC0FC92DF64B05D, 0x18AA270A2B1461DC, 0x86ADAC6A3BE4EBA0, 0x79495C4EC93DA33A, 0xE7175850A43CCAED, 0x0B2BC2A163DE1BF2
/* the generator of G1, x then y, Montgomery form (G1.lean) */
904:
    .quad   0x5CB38790FD530C16, 0x7817FC679976FFF5, 0x154F95C7143BA1C1, 0xF0AE6ACDF3D0E747, 0xEDCE6ECC21DBF440, 0x120177419E0BFB75
    .quad   0xBAAC93D50CE72271, 0x8C22631A7918FD8E, 0xDD595F13570725CE, 0x51AC582950405194, 0x0E1C8C3FAD0059C0, 0x0BBC3EFC5008A26A
/* p - 2, the exponent of Fp.inverse */
917:
    .quad   0xB9FEFFFFFFFFAAA9, 0x1EABFFFEB153FFFF, 0x6730D2A0F6B0F624, 0x64774B84F38512BF, 0x4B1BA7B6434BACD7, 0x1A0111EA397FE69A
/* (p + 1) / 4, the exponent of Fp.sqrt */
918:
    .quad   0xEE7FBFFFFFFFEAAB, 0x07AAFFFFAC54FFFF, 0xD9CC34A83DAC3D89, 0xD91DD2E13CE144AF, 0x92C6E9ED90D2EB35, 0x0680447A8E5FF9A6
/* b = 4 of E1, Montgomery form */
923:
    .quad   0xAA270000000CFFF3, 0x53CC0032FC34000A, 0x478FE97A6B0A807F, 0xB1D37EBEE6BA24D7, 0x8EC9733BBF78AB2F, 0x09D645513D83DE7E
/* r, the order of G1 and G2 (Fr.lean), 4 limbs */
924:
    .quad   0xFFFFFFFF00000001, 0x53BDA402FFFE5BFE, 0x3339D80809A1D805, 0x73EDA753299D7D48
/* beta, the cube root of 1 in Fp with sigma = -x^2 on G1 (crypto_bls_g1_in_subgroup), Montgomery form */
928:
    .quad   0x30F1361B798A64E8, 0xF3B8DDAB7ECE5A2A, 0x16A8CA3AC61577F7, 0xC26A2FF874FD029B, 0x3636B76660701C6E, 0x051BA4AB241B6160
/* the psi constants of HashToCurve.lean: c1Psi = 1 / (1 + u)^((p - 1) / 3), then c2Psi = 1 / (1 + u)^((p - 1) / 2), Montgomery form */
907:
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x890DC9E4867545C3, 0x2AF322533285A5D5, 0x50880866309B7E2C, 0xA20D1B8C7E881024, 0x14E4F04FE2DB9068, 0x14E56D3F1564853A
    .quad   0x3E2F585DA55C9AD1, 0x4294213D86C18183, 0x382844C88B623732, 0x92AD2AFD19103E18, 0x1D794E4FAC7CF0B9, 0x0BD592FC7D825EC8
    .quad   0x7BCFA7A25AA30FDA, 0xDC17DEC12A927E7C, 0x2F088DD86B4EBEF1, 0xD1CA2087DA74D4A7, 0x2DA2596696CEBC1D, 0x0E2B7EEDBBFD87D2
/* c1Psi2 = 1 / 2^((p - 1) / 3), in Fp, Montgomery form */
908:
    .quad   0xCD03C9E48671F071, 0x5DAB22461FCDA5D2, 0x587042AFD3851B95, 0x8EB60EBE01BACB9E, 0x03F97D6E83D050D2, 0x18F0206554638741
/* the SSWU constants of HashToCurve.lean: A' = 240 u, B' = 1012 (1 + u), Z = -(2 + u), Montgomery form */
910:
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0xE53A000003135242, 0x01080C0FDEF80285, 0xE7889EDBE340F6BD, 0x0B51375126310601, 0x02D6985717C744AB, 0x1220B4E979EA5467
    .quad   0x22EA00000CF89DB2, 0x6EC832DF71380AA4, 0x6E1B94403DB5A66E, 0x75BF3C53A79473BA, 0x3DD3A569412C0A34, 0x125CDB5E74DC4FD1
    .quad   0x22EA00000CF89DB2, 0x6EC832DF71380AA4, 0x6E1B94403DB5A66E, 0x75BF3C53A79473BA, 0x3DD3A569412C0A34, 0x125CDB5E74DC4FD1
    .quad   0x87EBFFFFFFF9555C, 0x656FFFE5DA8FFFFA, 0x0FD0749345D33AD2, 0xD951E663066576F4, 0xDE291A3D41E980D3, 0x0815664C7DFE040D
    .quad   0x43F5FFFFFFFCAAAE, 0x32B7FFF2ED47FFFD, 0x07E83A49A2E99D69, 0xECA8F3318332BB7A, 0xEF148D1EA0F4C069, 0x040AB3263EFF0206
/* the 3-isogeny of HashToCurve.lean: k10..k13, k20, k21, k30..k33, k40..k42, each c0 then c1, Montgomery form */
913:
/* k10 */
    .quad   0x47F671C71CE05E62, 0x06DD57071206393E, 0x7C80CD2AF3FD71A2, 0x048103EA9E6CD062, 0xC54516ACC8D037F6, 0x13808F550920EA41
    .quad   0x47F671C71CE05E62, 0x06DD57071206393E, 0x7C80CD2AF3FD71A2, 0x048103EA9E6CD062, 0xC54516ACC8D037F6, 0x13808F550920EA41
/* k11 */
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x5FE55555554C71D0, 0x873FFFDD236AAAA3, 0x6A6B4619B26EF918, 0x21C2888408874945, 0x2836CDA7028CABC5, 0x0AC73310A7FD5ABD
/* k12 */
    .quad   0x0A0C5555555971C3, 0xDB0C00101F9EAAAE, 0xB1FB2F941D797997, 0xD3960742EF416E1C, 0xB70040E2C20556F4, 0x149D7861E581393B
    .quad   0xAFF2AAAAAAA638E8, 0x439FFFEE91B55551, 0xB535A30CD9377C8C, 0x90E144420443A4A2, 0x941B66D3814655E2, 0x0563998853FEAD5E
/* k13 */
    .quad   0x40AAC71C71C725ED, 0x190955557A84E38E, 0xD817050A8F41ABC3, 0xD86485D4C87F6FB1, 0x696EB479F885D059, 0x198E1A74328002D2
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
/* k20 */
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x1F3AFFFFFF13AB97, 0xF25BFC611DA3FF3E, 0xCA3757CB3819B208, 0x3E6427366F8CEC18, 0x03977BC86095B089, 0x04F69DB13F39A952
/* k21 */
    .quad   0x447600000027552E, 0xDCB8009A43480020, 0x6F7EE9CE4A6E8B59, 0xB10330B7C0A95BC6, 0x6140B1FCFB1E54B7, 0x0381BE097F0BB4E1
    .quad   0x7588FFFFFFD8557D, 0x41F3FF646E0BFFDF, 0xF7B1E8D2AC426ACA, 0xB3741ACD32DBB6F8, 0xE9DAF5B9482D581F, 0x167F53E0BA7431B8
/* k30 */
    .quad   0x96D8F684BDFC77BE, 0xB530E4F43B66D0E2, 0x184A88FF379652FD, 0x57CB23ECFAE804E1, 0x0FD2E39EADA3EBA9, 0x08C8055E31C5D5C3
    .quad   0x96D8F684BDFC77BE, 0xB530E4F43B66D0E2, 0x184A88FF379652FD, 0x57CB23ECFAE804E1, 0x0FD2E39EADA3EBA9, 0x08C8055E31C5D5C3
/* k31 */
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0xBF0A71C71C91B406, 0x4D6D55D28B7638FD, 0x9D82F98E5F205AEE, 0xA27AA27B1D1A18D5, 0x02C3B2B2D2938E86, 0x0C7D13420B09807F
/* k32 */
    .quad   0xD7F9555555531C74, 0x21CFFFF748DAAAA8, 0x5A9AD1866C9BBE46, 0x4870A2210221D251, 0x4A0DB369C0A32AF1, 0x02B1CCC429FF56AF
    .quad   0xE205AAAAAAAC8E37, 0xFCDC000768795556, 0x0C96011A8A1537DD, 0x1C06A963F163406E, 0x010DF44C82A881E6, 0x174F45260F808FEB
/* k33 */
    .quad   0xA470BDA12F67F35C, 0xC0FE38E23327B425, 0xC9D3D0F2C6F0678D, 0x1C55C9935B5A982E, 0x27F6C0E2F0746764, 0x117C5E6E28AA9054
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
/* k40 */
    .quad   0x0162FFFFFA765ADF, 0x8F7BEA480083FB75, 0x561B3C2259E93611, 0x11E19FC1A9C875D5, 0xCA713EFC00367660, 0x03C6A03D41DA1151
    .quad   0x0162FFFFFA765ADF, 0x8F7BEA480083FB75, 0x561B3C2259E93611, 0x11E19FC1A9C875D5, 0xCA713EFC00367660, 0x03C6A03D41DA1151
/* k41 */
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x5DB0FFFFFD3B02C5, 0xD713F52358EBFDBA, 0x5EA60761A84D161A, 0xBB2C75A34EA6C44A, 0x0AC6735921C1119B, 0x0EE3D913BDACFBF6
/* k42 */
    .quad   0x66B10000003AFFC5, 0xCB1400E764EC0030, 0xA73E5EB56FA5D106, 0x8984C913A0FE09A9, 0x11E10AFB78AD7F13, 0x05429D0E3E918F52
    .quad   0x534DFFFFFFC4AAE6, 0x5397FF174C67FFCF, 0xBFF273EB870B251D, 0xDAF2827152870915, 0x393A9CBACA9E2DC3, 0x14BE74DBFAEE5748
/* R^3 mod p, R = 2^384, plain limbs (fpFromBytesL) */
925:
    .quad   0xED48AC6BD94CA1E0, 0x315F831E03A7ADF8, 0x9A53352A615E29DD, 0x34C04E5E921E1761, 0x2512D43565724728, 0x0AA6346091755D4D
/* |x| = 0xd201000000010000, the BLS parameter x = -|x|, 4 limbs (blsAbsX) */
926:
    .quad   0xD201000000010000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
/* "H2C-OVERSIZE-DST-" (RFC 9380 section 5.3.3) */
930:
    .ascii  "H2C-OVERSIZE-DST-"
    .p2align 3
/* the DST of the signatures (Signatures.lean DST), as a ByteList: size, offset, count, bytes */
    .p2align 3
931:
    .quad   72, 24, 43
    .ascii  "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_"
    .p2align 3
/* Fp12.frobeniusCoeff g = (1 + u)^((p - 1) / 6): g^0 to g^5, Montgomery form */
    .p2align 3
909:
    .quad   0x760900000002FFFD, 0xEBF4000BC40C0002, 0x5F48985753C758BA, 0x77CE585370525745, 0x5C071A97A256EC6D, 0x15F65EC3FA80E493
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x07089552B319D465, 0xC6695F92B50A8313, 0x97E83CCCD117228F, 0xA35BAECAB2DC29EE, 0x1CE393EA5DAACE4D, 0x08F2220FB0FB66EB
    .quad   0xB2F66AAD4CE5D646, 0x5842A06BFC497CEC, 0xCF4895D42599D394, 0xC11B9CBA40A8E8D0, 0x2E3813CBE5A0DE89, 0x110EEFDA88847FAF
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0xCD03C9E48671F071, 0x5DAB22461FCDA5D2, 0x587042AFD3851B95, 0x8EB60EBE01BACB9E, 0x03F97D6E83D050D2, 0x18F0206554638741
    .quad   0x7BCFA7A25AA30FDA, 0xDC17DEC12A927E7C, 0x2F088DD86B4EBEF1, 0xD1CA2087DA74D4A7, 0x2DA2596696CEBC1D, 0x0E2B7EEDBBFD87D2
    .quad   0x7BCFA7A25AA30FDA, 0xDC17DEC12A927E7C, 0x2F088DD86B4EBEF1, 0xD1CA2087DA74D4A7, 0x2DA2596696CEBC1D, 0x0E2B7EEDBBFD87D2
    .quad   0x890DC9E4867545C3, 0x2AF322533285A5D5, 0x50880866309B7E2C, 0xA20D1B8C7E881024, 0x14E4F04FE2DB9068, 0x14E56D3F1564853A
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x82D83CF50DBCE43F, 0xA2813E53DF9D018F, 0xC6F0CAA53C65E181, 0x7525CF528D50FE95, 0x4A85ED50F4798A6B, 0x171DA0FD6CF8EEBD
    .quad   0x3726C30AF242C66C, 0x7C2AC1AAD1B6FE70, 0xA04007FBBA4B14A2, 0xEF517C3266341429, 0x0095BA654ED2226B, 0x02E370ECCC86F7DD
/* the exponents of finalExponentiation: |x|, |x| + 1, (|x| + 1) / 3 */
927:
    .quad   0xD201000000010000, 0xD201000000010001, 0x460055555555AAAB
/* r, -r^-1 mod 2^64, 2^256 mod r, 2^512 mod r (Bls/Fr.lean Fr.params) */
    .p2align 3
940:
    .quad   0xFFFFFFFF00000001, 0x53BDA402FFFE5BFE, 0x3339D80809A1D805, 0x73EDA753299D7D48
    .quad   0xFFFFFFFEFFFFFFFF
    .quad   0x00000001FFFFFFFE, 0x5884B7FA00034802, 0x998C4FEFECBC4FF5, 0x1824B159ACC5056F
    .quad   0xC999E990F3F29C6D, 0x2B6CEDCB87925C23, 0x05D314967254398F, 0x0748D9D99F59FF11
/* r - 2, the exponent of Fr.inverse */
941:
    .quad   0xFFFFFFFEFFFFFFFF, 0x53BDA402FFFE5BFE, 0x3339D80809A1D805, 0x73EDA753299D7D48
/* r - 1, divided by the order for computeRootsOfUnity */
942:
    .quad   0xFFFFFFFF00000000, 0x53BDA402FFFE5BFE, 0x3339D80809A1D805, 0x73EDA753299D7D48
/* the domain separators of Kzg/Constants.lean, 16 bytes each */
945:
    .ascii  "FSBLOBVERIFY_V1_"
946:
    .ascii  "RCKZGBATCH___V1_"
947:
    .ascii  "RCKZGCBATCH__V1_"
/* Fp12.frobenius: the offset of each coefficient a_k in an element, then k */
    .p2align 2
932:
    .short  0, 0, 96, 2, 192, 4, 288, 1, 384, 3, 480, 5
    .p2align 3
