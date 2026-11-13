/*
 * X25519 (RFC 7748) for ARM64 (AAPCS64).
 * Requirements: docs/reference/x25519.md. Layouts: include/x25519.inc.
 *
 * Field elements are 4 limbs of 64 bits, least significant first, any
 * number below 2^256 that stands for its value mod p = 2^255 - 19. Sums and
 * products fold the bits above 2^256 back with 2^256 = 38 mod p; only the
 * result is reduced below p. The ladder of RFC 7748 section 5 runs all 255
 * steps and swaps with a mask, and the inverse uses the public exponent
 * p - 2, so no branch or address depends on the scalar or the point.
 * x18 is never used. Every function that calls keeps an x29 frame record.
 */
.set ISA_ARM64, 1
.include "crypto.inc"
.include "x25519.inc"
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
    OP      crypto_x25519_mul, \d, \a, \b
.endm

.macro FADD d, a, b
    OP      crypto_x25519_add, \d, \a, \b
.endm

.macro FSUB d, a, b
    OP      crypto_x25519_sub, \d, \a, \b
.endm

/* crypto_x25519_cswap(sp + a, sp + b, mask x19). */
.macro CSWAP a, b
    add     x0, sp, #\a
    add     x1, sp, #\b
    mov     x2, x19
    bl      crypto_x25519_cswap
.endm

/* ---------------------------------------------------------------- X25519 */

.set X_K, 0                         /* the clamped scalar */
.set X_X1, 32                       /* u */
.set X_X2, 64
.set X_Z2, 96
.set X_X3, 128
.set X_Z3, 160
.set X_A, 192
.set X_AA, 224
.set X_B, 256
.set X_BB, 288
.set X_E, 320
.set X_C, 352
.set X_D, 384
.set X_DA, 416
.set X_CB, 448
.set X_T, 480
.set X_FRAME, 512

/*
 * crypto_x25519(scalar, u, result) -> status
 * x19 swap mask, x20 result, x21 bit t, x22 swap, x23 k_t.
 */
FUNCTION crypto_x25519
    ENTER   0, X_FRAME
    mov     x20, x2
    ldp     x9, x10, [x0]                   /* decodeScalar25519 */
    ldp     x11, x12, [x0, #16]
    and     x9, x9, #0xFFFFFFFFFFFFFFF8
    and     x12, x12, #0x7FFFFFFFFFFFFFFF
    orr     x12, x12, #0x4000000000000000
    stp     x9, x10, [sp, #X_K]
    stp     x11, x12, [sp, #X_K + 16]
    ldp     x9, x10, [x1]                   /* decodeUCoordinate: the top bit is masked */
    ldp     x11, x12, [x1, #16]
    and     x12, x12, #0x7FFFFFFFFFFFFFFF
    stp     x9, x10, [sp, #X_X1]
    stp     x11, x12, [sp, #X_X1 + 16]
    stp     x9, x10, [sp, #X_X3]            /* x3 = u, z3 = 1, x2 = 1, z2 = 0 */
    stp     x11, x12, [sp, #X_X3 + 16]
    mov     x13, #1
    stp     x13, xzr, [sp, #X_Z3]
    stp     xzr, xzr, [sp, #X_Z3 + 16]
    stp     x13, xzr, [sp, #X_X2]
    stp     xzr, xzr, [sp, #X_X2 + 16]
    stp     xzr, xzr, [sp, #X_Z2]
    stp     xzr, xzr, [sp, #X_Z2 + 16]
    mov     x22, #0
    mov     x21, #254
1:  lsr     x9, x21, #6                     /* k_t */
    add     x10, sp, #X_K
    ldr     x10, [x10, x9, lsl #3]
    lsr     x10, x10, x21
    and     x23, x10, #1
    eor     x22, x22, x23
    neg     x19, x22
    CSWAP   X_X2, X_X3
    CSWAP   X_Z2, X_Z3
    mov     x22, x23
    FADD    X_A, X_X2, X_Z2
    FMUL    X_AA, X_A, X_A
    FSUB    X_B, X_X2, X_Z2
    FMUL    X_BB, X_B, X_B
    FSUB    X_E, X_AA, X_BB
    FADD    X_C, X_X3, X_Z3
    FSUB    X_D, X_X3, X_Z3
    FMUL    X_DA, X_D, X_A
    FMUL    X_CB, X_C, X_B
    FADD    X_T, X_DA, X_CB                 /* x3 = (DA + CB)^2 */
    FMUL    X_X3, X_T, X_T
    FSUB    X_T, X_DA, X_CB                 /* z3 = x1 * (DA - CB)^2 */
    FMUL    X_T, X_T, X_T
    FMUL    X_Z3, X_X1, X_T
    FMUL    X_X2, X_AA, X_BB                /* x2 = AA * BB */
    add     x0, sp, #X_T                    /* z2 = E * (AA + a24 * E) */
    add     x1, sp, #X_E
    bl      crypto_x25519_mul_a24
    FADD    X_T, X_AA, X_T
    FMUL    X_Z2, X_E, X_T
    subs    x21, x21, #1
    b.ge    1b
    neg     x19, x22
    CSWAP   X_X2, X_X3
    CSWAP   X_Z2, X_Z3
    add     x0, sp, #X_T                    /* x2 / z2 */
    add     x1, sp, #X_Z2
    bl      crypto_x25519_invert
    FMUL    X_T, X_X2, X_T
    ldp     x9, x10, [sp, #X_T]             /* reduce below p, then check for zero */
    ldp     x11, x12, [sp, #X_T + 16]
    .rept 2
    lsr     x13, x12, #63                   /* fold bit 255: 2^255 = 19 */
    and     x12, x12, #0x7FFFFFFFFFFFFFFF
    mov     x14, #19
    mul     x13, x13, x14
    adds    x9, x9, x13
    adcs    x10, x10, xzr
    adcs    x11, x11, xzr
    adc     x12, x12, xzr
    .endr
    adds    x13, x9, #19                    /* v + 19 reaches 2^255 when v >= p */
    adcs    x14, x10, xzr
    adcs    x15, x11, xzr
    adc     x16, x12, xzr
    tst     x16, #0x8000000000000000
    and     x16, x16, #0x7FFFFFFFFFFFFFFF
    csel    x9, x13, x9, ne
    csel    x10, x14, x10, ne
    csel    x11, x15, x11, ne
    csel    x12, x16, x12, ne
    orr     x13, x9, x10
    orr     x14, x11, x12
    orr     x13, x13, x14
    mov     x0, #CRYPTO_X25519_ZERO
    cbz     x13, 9f
    stp     x9, x10, [x20]
    stp     x11, x12, [x20, #16]
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, X_FRAME
END_FUNCTION crypto_x25519

/*
 * crypto_x25519_invert(result, a): a^(p - 2), by squaring and multiplying
 * from bit 254 down. The exponent is public. x19 result, x20 bit,
 * x21 the exponent limb. a at sp, the running value at sp + 32.
 */
LOCAL_FUNCTION crypto_x25519_invert
    ENTER   0, 64
    mov     x19, x0
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
    bl      crypto_x25519_mul
    adr     x9, 300f                        /* p - 2 */
    lsr     x10, x20, #6
    ldr     x9, [x9, x10, lsl #3]
    lsr     x9, x9, x20
    tbz     x9, #0, 2f
    add     x0, sp, #32
    add     x1, sp, #32
    mov     x2, sp
    bl      crypto_x25519_mul
2:  subs    x20, x20, #1
    b.ge    1b
    ldp     x9, x10, [sp, #32]
    ldp     x11, x12, [sp, #48]
    stp     x9, x10, [x19]
    stp     x11, x12, [x19, #16]
    LEAVE   0, 64
END_FUNCTION crypto_x25519_invert

/* ---------------------------------------------------------------- Field arithmetic */

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
 * crypto_x25519_mul(result, a, b): a * b mod p, below 2^256, for a, b below
 * 2^256. result may be a or b. A leaf: a x3 to x6, b x7 to x10, the column
 * x11 to x13, products x14, x15. The 8-limb product at sp.
 */
LOCAL_FUNCTION crypto_x25519_mul
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
END_FUNCTION crypto_x25519_mul

/*
 * crypto_x25519_mul_a24(result, a): a * 121665 mod p (a24 of RFC 7748
 * section 5), below 2^256. A leaf: a x3 to x6, the top x7.
 */
LOCAL_FUNCTION crypto_x25519_mul_a24
    UNWIND_END_PROLOGUE
    ldp     x3, x4, [x1]
    ldp     x5, x6, [x1, #16]
    movz    x17, #0xDB41                    /* 121665 */
    movk    x17, #0x1, lsl #16
    mul     x11, x3, x17
    umulh   x12, x3, x17
    mul     x13, x4, x17
    umulh   x14, x4, x17
    mul     x15, x5, x17
    umulh   x16, x5, x17
    mul     x9, x6, x17
    umulh   x7, x6, x17
    mov     x3, x11
    adds    x4, x13, x12
    adcs    x5, x15, x14
    adcs    x6, x9, x16
    adc     x7, x7, xzr
    mov     x17, #38
    mul     x7, x7, x17
    adds    x3, x3, x7
    adcs    x4, x4, xzr
    adcs    x5, x5, xzr
    adcs    x6, x6, xzr
    cset    x7, hs
    mul     x7, x7, x17
    add     x3, x3, x7
    stp     x3, x4, [x0]
    stp     x5, x6, [x0, #16]
    ret
END_FUNCTION crypto_x25519_mul_a24

/*
 * crypto_x25519_add(result, a, b): a + b mod p, below 2^256. A leaf:
 * the sum x3 to x6, b x7 to x10, the fold x11.
 */
LOCAL_FUNCTION crypto_x25519_add
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
END_FUNCTION crypto_x25519_add

/*
 * crypto_x25519_sub(result, a, b): a - b mod p, below 2^256. A leaf:
 * the difference x3 to x6, b x7 to x10, the fold x11.
 */
LOCAL_FUNCTION crypto_x25519_sub
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
END_FUNCTION crypto_x25519_sub

/*
 * crypto_x25519_cswap(a, b, mask): swaps the 32 bytes at a and b when mask
 * is all ones, and keeps them when it is 0, with the same instructions.
 * A leaf.
 */
LOCAL_FUNCTION crypto_x25519_cswap
    UNWIND_END_PROLOGUE
    .irp off, 0, 16
    ldp     x3, x4, [x0, #\off]
    ldp     x5, x6, [x1, #\off]
    eor     x7, x3, x5
    eor     x8, x4, x6
    and     x7, x7, x2
    and     x8, x8, x2
    eor     x3, x3, x7
    eor     x4, x4, x8
    eor     x5, x5, x7
    eor     x6, x6, x8
    stp     x3, x4, [x0, #\off]
    stp     x5, x6, [x1, #\off]
    .endr
    ret
END_FUNCTION crypto_x25519_cswap

/* ---------------------------------------------------------------- Constants */

    .p2align 3
/* p - 2 = 2^255 - 21: the exponent of 1 / a mod p. */
300:
    .quad   0xFFFFFFFFFFFFFFEB, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF
