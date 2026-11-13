/*
 * X25519 (RFC 7748) for RISC-V (RISC-V ELF psABI, LP64D).
 * Baseline RV64GC instructions only: carries and borrows come from sltu.
 * Requirements: docs/reference/x25519.md. Layouts: include/x25519.inc.
 *
 * The functions and their steps follow the ARM64 file one for one. Field
 * elements are 4 limbs of 64 bits, any number below 2^256 that stands for
 * its value mod p = 2^255 - 19; 2^256 = 38 mod p folds the high bits back.
 * The ladder runs all 255 steps and swaps with a mask, and the inverse uses
 * the public exponent p - 2, so no branch or address depends on the scalar
 * or the point.
 */
.set ISA_RISCV64, 1
.include "crypto.inc"
.include "x25519.inc"
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

/* fn(sp + d, sp + a, sp + b). The offsets are below 2048. */
.macro OP fn, d, a, b
    addi    a0, sp, \d
    addi    a1, sp, \a
    addi    a2, sp, \b
    call    \fn
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

/* crypto_x25519_cswap(sp + a, sp + b, mask s1). */
.macro CSWAP a, b
    addi    a0, sp, \a
    addi    a1, sp, \b
    mv      a2, s1
    call    crypto_x25519_cswap
.endm

/* d = s where the mask t1 is all ones, else d. Uses t0. */
.macro SELECT d, s
    xor     t0, \d, \s
    and     t0, t0, t1
    xor     \d, \d, t0
.endm

/* d = d + s + c, with the carry out in c. Uses t2. */
.macro ADDC d, s, c
    add     \d, \d, \s
    sltu    t2, \d, \s
    add     \d, \d, \c
    sltu    \c, \d, \c
    or      \c, \c, t2
.endm

/* d = d - s - b, with the borrow out in b. Uses t2. */
.macro SUBB d, s, b
    sltu    t2, \d, \s
    sub     \d, \d, \s
    sltu    \s, \d, \b
    sub     \d, \d, \b
    or      \b, \s, t2
.endm

/* ---------------------------------------------------------------- X25519 */

.set X_K, 0                         # the clamped scalar
.set X_X1, 32                       # u
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
 * s1 swap mask, s2 result, s3 bit t, s4 swap, s5 k_t.
 */
FUNCTION crypto_x25519
    ENTER   X_FRAME
    mv      s2, a2
    ld      t0, 0(a0)                       # decodeScalar25519
    andi    t0, t0, -8
    sd      t0, X_K(sp)
    ld      t0, 8(a0)
    sd      t0, X_K+8(sp)
    ld      t0, 16(a0)
    sd      t0, X_K+16(sp)
    ld      t0, 24(a0)
    slli    t0, t0, 1
    srli    t0, t0, 1
    li      t1, 1
    slli    t1, t1, 62
    or      t0, t0, t1
    sd      t0, X_K+24(sp)
    ld      t0, 0(a1)                       # decodeUCoordinate: the top bit is masked
    sd      t0, X_X1(sp)
    sd      t0, X_X3(sp)                    # x3 = u, z3 = 1, x2 = 1, z2 = 0
    ld      t0, 8(a1)
    sd      t0, X_X1+8(sp)
    sd      t0, X_X3+8(sp)
    ld      t0, 16(a1)
    sd      t0, X_X1+16(sp)
    sd      t0, X_X3+16(sp)
    ld      t0, 24(a1)
    slli    t0, t0, 1
    srli    t0, t0, 1
    sd      t0, X_X1+24(sp)
    sd      t0, X_X3+24(sp)
    li      t0, 1
    sd      t0, X_Z3(sp)
    sd      zero, X_Z3+8(sp)
    sd      zero, X_Z3+16(sp)
    sd      zero, X_Z3+24(sp)
    sd      t0, X_X2(sp)
    sd      zero, X_X2+8(sp)
    sd      zero, X_X2+16(sp)
    sd      zero, X_X2+24(sp)
    sd      zero, X_Z2(sp)
    sd      zero, X_Z2+8(sp)
    sd      zero, X_Z2+16(sp)
    sd      zero, X_Z2+24(sp)
    li      s4, 0
    li      s3, 254
1:  srli    t0, s3, 6                       # k_t
    slli    t0, t0, 3
    add     t0, sp, t0
    ld      t0, X_K(t0)
    srl     t0, t0, s3
    andi    s5, t0, 1
    xor     s4, s4, s5
    neg     s1, s4
    CSWAP   X_X2, X_X3
    CSWAP   X_Z2, X_Z3
    mv      s4, s5
    FADD    X_A, X_X2, X_Z2
    FMUL    X_AA, X_A, X_A
    FSUB    X_B, X_X2, X_Z2
    FMUL    X_BB, X_B, X_B
    FSUB    X_E, X_AA, X_BB
    FADD    X_C, X_X3, X_Z3
    FSUB    X_D, X_X3, X_Z3
    FMUL    X_DA, X_D, X_A
    FMUL    X_CB, X_C, X_B
    FADD    X_T, X_DA, X_CB                 # x3 = (DA + CB)^2
    FMUL    X_X3, X_T, X_T
    FSUB    X_T, X_DA, X_CB                 # z3 = x1 * (DA - CB)^2
    FMUL    X_T, X_T, X_T
    FMUL    X_Z3, X_X1, X_T
    FMUL    X_X2, X_AA, X_BB                # x2 = AA * BB
    addi    a0, sp, X_T                     # z2 = E * (AA + a24 * E)
    addi    a1, sp, X_E
    call    crypto_x25519_mul_a24
    FADD    X_T, X_AA, X_T
    FMUL    X_Z2, X_E, X_T
    addi    s3, s3, -1
    bgez    s3, 1b
    neg     s1, s4
    CSWAP   X_X2, X_X3
    CSWAP   X_Z2, X_Z3
    addi    a0, sp, X_T                     # x2 / z2
    addi    a1, sp, X_Z2
    call    crypto_x25519_invert
    FMUL    X_T, X_X2, X_T
    ld      a3, X_T(sp)                     # reduce below p, then check for zero
    ld      a4, X_T+8(sp)
    ld      a5, X_T+16(sp)
    ld      a6, X_T+24(sp)
    .rept 2
    srli    t0, a6, 63                      # fold bit 255: 2^255 = 19
    slli    a6, a6, 1
    srli    a6, a6, 1
    li      t1, 19
    mul     t0, t0, t1
    add     a3, a3, t0
    sltu    t0, a3, t0
    add     a4, a4, t0
    sltu    t0, a4, t0
    add     a5, a5, t0
    sltu    t0, a5, t0
    add     a6, a6, t0
    .endr
    addi    t3, a3, 19                      # v + 19 reaches 2^255 when v >= p
    sltu    t0, t3, a3
    add     t4, a4, t0
    sltu    t0, t4, t0
    add     t5, a5, t0
    sltu    t0, t5, t0
    add     t6, a6, t0
    srli    t1, t6, 63
    neg     t1, t1
    slli    t6, t6, 1
    srli    t6, t6, 1
    SELECT  a3, t3
    SELECT  a4, t4
    SELECT  a5, t5
    SELECT  a6, t6
    or      t0, a3, a4
    or      t0, t0, a5
    or      t0, t0, a6
    li      a0, CRYPTO_X25519_ZERO
    beqz    t0, 9f
    sd      a3, 0(s2)
    sd      a4, 8(s2)
    sd      a5, 16(s2)
    sd      a6, 24(s2)
    li      a0, CRYPTO_OK
9:  LEAVE   X_FRAME
END_FUNCTION crypto_x25519

/*
 * crypto_x25519_invert(result, a): a^(p - 2), by squaring and multiplying
 * from bit 254 down. The exponent is public. s1 result, s2 bit.
 * a at sp, the running value at sp + 32.
 */
LOCAL_FUNCTION crypto_x25519_invert
    ENTER   64
    mv      s1, a0
    ld      t0, 0(a1)
    sd      t0, 0(sp)
    ld      t0, 8(a1)
    sd      t0, 8(sp)
    ld      t0, 16(a1)
    sd      t0, 16(sp)
    ld      t0, 24(a1)
    sd      t0, 24(sp)
    li      t0, 1
    sd      t0, 32(sp)
    sd      zero, 40(sp)
    sd      zero, 48(sp)
    sd      zero, 56(sp)
    li      s2, 254
1:  addi    a0, sp, 32
    addi    a1, sp, 32
    addi    a2, sp, 32
    call    crypto_x25519_mul
    srli    t0, s2, 6                       # bit t of p - 2
    slli    t0, t0, 3
    lla     t1, 300f
    add     t1, t1, t0
    ld      t1, 0(t1)
    srl     t1, t1, s2
    andi    t1, t1, 1
    beqz    t1, 2f
    addi    a0, sp, 32
    addi    a1, sp, 32
    mv      a2, sp
    call    crypto_x25519_mul
2:  addi    s2, s2, -1
    bgez    s2, 1b
    ld      t0, 32(sp)
    sd      t0, 0(s1)
    ld      t0, 40(sp)
    sd      t0, 8(s1)
    ld      t0, 48(sp)
    sd      t0, 16(s1)
    ld      t0, 56(sp)
    sd      t0, 24(s1)
    LEAVE   64
END_FUNCTION crypto_x25519_invert

/* ---------------------------------------------------------------- Field arithmetic */

/* One column of the product: t4, t5, t6 += a * b. Uses t0 to t2. */
.macro MULACC a, b
    mul     t0, \a, \b
    mulhu   t1, \a, \b
    add     t4, t4, t0
    sltu    t2, t4, t0
    add     t1, t1, t2
    add     t5, t5, t1
    sltu    t2, t5, t1
    add     t6, t6, t2
.endm

/* Store the low word of the column at sp + off and shift the column down. */
.macro COLUMN off
    sd      t4, \off(sp)
    mv      t4, t5
    mv      t5, t6
    li      t6, 0
.endm

/*
 * Store at a0 the low half at sp plus 38 times the high half at sp + 32,
 * folded below 2^256. Uses a1 to a7, t0 to t6.
 */
.macro REDUCE38 unused=0
.if \unused
.endif
    li      a7, 38
    ld      t0, 32(sp)                      # 38 * high, 5 limbs: a3, a4, a5, a6, t3
    mul     a3, t0, a7
    mulhu   t3, t0, a7
    ld      t0, 40(sp)
    mul     a4, t0, a7
    mulhu   t1, t0, a7
    add     a4, a4, t3
    sltu    t3, a4, t3
    add     t3, t1, t3
    ld      t0, 48(sp)
    mul     a5, t0, a7
    mulhu   t1, t0, a7
    add     a5, a5, t3
    sltu    t3, a5, t3
    add     t3, t1, t3
    ld      t0, 56(sp)
    mul     a6, t0, a7
    mulhu   t1, t0, a7
    add     a6, a6, t3
    sltu    t3, a6, t3
    add     t3, t1, t3
    li      t4, 0                           # + low
    ld      t0, 0(sp)
    ADDC    a3, t0, t4
    ld      t0, 8(sp)
    ADDC    a4, t0, t4
    ld      t0, 16(sp)
    ADDC    a5, t0, t4
    ld      t0, 24(sp)
    ADDC    a6, t0, t4
    add     t3, t3, t4                      # the top, below 39
    mul     t3, t3, a7
    add     a3, a3, t3
    sltu    t0, a3, t3
    add     a4, a4, t0
    sltu    t0, a4, t0
    add     a5, a5, t0
    sltu    t0, a5, t0
    add     a6, a6, t0
    sltu    t0, a6, t0
    mul     t0, t0, a7
    add     a3, a3, t0                      # no carry: the sum wrapped, so it is small
    sd      a3, 0(a0)
    sd      a4, 8(a0)
    sd      a5, 16(a0)
    sd      a6, 24(a0)
.endm

/*
 * crypto_x25519_mul(result, a, b): a * b mod p, below 2^256, for a, b below
 * 2^256. result may be a or b. A leaf: a a3 to a6, b a7, a1, a2, t3, the
 * column t4 to t6. The 8-limb product at sp.
 */
LOCAL_FUNCTION crypto_x25519_mul
    addi    sp, sp, -64
    UNWIND_ALLOC 64
    UNWIND_END_PROLOGUE
    ld      a3, 0(a1)
    ld      a4, 8(a1)
    ld      a5, 16(a1)
    ld      a6, 24(a1)
    ld      a7, 0(a2)
    ld      t3, 24(a2)
    ld      a1, 8(a2)
    ld      a2, 16(a2)
    li      t4, 0
    li      t5, 0
    li      t6, 0
    MULACC  a3, a7
    COLUMN  0
    MULACC  a3, a1
    MULACC  a4, a7
    COLUMN  8
    MULACC  a3, a2
    MULACC  a4, a1
    MULACC  a5, a7
    COLUMN  16
    MULACC  a3, t3
    MULACC  a4, a2
    MULACC  a5, a1
    MULACC  a6, a7
    COLUMN  24
    MULACC  a4, t3
    MULACC  a5, a2
    MULACC  a6, a1
    COLUMN  32
    MULACC  a5, t3
    MULACC  a6, a2
    COLUMN  40
    MULACC  a6, t3
    sd      t4, 48(sp)
    sd      t5, 56(sp)
    REDUCE38
    UNWIND_BEGIN_EPILOGUE
    addi    sp, sp, 64
    UNWIND_FREE 64
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_x25519_mul

/*
 * crypto_x25519_mul_a24(result, a): a * 121665 mod p (a24 of RFC 7748
 * section 5), below 2^256. A leaf: the product a3 to a6, the top t3.
 */
LOCAL_FUNCTION crypto_x25519_mul_a24
    UNWIND_END_PROLOGUE
    li      a7, 121665
    ld      t0, 0(a1)
    mul     a3, t0, a7
    mulhu   t3, t0, a7
    ld      t0, 8(a1)
    mul     a4, t0, a7
    mulhu   t1, t0, a7
    add     a4, a4, t3
    sltu    t3, a4, t3
    add     t3, t1, t3
    ld      t0, 16(a1)
    mul     a5, t0, a7
    mulhu   t1, t0, a7
    add     a5, a5, t3
    sltu    t3, a5, t3
    add     t3, t1, t3
    ld      t0, 24(a1)
    mul     a6, t0, a7
    mulhu   t1, t0, a7
    add     a6, a6, t3
    sltu    t3, a6, t3
    add     t3, t1, t3
    li      a7, 38
    mul     t3, t3, a7
    add     a3, a3, t3
    sltu    t0, a3, t3
    add     a4, a4, t0
    sltu    t0, a4, t0
    add     a5, a5, t0
    sltu    t0, a5, t0
    add     a6, a6, t0
    sltu    t0, a6, t0
    mul     t0, t0, a7
    add     a3, a3, t0
    sd      a3, 0(a0)
    sd      a4, 8(a0)
    sd      a5, 16(a0)
    sd      a6, 24(a0)
    ret
END_FUNCTION crypto_x25519_mul_a24

/*
 * crypto_x25519_add(result, a, b): a + b mod p, below 2^256. A leaf:
 * the sum a3 to a6, the carry t4.
 */
LOCAL_FUNCTION crypto_x25519_add
    UNWIND_END_PROLOGUE
    ld      a3, 0(a1)
    ld      a4, 8(a1)
    ld      a5, 16(a1)
    ld      a6, 24(a1)
    li      t4, 0
    ld      t0, 0(a2)
    ADDC    a3, t0, t4
    ld      t0, 8(a2)
    ADDC    a4, t0, t4
    ld      t0, 16(a2)
    ADDC    a5, t0, t4
    ld      t0, 24(a2)
    ADDC    a6, t0, t4
    .rept 2
    neg     t4, t4                          # 2^256 = 38
    andi    t4, t4, 38
    add     a3, a3, t4
    sltu    t4, a3, t4
    add     a4, a4, t4
    sltu    t4, a4, t4
    add     a5, a5, t4
    sltu    t4, a5, t4
    add     a6, a6, t4
    sltu    t4, a6, t4
    .endr
    sd      a3, 0(a0)
    sd      a4, 8(a0)
    sd      a5, 16(a0)
    sd      a6, 24(a0)
    ret
END_FUNCTION crypto_x25519_add

/*
 * crypto_x25519_sub(result, a, b): a - b mod p, below 2^256. A leaf:
 * the difference a3 to a6, the borrow t4.
 */
LOCAL_FUNCTION crypto_x25519_sub
    UNWIND_END_PROLOGUE
    ld      a3, 0(a1)
    ld      a4, 8(a1)
    ld      a5, 16(a1)
    ld      a6, 24(a1)
    li      t4, 0
    ld      t0, 0(a2)
    SUBB    a3, t0, t4
    ld      t0, 8(a2)
    SUBB    a4, t0, t4
    ld      t0, 16(a2)
    SUBB    a5, t0, t4
    ld      t0, 24(a2)
    SUBB    a6, t0, t4
    .rept 2
    neg     t4, t4                          # a borrow of 2^256 = 38
    andi    t4, t4, 38
    sltu    t0, a3, t4
    sub     a3, a3, t4
    sltu    t1, a4, t0
    sub     a4, a4, t0
    sltu    t0, a5, t1
    sub     a5, a5, t1
    sltu    t4, a6, t0
    sub     a6, a6, t0
    .endr
    sd      a3, 0(a0)
    sd      a4, 8(a0)
    sd      a5, 16(a0)
    sd      a6, 24(a0)
    ret
END_FUNCTION crypto_x25519_sub

/*
 * crypto_x25519_cswap(a, b, mask): swaps the 32 bytes at a and b when mask
 * is all ones, and keeps them when it is 0, with the same instructions.
 * A leaf.
 */
LOCAL_FUNCTION crypto_x25519_cswap
    UNWIND_END_PROLOGUE
    .irp off, 0, 8, 16, 24
    ld      t0, \off(a0)
    ld      t1, \off(a1)
    xor     t2, t0, t1
    and     t2, t2, a2
    xor     t0, t0, t2
    xor     t1, t1, t2
    sd      t0, \off(a0)
    sd      t1, \off(a1)
    .endr
    ret
END_FUNCTION crypto_x25519_cswap

/* ---------------------------------------------------------------- Constants */

    .p2align 3
/* p - 2 = 2^255 - 21: the exponent of 1 / a mod p. */
300:
    .quad   0xFFFFFFFFFFFFFFEB, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF
