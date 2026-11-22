/*
 * BLS12-381 for RISC-V (RISC-V ELF psABI, LP64D): the field tower, the
 * groups G1 and G2, the optimal ate pairing, hash to G2 (RFC 9380) and the
 * BLS signatures of the proof of possession scheme, then the KZG commitments
 * of blobs and cells over it, as cryptography-specs v0.3.0 defines them
 * (EthLib/Cryptography/Bls and Kzg). Baseline RV64GC instructions only:
 * carries and borrows come from sltu, and big-endian bytes are read and
 * written one byte at a time.
 * Requirements: docs/reference/bls12-381.md, docs/reference/hash-to-curve.md,
 * docs/reference/bls-signatures.md, docs/reference/kzg.md,
 * docs/reference/kzg-cells.md. Layouts: include/bls12381.inc,
 * include/kzg.inc.
 *
 * The functions and their steps follow the ARM64 file one for one. The
 * pointers that ARM64 keeps in x19 to x28 are in s1 to s10. The flag
 * macros IS_ZERO and EQUAL leave their result in t0: 0 for zero or equal.
 */
.set ISA_RISCV64, 1
.include "crypto.inc"
.include "bls12381.inc"
.include "kzg.inc"
.include "platform.inc"

/* Frame of a non-leaf function: locals at sp, then ra and s0-s11. locals is a multiple of 16. */
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

/* rd = rs + off. Uses t6 when off is 2048 or more. */
.macro ADDR rd, rs, off
    .if (\off) < 2048
    addi    \rd, \rs, \off
    .else
    li      t6, \off
    add     \rd, \rs, t6
    .endif
.endm

/* a0 = ra + oa, a1 = rb + ob, a2 = rc + oc; then call fn. */
.macro C3 fn, ra, oa, rb, ob, rc, oc
    ADDR    a0, \ra, \oa
    ADDR    a1, \rb, \ob
    ADDR    a2, \rc, \oc
    call    \fn
.endm

.macro C2 fn, ra, oa, rb, ob
    ADDR    a0, \ra, \oa
    ADDR    a1, \rb, \ob
    call    \fn
.endm

/* The same with a global function of this library. */
.macro G3 fn, ra, oa, rb, ob, rc, oc
    ADDR    a0, \ra, \oa
    ADDR    a1, \rb, \ob
    ADDR    a2, \rc, \oc
    CALL_GLOBAL \fn
.endm

.macro G2 fn, ra, oa, rb, ob
    ADDR    a0, \ra, \oa
    ADDR    a1, \rb, \ob
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

/* Copy n bytes (a multiple of 8) from rs + os to rd + od. Uses t2 to t6. */
.macro COPY rd, od, rs, os, n
    ADDR    t4, \rs, \os
    ADDR    t5, \rd, \od
    li      t2, (\n) / 8
81: ld      t3, 0(t4)
    sd      t3, 0(t5)
    addi    t4, t4, 8
    addi    t5, t5, 8
    addi    t2, t2, -1
    bnez    t2, 81b
.endm

/* Zero n bytes (a multiple of 8) at rd + od. Uses t2, t5, t6. */
.macro ZERO rd, od, n
    ADDR    t5, \rd, \od
    li      t2, (\n) / 8
81: sd      zero, 0(t5)
    addi    t5, t5, 8
    addi    t2, t2, -1
    bnez    t2, 81b
.endm

/* t0 = 0 when the n bytes (a multiple of 8) at rs + os are all zero, else not 0. Uses t1, t2, t4, t6. */
.macro IS_ZERO rs, os, n
    ADDR    t4, \rs, \os
    li      t2, (\n) / 8
    li      t0, 0
81: ld      t1, 0(t4)
    or      t0, t0, t1
    addi    t4, t4, 8
    addi    t2, t2, -1
    bnez    t2, 81b
.endm

/* t0 = 0 when the n bytes (a multiple of 8) at ra + oa equal those at rb + ob, else not 0. Uses t1 to t6. */
.macro EQUAL ra, oa, rb, ob, n
    ADDR    t4, \ra, \oa
    ADDR    t5, \rb, \ob
    li      t2, (\n) / 8
    li      t0, 0
81: ld      t1, 0(t4)
    ld      t3, 0(t5)
    xor     t1, t1, t3
    or      t0, t0, t1
    addi    t4, t4, 8
    addi    t5, t5, 8
    addi    t2, t2, -1
    bnez    t2, 81b
.endm

/* The Fp element 1 (Montgomery form) at rd + od. Uses t2 to t6. */
.macro SET_ONE rd, od
    lla     t4, 900f
    addi    t4, t4, BLS_FP_RECORD_ONE
    ADDR    t5, \rd, \od
    li      t2, 6
81: ld      t3, 0(t4)
    sd      t3, 0(t5)
    addi    t4, t4, 8
    addi    t5, t5, 8
    addi    t2, t2, -1
    bnez    t2, 81b
.endm

/* t0 = bit n (a register) of the little-endian limbs at base (a register). */
.macro BIT base, n
    srli    t0, \n, 6
    slli    t0, t0, 3
    add     t0, \base, t0
    ld      t0, 0(t0)
    srl     t0, t0, \n
    andi    t0, t0, 1
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

/* d = d + s + c, with the carry out in c. Uses tmp. */
.macro ADDCARRY d, s, c, tmp
    add     \d, \d, \s
    sltu    \tmp, \d, \s
    add     \d, \d, \c
    sltu    \c, \d, \c
    or      \c, \c, \tmp
.endm

/* d = d - s - b, with the borrow out in b. Uses tmp1, tmp2. */
.macro SUBBORROW d, s, b, tmp1, tmp2
    sltu    \tmp1, \d, \s
    sub     \d, \d, \s
    sltu    \tmp2, \d, \b
    sub     \d, \d, \b
    or      \b, \tmp1, \tmp2
.endm

/* b = the borrow of x - y - b. Uses tmp1, tmp2. */
.macro BORROWOF x, y, b, tmp1, tmp2
    sltu    \tmp1, \x, \y
    sub     \tmp2, \x, \y
    sltu    \tmp2, \tmp2, \b
    or      \b, \tmp1, \tmp2
.endm

/* t0 = 0 when the bytes 1 to n - 1 at rs (8-byte aligned) are all zero, else not 0. Uses t1. */
.macro TAIL_ZERO rs, n
    lbu     t0, 1(\rs)
    lhu     t1, 2(\rs)
    or      t0, t0, t1
    lwu     t1, 4(\rs)
    or      t0, t0, t1
    .irp i, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88
    .if \i < \n
    ld      t1, \i(\rs)
    or      t0, t0, t1
    .endif
    .endr
.endm

/* ---------------------------------------------------------------- Fp */

/* T_j += a_j * b_i + c, with b_i in t6, c in s6; product s4 (low), s5 (high). */
.macro MAC tj, aj
    mul     s4, \aj, t6
    mulhu   s5, \aj, t6
    add     \tj, \tj, s4
    sltu    s4, \tj, s4
    add     \tj, \tj, s6
    sltu    s6, \tj, s6
    add     s6, s6, s4
    add     s6, s6, s5
.endm

/* T_j += q * p_j + c, with q in s3, p_j at off(s7), c in s6; product s4 (low), s5 (high). */
.macro MACQ tj, off
    ld      s4, \off(s7)
    mulhu   s5, s3, s4
    mul     s4, s3, s4
    add     \tj, \tj, s4
    sltu    s4, \tj, s4
    add     \tj, \tj, s6
    sltu    s6, \tj, s6
    add     s6, s6, s4
    add     s6, s6, s5
.endm

/* d_j = T_j - p_j - borrow s4, with the new borrow in s4; p_j at off(s7). Uses s5, s6, s8. */
.macro SUBP dj, tj, off
    ld      s5, \off(s7)
    sltu    s6, \tj, s5
    sub     \dj, \tj, s5
    sltu    s8, \dj, s4
    sub     \dj, \dj, s4
    or      s4, s6, s8
.endm

/* T_j = d_j when the mask s5 is all ones. Uses s6. */
.macro PICK tj, dj
    xor     s6, \dj, \tj
    and     s6, s6, s5
    xor     \tj, \tj, s6
.endm

/*
 * crypto_bls_fp_mul(result, a, b): a * b / 2^384 mod p, for a, b < p (CIOS).
 * result may be a or b. a a3 to a7 and s0, T t0 to t5 then s1 and s2, b_i
 * t6, q s3, product s4 and s5, carry s6, p record s7.
 */
LOCAL_FUNCTION crypto_bls_fp_mul
    addi    sp, sp, -80
    UNWIND_ALLOC 80
    sd      s0, 0(sp)
    UNWIND_SAVE s0, 0
    sd      s1, 8(sp)
    UNWIND_SAVE s1, 8
    sd      s2, 16(sp)
    UNWIND_SAVE s2, 16
    sd      s3, 24(sp)
    UNWIND_SAVE s3, 24
    sd      s4, 32(sp)
    UNWIND_SAVE s4, 32
    sd      s5, 40(sp)
    UNWIND_SAVE s5, 40
    sd      s6, 48(sp)
    UNWIND_SAVE s6, 48
    sd      s7, 56(sp)
    UNWIND_SAVE s7, 56
    sd      s8, 64(sp)
    UNWIND_SAVE s8, 64
    UNWIND_END_PROLOGUE
    ld      a3, 0(a1)
    ld      a4, 8(a1)
    ld      a5, 16(a1)
    ld      a6, 24(a1)
    ld      a7, 32(a1)
    ld      s0, 40(a1)
    lla     s7, 900f
    li      t0, 0
    li      t1, 0
    li      t2, 0
    li      t3, 0
    li      t4, 0
    li      t5, 0
    li      s1, 0
    .irp off, 0, 8, 16, 24, 32, 40
    ld      t6, \off(a2)                    # T += a * b_i
    li      s6, 0
    MAC     t0, a3
    MAC     t1, a4
    MAC     t2, a5
    MAC     t3, a6
    MAC     t4, a7
    MAC     t5, s0
    add     s1, s1, s6
    sltu    s2, s1, s6
    ld      s3, BLS_FP_RECORD_INVERSE(s7)
    mul     s3, t0, s3                      # q = T0 * -p^-1 mod 2^64
    li      s6, 0                           # T = (T + q * p) / 2^64
    MACQ    t0, 0
    MACQ    t1, 8
    MACQ    t2, 16
    MACQ    t3, 24
    MACQ    t4, 32
    MACQ    t5, 40
    add     s1, s1, s6
    sltu    s4, s1, s6
    add     s2, s2, s4
    mv      t0, t1
    mv      t1, t2
    mv      t2, t3
    mv      t3, t4
    mv      t4, t5
    mv      t5, s1
    mv      s1, s2
    .endr
    li      s4, 0                           # T - p when T >= p: borrow s4
    SUBP    a3, t0, 0
    SUBP    a4, t1, 8
    SUBP    a5, t2, 16
    SUBP    a6, t3, 24
    SUBP    a7, t4, 32
    SUBP    s0, t5, 40
    sltu    s5, s1, s4                      # mask s5: all ones when T >= p
    addi    s5, s5, -1
    PICK    t0, a3
    PICK    t1, a4
    PICK    t2, a5
    PICK    t3, a6
    PICK    t4, a7
    PICK    t5, s0
    sd      t0, 0(a0)
    sd      t1, 8(a0)
    sd      t2, 16(a0)
    sd      t3, 24(a0)
    sd      t4, 32(a0)
    sd      t5, 40(a0)
    UNWIND_BEGIN_EPILOGUE
    ld      s0, 0(sp)
    UNWIND_RESTORE s0
    ld      s1, 8(sp)
    UNWIND_RESTORE s1
    ld      s2, 16(sp)
    UNWIND_RESTORE s2
    ld      s3, 24(sp)
    UNWIND_RESTORE s3
    ld      s4, 32(sp)
    UNWIND_RESTORE s4
    ld      s5, 40(sp)
    UNWIND_RESTORE s5
    ld      s6, 48(sp)
    UNWIND_RESTORE s6
    ld      s7, 56(sp)
    UNWIND_RESTORE s7
    ld      s8, 64(sp)
    UNWIND_RESTORE s8
    addi    sp, sp, 80
    UNWIND_FREE 80
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_bls_fp_mul

/* crypto_bls_fp_add(result, a, b): a + b mod p, for a, b < p. result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp_add
    UNWIND_END_PROLOGUE
    li      t2, 0                           # the sum in a3 to a7 and t0, carry t2
    ld      a3, 0(a1)
    ld      t1, 0(a2)
    ADDCARRY a3, t1, t2, t3
    ld      a4, 8(a1)
    ld      t1, 8(a2)
    ADDCARRY a4, t1, t2, t3
    ld      a5, 16(a1)
    ld      t1, 16(a2)
    ADDCARRY a5, t1, t2, t3
    ld      a6, 24(a1)
    ld      t1, 24(a2)
    ADDCARRY a6, t1, t2, t3
    ld      a7, 32(a1)
    ld      t1, 32(a2)
    ADDCARRY a7, t1, t2, t3
    ld      t0, 40(a1)
    ld      t1, 40(a2)
    ADDCARRY t0, t1, t2, t3
    lla     a1, 900f                        # the borrow of the sum - p, in t4
    li      t4, 0
    ld      t1, 0(a1)
    BORROWOF a3, t1, t4, t3, t5
    ld      t1, 8(a1)
    BORROWOF a4, t1, t4, t3, t5
    ld      t1, 16(a1)
    BORROWOF a5, t1, t4, t3, t5
    ld      t1, 24(a1)
    BORROWOF a6, t1, t4, t3, t5
    ld      t1, 32(a1)
    BORROWOF a7, t1, t4, t3, t5
    ld      t1, 40(a1)
    BORROWOF t0, t1, t4, t3, t5
    xori    t4, t4, 1                       # mask t2: all ones on a carry or no borrow
    or      t2, t2, t4
    neg     t2, t2
    li      t4, 0                           # the sum - (p and mask)
    ld      t1, 0(a1)
    and     t1, t1, t2
    SUBBORROW a3, t1, t4, t3, t5
    ld      t1, 8(a1)
    and     t1, t1, t2
    SUBBORROW a4, t1, t4, t3, t5
    ld      t1, 16(a1)
    and     t1, t1, t2
    SUBBORROW a5, t1, t4, t3, t5
    ld      t1, 24(a1)
    and     t1, t1, t2
    SUBBORROW a6, t1, t4, t3, t5
    ld      t1, 32(a1)
    and     t1, t1, t2
    SUBBORROW a7, t1, t4, t3, t5
    ld      t1, 40(a1)
    and     t1, t1, t2
    SUBBORROW t0, t1, t4, t3, t5
    sd      a3, 0(a0)
    sd      a4, 8(a0)
    sd      a5, 16(a0)
    sd      a6, 24(a0)
    sd      a7, 32(a0)
    sd      t0, 40(a0)
    ret
END_FUNCTION crypto_bls_fp_add

/* crypto_bls_fp_sub(result, a, b): a - b mod p, for a, b < p. result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp_sub
    UNWIND_END_PROLOGUE
    li      t2, 0                           # the difference in a3 to a7 and t0, borrow t2
    ld      a3, 0(a1)
    ld      t1, 0(a2)
    SUBBORROW a3, t1, t2, t3, t5
    ld      a4, 8(a1)
    ld      t1, 8(a2)
    SUBBORROW a4, t1, t2, t3, t5
    ld      a5, 16(a1)
    ld      t1, 16(a2)
    SUBBORROW a5, t1, t2, t3, t5
    ld      a6, 24(a1)
    ld      t1, 24(a2)
    SUBBORROW a6, t1, t2, t3, t5
    ld      a7, 32(a1)
    ld      t1, 32(a2)
    SUBBORROW a7, t1, t2, t3, t5
    ld      t0, 40(a1)
    ld      t1, 40(a2)
    SUBBORROW t0, t1, t2, t3, t5
    neg     t2, t2                          # all ones on a borrow
    lla     a1, 900f                        # + (p and mask)
    li      t4, 0
    ld      t1, 0(a1)
    and     t1, t1, t2
    ADDCARRY a3, t1, t4, t3
    ld      t1, 8(a1)
    and     t1, t1, t2
    ADDCARRY a4, t1, t4, t3
    ld      t1, 16(a1)
    and     t1, t1, t2
    ADDCARRY a5, t1, t4, t3
    ld      t1, 24(a1)
    and     t1, t1, t2
    ADDCARRY a6, t1, t4, t3
    ld      t1, 32(a1)
    and     t1, t1, t2
    ADDCARRY a7, t1, t4, t3
    ld      t1, 40(a1)
    and     t1, t1, t2
    ADDCARRY t0, t1, t4, t3
    sd      a3, 0(a0)
    sd      a4, 8(a0)
    sd      a5, 16(a0)
    sd      a6, 24(a0)
    sd      a7, 32(a0)
    sd      t0, 40(a0)
    ret
END_FUNCTION crypto_bls_fp_sub

/* crypto_bls_fp_neg(result, a): -a mod p, for a < p; 0 stays 0. result may be a. */
LOCAL_FUNCTION crypto_bls_fp_neg
    UNWIND_END_PROLOGUE
    ld      a3, 0(a1)
    ld      a4, 8(a1)
    ld      a5, 16(a1)
    ld      a6, 24(a1)
    ld      a7, 32(a1)
    ld      t0, 40(a1)
    or      t1, a3, a4
    or      t1, t1, a5
    or      t1, t1, a6
    or      t1, t1, a7
    or      t1, t1, t0
    snez    t1, t1                          # mask t1: all ones when a != 0
    neg     t1, t1
    lla     a1, 900f                        # (p - a) and mask
    li      t2, 0
    ld      t3, 0(a1)
    SUBBORROW t3, a3, t2, t4, t5
    and     t3, t3, t1
    sd      t3, 0(a0)
    ld      t3, 8(a1)
    SUBBORROW t3, a4, t2, t4, t5
    and     t3, t3, t1
    sd      t3, 8(a0)
    ld      t3, 16(a1)
    SUBBORROW t3, a5, t2, t4, t5
    and     t3, t3, t1
    sd      t3, 16(a0)
    ld      t3, 24(a1)
    SUBBORROW t3, a6, t2, t4, t5
    and     t3, t3, t1
    sd      t3, 24(a0)
    ld      t3, 32(a1)
    SUBBORROW t3, a7, t2, t4, t5
    and     t3, t3, t1
    sd      t3, 32(a0)
    ld      t3, 40(a1)
    SUBBORROW t3, t0, t2, t4, t5
    and     t3, t3, t1
    sd      t3, 40(a0)
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
    ENTER   FW_SIZE
    mv      s1, a0
    mv      s2, a2
    COPY    sp, FW_BASE, a1, 0, 48
    SET_ONE sp, FW_ACC
    li      s3, 383                         # bit index
1:  BIT     s2, s3                          # skip the zero bits above the top set bit
    bnez    t0, 2f
    addi    s3, s3, -1
    bgez    s3, 1b
    j       4f
2:  FMUL    sp, FW_ACC, sp, FW_ACC, sp, FW_ACC
    BIT     s2, s3
    beqz    t0, 3f
    FMUL    sp, FW_ACC, sp, FW_ACC, sp, FW_BASE
3:  addi    s3, s3, -1
    bgez    s3, 2b
4:  COPY    s1, 0, sp, FW_ACC, 48
    LEAVE   FW_SIZE
END_FUNCTION crypto_bls_fp_pow

/* crypto_bls_fp_inverse(result, a): a^(p - 2) (Fp.inverse); 0 gives 0. result may be a. */
LOCAL_FUNCTION crypto_bls_fp_inverse
    ENTER   0
    lla     a2, 917f
    call    crypto_bls_fp_pow
    LEAVE   0
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
    ENTER   FS_SIZE
    mv      s1, a0
    mv      s2, a1
    addi    a0, sp, FS_C
    lla     a2, 918f
    call    crypto_bls_fp_pow
    FMUL    sp, FS_CC, sp, FS_C, sp, FS_C
    EQUAL   sp, FS_CC, s2, 0, 48
    bnez    t0, 9f
    COPY    s1, 0, sp, FS_C, 48
    li      a0, CRYPTO_OK
    LEAVE   FS_SIZE
9:  li      a0, CRYPTO_INVALID_ENCODING
    LEAVE   FS_SIZE
END_FUNCTION crypto_bls_fp_sqrt

/*
 * crypto_bls_fp_from_bytes(result, bytes) -> status: the 48 big-endian bytes
 * as an element of Fp, in Montgomery form (Fp.fromBytesBE).
 * CRYPTO_INVALID_ENCODING when the number is p or more; nothing is written.
 */
LOCAL_FUNCTION crypto_bls_fp_from_bytes
    ENTER   48
    mv      s1, a0
    LOAD_BE64 a2, a1, 40, t6
    LOAD_BE64 a3, a1, 32, t6
    LOAD_BE64 a4, a1, 24, t6
    LOAD_BE64 a5, a1, 16, t6
    LOAD_BE64 a6, a1, 8, t6
    LOAD_BE64 a7, a1, 0, t6
    lla     t4, 900f                        # below p?
    li      t0, 0
    ld      t1, 0(t4)
    BORROWOF a2, t1, t0, t2, t3
    ld      t1, 8(t4)
    BORROWOF a3, t1, t0, t2, t3
    ld      t1, 16(t4)
    BORROWOF a4, t1, t0, t2, t3
    ld      t1, 24(t4)
    BORROWOF a5, t1, t0, t2, t3
    ld      t1, 32(t4)
    BORROWOF a6, t1, t0, t2, t3
    ld      t1, 40(t4)
    BORROWOF a7, t1, t0, t2, t3
    beqz    t0, 9f
    sd      a2, 0(sp)
    sd      a3, 8(sp)
    sd      a4, 16(sp)
    sd      a5, 24(sp)
    sd      a6, 32(sp)
    sd      a7, 40(sp)
    mv      a0, s1                          # result = n * 2^768 / 2^384
    mv      a1, sp
    addi    a2, t4, BLS_FP_RECORD_R2
    call    crypto_bls_fp_mul
    li      a0, CRYPTO_OK
    LEAVE   48
9:  li      a0, CRYPTO_INVALID_ENCODING
    LEAVE   48
END_FUNCTION crypto_bls_fp_from_bytes

/* crypto_bls_fp_canonical(result, a): the value of a (Montgomery form) as 6 little-endian limbs. */
LOCAL_FUNCTION crypto_bls_fp_canonical
    ENTER   48
    li      t0, 1
    sd      t0, 0(sp)
    sd      zero, 8(sp)
    sd      zero, 16(sp)
    sd      zero, 24(sp)
    sd      zero, 32(sp)
    sd      zero, 40(sp)
    mv      a2, sp                          # a * 1 / 2^384
    call    crypto_bls_fp_mul
    LEAVE   48
END_FUNCTION crypto_bls_fp_canonical

/* crypto_bls_fp_to_bytes(bytes, a): the 48 big-endian bytes of a (Fp.toBytesBE). */
LOCAL_FUNCTION crypto_bls_fp_to_bytes
    ENTER   48
    mv      s1, a0
    mv      a0, sp
    call    crypto_bls_fp_canonical
    .irp i, 0, 1, 2, 3, 4, 5
    ld      t0, 8*\i(sp)
    STORE_BE64 t0, s1, 40-8*\i, t1
    .endr
    LEAVE   48
END_FUNCTION crypto_bls_fp_to_bytes

/*
 * crypto_bls_fp_sign_bit(bit, a): the u64 1 when the value y of a satisfies
 * y > p - y (Fp.signBit), else 0.
 */
LOCAL_FUNCTION crypto_bls_fp_sign_bit
    ENTER   48
    mv      s1, a0
    mv      a0, sp
    call    crypto_bls_fp_canonical
    ld      a2, 0(sp)
    ld      a3, 8(sp)
    ld      a4, 16(sp)
    ld      a5, 24(sp)
    ld      a6, 32(sp)
    ld      a7, 40(sp)
    lla     t4, 900f                        # d = p - y, in s2 to s7
    li      t0, 0
    ld      s2, 0(t4)
    SUBBORROW s2, a2, t0, t1, t2
    ld      s3, 8(t4)
    SUBBORROW s3, a3, t0, t1, t2
    ld      s4, 16(t4)
    SUBBORROW s4, a4, t0, t1, t2
    ld      s5, 24(t4)
    SUBBORROW s5, a5, t0, t1, t2
    ld      s6, 32(t4)
    SUBBORROW s6, a6, t0, t1, t2
    ld      s7, 40(t4)
    SUBBORROW s7, a7, t0, t1, t2
    li      t0, 0                           # d - y borrows when y > d
    BORROWOF s2, a2, t0, t1, t2
    BORROWOF s3, a3, t0, t1, t2
    BORROWOF s4, a4, t0, t1, t2
    BORROWOF s5, a5, t0, t1, t2
    BORROWOF s6, a6, t0, t1, t2
    BORROWOF s7, a7, t0, t1, t2
    sd      t0, 0(s1)
    LEAVE   48
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
    ENTER   GD_SIZE
    mv      s1, a0
    mv      s2, a1
    IS_ZERO s2, 96, 48
    bnez    t0, 1f
    COPY    s1, 0, s2, 0, 144
    LEAVE   GD_SIZE
1:  FMUL    sp, GD_A, s2, 0, s2, 0          # A = X * X
    FMUL    sp, GD_B, s2, 48, s2, 48        # B = Y * Y
    FMUL    sp, GD_C, sp, GD_B, sp, GD_B    # C = B * B
    FADD    sp, GD_T, s2, 0, sp, GD_B       # t = (X + B)^2 - A - C
    FMUL    sp, GD_T, sp, GD_T, sp, GD_T
    FSUB    sp, GD_T, sp, GD_T, sp, GD_A
    FSUB    sp, GD_T, sp, GD_T, sp, GD_C
    FADD    sp, GD_D, sp, GD_T, sp, GD_T    # D = t + t
    FADD    sp, GD_E, sp, GD_A, sp, GD_A    # E = A + A + A
    FADD    sp, GD_E, sp, GD_E, sp, GD_A
    FMUL    sp, GD_F, sp, GD_E, sp, GD_E    # F = E * E
    FADD    sp, GD_T, sp, GD_D, sp, GD_D    # x' = F - (D + D)
    FSUB    sp, GD_X, sp, GD_F, sp, GD_T
    FSUB    sp, GD_T, sp, GD_D, sp, GD_X    # y' = E (D - x') - (C4 + C4)
    FMUL    sp, GD_Y, sp, GD_E, sp, GD_T
    FADD    sp, GD_T, sp, GD_C, sp, GD_C
    FADD    sp, GD_T, sp, GD_T, sp, GD_T
    FADD    sp, GD_T, sp, GD_T, sp, GD_T
    FSUB    sp, GD_Y, sp, GD_Y, sp, GD_T
    FADD    sp, GD_T, s2, 48, s2, 48        # z' = (Y + Y) Z
    FMUL    sp, GD_Z, sp, GD_T, s2, 96
    COPY    s1, 0, sp, GD_X, 144
    LEAVE   GD_SIZE
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
    ENTER   GA_SIZE
    mv      s1, a0                          # first
    mv      s2, a1                          # second
    mv      s3, a2                          # point
    IS_ZERO s1, 96, 48
    bnez    t0, 1f
    COPY    s3, 0, s2, 0, 144               # first at infinity: second
    j       9f
1:  IS_ZERO s2, 96, 48
    bnez    t0, 2f
    COPY    s3, 0, s1, 0, 144               # second at infinity: first
    j       9f
2:  FMUL    sp, GA_Z1Z1, s1, 96, s1, 96
    FMUL    sp, GA_Z2Z2, s2, 96, s2, 96
    FMUL    sp, GA_U1, s1, 0, sp, GA_Z2Z2
    FMUL    sp, GA_U2, s2, 0, sp, GA_Z1Z1
    FMUL    sp, GA_S1, s1, 48, s2, 96       # s1 = Y1 Z2 z2z2
    FMUL    sp, GA_S1, sp, GA_S1, sp, GA_Z2Z2
    FMUL    sp, GA_S2, s2, 48, s1, 96       # s2 = Y2 Z1 z1z1
    FMUL    sp, GA_S2, sp, GA_S2, sp, GA_Z1Z1
    EQUAL   sp, GA_U1, sp, GA_U2, 48
    bnez    t0, 4f
    EQUAL   sp, GA_S1, sp, GA_S2, 48
    bnez    t0, 3f
    mv      a0, s3                          # equal points: double
    mv      a1, s1
    call    crypto_bls_g1_double
    j       9f
3:  SET_ONE s3, 0                           # opposite points: infinity
    SET_ONE s3, 48
    ZERO    s3, 96, 48
    j       9f
4:  FSUB    sp, GA_H, sp, GA_U2, sp, GA_U1  # h = u2 - u1
    FADD    sp, GA_T, sp, GA_H, sp, GA_H    # i = (2 h)^2
    FMUL    sp, GA_I, sp, GA_T, sp, GA_T
    FMUL    sp, GA_J, sp, GA_H, sp, GA_I    # j = h i
    FSUB    sp, GA_T, sp, GA_S2, sp, GA_S1  # r = 2 (s2 - s1)
    FADD    sp, GA_R, sp, GA_T, sp, GA_T
    FMUL    sp, GA_V, sp, GA_U1, sp, GA_I   # v = u1 i
    FMUL    sp, GA_X, sp, GA_R, sp, GA_R    # x' = r^2 - j - 2 v
    FSUB    sp, GA_X, sp, GA_X, sp, GA_J
    FSUB    sp, GA_X, sp, GA_X, sp, GA_V
    FSUB    sp, GA_X, sp, GA_X, sp, GA_V
    FSUB    sp, GA_T, sp, GA_V, sp, GA_X    # y' = r (v - x') - 2 s1 j
    FMUL    sp, GA_Y, sp, GA_R, sp, GA_T
    FADD    sp, GA_T, sp, GA_S1, sp, GA_S1
    FMUL    sp, GA_T, sp, GA_T, sp, GA_J
    FSUB    sp, GA_Y, sp, GA_Y, sp, GA_T
    FADD    sp, GA_T, s1, 96, s2, 96        # z' = ((Z1 + Z2)^2 - z1z1 - z2z2) h
    FMUL    sp, GA_T, sp, GA_T, sp, GA_T
    FSUB    sp, GA_T, sp, GA_T, sp, GA_Z1Z1
    FSUB    sp, GA_T, sp, GA_T, sp, GA_Z2Z2
    FMUL    sp, GA_Z, sp, GA_T, sp, GA_H
    COPY    s3, 0, sp, GA_X, 144
9:  li      a0, CRYPTO_OK
    LEAVE   GA_SIZE
END_FUNCTION crypto_bls_g1_add

/* crypto_bls_g1_neg(point, negated) -> status: (X, -Y, Z) (G1.neg). */
FUNCTION crypto_bls_g1_neg
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    COPY    s2, 0, s1, 0, 48
    COPY    s2, 96, s1, 96, 48
    C2      crypto_bls_fp_neg, s2, 48, s1, 48
    li      a0, CRYPTO_OK
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
    ENTER   GM_SIZE
    mv      s1, a0
    mv      s2, a2
    COPY    sp, GM_P, a1, 0, 144
    li      s3, 255
0:  BIT     s2, s3                          # the highest set bit of k
    bnez    t0, 3f
    addi    s3, s3, -1
    bgez    s3, 0b
    SET_ONE sp, GM_ACC                      # k = 0: the point at infinity
    SET_ONE sp, GM_ACC + 48
    ZERO    sp, GM_ACC + 96, 48
    j       4f
3:  COPY    sp, GM_ACC, sp, GM_P, 144
    addi    s3, s3, -1
    bltz    s3, 4f
1:  C2      crypto_bls_g1_double, sp, GM_ACC, sp, GM_ACC
    BIT     s2, s3
    beqz    t0, 2f
    G3      crypto_bls_g1_add, sp, GM_ACC, sp, GM_P, sp, GM_ACC
2:  addi    s3, s3, -1
    bgez    s3, 1b
4:  COPY    s1, 0, sp, GM_ACC, 144
    LEAVE   GM_SIZE
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
    ENTER   GF_SIZE
    mv      s1, a0
    mv      s2, a1
    IS_ZERO s2, 96, 48
    bnez    t0, 1f
    ZERO    s1, 0, 96
    LEAVE   GF_SIZE
1:  C2      crypto_bls_fp_inverse, sp, GF_ZI, s2, 96
    FMUL    sp, GF_ZI2, sp, GF_ZI, sp, GF_ZI
    FMUL    sp, GF_ZI3, sp, GF_ZI2, sp, GF_ZI
    FMUL    s1, 0, s2, 0, sp, GF_ZI2
    FMUL    s1, 48, s2, 48, sp, GF_ZI3
    LEAVE   GF_SIZE
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
    ENTER   GS_SIZE
    mv      s1, a0
    mv      s2, a1
    IS_ZERO s1, 96, 48
    beqz    t0, 1f
    mv      a0, sp                          # t = |x| (|x| P) = x^2 P
    mv      a1, s1
    lla     a2, 926f
    call    crypto_bls_g1_mul
    mv      a0, sp
    mv      a1, sp
    lla     a2, 926f
    call    crypto_bls_g1_mul
    IS_ZERO sp, GS_T + 96, 48               # x^2 P at infinity: sigma(P) is not
    beqz    t0, 2f
    FMUL    sp, GS_A, sp, GS_T + 96, sp, GS_T + 96  # a = Zt^2, b = Z^2
    FMUL    sp, GS_B, s1, 96, s1, 96
    addi    a0, sp, GS_C                    # c = beta X Zt^2, d = Xt Z^2
    mv      a1, s1
    lla     a2, 928f
    call    crypto_bls_fp_mul
    FMUL    sp, GS_C, sp, GS_C, sp, GS_A
    FMUL    sp, GS_D, sp, GS_T, sp, GS_B
    EQUAL   sp, GS_C, sp, GS_D, 48
    bnez    t0, 2f
    FMUL    sp, GS_A, sp, GS_A, sp, GS_T + 96  # c = Y Zt^3, d = Yt Z^3
    FMUL    sp, GS_B, sp, GS_B, s1, 96
    FMUL    sp, GS_C, s1, 48, sp, GS_A
    FMUL    sp, GS_D, sp, GS_T + 48, sp, GS_B
    FADD    sp, GS_C, sp, GS_C, sp, GS_D    # c + d = 0
    IS_ZERO sp, GS_C, 48
1:  seqz    t0, t0
    sd      t0, 0(s2)
    LEAVE   GS_SIZE
2:  sd      zero, 0(s2)
    LEAVE   GS_SIZE
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
    ENTER   GU_SIZE
    mv      s1, a0
    mv      s2, a1
    lbu     s3, 0(s1)
    andi    t0, s3, 0x80
    beqz    t0, 8f                          # no compression bit
    andi    t0, s3, 0x40
    beqz    t0, 2f
    li      t0, 0xC0                        # infinity: 0xC0, then zeros
    bne     s3, t0, 8f
    TAIL_ZERO s1, 48                        # bytes 1 to 47
    bnez    t0, 8f
    SET_ONE s2, 0
    SET_ONE s2, 48
    ZERO    s2, 96, 48
    j       9f
2:  COPY    sp, GU_RHS, s1, 0, 48           # x with the flag bits cleared
    lbu     t0, GU_RHS(sp)
    andi    t0, t0, 0x1F
    sb      t0, GU_RHS(sp)
    C2      crypto_bls_fp_from_bytes, sp, GU_X, sp, GU_RHS
    bnez    a0, 8f
    FMUL    sp, GU_RHS, sp, GU_X, sp, GU_X  # x^3 + 4
    FMUL    sp, GU_RHS, sp, GU_RHS, sp, GU_X
    ADDR    a0, sp, GU_RHS
    ADDR    a1, sp, GU_RHS
    lla     a2, 923f
    call    crypto_bls_fp_add
    C2      crypto_bls_fp_sqrt, sp, GU_Y, sp, GU_RHS
    bnez    a0, 8f
    C2      crypto_bls_fp_sign_bit, sp, GU_BIT, sp, GU_Y
    ld      t0, GU_BIT(sp)
    srli    t1, s3, 5
    andi    t1, t1, 1
    beq     t0, t1, 3f
    C2      crypto_bls_fp_neg, sp, GU_Y, sp, GU_Y
3:  SET_ONE sp, GU_Z
    COPY    s2, 0, sp, GU_X, 144
9:  li      a0, CRYPTO_OK
    LEAVE   GU_SIZE
8:  li      a0, CRYPTO_INVALID_ENCODING
    LEAVE   GU_SIZE
END_FUNCTION crypto_bls_g1_uncompress

/*
 * crypto_bls_g1_decode(bytes, point) -> status: G1.uncompress, then the
 * subgroup check (decodeG1Export).
 */
.set GE_P, 0
.set GE_V, 144
.set GE_SIZE, 160
FUNCTION crypto_bls_g1_decode
    ENTER   GE_SIZE
    mv      s1, a0
    mv      s2, a1
    mv      a1, sp
    call    crypto_bls_g1_uncompress
    bnez    a0, 8f
    C2      crypto_bls_g1_in_subgroup, sp, GE_P, sp, GE_V
    ld      t0, GE_V(sp)
    beqz    t0, 8f
    COPY    s2, 0, sp, GE_P, 144
    li      a0, CRYPTO_OK
    LEAVE   GE_SIZE
8:  li      a0, CRYPTO_INVALID_ENCODING
    LEAVE   GE_SIZE
END_FUNCTION crypto_bls_g1_decode

/* crypto_bls_g1_compress(point, bytes) -> status: G1.compress. */
.set GC_XY, 0
.set GC_BIT, 96
.set GC_SIZE, 112
FUNCTION crypto_bls_g1_compress
    ENTER   GC_SIZE
    mv      s1, a0
    mv      s2, a1
    IS_ZERO s1, 96, 48
    bnez    t0, 1f
    ZERO    s2, 0, 48
    li      t0, 0xC0
    sb      t0, 0(s2)
    j       9f
1:  C2      crypto_bls_g1_affine, sp, GC_XY, s1, 0
    C2      crypto_bls_fp_to_bytes, s2, 0, sp, GC_XY
    C2      crypto_bls_fp_sign_bit, sp, GC_BIT, sp, GC_XY + 48
    ld      t0, GC_BIT(sp)
    lbu     t1, 0(s2)
    ori     t1, t1, 0x80
    slli    t0, t0, 5
    or      t1, t1, t0
    sb      t1, 0(s2)
9:  li      a0, CRYPTO_OK
    LEAVE   GC_SIZE
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
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    FADD    s1, 0, s2, 0, s3, 0
    FADD    s1, 48, s2, 48, s3, 48
    LEAVE   0
END_FUNCTION crypto_bls_fp2_add

/* crypto_bls_fp2_sub(result, a, b): a - b (Fp2.sub). result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp2_sub
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    FSUB    s1, 0, s2, 0, s3, 0
    FSUB    s1, 48, s2, 48, s3, 48
    LEAVE   0
END_FUNCTION crypto_bls_fp2_sub

/* crypto_bls_fp2_neg(result, a): -a (Fp2.neg). result may be a. */
LOCAL_FUNCTION crypto_bls_fp2_neg
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    C2      crypto_bls_fp_neg, s1, 0, s2, 0
    C2      crypto_bls_fp_neg, s1, 48, s2, 48
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
    ENTER   M2_SIZE
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    FMUL    sp, M2_T0, s2, 0, s3, 0
    FMUL    sp, M2_T1, s2, 48, s3, 48
    FMUL    sp, M2_T2, s2, 0, s3, 48
    FMUL    sp, M2_T3, s2, 48, s3, 0
    FSUB    s1, 0, sp, M2_T0, sp, M2_T1
    FADD    s1, 48, sp, M2_T2, sp, M2_T3
    LEAVE   M2_SIZE
END_FUNCTION crypto_bls_fp2_mul

/* crypto_bls_fp2_mul_fp(result, a, k): (a0 k, a1 k), for k in Fp (Fp2.ofFp k * a). result may be a. */
LOCAL_FUNCTION crypto_bls_fp2_mul_fp
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    FMUL    s1, 0, s2, 0, s3, 0
    FMUL    s1, 48, s2, 48, s3, 0
    LEAVE   0
END_FUNCTION crypto_bls_fp2_mul_fp

/* crypto_bls_fp2_mul_nr(result, a): a (1 + u) = (a0 - a1, a0 + a1) (Fp2.mulByOnePlusI). result may be a. */
.set MN_T, 0
.set MN_SIZE, 48
LOCAL_FUNCTION crypto_bls_fp2_mul_nr
    ENTER   MN_SIZE
    mv      s1, a0
    mv      s2, a1
    FSUB    sp, MN_T, s2, 0, s2, 48
    FADD    s1, 48, s2, 0, s2, 48
    COPY    s1, 0, sp, MN_T, 48
    LEAVE   MN_SIZE
END_FUNCTION crypto_bls_fp2_mul_nr

/*
 * crypto_bls_fp2_inverse(result, a): (a0 / n, -a1 / n), n = a0^2 + a1^2
 * (Fp2.inverse); 0 gives 0. result may be a.
 */
.set I2_N, 0
.set I2_T, 48
.set I2_SIZE, 96
LOCAL_FUNCTION crypto_bls_fp2_inverse
    ENTER   I2_SIZE
    mv      s1, a0
    mv      s2, a1
    FMUL    sp, I2_N, s2, 0, s2, 0
    FMUL    sp, I2_T, s2, 48, s2, 48
    FADD    sp, I2_N, sp, I2_N, sp, I2_T
    C2      crypto_bls_fp_inverse, sp, I2_N, sp, I2_N
    FMUL    s1, 0, s2, 0, sp, I2_N
    FMUL    sp, I2_T, s2, 48, sp, I2_N
    C2      crypto_bls_fp_neg, s1, 48, sp, I2_T
    LEAVE   I2_SIZE
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
    ENTER   Q2_SIZE
    mv      s1, a0
    mv      s2, a1
    IS_ZERO s2, 48, 48
    bnez    t0, 3f
    C2      crypto_bls_fp_sqrt, sp, Q2_C0, s2, 0 # c1 = 0: sqrt(c0), else (0, sqrt(-c0))
    bnez    a0, 1f
    ZERO    sp, Q2_C1, 48
    j       7f
1:  C2      crypto_bls_fp_neg, sp, Q2_T, s2, 0
    C2      crypto_bls_fp_sqrt, sp, Q2_C1, sp, Q2_T
    bnez    a0, 8f
    ZERO    sp, Q2_C0, 48
    j       7f
3:  FMUL    sp, Q2_S, s2, 0, s2, 0          # n = c0^2 + c1^2, s = sqrt(n)
    FMUL    sp, Q2_T, s2, 48, s2, 48
    FADD    sp, Q2_S, sp, Q2_S, sp, Q2_T
    C2      crypto_bls_fp_sqrt, sp, Q2_S, sp, Q2_S
    bnez    a0, 8f
    FADD    sp, Q2_T, s2, 0, sp, Q2_S       # sqrt((c0 + s) / 2)
    lla     a2, 903f
    ADDR    a0, sp, Q2_T
    ADDR    a1, sp, Q2_T
    call    crypto_bls_fp_mul
    C2      crypto_bls_fp_sqrt, sp, Q2_C0, sp, Q2_T
    beqz    a0, 4f
    FSUB    sp, Q2_T, s2, 0, sp, Q2_S       # else sqrt((c0 - s) / 2)
    lla     a2, 903f
    ADDR    a0, sp, Q2_T
    ADDR    a1, sp, Q2_T
    call    crypto_bls_fp_mul
    C2      crypto_bls_fp_sqrt, sp, Q2_C0, sp, Q2_T
    bnez    a0, 8f
4:  FADD    sp, Q2_T, sp, Q2_C0, sp, Q2_C0  # c1 = a1 / (2 c0)
    C2      crypto_bls_fp_inverse, sp, Q2_T, sp, Q2_T
    FMUL    sp, Q2_C1, s2, 48, sp, Q2_T
7:  COPY    s1, 0, sp, Q2_C0, 96
    li      a0, CRYPTO_OK
    LEAVE   Q2_SIZE
8:  li      a0, CRYPTO_INVALID_ENCODING
    LEAVE   Q2_SIZE
END_FUNCTION crypto_bls_fp2_sqrt

/*
 * crypto_bls_fp2_sign_bit(bit, a): Fp2.signBit: the sign bit of c1 when c1
 * is not 0, else that of c0, as the u64 1 or 0.
 */
LOCAL_FUNCTION crypto_bls_fp2_sign_bit
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    IS_ZERO s2, 48, 48
    beqz    t0, 1f
    C2      crypto_bls_fp_sign_bit, s1, 0, s2, 48
    LEAVE   0
1:  C2      crypto_bls_fp_sign_bit, s1, 0, s2, 0
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
    ENTER   HD_SIZE
    mv      s1, a0
    mv      s2, a1
    IS_ZERO s2, 192, 96
    bnez    t0, 1f
    COPY    s1, 0, s2, 0, 288
    LEAVE   HD_SIZE
1:  F2MUL   sp, HD_A, s2, 0, s2, 0          # A = X * X
    F2MUL   sp, HD_B, s2, 96, s2, 96        # B = Y * Y
    F2MUL   sp, HD_C, sp, HD_B, sp, HD_B    # C = B * B
    F2ADD   sp, HD_T, s2, 0, sp, HD_B       # D = 2 ((X + B)^2 - A - C)
    F2MUL   sp, HD_T, sp, HD_T, sp, HD_T
    F2SUB   sp, HD_T, sp, HD_T, sp, HD_A
    F2SUB   sp, HD_T, sp, HD_T, sp, HD_C
    F2ADD   sp, HD_D, sp, HD_T, sp, HD_T
    F2ADD   sp, HD_E, sp, HD_A, sp, HD_A    # E = 3 A
    F2ADD   sp, HD_E, sp, HD_E, sp, HD_A
    F2MUL   sp, HD_F, sp, HD_E, sp, HD_E    # F = E * E
    F2ADD   sp, HD_T, sp, HD_D, sp, HD_D    # x' = F - 2 D
    F2SUB   sp, HD_X, sp, HD_F, sp, HD_T
    F2SUB   sp, HD_T, sp, HD_D, sp, HD_X    # y' = E (D - x') - 8 C
    F2MUL   sp, HD_Y, sp, HD_E, sp, HD_T
    F2ADD   sp, HD_T, sp, HD_C, sp, HD_C
    F2ADD   sp, HD_T, sp, HD_T, sp, HD_T
    F2ADD   sp, HD_T, sp, HD_T, sp, HD_T
    F2SUB   sp, HD_Y, sp, HD_Y, sp, HD_T
    F2ADD   sp, HD_T, s2, 96, s2, 96        # z' = 2 Y Z
    F2MUL   sp, HD_Z, sp, HD_T, s2, 192
    COPY    s1, 0, sp, HD_X, 288
    LEAVE   HD_SIZE
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
    ENTER   HA_SIZE
    mv      s3, a0                          # result
    mv      s1, a1                          # first
    mv      s2, a2                          # second
    IS_ZERO s1, 192, 96
    bnez    t0, 1f
    COPY    s3, 0, s2, 0, 288
    j       9f
1:  IS_ZERO s2, 192, 96
    bnez    t0, 2f
    COPY    s3, 0, s1, 0, 288
    j       9f
2:  F2MUL   sp, HA_Z1Z1, s1, 192, s1, 192
    F2MUL   sp, HA_Z2Z2, s2, 192, s2, 192
    F2MUL   sp, HA_U1, s1, 0, sp, HA_Z2Z2
    F2MUL   sp, HA_U2, s2, 0, sp, HA_Z1Z1
    F2MUL   sp, HA_S1, s1, 96, s2, 192
    F2MUL   sp, HA_S1, sp, HA_S1, sp, HA_Z2Z2
    F2MUL   sp, HA_S2, s2, 96, s1, 192
    F2MUL   sp, HA_S2, sp, HA_S2, sp, HA_Z1Z1
    EQUAL   sp, HA_U1, sp, HA_U2, 96
    bnez    t0, 4f
    EQUAL   sp, HA_S1, sp, HA_S2, 96
    bnez    t0, 3f
    mv      a0, s3
    mv      a1, s1
    call    crypto_bls_g2_double
    j       9f
3:  SET_ONE s3, 0                           # the point at infinity: (1, 1, 0)
    ZERO    s3, 48, 48
    SET_ONE s3, 96
    ZERO    s3, 144, 144
    j       9f
4:  F2SUB   sp, HA_U2, sp, HA_U2, sp, HA_U1 # h = u2 - u1
    F2ADD   sp, HA_I, sp, HA_U2, sp, HA_U2  # i = (2 h)^2
    F2MUL   sp, HA_I, sp, HA_I, sp, HA_I
    F2MUL   sp, HA_J, sp, HA_U2, sp, HA_I   # j = h i
    F2SUB   sp, HA_S2, sp, HA_S2, sp, HA_S1 # r = 2 (s2 - s1)
    F2ADD   sp, HA_S2, sp, HA_S2, sp, HA_S2
    F2MUL   sp, HA_U1, sp, HA_U1, sp, HA_I  # v = u1 i
    F2MUL   sp, HA_X, sp, HA_S2, sp, HA_S2  # x' = r^2 - j - 2 v
    F2SUB   sp, HA_X, sp, HA_X, sp, HA_J
    F2SUB   sp, HA_X, sp, HA_X, sp, HA_U1
    F2SUB   sp, HA_X, sp, HA_X, sp, HA_U1
    F2SUB   sp, HA_I, sp, HA_U1, sp, HA_X   # y' = r (v - x') - 2 s1 j
    F2MUL   sp, HA_Y, sp, HA_S2, sp, HA_I
    F2ADD   sp, HA_S1, sp, HA_S1, sp, HA_S1
    F2MUL   sp, HA_S1, sp, HA_S1, sp, HA_J
    F2SUB   sp, HA_Y, sp, HA_Y, sp, HA_S1
    F2ADD   sp, HA_I, s1, 192, s2, 192      # z' = ((Z1 + Z2)^2 - z1z1 - z2z2) h
    F2MUL   sp, HA_I, sp, HA_I, sp, HA_I
    F2SUB   sp, HA_I, sp, HA_I, sp, HA_Z1Z1
    F2SUB   sp, HA_I, sp, HA_I, sp, HA_Z2Z2
    F2MUL   sp, HA_Z, sp, HA_I, sp, HA_U2
    COPY    s3, 0, sp, HA_X, 288
9:  LEAVE   HA_SIZE
END_FUNCTION crypto_bls_g2_add

/* crypto_bls_g2_neg(result, point): (X, -Y, Z) (G2.neg). result may be point. */
LOCAL_FUNCTION crypto_bls_g2_neg
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    COPY    s1, 0, s2, 0, 96
    COPY    s1, 192, s2, 192, 96
    C2      crypto_bls_fp2_neg, s1, 96, s2, 96
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
    ENTER   HM_SIZE
    mv      s1, a0
    mv      s2, a2
    COPY    sp, HM_P, a1, 0, 288
    li      s3, 255
0:  BIT     s2, s3                          # the highest set bit of k
    bnez    t0, 3f
    addi    s3, s3, -1
    bgez    s3, 0b
    SET_ONE sp, HM_ACC                      # k = 0: the point at infinity
    ZERO    sp, HM_ACC + 48, 48
    SET_ONE sp, HM_ACC + 96
    ZERO    sp, HM_ACC + 144, 144
    j       4f
3:  COPY    sp, HM_ACC, sp, HM_P, 288
    addi    s3, s3, -1
    bltz    s3, 4f
1:  C2      crypto_bls_g2_double, sp, HM_ACC, sp, HM_ACC
    BIT     s2, s3
    beqz    t0, 2f
    C3      crypto_bls_g2_add, sp, HM_ACC, sp, HM_ACC, sp, HM_P
2:  addi    s3, s3, -1
    bgez    s3, 1b
4:  COPY    s1, 0, sp, HM_ACC, 288
    LEAVE   HM_SIZE
END_FUNCTION crypto_bls_g2_mul

/* crypto_bls_g2_affine(xy, point): x = X / Z^2, y = Y / Z^3 (G2.toAffine); 0 and 0 at infinity. */
.set HF_ZI, 0
.set HF_ZI2, 96
.set HF_ZI3, 192
.set HF_SIZE, 288
LOCAL_FUNCTION crypto_bls_g2_affine
    ENTER   HF_SIZE
    mv      s1, a0
    mv      s2, a1
    IS_ZERO s2, 192, 96
    bnez    t0, 1f
    ZERO    s1, 0, 192
    LEAVE   HF_SIZE
1:  C2      crypto_bls_fp2_inverse, sp, HF_ZI, s2, 192
    F2MUL   sp, HF_ZI2, sp, HF_ZI, sp, HF_ZI
    F2MUL   sp, HF_ZI3, sp, HF_ZI2, sp, HF_ZI
    F2MUL   s1, 0, s2, 0, sp, HF_ZI2
    F2MUL   s1, 96, s2, 96, sp, HF_ZI3
    LEAVE   HF_SIZE
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
    ENTER   HS_SIZE
    mv      s1, a0
    mv      s2, a1
    IS_ZERO s1, 192, 96
    beqz    t0, 1f
    mv      a0, sp                          # t = |x| P
    mv      a1, s1
    lla     a2, 926f
    call    crypto_bls_g2_mul
    IS_ZERO sp, HS_T + 192, 96              # x P at infinity: psi(P) is not
    beqz    t0, 2f
    lla     s3, 907f                        # c1Psi, then c2Psi
    COPY    sp, HS_E, s1, 192, 48           # e = Zs = conj(Z)
    C2      crypto_bls_fp_neg, sp, HS_E + 48, s1, 240
    F2MUL   sp, HS_A, sp, HS_T + 192, sp, HS_T + 192    # a = Zt^2, b = Zs^2
    F2MUL   sp, HS_B, sp, HS_E, sp, HS_E
    COPY    sp, HS_C, s1, 0, 48             # c = c1Psi conj(X) Zt^2, d = Xt Zs^2
    C2      crypto_bls_fp_neg, sp, HS_C + 48, s1, 48
    F2MUL   sp, HS_C, s3, 0, sp, HS_C
    F2MUL   sp, HS_C, sp, HS_C, sp, HS_A
    F2MUL   sp, HS_D, sp, HS_T, sp, HS_B
    EQUAL   sp, HS_C, sp, HS_D, 96
    bnez    t0, 2f
    F2MUL   sp, HS_A, sp, HS_A, sp, HS_T + 192  # a = Zt^3, b = Zs^3
    F2MUL   sp, HS_B, sp, HS_B, sp, HS_E
    COPY    sp, HS_C, s1, 96, 48            # c = c2Psi conj(Y) Zt^3, d = Yt Zs^3
    C2      crypto_bls_fp_neg, sp, HS_C + 48, s1, 144
    F2MUL   sp, HS_C, s3, 96, sp, HS_C
    F2MUL   sp, HS_C, sp, HS_C, sp, HS_A
    F2MUL   sp, HS_D, sp, HS_T + 96, sp, HS_B
    F2ADD   sp, HS_C, sp, HS_C, sp, HS_D    # c + d = 0
    IS_ZERO sp, HS_C, 96
1:  seqz    t0, t0
    sd      t0, 0(s2)
    LEAVE   HS_SIZE
2:  sd      zero, 0(s2)
    LEAVE   HS_SIZE
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
    ENTER   HU_SIZE
    mv      s1, a0
    mv      s2, a1
    lbu     s3, 0(s1)
    andi    t0, s3, 0x80
    beqz    t0, 8f
    andi    t0, s3, 0x40
    beqz    t0, 2f
    li      t0, 0xC0                        # infinity: 0xC0, then 95 zero bytes
    bne     s3, t0, 8f
    TAIL_ZERO s1, 96
    bnez    t0, 8f
    SET_ONE s2, 0
    ZERO    s2, 48, 48
    SET_ONE s2, 96
    ZERO    s2, 144, 144
    j       9f
2:  COPY    sp, HU_RHS, s1, 0, 96           # x1 with the flag bits cleared, then x0
    lbu     t0, HU_RHS(sp)
    andi    t0, t0, 0x1F
    sb      t0, HU_RHS(sp)
    C2      crypto_bls_fp_from_bytes, sp, HU_X + 48, sp, HU_RHS
    bnez    a0, 8f
    C2      crypto_bls_fp_from_bytes, sp, HU_X, sp, HU_RHS + 48
    bnez    a0, 8f
    F2MUL   sp, HU_RHS, sp, HU_X, sp, HU_X  # x^3 + 4 (1 + u)
    F2MUL   sp, HU_RHS, sp, HU_RHS, sp, HU_X
    ADDR    a0, sp, HU_RHS
    ADDR    a1, sp, HU_RHS
    lla     a2, 901f
    call    crypto_bls_fp2_add
    C2      crypto_bls_fp2_sqrt, sp, HU_Y, sp, HU_RHS
    bnez    a0, 8f
    C2      crypto_bls_fp2_sign_bit, sp, HU_BIT, sp, HU_Y
    ld      t0, HU_BIT(sp)
    srli    t1, s3, 5
    andi    t1, t1, 1
    beq     t0, t1, 3f
    C2      crypto_bls_fp2_neg, sp, HU_Y, sp, HU_Y
3:  SET_ONE sp, HU_Z
    ZERO    sp, HU_Z + 48, 48
    COPY    s2, 0, sp, HU_X, 288
9:  li      a0, CRYPTO_OK
    LEAVE   HU_SIZE
8:  li      a0, CRYPTO_INVALID_ENCODING
    LEAVE   HU_SIZE
END_FUNCTION crypto_bls_g2_uncompress

/* crypto_bls_g2_decode(bytes, point) -> status: G2.uncompress, then the subgroup check (decodeG2Export). */
.set HE_P, 0
.set HE_V, 288
.set HE_SIZE, 304
FUNCTION crypto_bls_g2_decode
    ENTER   HE_SIZE
    mv      s1, a0
    mv      s2, a1
    mv      a1, sp
    call    crypto_bls_g2_uncompress
    bnez    a0, 8f
    C2      crypto_bls_g2_in_subgroup, sp, HE_P, sp, HE_V
    ld      t0, HE_V(sp)
    beqz    t0, 8f
    COPY    s2, 0, sp, HE_P, 288
    li      a0, CRYPTO_OK
    LEAVE   HE_SIZE
8:  li      a0, CRYPTO_INVALID_ENCODING
    LEAVE   HE_SIZE
END_FUNCTION crypto_bls_g2_decode

/* crypto_bls_g2_compress(point, bytes) -> status: G2.compress. */
.set HC_XY, 0
.set HC_BIT, 192
.set HC_SIZE, 208
FUNCTION crypto_bls_g2_compress
    ENTER   HC_SIZE
    mv      s1, a0
    mv      s2, a1
    IS_ZERO s1, 192, 96
    bnez    t0, 1f
    ZERO    s2, 0, 96
    li      t0, 0xC0
    sb      t0, 0(s2)
    j       9f
1:  C2      crypto_bls_g2_affine, sp, HC_XY, s1, 0
    C2      crypto_bls_fp_to_bytes, s2, 0, sp, HC_XY + 48 # c1
    C2      crypto_bls_fp_to_bytes, s2, 48, sp, HC_XY # c0
    C2      crypto_bls_fp2_sign_bit, sp, HC_BIT, sp, HC_XY + 96
    ld      t0, HC_BIT(sp)
    lbu     t1, 0(s2)
    ori     t1, t1, 0x80
    slli    t0, t0, 5
    or      t1, t1, t0
    sb      t1, 0(s2)
9:  li      a0, CRYPTO_OK
    LEAVE   HC_SIZE
END_FUNCTION crypto_bls_g2_compress

/* ---------------------------------------------------------------- Hash to G2 (HashToCurve.lean) */

/* Copy the bytes [rs, rs + rn) to rd; rd and rs end past the bytes, rn ends at 0. Uses t0. */
.macro COPYB rd, rs, rn
    beqz    \rn, 82f
81: lbu     t0, 0(\rs)
    sb      t0, 0(\rd)
    addi    \rs, \rs, 1
    addi    \rd, \rd, 1
    addi    \rn, \rn, -1
    bnez    \rn, 81b
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
/* SHA-256 of the nreg bytes of the BUF data of work s4, digest at s4 + dig. Uses t5. */
.macro XHASH nreg, dig
    ADDR    a0, s4, XW_BUF
    addi    t5, \nreg, 24
    sd      t5, 0(a0)                       # size
    li      t5, 24
    sd      t5, 8(a0)                       # offset
    sd      \nreg, 16(a0)                   # count
    ADDR    a1, s4, \dig
    CALL_GLOBAL crypto_sha256
.endm

LOCAL_FUNCTION crypto_bls_xmd
    ENTER   0
    mv      s1, a0                          # message
    mv      s2, a1                          # dst
    ld      s3, 0(a2)                       # length
    mv      s4, a3                          # work
    mv      s5, a4                          # uniform
    ld      s6, 8(s2)                       # dst offset, count
    ld      s7, 16(s2)
    add     s6, s2, s6
    ADDR    s8, s4, XW_DATA
    li      t0, 255
    bleu    s7, t0, 1f
    lla     t0, 930f                        # a long DST: SHA-256("H2C-OVERSIZE-DST-" || DST)
    ld      t1, 0(t0)
    sd      t1, 0(s8)
    ld      t1, 8(t0)
    sd      t1, 8(s8)
    lbu     t1, 16(t0)
    sb      t1, 16(s8)
    addi    t1, s8, 17
    mv      t2, s6
    mv      t3, s7
    COPYB   t1, t2, t3
    addi    t4, s7, 17
    XHASH   t4, XW_DSTP
    li      s7, 32
    j       2f
1:  addi    t1, s4, XW_DSTP
    mv      t2, s6
    mv      t3, s7
    COPYB   t1, t2, t3
2:  addi    t0, s4, XW_DSTP                 # DST' = DST || I2OSP(len(DST), 1)
    add     t0, t0, s7
    sb      s7, 0(t0)
    ADDR    s7, s7, 1
    sd      s7, XW_DPLEN(s4)
    /* b_0 = H(Z_pad || msg || I2OSP(length, 2) || I2OSP(0, 1) || DST') */
    ZERO    s8, 0, 64
    addi    t1, s8, 64
    ld      t2, 8(s1)
    ld      t3, 16(s1)
    add     t2, s1, t2
    COPYB   t1, t2, t3
    srli    t0, s3, 8
    sb      t0, 0(t1)
    sb      s3, 1(t1)
    sb      zero, 2(t1)
    addi    t1, t1, 3
    addi    t2, s4, XW_DSTP
    ld      t3, XW_DPLEN(s4)
    COPYB   t1, t2, t3
    sub     t4, t1, s8
    XHASH   t4, XW_B0
    /* b_1 = H(b_0 || I2OSP(1, 1) || DST'); b_i = H((b_0 xor b_(i-1)) || I2OSP(i, 1) || DST') */
    COPY    s4, XW_DATA, s4, XW_B0, 32
    li      s9, 1                           # i
    li      s10, 0                          # bytes written
3:  addi    t1, s8, 32
    sb      s9, 0(t1)
    addi    t1, t1, 1
    addi    t2, s4, XW_DSTP
    ld      t3, XW_DPLEN(s4)
    COPYB   t1, t2, t3
    sub     t4, t1, s8
    XHASH   t4, XW_BI
    sub     t3, s3, s10                     # copy min(32, length - written) bytes
    li      t0, 32
    bltu    t3, t0, 5f
    mv      t3, t0
5:  add     t1, s5, s10
    addi    t2, s4, XW_BI
    add     s10, s10, t3
    COPYB   t1, t2, t3
    bgeu    s10, s3, 9f
    ADDR    s9, s9, 1
    .irp off, 0, 8, 16, 24
    ld      t0, XW_B0 + \off(s4)
    ld      t1, XW_BI + \off(s4)
    xor     t0, t0, t1
    sd      t0, \off(s8)
    .endr
    j       3b
9:  li      a0, CRYPTO_OK
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
    ENTER   F64_SIZE
    mv      s1, a0
    mv      s2, a1
    .irp i, 0, 1, 2, 3, 4, 5
    LOAD_BE64 t0, s2, 56-8*\i, t1           # lo: bytes 16 to 63, least significant last
    sd      t0, F64_LO+8*\i(sp)
    .endr
    LOAD_BE64 t0, s2, 8, t1                 # hi: bytes 0 to 15
    sd      t0, F64_HI(sp)
    LOAD_BE64 t0, s2, 0, t1
    sd      t0, F64_HI+8(sp)
    ZERO    sp, F64_HI + 16, 32
    lla     a2, 900f
    ADDR    a2, a2, BLS_FP_RECORD_R2
    ADDR    a0, sp, F64_A
    ADDR    a1, sp, F64_LO
    call    crypto_bls_fp_mul
    lla     a2, 925f
    ADDR    a0, sp, F64_LO
    ADDR    a1, sp, F64_HI
    call    crypto_bls_fp_mul
    FADD    s1, 0, sp, F64_A, sp, F64_LO
    LEAVE   F64_SIZE
END_FUNCTION crypto_bls_fp_from_bytes64

/*
 * crypto_bls_fp2_sgn0(bit, a): sgn0 of RFC 9380 section 4.1 for Fp2
 * (sgn0Fp2): s0 or (c0 = 0 and s1), with si the parity of ci, as the u64 1 or 0.
 */
.set SG_C, 0
.set SG_SIZE, 48
LOCAL_FUNCTION crypto_bls_fp2_sgn0
    ENTER   SG_SIZE
    mv      s1, a0
    mv      s2, a1
    C2      crypto_bls_fp_canonical, sp, SG_C, s2, 0
    ld      s3, SG_C(sp)
    andi    s3, s3, 1                       # s0
    IS_ZERO sp, SG_C, 48
    seqz    s4, t0                          # z0
    C2      crypto_bls_fp_canonical, sp, SG_C, s2, 48
    ld      t0, SG_C(sp)
    and     t0, t0, s4                      # z0 and s1
    or      t0, t0, s3
    sd      t0, 0(s1)
    LEAVE   SG_SIZE
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
    ENTER   SW_SIZE
    mv      s1, a0
    mv      s2, a1
    lla     s3, 910f                        # A', then B', then Z
    F2MUL   sp, SW_U2, s2, 0, s2, 0         # u2 = u u
    F2MUL   sp, SW_ZU2, s3, 192, sp, SW_U2  # zu2 = Z u2
    F2MUL   sp, SW_DEN, sp, SW_ZU2, sp, SW_ZU2
    F2ADD   sp, SW_DEN, sp, SW_DEN, sp, SW_ZU2
    IS_ZERO sp, SW_DEN, 96
    bnez    t0, 1f
    F2MUL   sp, SW_T, s3, 192, s3, 0        # x1 = B' / (Z A')
    C2      crypto_bls_fp2_inverse, sp, SW_T, sp, SW_T
    F2MUL   sp, SW_X1, s3, 96, sp, SW_T
    j       2f
1:  C2      crypto_bls_fp2_neg, sp, SW_S, s3, 96 # x1 = (-B' / A') (1 + 1 / denom)
    C2      crypto_bls_fp2_inverse, sp, SW_T, s3, 0
    F2MUL   sp, SW_S, sp, SW_S, sp, SW_T
    C2      crypto_bls_fp2_inverse, sp, SW_T, sp, SW_DEN
    ADDR    a0, sp, SW_T
    ADDR    a1, sp, SW_T
    lla     a2, 900f
    addi    a2, a2, BLS_FP_RECORD_ONE
    call    crypto_bls_fp_add               # 1 + c0; c1 unchanged
    F2MUL   sp, SW_X1, sp, SW_S, sp, SW_T
2:  COPY    sp, SW_X, sp, SW_X1, 96
    C2      crypto_bls_swu_g, sp, SW_GX, sp, SW_X # gx1 = x1^3 + A' x1 + B'
    C2      crypto_bls_fp2_sqrt, sp, SW_Y, sp, SW_GX
    beqz    a0, 3f
    F2MUL   sp, SW_X, sp, SW_ZU2, sp, SW_X1 # x2 = zu2 x1
    C2      crypto_bls_swu_g, sp, SW_GX, sp, SW_X
    C2      crypto_bls_fp2_sqrt, sp, SW_Y, sp, SW_GX
    bnez    a0, 8f
3:  C2      crypto_bls_fp2_sgn0, sp, SW_BIT, s2, 0
    C2      crypto_bls_fp2_sgn0, sp, SW_BIT + 8, sp, SW_Y
    ld      t0, SW_BIT(sp)
    ld      t1, SW_BIT + 8(sp)
    beq     t0, t1, 4f
    C2      crypto_bls_fp2_neg, sp, SW_Y, sp, SW_Y
4:  COPY    s1, 0, sp, SW_X, 192
    li      a0, CRYPTO_OK
    LEAVE   SW_SIZE
8:  li      a0, CRYPTO_INVALID_ENCODING
    LEAVE   SW_SIZE
END_FUNCTION crypto_bls_simple_swu

/* crypto_bls_swu_g(result, x): x^3 + A' x + B' on E2'. */
.set SV_T, 0
.set SV_SIZE, 96
LOCAL_FUNCTION crypto_bls_swu_g
    ENTER   SV_SIZE
    mv      s1, a0
    mv      s2, a1
    lla     s3, 910f
    F2MUL   s1, 0, s2, 0, s2, 0
    F2MUL   s1, 0, s1, 0, s2, 0
    F2MUL   sp, SV_T, s3, 0, s2, 0
    F2ADD   s1, 0, s1, 0, sp, SV_T
    F2ADD   s1, 0, s1, 0, s3, 96
    LEAVE   SV_SIZE
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
    ENTER   IM_SIZE
    mv      s1, a0
    mv      s2, a1
    lla     s3, 913f                        # k10..k13, then k20, k21, then k30..k33, then k40..k42
    F2MUL   sp, IM_X2, s2, 0, s2, 0
    F2MUL   sp, IM_X3, sp, IM_X2, s2, 0
    F2MUL   sp, IM_XN, s3, 288, sp, IM_X3   # x_num = k13 x^3 + k12 x^2 + k11 x + k10
    F2MUL   sp, IM_T, s3, 192, sp, IM_X2
    F2ADD   sp, IM_XN, sp, IM_XN, sp, IM_T
    F2MUL   sp, IM_T, s3, 96, s2, 0
    F2ADD   sp, IM_XN, sp, IM_XN, sp, IM_T
    F2ADD   sp, IM_XN, sp, IM_XN, s3, 0
    F2MUL   sp, IM_T, s3, 480, s2, 0        # x_den = x^2 + k21 x + k20
    F2ADD   sp, IM_XD, sp, IM_X2, sp, IM_T
    F2ADD   sp, IM_XD, sp, IM_XD, s3, 384
    ADDR    s4, s3, 576
    F2MUL   sp, IM_YN, s4, 288, sp, IM_X3   # y_num = k33 x^3 + k32 x^2 + k31 x + k30
    F2MUL   sp, IM_T, s4, 192, sp, IM_X2
    F2ADD   sp, IM_YN, sp, IM_YN, sp, IM_T
    F2MUL   sp, IM_T, s4, 96, s2, 0
    F2ADD   sp, IM_YN, sp, IM_YN, sp, IM_T
    F2ADD   sp, IM_YN, sp, IM_YN, s4, 0
    ADDR    s4, s3, 960
    F2MUL   sp, IM_T, s4, 192, sp, IM_X2    # y_den = x^3 + k42 x^2 + k41 x + k40
    F2ADD   sp, IM_YD, sp, IM_X3, sp, IM_T
    F2MUL   sp, IM_T, s4, 96, s2, 0
    F2ADD   sp, IM_YD, sp, IM_YD, sp, IM_T
    F2ADD   sp, IM_YD, sp, IM_YD, s4, 0
    IS_ZERO sp, IM_XD, 96
    beqz    t0, 1f
    IS_ZERO sp, IM_YD, 96
    beqz    t0, 1f
    C2      crypto_bls_fp2_inverse, sp, IM_T, sp, IM_XD
    F2MUL   s1, 0, sp, IM_XN, sp, IM_T
    F2MUL   sp, IM_YN, s2, 96, sp, IM_YN
    C2      crypto_bls_fp2_inverse, sp, IM_T, sp, IM_YD
    F2MUL   s1, 96, sp, IM_YN, sp, IM_T
    SET_ONE s1, 192
    ZERO    s1, 240, 48
    LEAVE   IM_SIZE
1:  SET_ONE s1, 0                           # the point at infinity
    ZERO    s1, 48, 48
    SET_ONE s1, 96
    ZERO    s1, 144, 144
    LEAVE   IM_SIZE
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
    ENTER   PS_SIZE
    mv      s1, a0
    mv      s2, a1
    IS_ZERO s2, 192, 96
    bnez    t0, 1f
    COPY    s1, 0, s2, 0, 288
    LEAVE   PS_SIZE
1:  C2      crypto_bls_g2_affine, sp, PS_XY, s2, 0
    lla     s3, 907f                        # c1Psi, then c2Psi
    COPY    sp, PS_T, sp, PS_XY, 48         # conj(x)
    C2      crypto_bls_fp_neg, sp, PS_T + 48, sp, PS_XY + 48
    F2MUL   s1, 0, s3, 0, sp, PS_T
    COPY    sp, PS_T, sp, PS_XY + 96, 48    # conj(y)
    C2      crypto_bls_fp_neg, sp, PS_T + 48, sp, PS_XY + 144
    F2MUL   s1, 96, s3, 96, sp, PS_T
    SET_ONE s1, 192
    ZERO    s1, 240, 48
    LEAVE   PS_SIZE
END_FUNCTION crypto_bls_psi

/*
 * crypto_bls_psi2(result, point): psi2 of RFC 9380 appendix G.3 (psi2):
 * the affine (c1Psi2 x, -y, 1); the point at infinity stays. result may be
 * point.
 */
.set P2_XY, 0
.set P2_SIZE, 192
LOCAL_FUNCTION crypto_bls_psi2
    ENTER   P2_SIZE
    mv      s1, a0
    mv      s2, a1
    IS_ZERO s2, 192, 96
    bnez    t0, 1f
    COPY    s1, 0, s2, 0, 288
    LEAVE   P2_SIZE
1:  C2      crypto_bls_g2_affine, sp, P2_XY, s2, 0
    lla     a2, 908f                        # c1Psi2, in Fp
    ADDR    a0, s1, 0
    ADDR    a1, sp, P2_XY
    call    crypto_bls_fp2_mul_fp
    C2      crypto_bls_fp2_neg, s1, 96, sp, P2_XY + 96
    SET_ONE s1, 192
    ZERO    s1, 240, 48
    LEAVE   P2_SIZE
END_FUNCTION crypto_bls_psi2

/* crypto_bls_g2_mul_neg_x(result, point): x * point, with the negative BLS parameter x = -|x| (mulNegX). */
LOCAL_FUNCTION crypto_bls_g2_mul_neg_x
    ENTER   0
    mv      s1, a0
    lla     a2, 926f
    call    crypto_bls_g2_mul
    C2      crypto_bls_g2_neg, s1, 0, s1, 0
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
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    C2      crypto_bls_g2_mul_neg_x, s3, CC_T1, s2, 0 # t1 = x P
    C2      crypto_bls_psi, s3, CC_T2, s2, 0 # t2 = psi(P)
    C2      crypto_bls_g2_double, s3, CC_T3, s2, 0 # t3 = psi2(2 P)
    C2      crypto_bls_psi2, s3, CC_T3, s3, CC_T3
    C2      crypto_bls_g2_neg, s3, CC_T4, s3, CC_T2 # t3 = t3 - t2
    C3      crypto_bls_g2_add, s3, CC_T3, s3, CC_T3, s3, CC_T4
    C3      crypto_bls_g2_add, s3, CC_T2, s3, CC_T1, s3, CC_T2 # t2 = t1 + t2
    C2      crypto_bls_g2_mul_neg_x, s3, CC_T2, s3, CC_T2 # t2 = x t2
    C3      crypto_bls_g2_add, s3, CC_T3, s3, CC_T3, s3, CC_T2 # t3 = t3 + t2
    C2      crypto_bls_g2_neg, s3, CC_T1, s3, CC_T1 # t3 = t3 - t1
    C3      crypto_bls_g2_add, s3, CC_T3, s3, CC_T3, s3, CC_T1
    C2      crypto_bls_g2_neg, s3, CC_T4, s2, 0 # result = t3 - P
    C3      crypto_bls_g2_add, s1, 0, s3, CC_T3, s3, CC_T4
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
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2                          # work
    mv      s4, a3                          # point
    li      t0, 256
    sd      t0, HW_LEN(s3)
    mv      a0, s1                          # uniform = expand_message_xmd(msg, DST, 256)
    mv      a1, s2
    ADDR    a2, s3, HW_LEN
    ADDR    a3, s3, HW_XMD
    ADDR    a4, s3, HW_U
    call    crypto_bls_xmd
    C2      crypto_bls_fp_from_bytes64, s3, HW_U0, s3, HW_U # hash_to_field: u0, u1
    C2      crypto_bls_fp_from_bytes64, s3, HW_U0 + 48, s3, HW_U + 64
    C2      crypto_bls_fp_from_bytes64, s3, HW_U1, s3, HW_U + 128
    C2      crypto_bls_fp_from_bytes64, s3, HW_U1 + 48, s3, HW_U + 192
    C2      crypto_bls_simple_swu, s3, HW_XY0, s3, HW_U0
    bnez    a0, 9f
    C2      crypto_bls_simple_swu, s3, HW_XY1, s3, HW_U1
    bnez    a0, 9f
    C2      crypto_bls_iso_map_g2, s3, HW_Q0, s3, HW_XY0
    C2      crypto_bls_iso_map_g2, s3, HW_Q1, s3, HW_XY1
    C3      crypto_bls_g2_add, s3, HW_Q0, s3, HW_Q0, s3, HW_Q1
    C3      crypto_bls_clear_cofactor, s4, 0, s3, HW_Q0, s3, HW_CC
    li      a0, CRYPTO_OK
9:  LEAVE   0
END_FUNCTION crypto_bls_hash_to_g2_point

/*
 * crypto_bls_expand_message_xmd(message, dst, length, scratch, uniform) ->
 * status: checks length, scratch and uniform, then crypto_bls_xmd.
 */
FUNCTION crypto_bls_expand_message_xmd
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      s5, a4
    ld      s6, 0(s3)                       # length
    li      t0, CRYPTO_BLS_XMD_MAX_LENGTH
    bgtu    s6, t0, 7f
    ld      t0, CRYPTO_BYTES_COUNT(s1)      # scratch: CRYPTO_BLS_H2C_SCRATCH + message + dst
    ld      t1, CRYPTO_BYTES_COUNT(s2)
    add     t0, t0, t1
    li      t1, CRYPTO_BLS_H2C_SCRATCH
    add     t0, t0, t1
    ld      t1, 0(s4)
    bltu    t1, t0, 8f
    addi    t0, s6, CRYPTO_BYTES_FIXED      # uniform: 24 + length
    ld      t1, 0(s5)
    bltu    t1, t0, 8f
    mv      a0, s1
    mv      a1, s2
    mv      a2, s3
    ADDR    a3, s4, 8
    ADDR    a4, s5, CRYPTO_BYTES_FIXED
    call    crypto_bls_xmd
    li      t0, CRYPTO_BYTES_FIXED
    sd      t0, CRYPTO_BYTES_OFFSET(s5)
    sd      s6, CRYPTO_BYTES_COUNT(s5)
    li      a0, CRYPTO_OK
    LEAVE   0
7:  li      a0, CRYPTO_BLS_XMD_LENGTH
    LEAVE   0
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
END_FUNCTION crypto_bls_expand_message_xmd

/*
 * crypto_bls_hash_to_g2(message, dst, scratch, point) -> status: checks
 * scratch, hashes, and writes the affine coordinates (hashToG2Export).
 */
.set HG_XY, 0
.set HG_SIZE, 192
FUNCTION crypto_bls_hash_to_g2
    ENTER   HG_SIZE
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    ld      t0, CRYPTO_BYTES_COUNT(s1)
    ld      t1, CRYPTO_BYTES_COUNT(s2)
    add     t0, t0, t1
    li      t1, CRYPTO_BLS_H2C_SCRATCH
    add     t0, t0, t1
    ld      t1, 0(s3)
    bltu    t1, t0, 8f
    ADDR    s5, s3, 8                       # work
    mv      a0, s1
    mv      a1, s2
    mv      a2, s5
    ADDR    a3, s5, HW_P
    call    crypto_bls_hash_to_g2_point
    bnez    a0, 9f
    IS_ZERO s5, HW_P + 192, 96
    beqz    t0, 7f
    C2      crypto_bls_g2_affine, sp, HG_XY, s5, HW_P
    C2      crypto_bls_fp_to_bytes, s4, 0, sp, HG_XY
    C2      crypto_bls_fp_to_bytes, s4, 48, sp, HG_XY + 48
    C2      crypto_bls_fp_to_bytes, s4, 96, sp, HG_XY + 96
    C2      crypto_bls_fp_to_bytes, s4, 144, sp, HG_XY + 144
    li      a0, CRYPTO_OK
9:  LEAVE   HG_SIZE
7:  li      a0, CRYPTO_BLS_POINT_AT_INFINITY
    LEAVE   HG_SIZE
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   HG_SIZE
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
    LOAD_BE64 a2, a1, 24, t6
    LOAD_BE64 a3, a1, 16, t6
    LOAD_BE64 a4, a1, 8, t6
    LOAD_BE64 a5, a1, 0, t6
    or      t0, a2, a3
    or      t1, a4, a5
    or      t0, t0, t1
    beqz    t0, 8f
    lla     t4, 924f                        # below r?
    li      t0, 0
    ld      t1, 0(t4)
    BORROWOF a2, t1, t0, t2, t3
    ld      t1, 8(t4)
    BORROWOF a3, t1, t0, t2, t3
    ld      t1, 16(t4)
    BORROWOF a4, t1, t0, t2, t3
    ld      t1, 24(t4)
    BORROWOF a5, t1, t0, t2, t3
    beqz    t0, 8f
    sd      a2, 0(a0)
    sd      a3, 8(a0)
    sd      a4, 16(a0)
    sd      a5, 24(a0)
    li      a0, CRYPTO_OK
    ret
8:  li      a0, CRYPTO_INVALID_PRIVATE_KEY
    ret
END_FUNCTION crypto_bls_secret_key

/* crypto_bls_sk_to_pk(secret_key, public_key) -> status: skToPk. */
.set SP_K, 0
.set SP_P, 32
.set SP_SIZE, 176
FUNCTION crypto_bls_sk_to_pk
    ENTER   SP_SIZE
    mv      s1, a0
    mv      s2, a1
    ADDR    a0, sp, SP_K
    mv      a1, s1
    call    crypto_bls_secret_key
    bnez    a0, 9f
    lla     t0, 904f                        # the generator of G1: (x, y, 1)
    COPY    sp, SP_P, t0, 0, 96
    SET_ONE sp, SP_P + 96
    C3      crypto_bls_g1_mul, sp, SP_P, sp, SP_P, sp, SP_K
    G2      crypto_bls_g1_compress, sp, SP_P, s2, 0
    li      a0, CRYPTO_OK
9:  LEAVE   SP_SIZE
END_FUNCTION crypto_bls_sk_to_pk

/*
 * crypto_bls_sign(secret_key, message, scratch, signature) -> status: sign:
 * the compressed SK * H(message), H the hash to G2 under the DST.
 * scratch: Q at work + 0, the hash work at work + 288.
 */
.set SN_K, 0
.set SN_SIZE, 32
FUNCTION crypto_bls_sign
    ENTER   SN_SIZE
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      a0, sp
    mv      a1, s1
    call    crypto_bls_secret_key
    bnez    a0, 9f
    ld      t0, CRYPTO_BYTES_COUNT(s2)
    li      t1, CRYPTO_BLS_SCRATCH
    add     t0, t0, t1
    ld      t1, 0(s3)
    bltu    t1, t0, 8f
    ADDR    s5, s3, 8                       # work
    mv      a0, s2
    lla     a1, 931f                        # the DST, as a ByteList
    ADDR    a2, s5, 288
    mv      a3, s5
    call    crypto_bls_hash_to_g2_point
    bnez    a0, 9f
    mv      a0, s5
    mv      a1, s5
    mv      a2, sp
    call    crypto_bls_g2_mul
    G2      crypto_bls_g2_compress, s5, 0, s4, 0
    li      a0, CRYPTO_OK
9:  LEAVE   SN_SIZE
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   SN_SIZE
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
    ENTER   KV_SIZE
    mv      s1, a0
    mv      s2, a1
    mv      a1, sp
    call    crypto_bls_g1_uncompress
    bnez    a0, 8f
    IS_ZERO sp, KV_P + 96, 48
    beqz    t0, 8f
    C2      crypto_bls_g1_in_subgroup, sp, KV_P, sp, KV_V
    ld      t0, KV_V(sp)
    beqz    t0, 8f
    COPY    s2, 0, sp, KV_P, 144
    li      a0, CRYPTO_OK
    LEAVE   KV_SIZE
8:  li      a0, CRYPTO_INVALID_PUBLIC_KEY
    LEAVE   KV_SIZE
END_FUNCTION crypto_bls_key_validate_point

/* crypto_bls_key_validate(public_key, valid) -> status: keyValidate, as 1 or 0. */
.set KW_P, 0
.set KW_SIZE, 144
FUNCTION crypto_bls_key_validate
    ENTER   KW_SIZE
    mv      s2, a1
    mv      a1, sp
    call    crypto_bls_key_validate_point
    addi    t0, a0, -CRYPTO_OK
    seqz    t0, t0
    sd      t0, 0(s2)
    li      a0, CRYPTO_OK
    LEAVE   KW_SIZE
END_FUNCTION crypto_bls_key_validate

/* crypto_bls_aggregate(signatures, signature) -> status: aggregate. */
.set AG_ACC, 0
.set AG_P, 288
.set AG_SIZE, 576
FUNCTION crypto_bls_aggregate
    ENTER   AG_SIZE
    mv      s1, a0
    mv      s2, a1
    ld      s3, CRYPTO_BLS_LIST_OFFSET(s1)  # offset, count
    ld      s4, CRYPTO_BLS_LIST_COUNT(s1)
    beqz    s4, 7f
    add     s3, s1, s3
    SET_ONE sp, AG_ACC                      # the point at infinity
    ZERO    sp, AG_ACC + 48, 48
    SET_ONE sp, AG_ACC + 96
    ZERO    sp, AG_ACC + 144, 144
1:  mv      a0, s3
    ADDR    a1, sp, AG_P
    call    crypto_bls_g2_uncompress
    bnez    a0, 8f
    C3      crypto_bls_g2_add, sp, AG_ACC, sp, AG_ACC, sp, AG_P
    ADDR    s3, s3, 96
    addi    s4, s4, -1
    bnez    s4, 1b
    G2      crypto_bls_g2_compress, sp, AG_ACC, s2, 0
    li      a0, CRYPTO_OK
    LEAVE   AG_SIZE
7:  li      a0, CRYPTO_EMPTY_LIST
    LEAVE   AG_SIZE
8:  li      a0, CRYPTO_INVALID_SIGNATURE
    LEAVE   AG_SIZE
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
    ENTER   AK_SIZE
    mv      s1, a0
    mv      s2, a1
    ld      s3, CRYPTO_BLS_LIST_OFFSET(s1)  # offset, count
    ld      s4, CRYPTO_BLS_LIST_COUNT(s1)
    beqz    s4, 7f
    add     s3, s1, s3
    SET_ONE sp, AK_ACC
    SET_ONE sp, AK_ACC + 48
    ZERO    sp, AK_ACC + 96, 48
1:  mv      a0, s3
    ADDR    a1, sp, AK_P
    call    crypto_bls_key_validate_point
    bnez    a0, 9f
    G3      crypto_bls_g1_add, sp, AK_ACC, sp, AK_P, sp, AK_ACC
    ADDR    s3, s3, 48
    addi    s4, s4, -1
    bnez    s4, 1b
    COPY    s2, 0, sp, AK_ACC, 144
    li      a0, CRYPTO_OK
9:  LEAVE   AK_SIZE
7:  li      a0, CRYPTO_EMPTY_LIST
    LEAVE   AK_SIZE
END_FUNCTION crypto_bls_aggregate_keys

/* crypto_bls_eth_aggregate_pubkeys(public_keys, public_key) -> status: ethAggregatePubkeys. */
.set EA_P, 0
.set EA_SIZE, 144
FUNCTION crypto_bls_eth_aggregate_pubkeys
    ENTER   EA_SIZE
    mv      s2, a1
    mv      a1, sp
    call    crypto_bls_aggregate_keys
    bnez    a0, 9f
    G2      crypto_bls_g1_compress, sp, EA_P, s2, 0
    li      a0, CRYPTO_OK
9:  LEAVE   EA_SIZE
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
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    F2ADD   s1, 0, s2, 0, s3, 0
    F2ADD   s1, 96, s2, 96, s3, 96
    F2ADD   s1, 192, s2, 192, s3, 192
    LEAVE   0
END_FUNCTION crypto_bls_fp6_add

/* crypto_bls_fp6_sub(result, a, b): a - b (Fp6.sub). result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp6_sub
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    F2SUB   s1, 0, s2, 0, s3, 0
    F2SUB   s1, 96, s2, 96, s3, 96
    F2SUB   s1, 192, s2, 192, s3, 192
    LEAVE   0
END_FUNCTION crypto_bls_fp6_sub

/* crypto_bls_fp6_neg(result, a): -a (Fp6.neg). result may be a. */
LOCAL_FUNCTION crypto_bls_fp6_neg
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    C2      crypto_bls_fp2_neg, s1, 0, s2, 0
    C2      crypto_bls_fp2_neg, s1, 96, s2, 96
    C2      crypto_bls_fp2_neg, s1, 192, s2, 192
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
    ENTER   M6_SIZE
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    F2MUL   sp, M6_T0, s2, 0, s3, 0
    F2MUL   sp, M6_T1, s2, 96, s3, 96
    F2MUL   sp, M6_T2, s2, 192, s3, 192
    F2ADD   sp, M6_S, s2, 96, s2, 192       # c0
    F2ADD   sp, M6_U, s3, 96, s3, 192
    F2MUL   sp, M6_C0, sp, M6_S, sp, M6_U
    F2SUB   sp, M6_C0, sp, M6_C0, sp, M6_T1
    F2SUB   sp, M6_C0, sp, M6_C0, sp, M6_T2
    F2NR    sp, M6_C0, sp, M6_C0
    F2ADD   sp, M6_C0, sp, M6_C0, sp, M6_T0
    F2ADD   sp, M6_S, s2, 0, s2, 96         # c1
    F2ADD   sp, M6_U, s3, 0, s3, 96
    F2MUL   sp, M6_C1, sp, M6_S, sp, M6_U
    F2SUB   sp, M6_C1, sp, M6_C1, sp, M6_T0
    F2SUB   sp, M6_C1, sp, M6_C1, sp, M6_T1
    F2NR    sp, M6_U, sp, M6_T2
    F2ADD   sp, M6_C1, sp, M6_C1, sp, M6_U
    F2ADD   sp, M6_S, s2, 0, s2, 192        # c2
    F2ADD   sp, M6_U, s3, 0, s3, 192
    F2MUL   sp, M6_C2, sp, M6_S, sp, M6_U
    F2SUB   sp, M6_C2, sp, M6_C2, sp, M6_T0
    F2SUB   sp, M6_C2, sp, M6_C2, sp, M6_T2
    F2ADD   sp, M6_C2, sp, M6_C2, sp, M6_T1
    COPY    s1, 0, sp, M6_C0, 288
    LEAVE   M6_SIZE
END_FUNCTION crypto_bls_fp6_mul

/* crypto_bls_fp6_mul_v(result, a): a v = (xi a2, a0, a1) (Fp6.mulByV). result may be a. */
.set MV_T, 0
.set MV_SIZE, 96
LOCAL_FUNCTION crypto_bls_fp6_mul_v
    ENTER   MV_SIZE
    mv      s1, a0
    mv      s2, a1
    F2NR    sp, MV_T, s2, 192
    COPY    s1, 192, s2, 96, 96
    COPY    s1, 96, s2, 0, 96
    COPY    s1, 0, sp, MV_T, 96
    LEAVE   MV_SIZE
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
    ENTER   N6_SIZE
    mv      s1, a0
    mv      s2, a1
    F2MUL   sp, N6_T0, s2, 0, s2, 0         # t0
    F2MUL   sp, N6_U, s2, 96, s2, 192
    F2NR    sp, N6_U, sp, N6_U
    F2SUB   sp, N6_T0, sp, N6_T0, sp, N6_U
    F2MUL   sp, N6_T1, s2, 192, s2, 192     # t1
    F2NR    sp, N6_T1, sp, N6_T1
    F2MUL   sp, N6_U, s2, 0, s2, 96
    F2SUB   sp, N6_T1, sp, N6_T1, sp, N6_U
    F2MUL   sp, N6_T2, s2, 96, s2, 96       # t2
    F2MUL   sp, N6_U, s2, 0, s2, 192
    F2SUB   sp, N6_T2, sp, N6_T2, sp, N6_U
    F2MUL   sp, N6_D, s2, 0, sp, N6_T0      # det
    F2MUL   sp, N6_U, s2, 192, sp, N6_T1
    F2NR    sp, N6_U, sp, N6_U
    F2ADD   sp, N6_D, sp, N6_D, sp, N6_U
    F2MUL   sp, N6_U, s2, 96, sp, N6_T2
    F2NR    sp, N6_U, sp, N6_U
    F2ADD   sp, N6_D, sp, N6_D, sp, N6_U
    C2      crypto_bls_fp2_inverse, sp, N6_D, sp, N6_D
    F2MUL   s1, 0, sp, N6_T0, sp, N6_D
    F2MUL   s1, 96, sp, N6_T1, sp, N6_D
    F2MUL   s1, 192, sp, N6_T2, sp, N6_D
    LEAVE   N6_SIZE
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
    ENTER   M12_SIZE
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    F6MUL   sp, M12_T0, s2, 0, s3, 0
    F6MUL   sp, M12_T1, s2, 288, s3, 288
    F6ADD   sp, M12_SA, s2, 0, s2, 288
    F6ADD   sp, M12_SB, s3, 0, s3, 288
    F6MUL   sp, M12_SA, sp, M12_SA, sp, M12_SB
    F6SUB   sp, M12_SA, sp, M12_SA, sp, M12_T0
    F6SUB   sp, M12_SA, sp, M12_SA, sp, M12_T1
    C2      crypto_bls_fp6_mul_v, sp, M12_T1, sp, M12_T1
    F6ADD   s1, 0, sp, M12_T0, sp, M12_T1
    COPY    s1, 288, sp, M12_SA, 288
    LEAVE   M12_SIZE
END_FUNCTION crypto_bls_fp12_mul

/* crypto_bls_fp12_conjugate(result, a): (a0, -a1) (Fp12.conjugate). result may be a. */
LOCAL_FUNCTION crypto_bls_fp12_conjugate
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    COPY    s1, 0, s2, 0, 288
    C2      crypto_bls_fp6_neg, s1, 288, s2, 288
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
    ENTER   N12_SIZE
    mv      s1, a0
    mv      s2, a1
    F6MUL   sp, N12_N, s2, 0, s2, 0
    F6MUL   sp, N12_U, s2, 288, s2, 288
    C2      crypto_bls_fp6_mul_v, sp, N12_U, sp, N12_U
    F6SUB   sp, N12_N, sp, N12_N, sp, N12_U
    C2      crypto_bls_fp6_inverse, sp, N12_N, sp, N12_N
    F6MUL   sp, N12_U, s2, 288, sp, N12_N
    C2      crypto_bls_fp6_neg, s1, 288, sp, N12_U
    F6MUL   s1, 0, s2, 0, sp, N12_N
    LEAVE   N12_SIZE
END_FUNCTION crypto_bls_fp12_inverse

/*
 * crypto_bls_fp12_frobenius(result, a): a^p (Fp12.frobenius): conj(a_k)
 * g^k, with a_k the coefficient of w^k and g the frobeniusCoeff. result may
 * be a.
 */
.set FR_T, 0
.set FR_SIZE, 96
LOCAL_FUNCTION crypto_bls_fp12_frobenius
    ENTER   FR_SIZE
    mv      s1, a0
    mv      s2, a1
    lla     s3, 909f                        # g^0, ..., g^5
    li      s4, 0                           # component: offset in a, then power of g
1:  lla     t0, 932f
    slli    t1, s4, 2
    add     t0, t0, t1
    lhu     s5, 0(t0)                       # offset of a_k in a
    lhu     s6, 2(t0)                       # k
    add     t1, s2, s5
    COPY    sp, FR_T, t1, 0, 48             # conj: c0, then -c1
    ADDR    a0, sp, FR_T + 48
    addi    a1, t1, 48
    call    crypto_bls_fp_neg
    li      t0, 96
    mul     a2, s6, t0
    add     a2, a2, s3
    add     a0, s1, s5
    ADDR    a1, sp, FR_T
    call    crypto_bls_fp2_mul
    ADDR    s4, s4, 1
    li      t0, 6
    bltu    s4, t0, 1b
    LEAVE   FR_SIZE
END_FUNCTION crypto_bls_fp12_frobenius

/*
 * crypto_bls_fp12_pow(result, base, exponent): base^e (Fp12.powNat), with e
 * the u64 at exponent, a public value. result must not be base.
 */
LOCAL_FUNCTION crypto_bls_fp12_pow
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    ld      s3, 0(a2)
    SET_ONE s1, 0
    ZERO    s1, 48, 528
    beqz    s3, 9f
    li      s4, 63                          # the top set bit
6:  srl     t0, s3, s4
    bnez    t0, 1f
    addi    s4, s4, -1
    j       6b
1:  F12MUL  s1, 0, s1, 0, s1, 0
    srl     t0, s3, s4
    andi    t0, t0, 1
    beqz    t0, 2f
    F12MUL  s1, 0, s1, 0, s2, 0
2:  addi    s4, s4, -1
    bgez    s4, 1b
9:  LEAVE   0
END_FUNCTION crypto_bls_fp12_pow

/* ---------------------------------------------------------------- Pairing (Pairing.lean) */

/* The line value c0 + c2 w^2 + c3 w^3 (lineValue) at rd + od, from the Fp2 values at rs + c0, c2 and c3. */
.macro LINE rd, od, rs, c0, c2, c3
    COPY    \rd, \od, \rs, \c0, 96
    COPY    \rd, \od + 96, \rs, \c2, 96
    ZERO    \rd, \od + 192, 192
    COPY    \rd, \od + 384, \rs, \c3, 96
    ZERO    \rd, \od + 480, 96
.endm

/*
 * crypto_bls_miller_double(f, t, p, work): millerDouble: with T the G2
 * point at t and P = (xp, yp) at p, f = f^2 l with l the tangent line at T,
 * then T = 2 T. work holds 1248 bytes: the line, then the temporaries.
 */
.set MD_XX, 576
.set MD_ZZ, 672
.set MD_A, 768
.set MD_C0, 864
.set MD_C2, 960
.set MD_C3, 1056
.set MD_U, 1152
LOCAL_FUNCTION crypto_bls_miller_double
    ENTER   0
    mv      s1, a0                          # f
    mv      s2, a1                          # T
    mv      s3, a2                          # P
    mv      s4, a3                          # work
    F2MUL   s4, MD_XX, s2, 0, s2, 0         # xx = X^2, zz = Z^2
    F2MUL   s4, MD_ZZ, s2, 192, s2, 192
    F2ADD   s4, MD_A, s4, MD_XX, s4, MD_XX  # 3 xx
    F2ADD   s4, MD_A, s4, MD_A, s4, MD_XX
    F2MUL   s4, MD_C0, s4, MD_A, s2, 0      # c0 = 3 xx X - 2 Y^2
    F2MUL   s4, MD_U, s2, 96, s2, 96
    F2ADD   s4, MD_U, s4, MD_U, s4, MD_U
    F2SUB   s4, MD_C0, s4, MD_C0, s4, MD_U
    F2MUL   s4, MD_C2, s4, MD_A, s4, MD_ZZ  # c2 = -(3 xx zz xp)
    C3      crypto_bls_fp2_mul_fp, s4, MD_C2, s4, MD_C2, s3, 0
    C2      crypto_bls_fp2_neg, s4, MD_C2, s4, MD_C2
    F2ADD   s4, MD_C3, s2, 96, s2, 96       # c3 = 2 Y zz Z yp
    F2MUL   s4, MD_C3, s4, MD_C3, s4, MD_ZZ
    F2MUL   s4, MD_C3, s4, MD_C3, s2, 192
    C3      crypto_bls_fp2_mul_fp, s4, MD_C3, s4, MD_C3, s3, 48
    C2      crypto_bls_g2_double, s2, 0, s2, 0
    F12MUL  s1, 0, s1, 0, s1, 0
    LINE    s4, 0, s4, MD_C0, MD_C2, MD_C3
    F12MUL  s1, 0, s1, 0, s4, 0
    LEAVE   0
END_FUNCTION crypto_bls_miller_double

/*
 * crypto_bls_miller_add(f, t, q, p, work): millerAdd: with Q = (xq, yq) at
 * q, f = f l with l the line through T and Q, then T = T + Q. work holds
 * 1536 bytes: the line, Q in Jacobian coordinates, then the temporaries.
 */
.set MA_ZZ, 864
.set MA_N, 960
.set MA_D, 1056
.set MA_U, 1152
.set MA_C0, 1248
.set MA_C2, 1344
.set MA_C3, 1440
LOCAL_FUNCTION crypto_bls_miller_add
    ENTER   0
    mv      s1, a0                          # f
    mv      s2, a1                          # T
    mv      s3, a2                          # Q
    mv      s4, a3                          # P
    mv      s5, a4                          # work
    F2MUL   s5, MA_ZZ, s2, 192, s2, 192     # zz = Z^2
    F2MUL   s5, MA_N, s3, 96, s5, MA_ZZ     # n = yq zz Z - Y
    F2MUL   s5, MA_N, s5, MA_N, s2, 192
    F2SUB   s5, MA_N, s5, MA_N, s2, 96
    F2MUL   s5, MA_D, s3, 0, s5, MA_ZZ      # d = (xq zz - X) Z
    F2SUB   s5, MA_D, s5, MA_D, s2, 0
    F2MUL   s5, MA_D, s5, MA_D, s2, 192
    F2MUL   s5, MA_C0, s5, MA_N, s3, 0      # c0 = n xq - d yq
    F2MUL   s5, MA_U, s5, MA_D, s3, 96
    F2SUB   s5, MA_C0, s5, MA_C0, s5, MA_U
    C3      crypto_bls_fp2_mul_fp, s5, MA_C2, s5, MA_N, s4, 0 # c2 = -(n xp)
    C2      crypto_bls_fp2_neg, s5, MA_C2, s5, MA_C2
    C3      crypto_bls_fp2_mul_fp, s5, MA_C3, s5, MA_D, s4, 48 # c3 = d yp
    COPY    s5, 576, s3, 0, 192             # Q = (xq, yq, 1)
    SET_ONE s5, 768
    ZERO    s5, 816, 48
    C3      crypto_bls_g2_add, s2, 0, s2, 0, s5, 576
    LINE    s5, 0, s5, MA_C0, MA_C2, MA_C3
    F12MUL  s1, 0, s1, 0, s5, 0
    LEAVE   0
END_FUNCTION crypto_bls_miller_add

/*
 * crypto_bls_miller_loop(f, q, p, work): millerLoop for |x|: T = Q, f = 1,
 * then for each bit of |x| below its top bit, a double step, and an add
 * step on a set bit. work holds 1824 bytes: T, then the work of the steps.
 */
LOCAL_FUNCTION crypto_bls_miller_loop
    ENTER   0
    mv      s1, a0                          # f
    mv      s2, a1                          # Q
    mv      s3, a2                          # P
    mv      s4, a3                          # work: T at 0, step work at 288
    COPY    s4, 0, s2, 0, 192               # T = (xq, yq, 1)
    SET_ONE s4, 192
    ZERO    s4, 240, 48
    SET_ONE s1, 0                           # f = 1
    ZERO    s1, 48, 528
    lla     t0, 927f
    ld      s5, 0(t0)                       # |x|
    li      s6, 62                          # bits 62 to 0; bit 63 is the top bit
1:  mv      a0, s1
    mv      a1, s4
    mv      a2, s3
    ADDR    a3, s4, 288
    call    crypto_bls_miller_double
    srl     t0, s5, s6
    andi    t0, t0, 1
    beqz    t0, 2f
    mv      a0, s1
    mv      a1, s4
    mv      a2, s2
    mv      a3, s3
    ADDR    a4, s4, 288
    call    crypto_bls_miller_add
2:  addi    s6, s6, -1
    bgez    s6, 1b
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
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2                          # work
    lla     s4, 927f                        # |x|, |x| + 1, (|x| + 1) / 3
    C2      crypto_bls_fp12_inverse, s3, FE_U, s2, 0 # t = conj(f) / f
    C2      crypto_bls_fp12_conjugate, s3, FE_T, s2, 0
    F12MUL  s3, FE_T, s3, FE_T, s3, FE_U
    C2      crypto_bls_fp12_frobenius, s3, FE_M, s3, FE_T # m = frob(frob(t)) t
    C2      crypto_bls_fp12_frobenius, s3, FE_M, s3, FE_M
    F12MUL  s3, FE_M, s3, FE_M, s3, FE_T
    C3      crypto_bls_fp12_pow, s3, FE_U, s3, FE_M, s4, 16 # a = (m^((|x| + 1) / 3))^(|x| + 1)
    C3      crypto_bls_fp12_pow, s3, FE_A, s3, FE_U, s4, 8
    C3      crypto_bls_fp12_pow, s3, FE_U, s3, FE_A, s4, 0 # b = frob(a) conj(a^|x|)
    C2      crypto_bls_fp12_conjugate, s3, FE_U, s3, FE_U
    C2      crypto_bls_fp12_frobenius, s3, FE_B, s3, FE_A
    F12MUL  s3, FE_B, s3, FE_B, s3, FE_U
    C3      crypto_bls_fp12_pow, s3, FE_U, s3, FE_B, s4, 0 # c = (b^|x|)^|x| frob(frob(b)) conj(b)
    C3      crypto_bls_fp12_pow, s3, FE_C, s3, FE_U, s4, 0
    C2      crypto_bls_fp12_frobenius, s3, FE_U, s3, FE_B
    C2      crypto_bls_fp12_frobenius, s3, FE_U, s3, FE_U
    F12MUL  s3, FE_C, s3, FE_C, s3, FE_U
    C2      crypto_bls_fp12_conjugate, s3, FE_U, s3, FE_B
    F12MUL  s3, FE_C, s3, FE_C, s3, FE_U
    F12MUL  s1, 0, s3, FE_C, s3, FE_M       # c m
    LEAVE   0
END_FUNCTION crypto_bls_final_exponentiation

/*
 * crypto_bls_pairing_check(pairs, work, valid): pairingCheck: the u64 1 when
 * the product of e(P_i, Q_i) is 1, else 0. pairs holds a u64 count, then the
 * pairs, each a G1 point and a G2 point (432 bytes). A pair with a point at
 * infinity counts as 1. work holds 4608 bytes.
 */
.set PC_ACC, 0
.set PC_F, 576
.set PC_PA, 1152
.set PC_QA, 1248
.set PC_ML, 1440
.set PC_R, 576
.set PC_FE, 1152
LOCAL_FUNCTION crypto_bls_pairing_check
    ENTER   0
    mv      s1, a0
    mv      s2, a1                          # work
    mv      s3, a2                          # valid
    ld      s4, 0(s1)                       # count
    ADDR    s5, s1, 8                       # the first pair
    SET_ONE s2, PC_ACC
    ZERO    s2, PC_ACC + 48, 528
    beqz    s4, 3f
1:  IS_ZERO s5, 96, 48                      # skip a point at infinity
    beqz    t0, 2f
    IS_ZERO s5, 144 + 192, 96
    beqz    t0, 2f
    C2      crypto_bls_g1_affine, s2, PC_PA, s5, 0
    C2      crypto_bls_g2_affine, s2, PC_QA, s5, 144
    mv      a0, s2
    ADDR    a0, a0, PC_F
    ADDR    a1, s2, PC_QA
    ADDR    a2, s2, PC_PA
    ADDR    a3, s2, PC_ML
    call    crypto_bls_miller_loop
    C2      crypto_bls_fp12_conjugate, s2, PC_F, s2, PC_F
    F12MUL  s2, PC_ACC, s2, PC_ACC, s2, PC_F
2:  ADDR    s5, s5, 432
    addi    s4, s4, -1
    bnez    s4, 1b
3:  C3      crypto_bls_final_exponentiation, s2, PC_R, s2, PC_ACC, s2, PC_FE
    lla     t0, 900f                        # is it 1?
    addi    t0, t0, BLS_FP_RECORD_ONE
    EQUAL   s2, PC_R, t0, 0, 48
    bnez    t0, 4f
    IS_ZERO s2, PC_R + 48, 528
4:  seqz    t0, t0
    sd      t0, 0(s3)
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
    ENTER   CV_SIZE
    mv      s1, a0                          # public_key
    mv      s2, a1                          # message
    mv      s3, a2                          # signature
    mv      s4, a3                          # work
    mv      s5, a4                          # valid
    sd      zero, 0(s5)
    mv      a0, s3                          # R: decompress, subgroup check
    ADDR    a1, s4, CV_G2A
    call    crypto_bls_g2_uncompress
    bnez    a0, 9f
    C2      crypto_bls_g2_in_subgroup, s4, CV_G2A, sp, CV_V
    ld      t0, CV_V(sp)
    beqz    t0, 9f
    mv      a0, s1                          # PK: KeyValidate
    ADDR    a1, s4, CV_G1B
    call    crypto_bls_key_validate_point
    bnez    a0, 9f
    G2      crypto_bls_g1_neg, s4, CV_G1B, s4, CV_G1B
    mv      a0, s2                          # Q = H(message)
    lla     a1, 931f
    ADDR    a2, s4, CV_AREA
    ADDR    a3, s4, CV_G2B
    call    crypto_bls_hash_to_g2_point
    bnez    a0, 9f
    lla     t0, 904f                        # P: the generator of G1
    COPY    s4, CV_G1A, t0, 0, 96
    SET_ONE s4, CV_G1A + 96
    li      t0, 2
    sd      t0, CV_PAIRS(s4)
    mv      a0, s4
    ADDR    a1, s4, CV_AREA
    mv      a2, s5
    call    crypto_bls_pairing_check
9:  LEAVE   CV_SIZE
END_FUNCTION crypto_bls_core_verify

/* Branch to label when the scratch at rs is smaller than CRYPTO_BLS_SCRATCH + count of the message at rm. Uses t0, t1. */
.macro SCRATCH_CHECK rs, rm, label
    ld      t0, CRYPTO_BYTES_COUNT(\rm)
    li      t1, CRYPTO_BLS_SCRATCH
    add     t0, t0, t1
    ld      t1, 0(\rs)
    bltu    t1, t0, \label
.endm

/* crypto_bls_verify(public_key, message, signature, scratch, valid) -> status: verify. */
FUNCTION crypto_bls_verify
    ENTER   0
    SCRATCH_CHECK a3, a1, 8f
    ADDR    a3, a3, 8
    call    crypto_bls_core_verify
    li      a0, CRYPTO_OK
    LEAVE   0
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
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
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      s5, a4
    sd      zero, 0(s5)
    ADDR    s6, s4, FV_AREA                 # the sum, in work after the area of core_verify
    mv      a0, s1
    ADDR    a1, s6, FV_P
    call    crypto_bls_aggregate_keys
    bnez    a0, 9f
    G2      crypto_bls_g1_compress, s6, FV_P, s6, FV_K
    ADDR    a0, s6, FV_K
    mv      a1, s2
    mv      a2, s3
    mv      a3, s4
    mv      a4, s5
    call    crypto_bls_core_verify
9:  LEAVE   0
END_FUNCTION crypto_bls_fast_verify

/* crypto_bls_fast_aggregate_verify(public_keys, message, signature, scratch, valid) -> status: fastAggregateVerify. */
FUNCTION crypto_bls_fast_aggregate_verify
    ENTER   0
    SCRATCH_CHECK a3, a1, 8f
    ADDR    a3, a3, 8
    call    crypto_bls_fast_verify
    li      a0, CRYPTO_OK
    LEAVE   0
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
END_FUNCTION crypto_bls_fast_aggregate_verify

/*
 * crypto_bls_eth_fast_aggregate_verify(public_keys, message, signature,
 * scratch, valid) -> status: ethFastAggregateVerify.
 */
FUNCTION crypto_bls_eth_fast_aggregate_verify
    ENTER   0
    SCRATCH_CHECK a3, a1, 8f
    ld      t0, CRYPTO_BLS_LIST_COUNT(a0)
    beqz    t0, 1f
    ADDR    a3, a3, 8
    call    crypto_bls_fast_verify
    li      a0, CRYPTO_OK
    LEAVE   0
1:  lbu     t0, 0(a2)                       # no key: 1 exactly for 0xC0 then 95 zero bytes
    xori    t2, t0, 0xC0
    TAIL_ZERO a2, 96
    or      t0, t0, t2
    seqz    t0, t0
    sd      t0, 0(a4)
    li      a0, CRYPTO_OK
    LEAVE   0
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
END_FUNCTION crypto_bls_eth_fast_aggregate_verify

/*
 * crypto_bls_core_verify_point(point, message, signature, work, valid):
 * crypto_bls_core_verify with the key as a point of G1 that is not the point
 * at infinity: the u64 1 when the signature decompresses into G2 and
 * e(P, R) e(-point, H(message)) = 1, else 0. work as for crypto_bls_core_verify.
 */
LOCAL_FUNCTION crypto_bls_core_verify_point
    ENTER   CV_SIZE
    mv      s1, a0                          # point
    mv      s2, a1                          # message
    mv      s3, a2                          # signature
    mv      s4, a3                          # work
    mv      s5, a4                          # valid
    sd      zero, 0(s5)
    mv      a0, s3                          # R: decompress, subgroup check
    ADDR    a1, s4, CV_G2A
    call    crypto_bls_g2_uncompress
    bnez    a0, 9f
    C2      crypto_bls_g2_in_subgroup, s4, CV_G2A, sp, CV_V
    ld      t0, CV_V(sp)
    beqz    t0, 9f
    COPY    s4, CV_G1B, s1, 0, 144          # -point
    G2      crypto_bls_g1_neg, s4, CV_G1B, s4, CV_G1B
    mv      a0, s2                          # Q = H(message)
    lla     a1, 931f
    ADDR    a2, s4, CV_AREA
    ADDR    a3, s4, CV_G2B
    call    crypto_bls_hash_to_g2_point
    bnez    a0, 9f
    lla     t0, 904f                        # P: the generator of G1
    COPY    s4, CV_G1A, t0, 0, 96
    SET_ONE s4, CV_G1A + 96
    li      t0, 2
    sd      t0, CV_PAIRS(s4)
    mv      a0, s4
    ADDR    a1, s4, CV_AREA
    mv      a2, s5
    call    crypto_bls_pairing_check
9:  LEAVE   CV_SIZE
END_FUNCTION crypto_bls_core_verify_point

/*
 * crypto_bls_fast_aggregate_verify_cached(keys, indices, cache, message,
 * signature, scratch, valid) -> status: fastAggregateVerify of the keys at
 * the indices, each key checked once through its cache entry.
 * s1 keys, s2 the next index, s3 cache, s4 message, s5 signature, s6 work,
 * s7 valid, s8 indices left, s9 key i, s10 entry i, s11 a status.
 * Stack: the sum (G1Point) at 0, a point (G1Point) at 144.
 */
.set FC_ACC, 0
.set FC_P, 144
.set FC_SIZE, 288
FUNCTION crypto_bls_fast_aggregate_verify_cached
    ENTER   FC_SIZE
    SCRATCH_CHECK a5, a3, 8f
    mv      s1, a0
    mv      s3, a2
    mv      s4, a3
    mv      s5, a4
    addi    s6, a5, 8
    mv      s7, a6
    sd      zero, 0(s7)
    ld      t0, CRYPTO_BLS_LIST_OFFSET(a1)
    ld      s8, CRYPTO_BLS_LIST_COUNT(a1)
    beqz    s8, 9f                          # no index: 0
    add     s2, a1, t0
    SET_ONE sp, FC_ACC                      # the sum: the point at infinity
    SET_ONE sp, FC_ACC + 48
    ZERO    sp, FC_ACC + 96, 48
1:  ld      t0, 0(s2)                       # index i
    addi    s2, s2, 8
    ld      t1, CRYPTO_BLS_CACHE_COUNT(s3)
    bgeu    t0, t1, 9f                      # at or past count: 0
    ld      t1, CRYPTO_BLS_CACHE_KEY_STRIDE(s3)
    mul     s9, t0, t1
    add     s9, s9, s1
    li      t1, CRYPTO_BLS_ENTRY_BYTES
    mul     s10, t0, t1
    ld      t1, CRYPTO_BLS_CACHE_OFFSET(s3)
    add     s10, s10, t1
    add     s10, s10, s3
    ld      t0, CRYPTO_BLS_ENTRY_STATUS(s10)
    beqz    t0, 3f                          # empty: check the key
    EQUAL   s10, CRYPTO_BLS_ENTRY_KEY, s9, 0, 48
    bnez    t0, 3f                          # the entry of another key: check this one
    ld      t0, CRYPTO_BLS_ENTRY_STATUS(s10)
    li      t1, 2
    beq     t0, t1, 9f                      # a key that fails KeyValidate: 0
    COPY    sp, FC_P, s10, CRYPTO_BLS_ENTRY_POINT, 96
    SET_ONE sp, FC_P + 96
    j       4f
3:  mv      a0, s9                          # KeyValidate, then the entry
    ADDR    a1, sp, FC_P
    call    crypto_bls_key_validate_point
    mv      s11, a0
    COPY    s10, CRYPTO_BLS_ENTRY_KEY, s9, 0, 48
    bnez    s11, 32f
    COPY    s10, CRYPTO_BLS_ENTRY_POINT, sp, FC_P, 96
    li      t0, 1
    sd      t0, CRYPTO_BLS_ENTRY_STATUS(s10)
    j       4f
32: li      t0, 2
    sd      t0, CRYPTO_BLS_ENTRY_STATUS(s10)
    j       9f
4:  G3      crypto_bls_g1_add, sp, FC_ACC, sp, FC_P, sp, FC_ACC
    addi    s8, s8, -1
    bnez    s8, 1b
    IS_ZERO sp, FC_ACC + 96, 48             # the sum at infinity: 0
    beqz    t0, 9f
    ADDR    a0, sp, FC_ACC
    mv      a1, s4
    mv      a2, s5
    mv      a3, s6
    mv      a4, s7
    call    crypto_bls_core_verify_point
9:  li      a0, CRYPTO_OK
    LEAVE   FC_SIZE
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   FC_SIZE
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

/* The Fr element 1 (Montgomery form) at rd + od. Uses t2 to t6. */
.macro SET_FR_ONE rd, od
    lla     t4, 940f
    addi    t4, t4, KZG_FR_RECORD_ONE
    ADDR    t5, \rd, \od
    li      t2, 4
81: ld      t3, 0(t4)
    sd      t3, 0(t5)
    addi    t4, t4, 8
    addi    t5, t5, 8
    addi    t2, t2, -1
    bnez    t2, 81b
.endm

/* The point at infinity of G1, (1, 1, 0), at rd + od. Uses t2 to t6. */
.macro G1_ZERO rd, od
    SET_ONE \rd, \od
    SET_ONE \rd, \od + 48
    ZERO    \rd, \od + 96, 48
.endm

/*
 * crypto_kzg_fr_mul(result, a, b): a * b / 2^256 mod r, for a < 2^256 and
 * b < r (CIOS). result may be a or b. a a3 to a6, T t0 to t3 then s1 and
 * s2, b_i t6, q s3, product s4 and s5, carry s6, r record s7.
 */
LOCAL_FUNCTION crypto_kzg_fr_mul
    addi    sp, sp, -80
    UNWIND_ALLOC 80
    sd      s0, 0(sp)
    UNWIND_SAVE s0, 0
    sd      s1, 8(sp)
    UNWIND_SAVE s1, 8
    sd      s2, 16(sp)
    UNWIND_SAVE s2, 16
    sd      s3, 24(sp)
    UNWIND_SAVE s3, 24
    sd      s4, 32(sp)
    UNWIND_SAVE s4, 32
    sd      s5, 40(sp)
    UNWIND_SAVE s5, 40
    sd      s6, 48(sp)
    UNWIND_SAVE s6, 48
    sd      s7, 56(sp)
    UNWIND_SAVE s7, 56
    sd      s8, 64(sp)
    UNWIND_SAVE s8, 64
    UNWIND_END_PROLOGUE
    ld      a3, 0(a1)
    ld      a4, 8(a1)
    ld      a5, 16(a1)
    ld      a6, 24(a1)
    lla     s7, 940f
    li      t0, 0
    li      t1, 0
    li      t2, 0
    li      t3, 0
    li      s1, 0
    .irp off, 0, 8, 16, 24
    ld      t6, \off(a2)                    # T += a * b_i
    li      s6, 0
    MAC     t0, a3
    MAC     t1, a4
    MAC     t2, a5
    MAC     t3, a6
    add     s1, s1, s6
    sltu    s2, s1, s6
    ld      s3, KZG_FR_RECORD_INVERSE(s7)
    mul     s3, t0, s3                      # q = T0 * -r^-1 mod 2^64
    li      s6, 0                           # T = (T + q * r) / 2^64
    MACQ    t0, 0
    MACQ    t1, 8
    MACQ    t2, 16
    MACQ    t3, 24
    add     s1, s1, s6
    sltu    s4, s1, s6
    add     s2, s2, s4
    mv      t0, t1
    mv      t1, t2
    mv      t2, t3
    mv      t3, s1
    mv      s1, s2
    .endr
    li      s4, 0                           # T - r when T >= r: borrow s4
    SUBP    a3, t0, 0
    SUBP    a4, t1, 8
    SUBP    a5, t2, 16
    SUBP    a6, t3, 24
    sltu    s5, s1, s4                      # mask s5: all ones when T >= r
    addi    s5, s5, -1
    PICK    t0, a3
    PICK    t1, a4
    PICK    t2, a5
    PICK    t3, a6
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
    ld      s4, 32(sp)
    UNWIND_RESTORE s4
    ld      s5, 40(sp)
    UNWIND_RESTORE s5
    ld      s6, 48(sp)
    UNWIND_RESTORE s6
    ld      s7, 56(sp)
    UNWIND_RESTORE s7
    ld      s8, 64(sp)
    UNWIND_RESTORE s8
    addi    sp, sp, 80
    UNWIND_FREE 80
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_kzg_fr_mul

/* crypto_kzg_fr_add(result, a, b): a + b mod r, for a, b < r. result may be a or b. A leaf. */
LOCAL_FUNCTION crypto_kzg_fr_add
    UNWIND_END_PROLOGUE
    li      t2, 0                           # the sum in a3 to a6, carry t2
    ld      a3, 0(a1)
    ld      t1, 0(a2)
    ADDCARRY a3, t1, t2, t3
    ld      a4, 8(a1)
    ld      t1, 8(a2)
    ADDCARRY a4, t1, t2, t3
    ld      a5, 16(a1)
    ld      t1, 16(a2)
    ADDCARRY a5, t1, t2, t3
    ld      a6, 24(a1)
    ld      t1, 24(a2)
    ADDCARRY a6, t1, t2, t3
    lla     a1, 940f                        # the borrow of the sum - r, in t4
    li      t4, 0
    ld      t1, 0(a1)
    BORROWOF a3, t1, t4, t3, t5
    ld      t1, 8(a1)
    BORROWOF a4, t1, t4, t3, t5
    ld      t1, 16(a1)
    BORROWOF a5, t1, t4, t3, t5
    ld      t1, 24(a1)
    BORROWOF a6, t1, t4, t3, t5
    xori    t4, t4, 1                       # mask t2: all ones on a carry or no borrow
    or      t2, t2, t4
    neg     t2, t2
    li      t4, 0                           # the sum - (r and mask)
    ld      t1, 0(a1)
    and     t1, t1, t2
    SUBBORROW a3, t1, t4, t3, t5
    ld      t1, 8(a1)
    and     t1, t1, t2
    SUBBORROW a4, t1, t4, t3, t5
    ld      t1, 16(a1)
    and     t1, t1, t2
    SUBBORROW a5, t1, t4, t3, t5
    ld      t1, 24(a1)
    and     t1, t1, t2
    SUBBORROW a6, t1, t4, t3, t5
    sd      a3, 0(a0)
    sd      a4, 8(a0)
    sd      a5, 16(a0)
    sd      a6, 24(a0)
    ret
END_FUNCTION crypto_kzg_fr_add

/* crypto_kzg_fr_sub(result, a, b): a - b mod r, for a, b < r. result may be a or b. A leaf. */
LOCAL_FUNCTION crypto_kzg_fr_sub
    UNWIND_END_PROLOGUE
    li      t2, 0                           # the difference in a3 to a6, borrow t2
    ld      a3, 0(a1)
    ld      t1, 0(a2)
    SUBBORROW a3, t1, t2, t3, t5
    ld      a4, 8(a1)
    ld      t1, 8(a2)
    SUBBORROW a4, t1, t2, t3, t5
    ld      a5, 16(a1)
    ld      t1, 16(a2)
    SUBBORROW a5, t1, t2, t3, t5
    ld      a6, 24(a1)
    ld      t1, 24(a2)
    SUBBORROW a6, t1, t2, t3, t5
    neg     t2, t2                          # all ones on a borrow
    lla     a1, 940f                        # + (r and mask)
    li      t4, 0
    ld      t1, 0(a1)
    and     t1, t1, t2
    ADDCARRY a3, t1, t4, t3
    ld      t1, 8(a1)
    and     t1, t1, t2
    ADDCARRY a4, t1, t4, t3
    ld      t1, 16(a1)
    and     t1, t1, t2
    ADDCARRY a5, t1, t4, t3
    ld      t1, 24(a1)
    and     t1, t1, t2
    ADDCARRY a6, t1, t4, t3
    sd      a3, 0(a0)
    sd      a4, 8(a0)
    sd      a5, 16(a0)
    sd      a6, 24(a0)
    ret
END_FUNCTION crypto_kzg_fr_sub

/* crypto_kzg_fr_neg(result, a): -a mod r, for a < r; 0 stays 0. result may be a. A leaf. */
LOCAL_FUNCTION crypto_kzg_fr_neg
    UNWIND_END_PROLOGUE
    ld      a3, 0(a1)
    ld      a4, 8(a1)
    ld      a5, 16(a1)
    ld      a6, 24(a1)
    or      t1, a3, a4
    or      t1, t1, a5
    or      t1, t1, a6
    snez    t1, t1                          # mask t1: all ones when a != 0
    neg     t1, t1
    lla     a1, 940f                        # (r - a) and mask
    li      t2, 0
    ld      t3, 0(a1)
    SUBBORROW t3, a3, t2, t4, t5
    and     t3, t3, t1
    sd      t3, 0(a0)
    ld      t3, 8(a1)
    SUBBORROW t3, a4, t2, t4, t5
    and     t3, t3, t1
    sd      t3, 8(a0)
    ld      t3, 16(a1)
    SUBBORROW t3, a5, t2, t4, t5
    and     t3, t3, t1
    sd      t3, 16(a0)
    ld      t3, 24(a1)
    SUBBORROW t3, a6, t2, t4, t5
    and     t3, t3, t1
    sd      t3, 24(a0)
    ret
END_FUNCTION crypto_kzg_fr_neg

/*
 * crypto_kzg_fr_pow(result, base, exponent): base^e (Fr.powNat), with e the
 * 4 little-endian limbs at exponent, a public value. result may be base.
 */
.set RW_ACC, 0
.set RW_BASE, 32
.set RW_SIZE, 64
LOCAL_FUNCTION crypto_kzg_fr_pow
    ENTER   RW_SIZE
    mv      s1, a0
    mv      s2, a2
    COPY    sp, RW_BASE, a1, 0, 32
    SET_FR_ONE sp, RW_ACC
    li      s3, 255                         # bit index
1:  BIT     s2, s3                          # skip the zero bits above the top set bit
    bnez    t0, 2f
    addi    s3, s3, -1
    bgez    s3, 1b
    j       4f
2:  RMUL    sp, RW_ACC, sp, RW_ACC, sp, RW_ACC
    BIT     s2, s3
    beqz    t0, 3f
    RMUL    sp, RW_ACC, sp, RW_ACC, sp, RW_BASE
3:  addi    s3, s3, -1
    bgez    s3, 2b
4:  COPY    s1, 0, sp, RW_ACC, 32
    LEAVE   RW_SIZE
END_FUNCTION crypto_kzg_fr_pow

/* crypto_kzg_fr_inverse(result, a): a^(r - 2) (Fr.inverse); 0 gives 0. result may be a. */
LOCAL_FUNCTION crypto_kzg_fr_inverse
    ENTER   0
    lla     a2, 941f
    call    crypto_kzg_fr_pow
    LEAVE   0
END_FUNCTION crypto_kzg_fr_inverse

/*
 * crypto_kzg_fr_from_bytes(result, bytes) -> status: the 32 big-endian bytes
 * as an element of Fr (Fr.fromBytesBE, bytesToBlsField).
 * CRYPTO_INVALID_ENCODING when the number is r or more; nothing is written.
 */
LOCAL_FUNCTION crypto_kzg_fr_from_bytes
    ENTER   32
    mv      s1, a0
    LOAD_BE64 a2, a1, 24, t6
    LOAD_BE64 a3, a1, 16, t6
    LOAD_BE64 a4, a1, 8, t6
    LOAD_BE64 a5, a1, 0, t6
    lla     t4, 940f                        # below r?
    li      t0, 0
    ld      t1, 0(t4)
    BORROWOF a2, t1, t0, t2, t3
    ld      t1, 8(t4)
    BORROWOF a3, t1, t0, t2, t3
    ld      t1, 16(t4)
    BORROWOF a4, t1, t0, t2, t3
    ld      t1, 24(t4)
    BORROWOF a5, t1, t0, t2, t3
    beqz    t0, 9f
    sd      a2, 0(sp)
    sd      a3, 8(sp)
    sd      a4, 16(sp)
    sd      a5, 24(sp)
    mv      a0, s1                          # result = n * 2^512 / 2^256
    mv      a1, sp
    addi    a2, t4, KZG_FR_RECORD_R2
    call    crypto_kzg_fr_mul
    li      a0, CRYPTO_OK
    LEAVE   32
9:  li      a0, CRYPTO_INVALID_ENCODING
    LEAVE   32
END_FUNCTION crypto_kzg_fr_from_bytes

/*
 * crypto_kzg_fr_from_digest(result, bytes): the 32 big-endian bytes, a
 * number n below 2^256, as n mod r (Fr.ofNat in hashToBlsField).
 */
LOCAL_FUNCTION crypto_kzg_fr_from_digest
    ENTER   32
    LOAD_BE64 a2, a1, 24, t6
    LOAD_BE64 a3, a1, 16, t6
    LOAD_BE64 a4, a1, 8, t6
    LOAD_BE64 a5, a1, 0, t6
    sd      a2, 0(sp)
    sd      a3, 8(sp)
    sd      a4, 16(sp)
    sd      a5, 24(sp)
    mv      a1, sp                          # n * 2^512 / 2^256, with n < 2^256
    lla     a2, 940f
    addi    a2, a2, KZG_FR_RECORD_R2
    call    crypto_kzg_fr_mul
    LEAVE   32
END_FUNCTION crypto_kzg_fr_from_digest

/* crypto_kzg_fr_from_u64(result, value): the u64 value in a1 as an element of Fr (Fr.ofNat). */
LOCAL_FUNCTION crypto_kzg_fr_from_u64
    ENTER   32
    sd      a1, 0(sp)
    sd      zero, 8(sp)
    sd      zero, 16(sp)
    sd      zero, 24(sp)
    mv      a1, sp
    lla     a2, 940f
    addi    a2, a2, KZG_FR_RECORD_R2
    call    crypto_kzg_fr_mul
    LEAVE   32
END_FUNCTION crypto_kzg_fr_from_u64

/* crypto_kzg_fr_canonical(result, a): the value of a (Fr.val) as 4 little-endian limbs. result may be a. */
LOCAL_FUNCTION crypto_kzg_fr_canonical
    ENTER   32
    li      t0, 1
    sd      t0, 0(sp)
    sd      zero, 8(sp)
    sd      zero, 16(sp)
    sd      zero, 24(sp)
    mv      a2, sp                          # a * 1 / 2^256
    call    crypto_kzg_fr_mul
    LEAVE   32
END_FUNCTION crypto_kzg_fr_canonical

/* crypto_kzg_fr_to_bytes(bytes, a): the 32 big-endian bytes of a (blsFieldToBytes). */
LOCAL_FUNCTION crypto_kzg_fr_to_bytes
    ENTER   32
    mv      s1, a0
    mv      a0, sp
    call    crypto_kzg_fr_canonical
    .irp i, 0, 1, 2, 3
    ld      t0, 8*\i(sp)
    STORE_BE64 t0, s1, 24-8*\i, t1
    .endr
    LEAVE   32
END_FUNCTION crypto_kzg_fr_to_bytes

/* ---------------------------------------------------------------- Roots of unity, bit reversal, FFT (Kzg) */

/* t0 = log2 of the power of two in rs. Uses t1. */
.macro LOG2 rs
    li      t0, 0
    mv      t1, \rs
82: srli    t1, t1, 1
    beqz    t1, 83f
    addi    t0, t0, 1
    j       82b
83:
.endm

/* rd = the low n bits of rs reversed (reverseBits), n in rn. Uses t1, t2, rs and rn change. */
.macro REV_BITS rd, rs, rn
    li      \rd, 0
84: beqz    \rn, 85f
    slli    \rd, \rd, 1
    andi    t1, \rs, 1
    or      \rd, \rd, t1
    srli    \rs, \rs, 1
    addi    \rn, \rn, -1
    j       84b
85:
.endm

/*
 * crypto_kzg_roots_of_unity(roots, order): the powers 1, w, ..., w^(order - 1)
 * of w = 7^((r - 1) / order) (computeRootsOfUnity), for order a power of two
 * from 2 to 2^32, in a1.
 */
.set RU_E, 0
.set RU_W, 32
.set RU_SIZE, 64
LOCAL_FUNCTION crypto_kzg_roots_of_unity
    ENTER   RU_SIZE
    mv      s1, a0
    mv      s2, a1
    LOG2    s2                              # k = log2 order; e = (r - 1) >> k
    li      t1, 64
    sub     t1, t1, t0                      # 64 - k
    lla     t2, 942f
    ld      a2, 0(t2)
    ld      a3, 8(t2)
    ld      a4, 16(t2)
    ld      a5, 24(t2)
    srl     a2, a2, t0
    sll     a6, a3, t1
    or      a2, a2, a6
    srl     a3, a3, t0
    sll     a6, a4, t1
    or      a3, a3, a6
    srl     a4, a4, t0
    sll     a6, a5, t1
    or      a4, a4, a6
    srl     a5, a5, t0
    sd      a2, RU_E(sp)
    sd      a3, RU_E+8(sp)
    sd      a4, RU_E+16(sp)
    sd      a5, RU_E+24(sp)
    addi    a0, sp, RU_W                    # w = 7^e
    li      a1, 7
    call    crypto_kzg_fr_from_u64
    C3      crypto_kzg_fr_pow, sp, RU_W, sp, RU_W, sp, RU_E
    SET_FR_ONE s1, 0                        # computePowers
    li      s3, 1
1:  bgeu    s3, s2, 9f
    slli    a0, s3, 5
    add     a0, s1, a0
    addi    a1, a0, -32
    addi    a2, sp, RU_W
    call    crypto_kzg_fr_mul
    addi    s3, s3, 1
    j       1b
9:  LEAVE   RU_SIZE
END_FUNCTION crypto_kzg_roots_of_unity

/*
 * crypto_kzg_bit_reversal(array, n, size): the bit-reversal permutation
 * (bitReversalPermutation) of the n entries of size bytes at array, in
 * place: entry i swaps with entry rev(i), with rev the reversal of log2 n
 * bits (reverseBits). n is a power of two from 2 up, in a1; size is a
 * multiple of 8, in a2. A leaf.
 */
LOCAL_FUNCTION crypto_kzg_bit_reversal
    UNWIND_END_PROLOGUE
    LOG2    a1                              # t0 = log2 n
    mv      a3, t0
    li      a4, 0                           # i
1:  mv      a5, a4                          # j = rev(i)
    mv      a6, a3
    REV_BITS a7, a5, a6
    bgeu    a4, a7, 3f
    mul     a5, a4, a2                      # swap entries i and j
    add     a5, a0, a5
    mul     a6, a7, a2
    add     a6, a0, a6
    mv      t3, a2
2:  ld      t4, 0(a5)
    ld      t5, 0(a6)
    sd      t5, 0(a5)
    sd      t4, 0(a6)
    addi    a5, a5, 8
    addi    a6, a6, 8
    addi    t3, t3, -8
    bnez    t3, 2b
3:  addi    a4, a4, 1
    bltu    a4, a1, 1b
    ret
END_FUNCTION crypto_kzg_bit_reversal

/*
 * crypto_kzg_fft(vals, n, roots, inverse): the FFT of the n values at vals,
 * in place (fftField): the bit-reversal permutation, then the stages of
 * fftStages, each pair r < h of a block of 2 h values with the root at m r,
 * for m = n / (2 h). With inverse 1, root i is root (n - i) mod n and each
 * value is divided by n. n (a power of two) and inverse are in a1 and a3;
 * roots holds the n-th roots of unity.
 */
.set KF_T, 0
.set KF_SIZE, 32
LOCAL_FUNCTION crypto_kzg_fft
    ENTER   KF_SIZE
    mv      s1, a0                          # vals
    mv      s2, a1                          # n
    mv      s3, a2                          # roots
    mv      s4, a3                          # inverse
    li      a2, 32
    call    crypto_kzg_bit_reversal
    li      s5, 0                           # log2 h
    srli    s6, s2, 1                       # m
1:  beqz    s6, 5f
    li      s7, 0                           # pair j < n / 2
2:  srl     t0, s7, s5                      # block b = j / h, r = j mod h
    li      t1, 1
    sll     t1, t1, s5                      # h
    addi    t2, t1, -1
    and     t2, s7, t2                      # r
    addi    t3, s5, 1
    sll     t0, t0, t3
    add     s8, t0, t2                      # i1 = 2 h b + r
    add     s9, s8, t1                      # i2 = i1 + h
    mul     t4, s6, t2                      # root index m r, or (n - m r) mod n
    beqz    s4, 3f
    sub     t4, s2, t4
    addi    t5, s2, -1
    and     t4, t4, t5
3:  addi    a0, sp, KF_T                    # t = x[i2] * root
    slli    a1, s9, 5
    add     a1, s1, a1
    slli    a2, t4, 5
    add     a2, s3, a2
    call    crypto_kzg_fr_mul
    slli    a0, s9, 5                       # x[i2] = x[i1] - t
    add     a0, s1, a0
    slli    a1, s8, 5
    add     a1, s1, a1
    addi    a2, sp, KF_T
    call    crypto_kzg_fr_sub
    slli    a0, s8, 5                       # x[i1] = x[i1] + t
    add     a0, s1, a0
    mv      a1, a0
    addi    a2, sp, KF_T
    call    crypto_kzg_fr_add
    addi    s7, s7, 1
    srli    t0, s2, 1
    bltu    s7, t0, 2b
    addi    s5, s5, 1
    srli    s6, s6, 1
    j       1b
5:  beqz    s4, 9f                          # inverse: times 1 / n
    addi    a0, sp, KF_T
    mv      a1, s2
    call    crypto_kzg_fr_from_u64
    C2      crypto_kzg_fr_inverse, sp, KF_T, sp, KF_T
    li      s7, 0
6:  slli    a0, s7, 5
    add     a0, s1, a0
    mv      a1, a0
    addi    a2, sp, KF_T
    call    crypto_kzg_fr_mul
    addi    s7, s7, 1
    bltu    s7, s2, 6b
9:  LEAVE   KF_SIZE
END_FUNCTION crypto_kzg_fft

/* crypto_kzg_shift_vals(vals, n, factor): vals[i] times factor^i, in place (shiftVals); n in a1. */
.set SH_S, 0
.set SH_SIZE, 32
LOCAL_FUNCTION crypto_kzg_shift_vals
    ENTER   SH_SIZE
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    SET_FR_ONE sp, SH_S
    li      s4, 0
1:  bgeu    s4, s2, 9f
    slli    a0, s4, 5
    add     a0, s1, a0
    mv      a1, a0
    addi    a2, sp, SH_S
    call    crypto_kzg_fr_mul
    C3      crypto_kzg_fr_mul, sp, SH_S, sp, SH_S, s3, 0
    addi    s4, s4, 1
    j       1b
9:  LEAVE   SH_SIZE
END_FUNCTION crypto_kzg_shift_vals

/*
 * crypto_kzg_coset_fft(vals, n, roots, inverse): cosetFftField with the shift
 * 7: shiftVals by 7 then the FFT; or the inverse FFT then shiftVals by 1 / 7.
 * n and inverse are in a1 and a3.
 */
.set CF_F, 0
.set CF_SIZE, 32
LOCAL_FUNCTION crypto_kzg_coset_fft
    ENTER   CF_SIZE
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    addi    a0, sp, CF_F
    li      a1, 7
    call    crypto_kzg_fr_from_u64
    bnez    s4, 1f
    mv      a0, s1
    mv      a1, s2
    addi    a2, sp, CF_F
    call    crypto_kzg_shift_vals
    mv      a0, s1
    mv      a1, s2
    mv      a2, s3
    li      a3, 0
    call    crypto_kzg_fft
    LEAVE   CF_SIZE
1:  mv      a0, s1
    mv      a1, s2
    mv      a2, s3
    li      a3, 1
    call    crypto_kzg_fft
    C2      crypto_kzg_fr_inverse, sp, CF_F, sp, CF_F
    mv      a0, s1
    mv      a1, s2
    addi    a2, sp, CF_F
    call    crypto_kzg_shift_vals
    LEAVE   CF_SIZE
END_FUNCTION crypto_kzg_coset_fft

/*
 * crypto_kzg_batch_inverse(out, in, n): out[i] = 1 / in[i], and 0 for 0
 * (Fr.batchInverse): the products of the nonzero values before each one, one
 * inversion, then the walk back. out must not be in. n in a2.
 */
.set BI_P, 0
.set BI_S, 32
.set BI_SIZE, 64
LOCAL_FUNCTION crypto_kzg_batch_inverse
    ENTER   BI_SIZE
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    SET_FR_ONE sp, BI_P
    li      s4, 0
1:  bgeu    s4, s3, 3f                      # out[i] = pre, the product of the nonzero values before i
    slli    s5, s4, 5
    add     s6, s1, s5
    add     s5, s2, s5
    COPY    s6, 0, sp, BI_P, 32
    IS_ZERO s5, 0, 32
    beqz    t0, 2f
    C3      crypto_kzg_fr_mul, sp, BI_P, sp, BI_P, s5, 0
2:  addi    s4, s4, 1
    j       1b
3:  C2      crypto_kzg_fr_inverse, sp, BI_S, sp, BI_P      # s = 1 / the product
4:  beqz    s4, 9f
    addi    s4, s4, -1
    slli    s5, s4, 5
    add     s6, s1, s5
    add     s5, s2, s5
    IS_ZERO s5, 0, 32
    bnez    t0, 5f
    ZERO    s6, 0, 32
    j       4b
5:  C3      crypto_kzg_fr_mul, s6, 0, s6, 0, sp, BI_S      # out[i] = pre s; s = s in[i]
    C3      crypto_kzg_fr_mul, sp, BI_S, sp, BI_S, s5, 0
    j       4b
9:  LEAVE   BI_SIZE
END_FUNCTION crypto_kzg_batch_inverse

/*
 * crypto_kzg_blob_to_poly(poly, bytes, count) -> status: count field
 * elements of 32 big-endian bytes (bytesToBlsFields). CRYPTO_INVALID_ENCODING
 * when one is r or more. count in a2.
 */
LOCAL_FUNCTION crypto_kzg_blob_to_poly
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    li      s4, 0
1:  bgeu    s4, s3, 8f
    slli    a1, s4, 5
    add     a0, s1, a1
    add     a1, s2, a1
    call    crypto_kzg_fr_from_bytes
    bnez    a0, 9f
    addi    s4, s4, 1
    j       1b
8:  li      a0, CRYPTO_OK
9:  LEAVE   0
END_FUNCTION crypto_kzg_blob_to_poly

/*
 * crypto_kzg_eval_to_coeff(poly, roots): the 4096 coefficients of the
 * polynomial of 4096 values, in place (polynomialEvalToCoeff): the inverse
 * FFT of the bit-reversed values. roots receives the 4096-th roots of unity.
 */
LOCAL_FUNCTION crypto_kzg_eval_to_coeff
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      a0, s2
    li      a1, 4096
    call    crypto_kzg_roots_of_unity
    mv      a0, s1
    li      a1, 4096
    li      a2, 32
    call    crypto_kzg_bit_reversal
    mv      a0, s1
    li      a1, 4096
    mv      a2, s2
    li      a3, 1
    call    crypto_kzg_fft
    LEAVE   0
END_FUNCTION crypto_kzg_eval_to_coeff

/* Copy the n bytes (a multiple of 8) at rs to rd; rd and rs end past them. Uses t0, rn ends at 0. */
.macro COPY_BYTES rd, rs, rn
86: ld      t0, 0(\rs)
    sd      t0, 0(\rd)
    addi    \rs, \rs, 8
    addi    \rd, \rd, 8
    addi    \rn, \rn, -8
    bnez    \rn, 86b
.endm

/* Zero the n bytes (a multiple of 8, not 0) at rd; rd ends past them, rn at 0. */
.macro ZERO_BYTES rd, rn
87: sd      zero, 0(\rd)
    addi    \rd, \rd, 8
    addi    \rn, \rn, -8
    bnez    \rn, 87b
.endm

/*
 * crypto_kzg_extended_cells(cells, coeff, work): the cells of the 4096
 * coefficients at coeff (cellsOfExtendedEvaluations of extendedEvaluations):
 * zero padding to 8192, the FFT over the 8192-th roots of unity, the
 * bit-reversal permutation, then 32 big-endian bytes per value. work holds
 * 524288 bytes: the values, then the roots.
 */
LOCAL_FUNCTION crypto_kzg_extended_cells
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2                          # values
    li      t1, 262144
    add     s4, s3, t1                      # roots
    mv      a3, s3
    mv      a4, s2
    li      a5, 131072
    COPY_BYTES a3, a4, a5
    li      a5, 131072
    ZERO_BYTES a3, a5
    mv      a0, s4
    li      a1, 8192
    call    crypto_kzg_roots_of_unity
    mv      a0, s3
    li      a1, 8192
    mv      a2, s4
    li      a3, 0
    call    crypto_kzg_fft
    mv      a0, s3
    li      a1, 8192
    li      a2, 32
    call    crypto_kzg_bit_reversal
    li      s5, 0
1:  slli    a1, s5, 5
    add     a0, s1, a1
    add     a1, s3, a1
    call    crypto_kzg_fr_to_bytes
    addi    s5, s5, 1
    li      t0, 8192
    bltu    s5, t0, 1b
    LEAVE   0
END_FUNCTION crypto_kzg_extended_cells

/* Branch to label when the scratch at rs holds fewer than CRYPTO_KZG_SCRATCH + rn * CRYPTO_KZG_SCRATCH_PER_ENTRY bytes. Uses t0, t1. */
.macro KZG_SCRATCH_CHECK rs, rn, label
    slli    t0, \rn, 13
    li      t1, CRYPTO_KZG_SCRATCH
    add     t0, t0, t1
    ld      t1, 0(\rs)
    bltu    t1, t0, \label
.endm

/* crypto_kzg_compute_cells(blob, scratch, cells) -> status: computeCells. work: the polynomial, then 524288 bytes. */
FUNCTION crypto_kzg_compute_cells
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    KZG_SCRATCH_CHECK s2, zero, 8f
    addi    s4, s2, 8                       # the polynomial
    mv      a0, s4
    mv      a1, s1
    li      a2, 4096
    call    crypto_kzg_blob_to_poly
    bnez    a0, 9f
    li      t0, 131072
    add     s5, s4, t0
    mv      a0, s4
    mv      a1, s5
    call    crypto_kzg_eval_to_coeff
    mv      a0, s3
    mv      a1, s4
    mv      a2, s5
    call    crypto_kzg_extended_cells
    li      a0, CRYPTO_OK
9:  LEAVE   0
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
END_FUNCTION crypto_kzg_compute_cells

/* ---------------------------------------------------------------- Trusted setup (TrustedSetup.lean) */

/* crypto_kzg_trusted_setup_of_bytes(g1_lagrange, g1_monomial, g2_monomial, settings) -> status: TrustedSetup.ofBytes. */
FUNCTION crypto_kzg_trusted_setup_of_bytes
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    ld      t0, CRYPTO_BYTES_COUNT(s1)      # the counts
    li      t1, CRYPTO_KZG_SETUP_G1_SIZE
    bne     t0, t1, 8f
    ld      t0, CRYPTO_BYTES_COUNT(s2)
    bne     t0, t1, 8f
    ld      t0, CRYPTO_BYTES_COUNT(s3)
    li      t1, CRYPTO_KZG_SETUP_G2_SIZE
    bne     t0, t1, 8f
    ld      s5, CRYPTO_BYTES_OFFSET(s1)     # Lagrange point i at rev(i)
    add     s5, s1, s5
    li      s6, 0
1:  mv      a2, s6
    li      a3, 12
    REV_BITS a4, a2, a3
    li      t0, BLS_G1
    mul     a1, a4, t0
    add     a1, s4, a1
    li      t0, 48
    mul     a0, s6, t0
    add     a0, s5, a0
    call    crypto_bls_g1_uncompress
    bnez    a0, 8f
    addi    s6, s6, 1
    li      t0, 4096
    bltu    s6, t0, 1b
    ld      s5, CRYPTO_BYTES_OFFSET(s2)     # the monomial points
    add     s5, s2, s5
    li      t0, CRYPTO_KZG_SETTINGS_G1_MONOMIAL
    add     s7, s4, t0
    li      s6, 0
2:  li      t0, BLS_G1
    mul     a1, s6, t0
    add     a1, s7, a1
    li      t0, 48
    mul     a0, s6, t0
    add     a0, s5, a0
    call    crypto_bls_g1_uncompress
    bnez    a0, 8f
    addi    s6, s6, 1
    li      t0, 4096
    bltu    s6, t0, 2b
    ld      s5, CRYPTO_BYTES_OFFSET(s3)     # the G2 points
    add     s5, s3, s5
    li      t0, CRYPTO_KZG_SETTINGS_G2_MONOMIAL
    add     s7, s4, t0
    li      s6, 0
3:  li      t0, BLS_G2
    mul     a1, s6, t0
    add     a1, s7, a1
    li      t0, 96
    mul     a0, s6, t0
    add     a0, s5, a0
    call    crypto_bls_g2_uncompress
    bnez    a0, 8f
    addi    s6, s6, 1
    li      t0, 65
    bltu    s6, t0, 3b
    li      a0, CRYPTO_OK
    LEAVE   0
8:  li      a0, CRYPTO_KZG_INVALID_TRUSTED_SETUP
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
    mv      s1, a0
    mv      s2, a1
    lbu     t0, 0(s1)
    li      t1, 0xC0
    bne     t0, t1, 1f
    TAIL_ZERO s1, 48
    bnez    t0, 1f
    G1_ZERO s2, 0
    li      a0, CRYPTO_OK
    LEAVE   0
1:  mv      a0, s1
    mv      a1, s2
    call    crypto_bls_key_validate_point
    LEAVE   0
END_FUNCTION crypto_kzg_validate_g1

/*
 * crypto_kzg_challenge(result, blob, commitment, work): computeChallenge:
 * SHA-256 of "FSBLOBVERIFY_V1_" || I2OSP(4096, 16) || blob || commitment, as
 * a number mod r. work holds 131232 bytes: the data as a ByteList, then the
 * digest.
 */
.set CH_DIGEST, 131200
LOCAL_FUNCTION crypto_kzg_challenge
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    li      t0, CH_DIGEST                   # size, offset 24, count 131152
    sd      t0, 0(s4)
    li      t0, 24
    sd      t0, 8(s4)
    li      t0, 131152
    sd      t0, 16(s4)
    lla     t1, 945f
    ld      t0, 0(t1)
    sd      t0, 24(s4)
    ld      t0, 8(t1)
    sd      t0, 32(s4)
    sd      zero, 40(s4)                    # I2OSP(4096, 16): byte 14 is 0x10
    li      t0, 0x10
    slli    t0, t0, 48
    sd      t0, 48(s4)
    addi    a3, s4, 56                      # the blob, then the commitment
    mv      a4, s2
    li      a5, 131072
    COPY_BYTES a3, a4, a5
    mv      a4, s3
    li      a5, 48
    COPY_BYTES a3, a4, a5
    mv      a0, s4
    li      t0, CH_DIGEST
    add     a1, s4, t0
    CALL_GLOBAL crypto_sha256
    mv      a0, s1
    li      t0, CH_DIGEST
    add     a1, s4, t0
    call    crypto_kzg_fr_from_digest
    LEAVE   0
END_FUNCTION crypto_kzg_challenge

/*
 * crypto_kzg_compute_challenge(blob, commitment, scratch, challenge) ->
 * status: computeChallengeExport. work: the polynomial, then the point, then
 * the challenge work.
 */
.set CC_POINT, 131072
.set CC_FR, 131216
.set CC_WORK, 131248
FUNCTION crypto_kzg_compute_challenge
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    KZG_SCRATCH_CHECK s3, zero, 7f
    addi    s5, s3, 8                       # work
    mv      a0, s5
    mv      a1, s1
    li      a2, 4096
    call    crypto_kzg_blob_to_poly
    bnez    a0, 9f
    mv      a0, s2
    li      t0, CC_POINT
    add     a1, s5, t0
    call    crypto_kzg_validate_g1
    bnez    a0, 8f
    li      t0, CC_FR
    add     a0, s5, t0
    mv      a1, s1
    mv      a2, s2
    li      t0, CC_WORK
    add     a3, s5, t0
    call    crypto_kzg_challenge
    C2      crypto_kzg_fr_to_bytes, s4, 0, s5, CC_FR
    li      a0, CRYPTO_OK
9:  LEAVE   0
7:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
8:  li      a0, CRYPTO_KZG_INVALID_COMMITMENT
    LEAVE   0
END_FUNCTION crypto_kzg_compute_challenge

/* ---------------------------------------------------------------- Linear combinations and evaluation (Core.lean, Polynomials.lean) */

/* The generator of G1 as a G1 point at rd + od. Uses t2 to t6. */
.macro G1_GEN rd, od
    lla     t0, 904f
    COPY    \rd, \od, t0, 0, 96
    SET_ONE \rd, \od + 96
.endm

/* The generator of G2 as a G2 point at rd + od. Uses t0, t2 to t6. */
.macro G2_GEN rd, od
    lla     t0, 905f
    COPY    \rd, \od, t0, 0, 192
    SET_ONE \rd, \od + 192
    ZERO    \rd, \od + 240, 48
.endm

/*
 * crypto_kzg_g1_lincomb(result, points, scalars, n, work): the sum of
 * scalars[j] times points[j] (g1LincombPoints), by the steps of G1.msm:
 * Pippenger's method with windows of 8 bits, from the top window down, the
 * point at infinity for n = 0 or all scalars 0. n in a3. work holds 32 n +
 * 37296 bytes: the values of the scalars, the 256 buckets, then the sum,
 * the running sum and the partial sum.
 */
LOCAL_FUNCTION crypto_kzg_g1_lincomb
    ENTER   0
    mv      s1, a0                          # result
    mv      s2, a1                          # points
    mv      s3, a2                          # scalars
    mv      s4, a3                          # n
    mv      s5, a4                          # work: the values
    beqz    s4, 8f
    li      s6, 0                           # vals = the values of the scalars
1:  slli    a1, s6, 5
    add     a0, s5, a1
    add     a1, s3, a1
    call    crypto_kzg_fr_canonical
    addi    s6, s6, 1
    bltu    s6, s4, 1b
    li      s7, 0                           # msmMaxBits
    li      s6, 0
2:  slli    t0, s6, 5
    add     t0, s5, t0
    li      a5, 192
    ld      a4, 24(t0)
    bnez    a4, 3f
    li      a5, 128
    ld      a4, 16(t0)
    bnez    a4, 3f
    li      a5, 64
    ld      a4, 8(t0)
    bnez    a4, 3f
    li      a5, 0
    ld      a4, 0(t0)
    beqz    a4, 4f
3:  addi    a5, a5, 1                       # bit length: 1 + the base + the top set bit of a4
30: srli    a4, a4, 1
    beqz    a4, 31f
    addi    a5, a5, 1
    j       30b
31: bleu    a5, s7, 4f
    mv      s7, a5
4:  addi    s6, s6, 1
    bltu    s6, s4, 2b
    beqz    s7, 8f
    addi    s7, s7, 7                       # nW
    srli    s7, s7, 3
    slli    s8, s4, 5                       # the buckets
    add     s8, s5, s8
    li      t0, 256 * BLS_G1                # the sum, then the running and partial sums
    add     s10, s8, t0
    G1_ZERO s10, 0
    li      s9, 0                           # kk
5:  li      s6, 1                           # buckets 1 to 255 at infinity
6:  li      t0, BLS_G1
    mul     a4, s6, t0
    add     a4, s8, a4
    G1_ZERO a4, 0
    addi    s6, s6, 1
    li      t0, 256
    bltu    s6, t0, 6b
    li      s6, 0                           # msmBuckets
7:  sub     t0, s7, s9                      # k = nW - 1 - kk
    addi    t0, t0, -1
    slli    t1, s6, 5
    add     t1, s5, t1
    add     t1, t1, t0
    lbu     t1, 0(t1)                       # digit k of vals[j]
    beqz    t1, 70f
    li      t0, BLS_G1
    mul     a0, t1, t0
    add     a0, s8, a0
    mul     a1, s6, t0
    add     a1, s2, a1
    mv      a2, a0
    CALL_GLOBAL crypto_bls_g1_add
70: addi    s6, s6, 1
    bltu    s6, s4, 7b
    G1_ZERO s10, BLS_G1                     # msmRunning: from bucket 255 down to 1
    G1_ZERO s10, 2 * BLS_G1
    li      s6, 255
71: li      t0, BLS_G1
    mul     a1, s6, t0
    add     a1, s8, a1
    addi    a0, s10, BLS_G1
    addi    a2, s10, BLS_G1
    CALL_GLOBAL crypto_bls_g1_add           # running += B_v
    addi    a0, s10, 2 * BLS_G1
    addi    a1, s10, BLS_G1
    addi    a2, s10, 2 * BLS_G1
    CALL_GLOBAL crypto_bls_g1_add           # partial += running
    addi    s6, s6, -1
    bnez    s6, 71b
    beqz    s9, 73f                         # msmCombine: 8 doublings, except for the first window
    li      s6, 8
72: mv      a0, s10
    mv      a1, s10
    call    crypto_bls_g1_double
    addi    s6, s6, -1
    bnez    s6, 72b
73: mv      a0, s10
    addi    a1, s10, 2 * BLS_G1
    mv      a2, s10
    CALL_GLOBAL crypto_bls_g1_add
    addi    s9, s9, 1
    bltu    s9, s7, 5b
    COPY    s1, 0, s10, 0, BLS_G1
    LEAVE   0
8:  G1_ZERO s1, 0
    LEAVE   0
END_FUNCTION crypto_kzg_g1_lincomb

/* crypto_kzg_domain(domain): the bit-reversed 4096-th roots of unity (rootsOfUnityBrp 4096). */
LOCAL_FUNCTION crypto_kzg_domain
    ENTER   0
    mv      s1, a0
    li      a1, 4096
    call    crypto_kzg_roots_of_unity
    mv      a0, s1
    li      a1, 4096
    li      a2, 32
    call    crypto_kzg_bit_reversal
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
    ENTER   EV_SIZE
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3                          # the domain
    li      t0, 131072
    add     s5, s4, t0                      # z - d_i
    li      t0, 262144
    add     s6, s4, t0                      # the inverses
    mv      a0, s4
    call    crypto_kzg_domain
    li      s7, 0                           # z in the domain: its value
1:  slli    s8, s7, 5
    add     s8, s4, s8
    EQUAL   s8, 0, s3, 0, 32
    bnez    t0, 2f
    slli    t0, s7, 5
    add     t0, s2, t0
    COPY    s1, 0, t0, 0, 32
    LEAVE   EV_SIZE
2:  addi    s7, s7, 1
    li      t0, 4096
    bltu    s7, t0, 1b
    li      s7, 0
3:  slli    a2, s7, 5
    add     a0, s5, a2
    mv      a1, s3
    add     a2, s4, a2
    call    crypto_kzg_fr_sub
    addi    s7, s7, 1
    li      t0, 4096
    bltu    s7, t0, 3b
    mv      a0, s6
    mv      a1, s5
    li      a2, 4096
    call    crypto_kzg_batch_inverse
    ZERO    sp, EV_ACC, 32
    li      s7, 0
4:  slli    a2, s7, 5                       # acc += p_i d_i inv_i
    addi    a0, sp, EV_T
    add     a1, s2, a2
    add     a2, s4, a2
    call    crypto_kzg_fr_mul
    addi    a0, sp, EV_T
    addi    a1, sp, EV_T
    slli    a2, s7, 5
    add     a2, s6, a2
    call    crypto_kzg_fr_mul
    RADD    sp, EV_ACC, sp, EV_ACC, sp, EV_T
    addi    s7, s7, 1
    li      t0, 4096
    bltu    s7, t0, 4b
    li      t0, 4096                        # r = z^4096 - 1
    sd      t0, EV_E(sp)
    sd      zero, EV_E+8(sp)
    sd      zero, EV_E+16(sp)
    sd      zero, EV_E+24(sp)
    C3      crypto_kzg_fr_pow, sp, EV_T, s3, 0, sp, EV_E
    SET_FR_ONE sp, EV_E
    RSUB    sp, EV_T, sp, EV_T, sp, EV_E
    RMUL    sp, EV_ACC, sp, EV_ACC, sp, EV_T        # acc r / 4096
    addi    a0, sp, EV_T
    li      a1, 4096
    call    crypto_kzg_fr_from_u64
    C2      crypto_kzg_fr_inverse, sp, EV_T, sp, EV_T
    RMUL    s1, 0, sp, EV_ACC, sp, EV_T
    LEAVE   EV_SIZE
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
    ENTER   QD_SIZE
    mv      s1, a0
    mv      s2, a1                          # z
    mv      s3, a2                          # poly
    mv      s4, a3                          # y
    mv      s5, a4                          # the domain
    li      t0, 131072
    add     s6, s5, t0                      # z (z - d_i)
    li      t0, 262144
    add     s7, s5, t0                      # the inverses
    mv      a0, s5
    call    crypto_kzg_domain
    li      s8, 0
1:  slli    a2, s8, 5
    add     a0, s6, a2
    mv      a1, s2
    add     a2, s5, a2
    call    crypto_kzg_fr_sub
    slli    a0, s8, 5
    add     a0, s6, a0
    mv      a1, s2
    mv      a2, a0
    call    crypto_kzg_fr_mul
    addi    s8, s8, 1
    li      t0, 4096
    bltu    s8, t0, 1b
    mv      a0, s7
    mv      a1, s6
    li      a2, 4096
    call    crypto_kzg_batch_inverse
    ZERO    s1, 0, 32
    li      s8, 0
2:  slli    s9, s8, 5
    add     s9, s5, s9
    EQUAL   s9, 0, s2, 0, 32                # skip d_i = z
    beqz    t0, 3f
    addi    a0, sp, QD_T
    slli    a1, s8, 5
    add     a1, s3, a1
    mv      a2, s4
    call    crypto_kzg_fr_sub
    RMUL    sp, QD_T, sp, QD_T, s9, 0
    addi    a0, sp, QD_T
    addi    a1, sp, QD_T
    slli    a2, s8, 5
    add     a2, s7, a2
    call    crypto_kzg_fr_mul
    RADD    s1, 0, s1, 0, sp, QD_T
3:  addi    s8, s8, 1
    li      t0, 4096
    bltu    s8, t0, 2b
    LEAVE   QD_SIZE
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
    mv      s1, a0                          # settings
    mv      s2, a1                          # poly
    mv      s3, a2                          # z
    mv      s4, a3                          # work
    mv      s5, a4                          # proof
    mv      s6, a5                          # y
    mv      a0, s6
    mv      a1, s2
    mv      a2, s3
    li      t0, PI_WORK
    add     a3, s4, t0
    call    crypto_kzg_evaluate
    mv      a0, s4
    call    crypto_kzg_domain
    li      s7, 0
1:  slli    s8, s7, 5                       # p_i - y, and d_i - z
    li      t0, PI_SHIFT
    add     a0, s4, t0
    add     a0, a0, s8
    add     a1, s2, s8
    mv      a2, s6
    call    crypto_kzg_fr_sub
    li      t0, PI_DEN
    add     a0, s4, t0
    add     a0, a0, s8
    add     a1, s4, s8
    mv      a2, s3
    call    crypto_kzg_fr_sub
    addi    s7, s7, 1
    li      t0, 4096
    bltu    s7, t0, 1b
    li      t0, PI_INV
    add     a0, s4, t0
    li      t0, PI_DEN
    add     a1, s4, t0
    li      a2, 4096
    call    crypto_kzg_batch_inverse
    li      s7, 0
2:  slli    s8, s7, 5
    li      t0, PI_DEN
    add     s9, s4, t0
    add     s9, s9, s8
    IS_ZERO s9, 0, 32
    bnez    t0, 3f
    li      t0, PI_Q                        # z is the domain point d_i
    add     a0, s4, t0
    add     a0, a0, s8
    add     a1, s4, s8
    mv      a2, s2
    mv      a3, s6
    li      t0, PI_WORK
    add     a4, s4, t0
    call    crypto_kzg_quotient_in_domain
    j       4f
3:  li      t0, PI_Q
    add     a0, s4, t0
    add     a0, a0, s8
    li      t0, PI_SHIFT
    add     a1, s4, t0
    add     a1, a1, s8
    li      t0, PI_INV
    add     a2, s4, t0
    add     a2, a2, s8
    call    crypto_kzg_fr_mul
4:  addi    s7, s7, 1
    li      t0, 4096
    bltu    s7, t0, 2b
    mv      a0, s5
    addi    a1, s1, CRYPTO_KZG_SETTINGS_G1_LAGRANGE
    li      t0, PI_Q
    add     a2, s4, t0
    li      a3, 4096
    li      t0, PI_WORK
    add     a4, s4, t0
    call    crypto_kzg_g1_lincomb
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
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    addi    s4, s2, VI_PAIRS                # pair 1: (C - [y], -[1])
    C2      crypto_kzg_fr_neg, s2, VI_K, s2, VI_Y
    C2      crypto_kzg_fr_canonical, s2, VI_K, s2, VI_K
    G1_GEN  s4, 8
    C3      crypto_bls_g1_mul, s4, 8, s4, 8, s2, VI_K
    G3      crypto_bls_g1_add, s2, VI_C, s4, 8, s4, 8
    G2_GEN  s4, 152
    C2      crypto_bls_g2_neg, s4, 152, s4, 152
    COPY    s4, 440, s2, VI_P, BLS_G1       # pair 2: (proof, [s] - [z])
    C2      crypto_kzg_fr_neg, s2, VI_K, s2, VI_Z
    C2      crypto_kzg_fr_canonical, s2, VI_K, s2, VI_K
    G2_GEN  s4, 584
    C3      crypto_bls_g2_mul, s4, 584, s4, 584, s2, VI_K
    C3      crypto_bls_g2_add, s4, 584, s1, 0, s4, 584
    li      t0, 2
    sd      t0, 0(s4)
    mv      a0, s4
    addi    a1, s2, VI_WORK
    mv      a2, s3
    call    crypto_bls_pairing_check
    LEAVE   0
END_FUNCTION crypto_kzg_verify_impl

/* ---------------------------------------------------------------- Blob functions (Core.lean) */

/* crypto_kzg_blob_to_kzg_commitment(settings, blob, scratch, commitment) -> status: blobToKzgCommitment. */
.set BC_POINT, 131072
.set BC_WORK, 131216
FUNCTION crypto_kzg_blob_to_kzg_commitment
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    KZG_SCRATCH_CHECK s3, zero, 8f
    addi    s5, s3, 8
    mv      a0, s5
    mv      a1, s2
    li      a2, 4096
    call    crypto_kzg_blob_to_poly
    bnez    a0, 9f
    li      t0, BC_POINT
    add     s6, s5, t0
    mv      a0, s6
    addi    a1, s1, CRYPTO_KZG_SETTINGS_G1_LAGRANGE
    mv      a2, s5
    li      a3, 4096
    addi    a4, s6, (BC_WORK - BC_POINT)
    call    crypto_kzg_g1_lincomb
    G2      crypto_bls_g1_compress, s6, 0, s4, 0
    li      a0, CRYPTO_OK
9:  LEAVE   0
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
END_FUNCTION crypto_kzg_blob_to_kzg_commitment

/* crypto_kzg_compute_kzg_proof(settings, blob, z, scratch, proof, y) -> status: computeKzgProof. */
.set KP_Z, 131072
.set KP_Y, 131104
.set KP_POINT, 131136
.set KP_WORK, 131280
FUNCTION crypto_kzg_compute_kzg_proof
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      s5, a4
    mv      s6, a5
    KZG_SCRATCH_CHECK s4, zero, 8f
    addi    s7, s4, 8
    mv      a0, s7
    mv      a1, s2
    li      a2, 4096
    call    crypto_kzg_blob_to_poly
    bnez    a0, 9f
    li      t0, KP_Z
    add     s8, s7, t0
    mv      a0, s8
    mv      a1, s3
    call    crypto_kzg_fr_from_bytes
    bnez    a0, 9f
    mv      a0, s1
    mv      a1, s7
    mv      a2, s8
    addi    a3, s8, (KP_WORK - KP_Z)
    addi    a4, s8, (KP_POINT - KP_Z)
    addi    a5, s8, (KP_Y - KP_Z)
    call    crypto_kzg_proof_impl
    G2      crypto_bls_g1_compress, s8, (KP_POINT - KP_Z), s5, 0
    C2      crypto_kzg_fr_to_bytes, s6, 0, s8, (KP_Y - KP_Z)
    li      a0, CRYPTO_OK
9:  LEAVE   0
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
END_FUNCTION crypto_kzg_compute_kzg_proof

/* crypto_kzg_verify_kzg_proof(settings, commitment, z, y, proof, scratch, valid) -> status: verifyKzgProof. */
FUNCTION crypto_kzg_verify_kzg_proof
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      s5, a4
    mv      s6, a5
    mv      s7, a6
    KZG_SCRATCH_CHECK s6, zero, 8f
    addi    s8, s6, 8                       # the area of crypto_kzg_verify_impl
    C2      crypto_kzg_validate_g1, s2, 0, s8, VI_C
    bnez    a0, 5f
    C2      crypto_kzg_validate_g1, s5, 0, s8, VI_P
    bnez    a0, 6f
    C2      crypto_kzg_fr_from_bytes, s8, VI_Z, s3, 0
    bnez    a0, 9f
    C2      crypto_kzg_fr_from_bytes, s8, VI_Y, s4, 0
    bnez    a0, 9f
    li      t0, CRYPTO_KZG_SETTINGS_G2_MONOMIAL + BLS_G2    # [s]
    add     a0, s1, t0
    mv      a1, s8
    mv      a2, s7
    call    crypto_kzg_verify_impl
    li      a0, CRYPTO_OK
9:  LEAVE   0
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
5:  li      a0, CRYPTO_KZG_INVALID_COMMITMENT
    LEAVE   0
6:  li      a0, CRYPTO_KZG_INVALID_PROOF
    LEAVE   0
END_FUNCTION crypto_kzg_verify_kzg_proof

/* crypto_kzg_compute_blob_kzg_proof(settings, blob, commitment, scratch, proof) -> status: computeBlobKzgProof. */
FUNCTION crypto_kzg_compute_blob_kzg_proof
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      s5, a4
    KZG_SCRATCH_CHECK s4, zero, 8f
    addi    s6, s4, 8
    li      t0, KP_Z
    add     s7, s6, t0
    mv      a0, s3                          # bytesToKzgCommitment
    addi    a1, s7, (KP_POINT - KP_Z)
    call    crypto_kzg_validate_g1
    bnez    a0, 7f
    mv      a0, s6
    mv      a1, s2
    li      a2, 4096
    call    crypto_kzg_blob_to_poly
    bnez    a0, 9f
    mv      a0, s7                          # z = the challenge
    mv      a1, s2
    mv      a2, s3
    addi    a3, s7, (KP_WORK - KP_Z)
    call    crypto_kzg_challenge
    mv      a0, s1
    mv      a1, s6
    mv      a2, s7
    addi    a3, s7, (KP_WORK - KP_Z)
    addi    a4, s7, (KP_POINT - KP_Z)
    addi    a5, s7, (KP_Y - KP_Z)
    call    crypto_kzg_proof_impl
    G2      crypto_bls_g1_compress, s7, (KP_POINT - KP_Z), s5, 0
    li      a0, CRYPTO_OK
9:  LEAVE   0
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
7:  li      a0, CRYPTO_KZG_INVALID_COMMITMENT
    LEAVE   0
END_FUNCTION crypto_kzg_compute_blob_kzg_proof

/* crypto_kzg_verify_blob_kzg_proof(settings, blob, commitment, proof, scratch, valid) -> status: verifyBlobKzgProof. */
.set VB_AREA, 131072
.set VB_WORK, 138240
FUNCTION crypto_kzg_verify_blob_kzg_proof
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      s5, a4
    mv      s6, a5
    KZG_SCRATCH_CHECK s5, zero, 8f
    addi    s7, s5, 8
    li      t0, VB_AREA
    add     s8, s7, t0
    C2      crypto_kzg_validate_g1, s3, 0, s8, VI_C
    bnez    a0, 5f
    mv      a0, s7
    mv      a1, s2
    li      a2, 4096
    call    crypto_kzg_blob_to_poly
    bnez    a0, 9f
    addi    a0, s8, VI_Z                    # z = the challenge, y = p(z)
    mv      a1, s2
    mv      a2, s3
    li      t0, VB_WORK
    add     a3, s7, t0
    call    crypto_kzg_challenge
    addi    a0, s8, VI_Y
    mv      a1, s7
    addi    a2, s8, VI_Z
    li      t0, VB_WORK
    add     a3, s7, t0
    call    crypto_kzg_evaluate
    C2      crypto_kzg_validate_g1, s4, 0, s8, VI_P
    bnez    a0, 6f
    li      t0, CRYPTO_KZG_SETTINGS_G2_MONOMIAL + BLS_G2
    add     a0, s1, t0
    mv      a1, s8
    mv      a2, s6
    call    crypto_kzg_verify_impl
    li      a0, CRYPTO_OK
9:  LEAVE   0
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
5:  li      a0, CRYPTO_KZG_INVALID_COMMITMENT
    LEAVE   0
6:  li      a0, CRYPTO_KZG_INVALID_PROOF
    LEAVE   0
END_FUNCTION crypto_kzg_verify_blob_kzg_proof

/*
 * crypto_kzg_verify_blob_kzg_proof_batch(settings, blobs, commitments, proofs,
 * scratch, valid) -> status: verifyBlobKzgProofBatch, then verifyKzgProofBatch.
 * work: the polynomial, the work of the evaluation and the challenges, the
 * fixed points, then the arrays of the n entries and the work of the sums.
 * The arrays: CG s9, PG s10, ZS s11, YS s0, then RP, ZR, CM, the data and
 * the work of the sums on the stack.
 */
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
.set VBS_RP, 0
.set VBS_ZR, 8
.set VBS_CM, 16
.set VBS_DATA, 24
.set VBS_MSM, 32
.set VBS_SIZE, 48
FUNCTION crypto_kzg_verify_blob_kzg_proof_batch
    ENTER   VBS_SIZE
    mv      s1, a0                          # settings
    mv      s5, a4                          # scratch, then work
    mv      s6, a5                          # valid
    ld      s7, CRYPTO_KZG_LIST_COUNT(a1)   # n
    KZG_SCRATCH_CHECK s5, s7, 8f
    ld      t0, CRYPTO_KZG_LIST_COUNT(a2)
    bne     t0, s7, 4f
    ld      t0, CRYPTO_KZG_LIST_COUNT(a3)
    bne     t0, s7, 4f
    ld      t0, CRYPTO_KZG_LIST_OFFSET(a1)
    add     s2, a1, t0                      # the blobs
    ld      t0, CRYPTO_KZG_LIST_OFFSET(a2)
    add     s3, a2, t0                      # the commitments
    ld      t0, CRYPTO_KZG_LIST_OFFSET(a3)
    add     s4, a3, t0                      # the proofs
    addi    s5, s5, 8
    li      t0, VBB_ARR                     # the arrays
    add     s9, s5, t0
    li      t0, BLS_G1
    mul     t1, s7, t0                      # 144 n
    slli    t2, s7, 5                       # 32 n
    add     s10, s9, t1
    add     s11, s10, t1
    add     s0, s11, t2
    add     t0, s0, t2
    sd      t0, VBS_RP(sp)
    add     t0, t0, t2
    sd      t0, VBS_ZR(sp)
    add     t0, t0, t2
    sd      t0, VBS_CM(sp)
    add     t0, t0, t1
    sd      t0, VBS_DATA(sp)
    li      t3, 160                         # the data: 24 + 32 + 160 n, then the digest
    mul     t3, t3, s7
    add     t0, t0, t3
    addi    t0, t0, 24 + 32 + 32
    sd      t0, VBS_MSM(sp)
    li      s8, 0                           # each triple: commitment, blob, proof
1:  bgeu    s8, s7, 2f
    li      t0, 48
    mul     a0, s8, t0
    add     a0, s3, a0
    li      t0, BLS_G1
    mul     a1, s8, t0
    add     a1, s9, a1
    call    crypto_kzg_validate_g1
    bnez    a0, 5f
    mv      a0, s5
    slli    a1, s8, 17
    add     a1, s2, a1
    li      a2, 4096
    call    crypto_kzg_blob_to_poly
    bnez    a0, 9f
    slli    a0, s8, 5                       # z_i = the challenge
    add     a0, s11, a0
    slli    a1, s8, 17
    add     a1, s2, a1
    li      t0, 48
    mul     a2, s8, t0
    add     a2, s3, a2
    li      t0, VBB_EVAL
    add     a3, s5, t0
    call    crypto_kzg_challenge
    slli    a0, s8, 5                       # y_i = p_i(z_i)
    add     a0, s0, a0
    mv      a1, s5
    slli    a2, s8, 5
    add     a2, s11, a2
    li      t0, VBB_EVAL
    add     a3, s5, t0
    call    crypto_kzg_evaluate
    li      t0, 48
    mul     a0, s8, t0
    add     a0, s4, a0
    li      t0, BLS_G1
    mul     a1, s8, t0
    add     a1, s10, a1
    call    crypto_kzg_validate_g1
    bnez    a0, 6f
    addi    s8, s8, 1
    j       1b
2:  ld      a3, VBS_DATA(sp)                # r: computeVerifyKzgProofBatchChallenge
    li      t0, 160
    mul     t0, t0, s7
    addi    t1, t0, 32                      # count
    addi    t0, t0, 24 + 32 + 32            # size
    sd      t0, 0(a3)
    li      t0, 24
    sd      t0, 8(a3)
    sd      t1, 16(a3)
    lla     t1, 946f
    ld      t0, 0(t1)
    sd      t0, 24(a3)
    ld      t0, 8(t1)
    sd      t0, 32(a3)
    li      t0, 0x10                        # I2OSP(4096, 8)
    slli    t0, t0, 48
    sd      t0, 40(a3)
    mv      a4, s7                          # I2OSP(n, 8)
    STORE_BE64 a4, a3, 48, t0
    addi    s8, a3, 56                      # the next byte of the data
    li      a7, 0
    sd      a7, VBS_SIZE - 8(sp)
3:  ld      a7, VBS_SIZE - 8(sp)
    bgeu    a7, s7, 30f
    li      t0, 48                          # commitment, z, y, proof
    mul     a4, a7, t0
    add     a4, s3, a4
    li      a5, 48
    COPY_BYTES s8, a4, a5
    mv      a0, s8
    ld      a7, VBS_SIZE - 8(sp)
    slli    a1, a7, 5
    add     a1, s11, a1
    call    crypto_kzg_fr_to_bytes
    addi    a0, s8, 32
    ld      a7, VBS_SIZE - 8(sp)
    slli    a1, a7, 5
    add     a1, s0, a1
    call    crypto_kzg_fr_to_bytes
    addi    s8, s8, 64
    ld      a7, VBS_SIZE - 8(sp)
    li      t0, 48
    mul     a4, a7, t0
    add     a4, s4, a4
    li      a5, 48
    COPY_BYTES s8, a4, a5
    addi    a7, a7, 1
    sd      a7, VBS_SIZE - 8(sp)
    j       3b
30: ld      a0, VBS_DATA(sp)
    mv      a1, s8                          # the digest, after the data
    CALL_GLOBAL crypto_sha256
    li      t0, VBB_R
    add     a0, s5, t0
    mv      a1, s8
    call    crypto_kzg_fr_from_digest
    beqz    s7, 32f                         # r^i: computePowers
    ld      s8, VBS_RP(sp)
    SET_FR_ONE s8, 0
    li      a7, 1
    sd      a7, VBS_SIZE - 8(sp)
31: ld      a7, VBS_SIZE - 8(sp)
    bgeu    a7, s7, 32f
    slli    a0, a7, 5
    add     a0, s8, a0
    addi    a1, a0, -32
    li      t0, VBB_R
    add     a2, s5, t0
    call    crypto_kzg_fr_mul
    ld      a7, VBS_SIZE - 8(sp)
    addi    a7, a7, 1
    sd      a7, VBS_SIZE - 8(sp)
    j       31b
32: li      t0, VBB_L1                      # the sum of r^i proof_i
    add     a0, s5, t0
    mv      a1, s10
    ld      a2, VBS_RP(sp)
    mv      a3, s7
    ld      a4, VBS_MSM(sp)
    call    crypto_kzg_g1_lincomb
    li      s8, 0                           # z_i r^i
33: bgeu    s8, s7, 34f
    slli    t1, s8, 5
    ld      a0, VBS_ZR(sp)
    add     a0, a0, t1
    add     a1, s11, t1
    ld      a2, VBS_RP(sp)
    add     a2, a2, t1
    call    crypto_kzg_fr_mul
    addi    s8, s8, 1
    j       33b
34: li      t0, VBB_L2                      # the sum of z_i r^i proof_i
    add     a0, s5, t0
    mv      a1, s10
    ld      a2, VBS_ZR(sp)
    mv      a3, s7
    ld      a4, VBS_MSM(sp)
    call    crypto_kzg_g1_lincomb
    li      t0, VBB_K                       # C_i - [y_i]
    add     s2, s5, t0                      # the blobs are done: s2 is the k area
    li      s8, 0
35: bgeu    s8, s7, 36f
    mv      a0, s2
    slli    a1, s8, 5
    add     a1, s0, a1
    call    crypto_kzg_fr_neg
    C2      crypto_kzg_fr_canonical, s2, 0, s2, 0
    G1_GEN  s2, (VBB_TMP - VBB_K)
    C3      crypto_bls_g1_mul, s2, (VBB_TMP - VBB_K), s2, (VBB_TMP - VBB_K), s2, 0
    li      t0, BLS_G1
    mul     t1, s8, t0
    add     a0, s9, t1
    addi    a1, s2, (VBB_TMP - VBB_K)
    ld      a2, VBS_CM(sp)
    add     a2, a2, t1
    CALL_GLOBAL crypto_bls_g1_add
    addi    s8, s8, 1
    j       35b
36: li      t0, VBB_L3                      # the sum of r^i (C_i - [y_i])
    add     a0, s5, t0
    ld      a1, VBS_CM(sp)
    ld      a2, VBS_RP(sp)
    mv      a3, s7
    ld      a4, VBS_MSM(sp)
    call    crypto_kzg_g1_lincomb
    li      t0, VBB_PAIRS                   # the pairs
    add     s8, s5, t0
    li      t0, 2
    sd      t0, 0(s8)
    li      t0, VBB_L1
    add     t0, s5, t0
    COPY    s8, 8, t0, 0, BLS_G1
    addi    a0, s8, 152                     # -[s]
    li      t0, CRYPTO_KZG_SETTINGS_G2_MONOMIAL + BLS_G2
    add     a1, s1, t0
    call    crypto_bls_g2_neg
    li      t0, VBB_L3
    add     a0, s5, t0
    li      t0, VBB_L2
    add     a1, s5, t0
    addi    a2, s8, 440
    CALL_GLOBAL crypto_bls_g1_add
    G2_GEN  s8, 584
    mv      a0, s8
    li      t0, VBB_PW
    add     a1, s5, t0
    mv      a2, s6
    call    crypto_bls_pairing_check
    li      a0, CRYPTO_OK
9:  LEAVE   VBS_SIZE
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   VBS_SIZE
4:  li      a0, CRYPTO_KZG_LENGTH_MISMATCH
    LEAVE   VBS_SIZE
5:  li      a0, CRYPTO_KZG_INVALID_COMMITMENT
    LEAVE   VBS_SIZE
6:  li      a0, CRYPTO_KZG_INVALID_PROOF
    LEAVE   VBS_SIZE
END_FUNCTION crypto_kzg_verify_blob_kzg_proof_batch

/* ---------------------------------------------------------------- Cells (Cells.lean, Fft.lean) */

/*
 * crypto_kzg_g1_fft(vals, n, roots, work): the FFT in G1 of the n points at
 * vals, in place (fftG1): the butterflies of fftG1Vector, in the order of
 * fftFieldIter: the bit-reversal permutation, then for each pair the
 * product t of the second point by its root, and the pair (l + t, l - t).
 * n (a power of two) in a1; roots holds the n-th roots of unity. work holds
 * 320 bytes.
 */
.set GF_T, 0
.set GF_N, 144
.set GF_K, 288
LOCAL_FUNCTION crypto_kzg_g1_fft
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    li      a2, BLS_G1
    call    crypto_kzg_bit_reversal
    li      s5, 0                           # log2 h
    srli    s6, s2, 1                       # m
1:  beqz    s6, 9f
    li      s7, 0                           # pair j < n / 2
2:  srl     t0, s7, s5
    li      t1, 1
    sll     t1, t1, s5                      # h
    addi    t2, t1, -1
    and     t2, s7, t2                      # r = j mod h
    addi    t3, s5, 1
    sll     t0, t0, t3
    add     t0, t0, t2                      # i1
    add     t1, t0, t1                      # i2 = i1 + h
    li      t3, BLS_G1
    mul     s8, t0, t3
    add     s8, s1, s8                      # the points
    mul     s9, t1, t3
    add     s9, s1, s9
    mul     t4, s6, t2                      # root m r
    addi    a0, s4, GF_K
    slli    a1, t4, 5
    add     a1, s3, a1
    call    crypto_kzg_fr_canonical
    C3      crypto_bls_g1_mul, s4, GF_T, s9, 0, s4, GF_K
    G2      crypto_bls_g1_neg, s4, GF_T, s4, GF_N
    G3      crypto_bls_g1_add, s8, 0, s4, GF_N, s9, 0       # l - t
    G3      crypto_bls_g1_add, s8, 0, s4, GF_T, s8, 0       # l + t
    addi    s7, s7, 1
    srli    t0, s2, 1
    bltu    s7, t0, 2b
    addi    s5, s5, 1
    srli    s6, s6, 1
    j       1b
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
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      s5, a4
    mv      a0, s4                          # the cells
    mv      a1, s2
    addi    a2, s3, FK_EXT
    call    crypto_kzg_extended_cells
    li      t0, FK_H
    add     s6, s3, t0
    li      s7, 1                           # d
1:  addi    t1, s7, -1                      # H_d, in entry d - 1
    li      t0, BLS_G1
    mul     a0, t1, t0
    add     a0, s6, a0
    li      t0, CRYPTO_KZG_SETTINGS_G1_MONOMIAL
    add     a1, s1, t0
    slli    a2, s7, 11                      # coeff[64 d]
    add     a2, s2, a2
    slli    a3, s7, 6                       # 4096 - 64 d points
    li      t0, 4096
    sub     a3, t0, a3
    li      t0, FK_MSM
    add     a4, s3, t0
    call    crypto_kzg_g1_lincomb
    addi    s7, s7, 1
    li      t0, 64
    bltu    s7, t0, 1b
    li      s7, 63                          # padding
2:  li      t0, BLS_G1
    mul     a4, s7, t0
    add     a4, s6, a4
    G1_ZERO a4, 0
    addi    s7, s7, 1
    li      t0, 128
    bltu    s7, t0, 2b
    li      t0, FK_R
    add     a0, s3, t0
    li      a1, 128
    call    crypto_kzg_roots_of_unity
    mv      a0, s6
    li      a1, 128
    li      t0, FK_R
    add     a2, s3, t0
    li      t0, FK_FW
    add     a3, s3, t0
    call    crypto_kzg_g1_fft
    mv      a0, s6
    li      a1, 128
    li      a2, BLS_G1
    call    crypto_kzg_bit_reversal
    li      s7, 0
3:  li      t0, BLS_G1
    mul     a0, s7, t0
    add     a0, s6, a0
    li      t0, 48
    mul     a1, s7, t0
    add     a1, s5, a1
    CALL_GLOBAL crypto_bls_g1_compress
    addi    s7, s7, 1
    li      t0, 128
    bltu    s7, t0, 3b
    LEAVE   0
END_FUNCTION crypto_kzg_fk20

/* crypto_kzg_compute_cells_and_kzg_proofs(settings, blob, scratch, cells, proofs) -> status: computeCellsAndKzgProofs. */
FUNCTION crypto_kzg_compute_cells_and_kzg_proofs
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      s5, a4
    KZG_SCRATCH_CHECK s3, zero, 8f
    addi    s6, s3, 8                       # the polynomial, then the roots, then the work of crypto_kzg_fk20
    mv      a0, s6
    mv      a1, s2
    li      a2, 4096
    call    crypto_kzg_blob_to_poly
    bnez    a0, 9f
    mv      a0, s6
    li      t0, 131072
    add     a1, s6, t0
    call    crypto_kzg_eval_to_coeff
    mv      a0, s1
    mv      a1, s6
    li      t0, 262144
    add     a2, s6, t0
    mv      a3, s4
    mv      a4, s5
    call    crypto_kzg_fk20
    li      a0, CRYPTO_OK
9:  LEAVE   0
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
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
 * 104 + 48 m + 2112 n bytes.
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
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    ld      s4, CQ_M(s2)
    ld      s5, CQ_N(s2)
    li      t0, 48                          # count = 48 + 48 m + 2112 n
    mul     t1, s4, t0
    li      t0, 2112
    mul     t2, s5, t0
    add     t1, t1, t2
    addi    t1, t1, 48
    sd      t1, 16(s3)
    addi    t1, t1, 24 + 32                 # size, with room for the digest
    sd      t1, 0(s3)
    li      t0, 24
    sd      t0, 8(s3)
    lla     t1, 947f
    ld      t0, 0(t1)
    sd      t0, 24(s3)
    ld      t0, 8(t1)
    sd      t0, 32(s3)
    li      t0, 0x10                        # I2OSP(4096, 8)
    slli    t0, t0, 48
    sd      t0, 40(s3)
    li      t0, 0x40                        # I2OSP(64, 8)
    slli    t0, t0, 56
    sd      t0, 48(s3)
    STORE_BE64 s4, s3, 56, t0
    STORE_BE64 s5, s3, 64, t0
    addi    s6, s3, 72
    li      s7, 0                           # the commitments
1:  bgeu    s7, s4, 2f
    ld      t1, CQ_COMMITMENTS(s2)
    slli    t2, s7, 3
    add     t1, t1, t2
    ld      a4, 0(t1)
    li      a5, 48
    COPY_BYTES s6, a4, a5
    addi    s7, s7, 1
    j       1b
2:  li      s7, 0                           # the cells
3:  bgeu    s7, s5, 5f
    slli    t2, s7, 3
    ld      t1, CQ_CIDX(s2)
    add     t1, t1, t2
    ld      a4, 0(t1)
    STORE_BE64 a4, s6, 0, t0
    ld      t1, CQ_IDX(s2)
    add     t1, t1, t2
    ld      a4, 0(t1)
    STORE_BE64 a4, s6, 8, t0
    addi    s6, s6, 16
    ld      a4, CQ_CELLS(s2)
    slli    t1, s7, 11
    add     a4, a4, t1
    li      a5, 2048
    COPY_BYTES s6, a4, a5
    ld      a4, CQ_PROOFS(s2)
    li      t0, 48
    mul     t1, s7, t0
    add     a4, a4, t1
    li      a5, 48
    COPY_BYTES s6, a4, a5
    addi    s7, s7, 1
    j       3b
5:  mv      a0, s3
    mv      a1, s6                          # the digest, after the data
    CALL_GLOBAL crypto_sha256
    mv      a0, s1
    mv      a1, s6
    call    crypto_kzg_fr_from_digest
    LEAVE   0
END_FUNCTION crypto_kzg_cell_challenge

/*
 * crypto_kzg_check_cell_indices(indices, n) -> status: CRYPTO_KZG_CELL_INDEX
 * when one of the n u64 values is 128 or more. A leaf.
 */
LOCAL_FUNCTION crypto_kzg_check_cell_indices
    UNWIND_END_PROLOGUE
    beqz    a1, 2f
    li      t1, CRYPTO_KZG_CELLS_PER_EXT_BLOB
1:  ld      t0, 0(a0)
    bgeu    t0, t1, 8f
    addi    a0, a0, 8
    addi    a1, a1, -1
    bnez    a1, 1b
2:  li      a0, CRYPTO_OK
    ret
8:  li      a0, CRYPTO_KZG_CELL_INDEX
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
    mv      s1, a0                          # commitments
    mv      s2, a1                          # commitment indices
    mv      s3, a2                          # cell indices
    mv      s4, a3                          # cells
    mv      s5, a4                          # proofs
    mv      s6, a5                          # scratch, then work
    mv      s7, a6                          # challenge
    ld      s8, CRYPTO_KZG_LIST_COUNT(s1)   # m
    ld      s9, CRYPTO_KZG_LIST_COUNT(s2)   # n
    add     t2, s8, s9
    KZG_SCRATCH_CHECK s6, t2, 8f
    addi    s6, s6, 8
    ld      t0, CRYPTO_KZG_LIST_COUNT(s3)
    bne     t0, s9, 4f
    ld      t0, CRYPTO_KZG_LIST_COUNT(s4)
    bne     t0, s9, 4f
    ld      t0, CRYPTO_KZG_LIST_COUNT(s5)
    bne     t0, s9, 4f
    .irp r, s1, s2, s3, s4, s5
    ld      t0, CRYPTO_KZG_LIST_OFFSET(\r)
    add     \r, \r, t0
    .endr
    sd      s8, VQ_REQ+CQ_M(s6)             # the request
    li      t0, VQ_PTRS
    add     t0, s6, t0
    sd      t0, VQ_REQ+CQ_COMMITMENTS(s6)
    sd      s9, VQ_REQ+CQ_N(s6)
    sd      s2, VQ_REQ+CQ_CIDX(s6)
    sd      s3, VQ_REQ+CQ_IDX(s6)
    sd      s4, VQ_REQ+CQ_CELLS(s6)
    sd      s5, VQ_REQ+CQ_PROOFS(s6)
    li      s10, 0                          # each commitment
1:  bgeu    s10, s8, 2f
    li      t0, 48
    mul     a0, s10, t0
    add     a0, s1, a0
    slli    t1, s10, 3
    li      t2, VQ_PTRS
    add     t2, s6, t2
    add     t1, t2, t1
    sd      a0, 0(t1)
    addi    a1, s6, VQ_POINT
    call    crypto_kzg_validate_g1
    bnez    a0, 5f
    addi    s10, s10, 1
    j       1b
2:  li      t1, 0                           # each commitment index
21: bgeu    t1, s9, 22f
    slli    t2, t1, 3
    add     t2, s2, t2
    ld      t2, 0(t2)
    bgeu    t2, s8, 6f
    addi    t1, t1, 1
    j       21b
22: mv      a0, s3                          # the cell indices
    mv      a1, s9
    call    crypto_kzg_check_cell_indices
    bnez    a0, 9f
    li      s10, 0                          # each proof
3:  bgeu    s10, s9, 31f
    li      t0, 48
    mul     a0, s10, t0
    add     a0, s5, a0
    addi    a1, s6, VQ_POINT
    call    crypto_kzg_validate_g1
    bnez    a0, 7f
    addi    s10, s10, 1
    j       3b
31: li      s10, 0                          # each cell
32: bgeu    s10, s9, 33f
    addi    a0, s6, VQ_EVALS
    slli    a1, s10, 11
    add     a1, s4, a1
    li      a2, 64
    call    crypto_kzg_blob_to_poly
    bnez    a0, 9f
    addi    s10, s10, 1
    j       32b
33: addi    a0, s6, VQ_FR
    addi    a1, s6, VQ_REQ
    li      t0, VQ_PTRS                     # the data, after the m addresses
    add     a2, s6, t0
    slli    t0, s8, 3
    add     a2, a2, t0
    call    crypto_kzg_cell_challenge
    C2      crypto_kzg_fr_to_bytes, s7, 0, s6, VQ_FR
    li      a0, CRYPTO_OK
9:  LEAVE   0
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   0
4:  li      a0, CRYPTO_KZG_LENGTH_MISMATCH
    LEAVE   0
5:  li      a0, CRYPTO_KZG_INVALID_COMMITMENT
    LEAVE   0
6:  li      a0, CRYPTO_KZG_COMMITMENT_INDEX
    LEAVE   0
7:  li      a0, CRYPTO_KZG_INVALID_PROOF
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
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      a3, s1
    mv      a4, s3
    li      a5, 2048
    COPY_BYTES a3, a4, a5
    mv      a0, s1
    li      a1, 64
    li      a2, 32
    call    crypto_kzg_bit_reversal
    mv      a0, s4
    li      a1, 64
    call    crypto_kzg_roots_of_unity
    mv      a0, s1
    li      a1, 64
    mv      a2, s4
    li      a3, 1
    call    crypto_kzg_fft
    C2      crypto_kzg_fr_inverse, s4, IP_H, s2, 0
    mv      a0, s1
    li      a1, 64
    li      t0, IP_H
    add     a2, s4, t0
    call    crypto_kzg_shift_vals
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
/* stack: the arrays of the n entries, counters */
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
    ENTER   VCS_SIZE
    mv      s1, a0                          # settings
    mv      s2, a1                          # commitments
    mv      s3, a2                          # cell indices
    mv      s4, a3                          # cells
    mv      s5, a4                          # proofs
    mv      s6, a5                          # scratch, then work
    mv      s7, a6                          # valid
    ld      s8, CRYPTO_KZG_LIST_COUNT(s2)   # n
    KZG_SCRATCH_CHECK s6, s8, 8f
    addi    s6, s6, 8
    ld      t0, CRYPTO_KZG_LIST_COUNT(s4)
    bne     t0, s8, 4f
    ld      t0, CRYPTO_KZG_LIST_COUNT(s5)
    bne     t0, s8, 4f
    ld      t0, CRYPTO_KZG_LIST_COUNT(s3)
    bne     t0, s8, 4f
    .irp r, s2, s3, s4, s5
    ld      t0, CRYPTO_KZG_LIST_OFFSET(\r)
    add     \r, \r, t0
    .endr
    mv      a0, s3
    mv      a1, s8
    call    crypto_kzg_check_cell_indices
    bnez    a0, 9f
    li      t0, VC_ARR                      # the arrays
    add     t0, s6, t0
    slli    t1, s8, 3                       # 8 n
    slli    t2, s8, 5                       # 32 n
    li      t3, BLS_G1
    mul     t3, t3, s8                      # 144 n
    sd      t0, VCS_CPTR(sp)
    add     t0, t0, t1
    sd      t0, VCS_CIDX(sp)
    add     t0, t0, t1
    sd      t0, VCS_CG(sp)
    add     t0, t0, t3
    sd      t0, VCS_PG(sp)
    add     t0, t0, t3
    sd      t0, VCS_EV(sp)
    slli    t4, s8, 11
    add     t0, t0, t4
    sd      t0, VCS_RP(sp)
    add     t0, t0, t2
    sd      t0, VCS_WT(sp)
    add     t0, t0, t2
    sd      t0, VCS_SH(sp)
    add     t0, t0, t2
    sd      t0, VCS_WR(sp)
    add     t0, t0, t2
    sd      t0, VCS_DATA(sp)
    li      t4, 2160                        # the data: 104 + 48 m + 2112 n bytes, m <= n
    mul     t4, t4, s8
    add     t0, t0, t4
    addi    t0, t0, 104
    sd      t0, VCS_MSM(sp)
    li      s9, 0                           # each commitment: check, and keep the first of equal ones
    sd      zero, VCS_M(sp)
1:  bgeu    s9, s8, 20f
    li      t0, 48
    mul     s10, s9, t0
    add     s10, s2, s10                    # commitment k
    ld      t1, VCS_M(sp)
    li      t0, BLS_G1
    mul     a1, t1, t0
    ld      t0, VCS_CG(sp)
    add     a1, t0, a1
    mv      a0, s10
    call    crypto_kzg_validate_g1
    bnez    a0, 5f
    sd      zero, VCS_J(sp)                 # j: the kept commitment with these bytes
10: ld      a7, VCS_J(sp)
    ld      t1, VCS_M(sp)
    bgeu    a7, t1, 12f
    ld      a5, VCS_CPTR(sp)
    slli    a6, a7, 3
    add     a5, a5, a6
    ld      a5, 0(a5)
    EQUAL   a5, 0, s10, 0, 48
    beqz    t0, 13f
    ld      a7, VCS_J(sp)
    addi    a7, a7, 1
    sd      a7, VCS_J(sp)
    j       10b
12: ld      a5, VCS_CPTR(sp)                # a new one: j = m, m + 1
    slli    a6, a7, 3
    add     a5, a5, a6
    sd      s10, 0(a5)
    addi    a6, a7, 1
    sd      a6, VCS_M(sp)
13: ld      a7, VCS_J(sp)
    ld      a5, VCS_CIDX(sp)
    slli    a6, s9, 3
    add     a5, a5, a6
    sd      a7, 0(a5)
    addi    s9, s9, 1
    j       1b
20: li      s9, 0                           # each cell: cellToCosetEvals
2:  bgeu    s9, s8, 3f
    slli    t1, s9, 11
    ld      a0, VCS_EV(sp)
    add     a0, a0, t1
    add     a1, s4, t1
    li      a2, 64
    call    crypto_kzg_blob_to_poly
    bnez    a0, 9f
    addi    s9, s9, 1
    j       2b
3:  li      s9, 0                           # each proof
30: bgeu    s9, s8, 31f
    li      t0, 48
    mul     a0, s9, t0
    add     a0, s5, a0
    li      t0, BLS_G1
    mul     a1, s9, t0
    ld      t0, VCS_PG(sp)
    add     a1, t0, a1
    call    crypto_kzg_validate_g1
    bnez    a0, 6f
    addi    s9, s9, 1
    j       30b
31: li      t0, VC_REQ                      # r
    add     s10, s6, t0
    ld      t0, VCS_M(sp)
    sd      t0, CQ_M(s10)
    ld      t0, VCS_CPTR(sp)
    sd      t0, CQ_COMMITMENTS(s10)
    sd      s8, CQ_N(s10)
    ld      t0, VCS_CIDX(sp)
    sd      t0, CQ_CIDX(s10)
    sd      s3, CQ_IDX(s10)
    sd      s4, CQ_CELLS(s10)
    sd      s5, CQ_PROOFS(s10)
    li      t0, VC_R
    add     a0, s6, t0
    mv      a1, s10
    ld      a2, VCS_DATA(sp)
    call    crypto_kzg_cell_challenge
    beqz    s8, 41f                         # r^k
    ld      s10, VCS_RP(sp)
    SET_FR_ONE s10, 0
    li      s9, 1
40: bgeu    s9, s8, 41f
    slli    a0, s9, 5
    add     a0, s10, a0
    addi    a1, a0, -32
    li      t0, VC_R
    add     a2, s6, t0
    call    crypto_kzg_fr_mul
    addi    s9, s9, 1
    j       40b
41: li      t0, VC_LL                       # LL = the sum of r^k proof_k
    add     a0, s6, t0
    ld      a1, VCS_PG(sp)
    ld      a2, VCS_RP(sp)
    mv      a3, s8
    ld      a4, VCS_MSM(sp)
    call    crypto_kzg_g1_lincomb
    ld      a5, VCS_M(sp)                   # weights[i] = the sum of r^k over the cells of commitment i
    slli    a5, a5, 5
    ld      a3, VCS_WT(sp)
    beqz    a5, 43f
    ZERO_BYTES a3, a5
43: li      s9, 0
44: bgeu    s9, s8, 45f
    ld      t1, VCS_CIDX(sp)
    slli    t2, s9, 3
    add     t1, t1, t2
    ld      t1, 0(t1)
    slli    t1, t1, 5
    ld      a0, VCS_WT(sp)
    add     a0, a0, t1
    mv      a1, a0
    slli    t2, s9, 5
    ld      a2, VCS_RP(sp)
    add     a2, a2, t2
    call    crypto_kzg_fr_add
    addi    s9, s9, 1
    j       44b
45: li      t0, VC_RLC                      # RLC = the sum of weights[i] C_i
    add     a0, s6, t0
    ld      a1, VCS_CG(sp)
    ld      a2, VCS_WT(sp)
    ld      a3, VCS_M(sp)
    ld      a4, VCS_MSM(sp)
    call    crypto_kzg_g1_lincomb
    mv      a0, s6                          # the domain: rootsOfUnityBrp 8192
    li      a1, 8192
    call    crypto_kzg_roots_of_unity
    mv      a0, s6
    li      a1, 8192
    li      a2, 32
    call    crypto_kzg_bit_reversal
    li      s9, 0                           # shift_k = domain[64 cell index]
46: bgeu    s9, s8, 47f
    slli    t1, s9, 3
    add     t1, s3, t1
    ld      t1, 0(t1)
    slli    t1, t1, 11
    add     a4, s6, t1
    slli    t1, s9, 5
    ld      a3, VCS_SH(sp)
    add     a3, a3, t1
    li      a5, 32
    COPY_BYTES a3, a4, a5
    addi    s9, s9, 1
    j       46b
47: li      t0, VC_SUM                      # the sum of r^k I_k
    add     s10, s6, t0
    mv      a3, s10
    li      a5, 2048
    ZERO_BYTES a3, a5
    li      s9, 0
48: bgeu    s9, s8, 49f
    li      t0, VC_INTERP - VC_SUM
    add     a0, s10, t0
    slli    t1, s9, 5
    ld      a1, VCS_SH(sp)
    add     a1, a1, t1
    slli    t1, s9, 11
    ld      a2, VCS_EV(sp)
    add     a2, a2, t1
    li      t0, VC_IW - VC_SUM
    add     a3, s10, t0
    call    crypto_kzg_interpolate
    li      s11, 0                          # sum += r^k interp
480: slli   t1, s11, 5
    li      t0, VC_INTERP - VC_SUM
    add     a0, s10, t0
    add     a0, a0, t1
    mv      a1, a0
    slli    t2, s9, 5
    ld      a2, VCS_RP(sp)
    add     a2, a2, t2
    call    crypto_kzg_fr_mul
    slli    t1, s11, 5
    add     a0, s10, t1
    mv      a1, a0
    li      t0, VC_INTERP - VC_SUM
    add     a2, s10, t0
    add     a2, a2, t1
    call    crypto_kzg_fr_add
    addi    s11, s11, 1
    li      t0, 64
    bltu    s11, t0, 480b
    addi    s9, s9, 1
    j       48b
49: li      t0, VC_RLI                      # RLI = [the sum at s]
    add     a0, s6, t0
    li      t0, CRYPTO_KZG_SETTINGS_G1_MONOMIAL
    add     a1, s1, t0
    mv      a2, s10
    li      a3, 64
    ld      a4, VCS_MSM(sp)
    call    crypto_kzg_g1_lincomb
    li      t0, VC_K                        # r^k shift_k^64
    add     s10, s6, t0
    li      t0, 64                          # the exponent 64, at VC_E = VC_K + 32
    sd      t0, 32(s10)
    sd      zero, 40(s10)
    sd      zero, 48(s10)
    sd      zero, 56(s10)
    li      s9, 0
50: bgeu    s9, s8, 51f
    mv      a0, s10
    slli    t1, s9, 5
    ld      a1, VCS_SH(sp)
    add     a1, a1, t1
    addi    a2, s10, (VC_E - VC_K)
    call    crypto_kzg_fr_pow
    slli    t1, s9, 5
    ld      a0, VCS_WR(sp)
    add     a0, a0, t1
    ld      a1, VCS_RP(sp)
    add     a1, a1, t1
    mv      a2, s10
    call    crypto_kzg_fr_mul
    addi    s9, s9, 1
    j       50b
51: li      t0, VC_RLP                      # RLP = the sum of r^k shift_k^64 proof_k
    add     a0, s6, t0
    ld      a1, VCS_PG(sp)
    ld      a2, VCS_WR(sp)
    mv      a3, s8
    ld      a4, VCS_MSM(sp)
    call    crypto_kzg_g1_lincomb
    li      t0, VC_PAIRS                    # the pairs: (LL, [s^64]), (RLC - RLI + RLP, -[1])
    add     s10, s6, t0
    li      t0, 2
    sd      t0, 0(s10)
    li      t0, VC_LL
    add     t0, s6, t0
    COPY    s10, 8, t0, 0, BLS_G1
    li      t0, CRYPTO_KZG_SETTINGS_G2_MONOMIAL + 64 * BLS_G2
    add     t0, s1, t0
    COPY    s10, 152, t0, 0, BLS_G2
    li      t0, VC_RLI
    add     a0, s6, t0
    mv      a1, a0
    CALL_GLOBAL crypto_bls_g1_neg
    li      t0, VC_RLC
    add     a0, s6, t0
    li      t0, VC_RLI
    add     a1, s6, t0
    addi    a2, s10, 440
    CALL_GLOBAL crypto_bls_g1_add
    addi    a0, s10, 440
    li      t0, VC_RLP
    add     a1, s6, t0
    addi    a2, s10, 440
    CALL_GLOBAL crypto_bls_g1_add
    addi    a0, s10, 584
    li      t0, CRYPTO_KZG_SETTINGS_G2_MONOMIAL
    add     a1, s1, t0
    call    crypto_bls_g2_neg
    mv      a0, s10
    li      t0, VC_PW
    add     a1, s6, t0
    mv      a2, s7
    call    crypto_bls_pairing_check
    li      a0, CRYPTO_OK
9:  LEAVE   VCS_SIZE
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   VCS_SIZE
4:  li      a0, CRYPTO_KZG_LENGTH_MISMATCH
    LEAVE   VCS_SIZE
5:  li      a0, CRYPTO_KZG_INVALID_COMMITMENT
    LEAVE   VCS_SIZE
6:  li      a0, CRYPTO_KZG_INVALID_PROOF
    LEAVE   VCS_SIZE
END_FUNCTION crypto_kzg_verify_cell_kzg_proof_batch

/*
 * crypto_kzg_recover_cells_and_kzg_proofs(settings, cell_indices, cells,
 * scratch, recovered_cells, recovered_proofs) -> status:
 * recoverCellsAndKzgProofs: the checks, recoverPolynomialcoeff, then the
 * cells and proofs of crypto_kzg_fk20. The stack holds the count of the
 * missing cells done.
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
    ENTER   16
    mv      s1, a0                          # settings
    mv      s2, a1                          # cell indices
    mv      s3, a2                          # cells
    mv      s4, a3                          # scratch, then work
    mv      s5, a4
    mv      s6, a5
    KZG_SCRATCH_CHECK s4, zero, 8f
    addi    s4, s4, 8
    ld      s7, CRYPTO_KZG_LIST_COUNT(s2)   # n
    ld      t0, CRYPTO_KZG_LIST_COUNT(s3)
    bne     t0, s7, 4f
    li      t0, CRYPTO_KZG_CELLS_PER_EXT_BLOB / 2
    bltu    s7, t0, 5f
    li      t0, CRYPTO_KZG_CELLS_PER_EXT_BLOB
    bgtu    s7, t0, 6f
    ld      t0, CRYPTO_KZG_LIST_OFFSET(s2)
    add     s2, s2, t0
    ld      t0, CRYPTO_KZG_LIST_OFFSET(s3)
    add     s3, s3, t0
    mv      a0, s2
    mv      a1, s7
    call    crypto_kzg_check_cell_indices
    bnez    a0, 9f
    li      t0, 1                           # strictly ascending
1:  bgeu    t0, s7, 2f
    slli    t1, t0, 3
    add     t1, s2, t1
    ld      t2, -8(t1)
    ld      t3, 0(t1)
    bleu    t3, t2, 7f
    addi    t0, t0, 1
    j       1b
2:  li      s8, 0                           # cellToCosetEvals
3:  bgeu    s8, s7, 10f
    slli    t1, s8, 11
    add     a0, s4, t1
    add     a1, s3, t1
    li      a2, 64
    call    crypto_kzg_blob_to_poly
    bnez    a0, 9f
    addi    s8, s8, 1
    j       3b
10: li      t0, RC_ROU                      # the 8192-th roots of unity
    add     s9, s4, t0
    mv      a0, s9
    li      a1, 8192
    call    crypto_kzg_roots_of_unity
    li      t0, RC_EXT                      # E: the values in their places, zeros elsewhere
    add     s10, s4, t0
    mv      a3, s10
    li      a5, 262144
    ZERO_BYTES a3, a5
    li      s8, 0
12: bgeu    s8, s7, 14f
    slli    t1, s8, 3
    add     t1, s2, t1
    ld      t1, 0(t1)
    slli    t1, t1, 11
    add     a3, s10, t1
    slli    t1, s8, 11
    add     a4, s4, t1
    li      a5, 2048
    COPY_BYTES a3, a4, a5
    addi    s8, s8, 1
    j       12b
14: mv      a0, s10
    li      a1, 8192
    li      a2, 32
    call    crypto_kzg_bit_reversal
    li      t0, RC_R128                     # the missing cells, and their roots
    add     a0, s4, t0
    li      a1, 128
    call    crypto_kzg_roots_of_unity
    li      t0, RC_MISS
    add     s11, s4, t0                     # the missing list; its count in s0
    li      a3, 0                           # cell index ci
    li      s0, 0
15: li      a4, 0
16: bgeu    a4, s7, 17f
    slli    t1, a4, 3
    add     t1, s2, t1
    ld      t1, 0(t1)
    beq     t1, a3, 18f
    addi    a4, a4, 1
    j       16b
17: slli    t1, s0, 3
    add     t1, s11, t1
    sd      a3, 0(t1)
    addi    s0, s0, 1
18: addi    a3, a3, 1
    li      t0, 128
    bltu    a3, t0, 15b
    li      t0, RC_SHORT                    # the short polynomial: 1, then times (X - x) for each
    add     s8, s4, t0
    SET_FR_ONE s8, 0
    li      a7, 0                           # missing cells done; also the length - 1
    sd      a7, 0(sp)
20: ld      a7, 0(sp)
    bgeu    a7, s0, 25f
    slli    t1, a7, 3                       # x = root rev(mci) of 128
    add     t1, s11, t1
    ld      a2, 0(t1)
    li      a3, 7
    REV_BITS a4, a2, a3
    slli    a4, a4, 5
    li      t0, RC_R128
    add     a4, a4, t0
    add     a4, s4, a4
    li      t0, RC_X
    add     a3, s4, t0
    li      a5, 32
    COPY_BYTES a3, a4, a5
    ld      a7, 0(sp)                    # p[L] = p[L - 1], L = count + 1
    slli    t1, a7, 5
    add     a4, s8, t1
    addi    a3, a4, 32
    li      a5, 32
    COPY_BYTES a3, a4, a5
    ld      s9, 0(sp)                    # k from L - 1 down to 1: p[k] = p[k - 1] - x p[k]
21: beqz    s9, 22f
    li      t0, RC_T + 32
    add     a0, s4, t0
    slli    a1, s9, 5
    add     a1, s8, a1
    li      t0, RC_X
    add     a2, s4, t0
    call    crypto_kzg_fr_mul
    slli    a0, s9, 5
    add     a0, s8, a0
    addi    a1, a0, -32
    li      t0, RC_T + 32
    add     a2, s4, t0
    call    crypto_kzg_fr_sub
    addi    s9, s9, -1
    j       21b
22: mv      a0, s8                          # p[0] = -(x p[0])
    mv      a1, s8
    li      t0, RC_X
    add     a2, s4, t0
    call    crypto_kzg_fr_mul
    mv      a0, s8
    mv      a1, s8
    call    crypto_kzg_fr_neg
    ld      a7, 0(sp)
    addi    a7, a7, 1
    sd      a7, 0(sp)
    j       20b
25: li      t0, RC_ZC                       # Z: coefficient i of the short one at 64 i
    add     s9, s4, t0
    mv      a3, s9
    li      a5, 262144
    ZERO_BYTES a3, a5
    li      a6, 0
27: bgtu    a6, s0, 28f
    slli    t1, a6, 5
    add     a4, s8, t1
    slli    t1, a6, 11
    add     a3, s9, t1
    li      a5, 32
    COPY_BYTES a3, a4, a5
    addi    a6, a6, 1
    j       27b
28: li      t0, RC_ZE                       # the FFT of Z
    add     s8, s4, t0
    mv      a3, s8
    mv      a4, s9
    li      a5, 262144
    COPY_BYTES a3, a4, a5
    mv      a0, s8
    li      a1, 8192
    li      t0, RC_ROU
    add     a2, s4, t0
    li      a3, 0
    call    crypto_kzg_fft
    li      s11, 0                          # E Z, then P Z = its inverse FFT
29: slli    t1, s11, 5
    add     a0, s10, t1
    add     a1, s8, t1
    mv      a2, a0
    call    crypto_kzg_fr_mul
    addi    s11, s11, 1
    li      t0, 8192
    bltu    s11, t0, 29b
    mv      a0, s10
    li      a1, 8192
    li      t0, RC_ROU
    add     a2, s4, t0
    li      a3, 1
    call    crypto_kzg_fft
    mv      a0, s10                         # P Z and Z over the coset
    li      a1, 8192
    li      t0, RC_ROU
    add     a2, s4, t0
    li      a3, 0
    call    crypto_kzg_coset_fft
    mv      a3, s8
    mv      a4, s9
    li      a5, 262144
    COPY_BYTES a3, a4, a5
    mv      a0, s8
    li      a1, 8192
    li      t0, RC_ROU
    add     a2, s4, t0
    li      a3, 0
    call    crypto_kzg_coset_fft
    li      t0, RC_ZI                       # P = P Z / Z over the coset
    add     s9, s4, t0
    mv      a0, s9
    mv      a1, s8
    li      a2, 8192
    call    crypto_kzg_batch_inverse
    li      s11, 0
30: slli    t1, s11, 5
    add     a0, s10, t1
    mv      a1, a0
    add     a2, s9, t1
    call    crypto_kzg_fr_mul
    addi    s11, s11, 1
    li      t0, 8192
    bltu    s11, t0, 30b
    mv      a0, s10
    li      a1, 8192
    li      t0, RC_ROU
    add     a2, s4, t0
    li      a3, 1
    call    crypto_kzg_coset_fft
    mv      a0, s1                          # the cells and proofs of the first 4096 coefficients
    mv      a1, s10
    li      t0, RC_ROU
    add     a2, s4, t0
    mv      a3, s5
    mv      a4, s6
    call    crypto_kzg_fk20
    li      a0, CRYPTO_OK
9:  LEAVE   16
8:  li      a0, CRYPTO_BUFFER_TOO_SMALL
    LEAVE   16
4:  li      a0, CRYPTO_KZG_LENGTH_MISMATCH
    LEAVE   16
5:  li      a0, CRYPTO_KZG_NOT_ENOUGH_CELLS
    LEAVE   16
6:  li      a0, CRYPTO_KZG_TOO_MANY_CELLS
    LEAVE   16
7:  li      a0, CRYPTO_KZG_INDICES_NOT_ASCENDING
    LEAVE   16
END_FUNCTION crypto_kzg_recover_cells_and_kzg_proofs

/* ---------------------------------------------------------------- Constants */

/*
 * Every constant has a size that is a multiple of 8, with explicit zero
 * padding after a string: under linker relaxation, an alignment directive
 * after data of odd size cannot be padded.
 */

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
    .zero   7
/* the DST of the signatures (Signatures.lean DST), as a ByteList: size, offset, count, bytes */
931:
    .quad   72, 24, 43
    .ascii  "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_"
    .zero   5
/* Fp12.frobeniusCoeff g = (1 + u)^((p - 1) / 6): g^0 to g^5, Montgomery form */
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
932:
    .short  0, 0, 96, 2, 192, 4, 288, 1, 384, 3, 480, 5
