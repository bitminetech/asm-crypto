/*
 * Ed25519 (RFC 8032 section 5.1) for RISC-V (RISC-V ELF psABI, LP64D).
 * Baseline RV64GC instructions only: carries and borrows come from sltu.
 * Requirements: docs/reference/ed25519.md. Layouts: include/ed25519.inc.
 *
 * The functions and their steps follow the ARM64 file one for one. Field
 * elements are 4 limbs of 64 bits below 2^256, mod p = 2^255 - 19, as in
 * x25519.s. A scalar multiplication doubles and adds for every bit and
 * keeps the sum with a mask, so no branch or address depends on a secret
 * scalar. Numbers mod L use Montgomery multiplication (CIOS).
 */
.set ISA_RISCV64, 1
.include "crypto.inc"
.include "sha512.inc"
.include "ed25519.inc"
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
    OP      crypto_ed25519_fe_mul, \d, \a, \b
.endm

.macro FADD d, a, b
    OP      crypto_ed25519_fe_add, \d, \a, \b
.endm

.macro FSUB d, a, b
    OP      crypto_ed25519_fe_sub, \d, \a, \b
.endm

/* Copy 32 bytes from soff(src) to doff(dst). Uses t0. */
.macro COPY32 dst, doff, src, soff
    .irp w, 0, 8, 16, 24
    ld      t0, (\soff + \w)(\src)
    sd      t0, (\doff + \w)(\dst)
    .endr
.endm

/* Copy a 128-byte point. Uses t0. */
.macro COPY128 dst, doff, src, soff
    COPY32  \dst, \doff, \src, \soff
    COPY32  \dst, (\doff + 32), \src, (\soff + 32)
    COPY32  \dst, (\doff + 64), \src, (\soff + 64)
    COPY32  \dst, (\doff + 96), \src, (\soff + 96)
.endm

/* Store the small number v as a field element at off(base). Uses t0. */
.macro SETSMALL base, off, v
    li      t0, \v
    sd      t0, \off(\base)
    sd      zero, (\off + 8)(\base)
    sd      zero, (\off + 16)(\base)
    sd      zero, (\off + 24)(\base)
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

/* ---------------------------------------------------------------- Public key */

.set PK_H, 0                        # SHA-512 of the private key, clamped
.set PK_P, 64                       # A
.set PK_FRAME, 192

/* crypto_ed25519_public_key(private_key, public_key) -> status. s0 public_key. */
FUNCTION crypto_ed25519_public_key
    ENTER   PK_FRAME
    mv      s0, a1
    mv      a1, a0
    addi    a0, sp, PK_H
    call    crypto_ed25519_expand
    addi    a0, sp, PK_P
    addi    a1, sp, PK_H
    lla     a2, 330f
    call    crypto_ed25519_point_mul
    mv      a0, s0
    addi    a1, sp, PK_P
    call    crypto_ed25519_point_encode
    li      a0, CRYPTO_OK
    LEAVE   PK_FRAME
END_FUNCTION crypto_ed25519_public_key

/* ---------------------------------------------------------------- Sign */

.set SG_H, 0                        # a (clamped), then the prefix
.set SG_RA, 64                      # R, then A: encodings
.set SG_RH, 128                     # SHA-512(prefix || M)
.set SG_KH, 192                     # SHA-512(R || A || M)
.set SG_R, 256                      # r mod L
.set SG_K, 288                      # k mod L
.set SG_T, 320                      # k * a mod L
.set SG_P, 352                      # a point
.set SG_FRAME, 480

/*
 * crypto_ed25519_sign(private_key, message, signature) -> status.
 * s0 message, s1 signature, s2 the modulus record of L.
 */
FUNCTION crypto_ed25519_sign
    ENTER   SG_FRAME
    mv      s0, a1
    mv      s1, a2
    lla     s2, 320f
    mv      a1, a0                          # h = SHA-512(private key), a clamped
    addi    a0, sp, SG_H
    call    crypto_ed25519_expand
    addi    a0, sp, SG_P                    # A = [a]B
    addi    a1, sp, SG_H
    lla     a2, 330f
    call    crypto_ed25519_point_mul
    addi    a0, sp, SG_RA + 32
    addi    a1, sp, SG_P
    call    crypto_ed25519_point_encode
    addi    a0, sp, SG_RH                   # r = SHA-512(prefix || M) mod L
    addi    a1, sp, SG_H + 32
    li      a2, 32
    mv      a3, s0
    call    crypto_ed25519_hash
    addi    a0, sp, SG_R
    addi    a1, sp, SG_RH
    call    crypto_ed25519_scalar_reduce
    addi    a0, sp, SG_P                    # R = [r]B
    addi    a1, sp, SG_R
    lla     a2, 330f
    call    crypto_ed25519_point_mul
    addi    a0, sp, SG_RA
    addi    a1, sp, SG_P
    call    crypto_ed25519_point_encode
    addi    a0, sp, SG_KH                   # k = SHA-512(R || A || M) mod L
    addi    a1, sp, SG_RA
    li      a2, 64
    mv      a3, s0
    call    crypto_ed25519_hash
    addi    a0, sp, SG_K
    addi    a1, sp, SG_KH
    call    crypto_ed25519_scalar_reduce
    addi    a0, sp, SG_T                    # k * a / 2^256, then * 2^512 / 2^256
    addi    a1, sp, SG_H
    addi    a2, sp, SG_K
    mv      a3, s2
    call    crypto_ed25519_scalar_mul
    addi    a0, sp, SG_T
    addi    a1, sp, SG_T
    addi    a2, s2, CRYPTO_ED25519_MOD_R2
    mv      a3, s2
    call    crypto_ed25519_scalar_mul
    addi    a0, s1, 32                      # S = r + k * a mod L
    addi    a1, sp, SG_R
    addi    a2, sp, SG_T
    mv      a3, s2
    call    crypto_ed25519_scalar_add
    COPY32  s1, 0, sp, SG_RA
    li      a0, CRYPTO_OK
    LEAVE   SG_FRAME
END_FUNCTION crypto_ed25519_sign

/* ---------------------------------------------------------------- Verify */

.set VF_A, 0                        # the point A
.set VF_P1, 128                     # [S]B
.set VF_P2, 256                     # [k]A
.set VF_KH, 384                     # SHA-512(R || A || M)
.set VF_K, 448                      # k mod L
.set VF_RA, 480                     # R, then A: encodings
.set VF_E, 544                      # the encoding of [S]B - [k]A
.set VF_ZERO, 576
.set VF_FRAME, 608

/*
 * crypto_ed25519_verify(public_key, message, signature, valid) -> status.
 * s0 public_key, s1 message, s2 signature, s3 valid.
 */
FUNCTION crypto_ed25519_verify
    ENTER   VF_FRAME
    mv      s0, a0
    mv      s1, a1
    mv      s2, a2
    mv      s3, a3
    addi    a0, sp, VF_A
    mv      a1, s0
    call    crypto_ed25519_point_decode
    beqz    a0, 1f
    li      a0, CRYPTO_INVALID_PUBLIC_KEY
    j       9f
1:  lla     t3, 320f                        # S < L: the borrow of S - L
    li      t4, 0
    .irp off, 0, 8, 16, 24
    ld      t0, (32 + \off)(s2)
    ld      t1, \off(t3)
    sltu    t2, t0, t1
    sub     t0, t0, t1
    sltu    t1, t0, t4
    or      t4, t2, t1
    .endr
    beqz    t4, 8f                          # S >= L: not valid
    COPY32  sp, VF_RA, s2, 0
    COPY32  sp, VF_RA + 32, s0, 0
    addi    a0, sp, VF_KH
    addi    a1, sp, VF_RA
    li      a2, 64
    mv      a3, s1
    call    crypto_ed25519_hash
    addi    a0, sp, VF_K
    addi    a1, sp, VF_KH
    call    crypto_ed25519_scalar_reduce
    addi    a0, sp, VF_P1                   # [S]B
    addi    a1, s2, 32
    lla     a2, 330f
    call    crypto_ed25519_point_mul
    addi    a0, sp, VF_P2                   # [k]A
    addi    a1, sp, VF_K
    addi    a2, sp, VF_A
    call    crypto_ed25519_point_mul
    SETSMALL sp, VF_ZERO, 0
    FSUB    VF_P2 + CRYPTO_ED25519_POINT_X, VF_ZERO, VF_P2 + CRYPTO_ED25519_POINT_X   # -[k]A
    FSUB    VF_P2 + CRYPTO_ED25519_POINT_T, VF_ZERO, VF_P2 + CRYPTO_ED25519_POINT_T
    addi    a0, sp, VF_P1
    addi    a1, sp, VF_P1
    addi    a2, sp, VF_P2
    call    crypto_ed25519_point_add
    addi    a0, sp, VF_E
    addi    a1, sp, VF_P1
    call    crypto_ed25519_point_encode
    li      t1, 0                           # valid when the encoding equals R
    .irp off, 0, 8, 16, 24
    ld      t0, (VF_E + \off)(sp)
    ld      t2, \off(s2)
    xor     t0, t0, t2
    or      t1, t1, t0
    .endr
    seqz    t1, t1
    sd      t1, 0(s3)
    li      a0, CRYPTO_OK
    j       9f
8:  sd      zero, 0(s3)
    li      a0, CRYPTO_OK
9:  LEAVE   VF_FRAME
END_FUNCTION crypto_ed25519_verify

/* ---------------------------------------------------------------- Hashing */

/*
 * crypto_ed25519_expand(h, private_key): h = SHA-512(private_key), then
 * the first half clamped as section 5.1.5 step 2 says. The 32-byte message
 * as a ByteList at sp. s0 h.
 */
LOCAL_FUNCTION crypto_ed25519_expand
    ENTER   64
    mv      s0, a0
    li      t0, 56                          # size, offset, count
    sd      t0, 0(sp)
    li      t0, 24
    sd      t0, 8(sp)
    li      t0, 32
    sd      t0, 16(sp)
    COPY32  sp, 24, a1, 0
    mv      a0, sp
    mv      a1, s0
    CALL_GLOBAL crypto_sha512
    lbu     t0, 0(s0)
    andi    t0, t0, 248
    sb      t0, 0(s0)
    lbu     t0, 31(s0)
    andi    t0, t0, 127
    ori     t0, t0, 64
    sb      t0, 31(s0)
    LEAVE   64
END_FUNCTION crypto_ed25519_expand

/*
 * crypto_ed25519_hash(digest, prefix, prefix_length, message): SHA-512 of
 * the prefix (32 or 64 bytes) followed by the message bytes. The state at
 * sp, the prefix as a ByteList at sp + 208. s0 digest, s1 message.
 */
LOCAL_FUNCTION crypto_ed25519_hash
    ENTER   304
    mv      s0, a0
    mv      s1, a3
    li      t0, 88                          # size, offset, count
    sd      t0, 208(sp)
    li      t0, 24
    sd      t0, 216(sp)
    sd      a2, 224(sp)
    addi    t1, sp, 232
1:  ld      t0, 0(a1)
    sd      t0, 0(t1)
    addi    a1, a1, 8
    addi    t1, t1, 8
    addi    a2, a2, -8
    bnez    a2, 1b
    mv      a0, sp
    CALL_GLOBAL crypto_sha512_init
    mv      a0, sp
    addi    a1, sp, 208
    CALL_GLOBAL crypto_sha512_update
    mv      a0, sp
    mv      a1, s1
    CALL_GLOBAL crypto_sha512_update
    mv      a0, sp
    mv      a1, s0
    CALL_GLOBAL crypto_sha512_final
    LEAVE   304
END_FUNCTION crypto_ed25519_hash

/* ---------------------------------------------------------------- Numbers mod L */

/*
 * crypto_ed25519_scalar_reduce(result, h): the 64-byte little-endian h
 * mod L. With lo and hi the halves: lo * 2^256 + hi * 2^512 mod L, from
 * two Montgomery products, then one more by 1 removes the 2^256.
 * s0 result, s1 the modulus record. lo at sp, hi at sp + 32, the sum at
 * sp + 64, 1 at sp + 96.
 */
LOCAL_FUNCTION crypto_ed25519_scalar_reduce
    ENTER   128
    mv      s0, a0
    lla     s1, 320f
    COPY32  sp, 0, a1, 0
    COPY32  sp, 32, a1, 32
    mv      a0, sp
    mv      a1, sp
    addi    a2, s1, CRYPTO_ED25519_MOD_R2
    mv      a3, s1
    call    crypto_ed25519_scalar_mul
    addi    a0, sp, 32
    addi    a1, sp, 32
    addi    a2, s1, CRYPTO_ED25519_MOD_R3
    mv      a3, s1
    call    crypto_ed25519_scalar_mul
    addi    a0, sp, 64
    mv      a1, sp
    addi    a2, sp, 32
    mv      a3, s1
    call    crypto_ed25519_scalar_add
    SETSMALL sp, 96, 1
    mv      a0, s0
    addi    a1, sp, 64
    addi    a2, sp, 96
    mv      a3, s1
    call    crypto_ed25519_scalar_mul
    LEAVE   128
END_FUNCTION crypto_ed25519_scalar_reduce

/*
 * crypto_ed25519_scalar_mul(result, a, b, modulus): a * b / 2^256 mod m, for
 * a below 2^256 and b below m (CIOS). result may be a or b.
 * a a4 to a7, T t0 to t5, b_i t6, q s0, product s1 and s2, carry s3.
 */
LOCAL_FUNCTION crypto_ed25519_scalar_mul
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
    ld      s0, CRYPTO_ED25519_MOD_INVERSE(a3)
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
END_FUNCTION crypto_ed25519_scalar_mul

/* crypto_ed25519_scalar_add(result, a, b, modulus): a + b mod m, for a, b < m. */
LOCAL_FUNCTION crypto_ed25519_scalar_add
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
END_FUNCTION crypto_ed25519_scalar_add

/* ---------------------------------------------------------------- Points */

/*
 * crypto_ed25519_point_mul(result, scalar, point): [scalar]point for a
 * 32-byte little-endian scalar. From bit 255 down: double, add the point,
 * and keep the sum when the bit is 1, through a mask.
 * s0 result, s1 scalar, s2 bit index. The sum at sp, the next sum at
 * sp + 128, the point at sp + 256.
 */
LOCAL_FUNCTION crypto_ed25519_point_mul
    ENTER   384
    mv      s0, a0
    mv      s1, a1
    COPY128 sp, 256, a2, 0
    SETSMALL sp, 0, 0                       # the neutral point (0, 1, 1, 0)
    SETSMALL sp, 32, 1
    SETSMALL sp, 64, 1
    SETSMALL sp, 96, 0
    li      s2, 255
1:  mv      a0, sp
    mv      a1, sp
    call    crypto_ed25519_point_double
    addi    a0, sp, 128
    mv      a1, sp
    addi    a2, sp, 256
    call    crypto_ed25519_point_add
    srli    t0, s2, 3                       # mask = -bit
    add     t0, s1, t0
    lbu     t0, 0(t0)
    andi    t1, s2, 7
    srl     t0, t0, t1
    andi    t0, t0, 1
    neg     t1, t0
    mv      t2, sp
    addi    t3, sp, 128
2:  ld      t4, 0(t2)                       # sum ^= (sum ^ next) & mask
    ld      t5, 128(t2)
    xor     t5, t5, t4
    and     t5, t5, t1
    xor     t4, t4, t5
    sd      t4, 0(t2)
    addi    t2, t2, 8
    bltu    t2, t3, 2b
    addi    s2, s2, -1
    bgez    s2, 1b
    COPY128 s0, 0, sp, 0
    LEAVE   384
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
 * section 5.1.4. result may be p or q. s0 result.
 */
LOCAL_FUNCTION crypto_ed25519_point_add
    ENTER   PA_FRAME
    mv      s0, a0
    COPY128 sp, PA_P, a1, 0
    COPY128 sp, PA_Q, a2, 0
    FSUB    PA_T1, PA_P + 32, PA_P          # A = (Y1 - X1) * (Y2 - X2)
    FSUB    PA_T2, PA_Q + 32, PA_Q
    FMUL    PA_A, PA_T1, PA_T2
    FADD    PA_T1, PA_P + 32, PA_P          # B = (Y1 + X1) * (Y2 + X2)
    FADD    PA_T2, PA_Q + 32, PA_Q
    FMUL    PA_B, PA_T1, PA_T2
    FMUL    PA_C, PA_P + 96, PA_Q + 96      # C = T1 * 2d * T2
    addi    a0, sp, PA_C
    addi    a1, sp, PA_C
    lla     a2, 310f
    call    crypto_ed25519_fe_mul
    FMUL    PA_D, PA_P + 64, PA_Q + 64      # D = Z1 * 2 * Z2
    FADD    PA_D, PA_D, PA_D
    FSUB    PA_E, PA_B, PA_A
    FSUB    PA_F, PA_D, PA_C
    FADD    PA_G, PA_D, PA_C
    FADD    PA_H, PA_B, PA_A
    mv      a0, s0                          # X3 = E * F
    addi    a1, sp, PA_E
    addi    a2, sp, PA_F
    call    crypto_ed25519_fe_mul
    addi    a0, s0, 32                      # Y3 = G * H
    addi    a1, sp, PA_G
    addi    a2, sp, PA_H
    call    crypto_ed25519_fe_mul
    addi    a0, s0, 96                      # T3 = E * H
    addi    a1, sp, PA_E
    addi    a2, sp, PA_H
    call    crypto_ed25519_fe_mul
    addi    a0, s0, 64                      # Z3 = F * G
    addi    a1, sp, PA_F
    addi    a2, sp, PA_G
    call    crypto_ed25519_fe_mul
    LEAVE   PA_FRAME
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
 * of section 5.1.4. result may be p. s0 result.
 */
LOCAL_FUNCTION crypto_ed25519_point_double
    ENTER   PD_FRAME
    mv      s0, a0
    COPY128 sp, PD_P, a1, 0
    FMUL    PD_A, PD_P, PD_P                # A = X1^2
    FMUL    PD_B, PD_P + 32, PD_P + 32      # B = Y1^2
    FMUL    PD_C, PD_P + 64, PD_P + 64      # C = 2 * Z1^2
    FADD    PD_C, PD_C, PD_C
    FADD    PD_H, PD_A, PD_B                # H = A + B
    FADD    PD_T, PD_P, PD_P + 32           # E = H - (X1 + Y1)^2
    FMUL    PD_T, PD_T, PD_T
    FSUB    PD_E, PD_H, PD_T
    FSUB    PD_G, PD_A, PD_B                # G = A - B
    FADD    PD_F, PD_C, PD_G                # F = C + G
    mv      a0, s0                          # X3 = E * F
    addi    a1, sp, PD_E
    addi    a2, sp, PD_F
    call    crypto_ed25519_fe_mul
    addi    a0, s0, 32                      # Y3 = G * H
    addi    a1, sp, PD_G
    addi    a2, sp, PD_H
    call    crypto_ed25519_fe_mul
    addi    a0, s0, 96                      # T3 = E * H
    addi    a1, sp, PD_E
    addi    a2, sp, PD_H
    call    crypto_ed25519_fe_mul
    addi    a0, s0, 64                      # Z3 = F * G
    addi    a1, sp, PD_F
    addi    a2, sp, PD_G
    call    crypto_ed25519_fe_mul
    LEAVE   PD_FRAME
END_FUNCTION crypto_ed25519_point_double

/*
 * crypto_ed25519_point_encode(encoding, p): y = Y / Z with the low bit of
 * x = X / Z in bit 255 (section 5.1.2). s0 encoding, s1 p.
 * 1 / Z at sp, x at sp + 32, y at sp + 64.
 */
LOCAL_FUNCTION crypto_ed25519_point_encode
    ENTER   96
    mv      s0, a0
    mv      s1, a1
    mv      a0, sp
    addi    a1, s1, 64
    lla     a2, 300f
    call    crypto_ed25519_fe_pow
    addi    a0, sp, 32
    mv      a1, s1
    mv      a2, sp
    call    crypto_ed25519_fe_mul
    addi    a0, sp, 64
    addi    a1, s1, 32
    mv      a2, sp
    call    crypto_ed25519_fe_mul
    addi    a0, sp, 32
    addi    a1, sp, 32
    call    crypto_ed25519_fe_freeze
    addi    a0, sp, 64
    addi    a1, sp, 64
    call    crypto_ed25519_fe_freeze
    ld      t0, 32(sp)
    slli    t0, t0, 63
    ld      t1, 88(sp)
    or      t1, t1, t0
    COPY32  s0, 0, sp, 64
    sd      t1, 24(s0)
    LEAVE   96
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

/* t0 = 0 when the 32 bytes at sp + a and sp + b are equal. Uses t1, t2. */
.macro FEQ a, b
    li      t0, 0
    .irp off, 0, 8, 16, 24
    ld      t1, (\a + \off)(sp)
    ld      t2, (\b + \off)(sp)
    xor     t1, t1, t2
    or      t0, t0, t1
    .endr
.endm

/*
 * crypto_ed25519_point_decode(result, encoding) -> 0, or 1 when the
 * encoding is not a point: section 5.1.3, with y below p and no x = 0
 * with the sign bit set. Public data: it branches on it.
 * s0 result, s1 the sign bit.
 */
LOCAL_FUNCTION crypto_ed25519_point_decode
    ENTER   DC_FRAME
    mv      s0, a0
    ld      t3, 0(a1)
    ld      t4, 8(a1)
    ld      t5, 16(a1)
    ld      t6, 24(a1)
    srli    s1, t6, 63
    slli    t6, t6, 1
    srli    t6, t6, 1
    sd      t3, DC_Y(sp)
    sd      t4, DC_Y + 8(sp)
    sd      t5, DC_Y + 16(sp)
    sd      t6, DC_Y + 24(sp)
    and     t0, t4, t5                      # y >= p: the top limbs all ones and y0 >= 2^64 - 19
    li      t1, -1
    bne     t0, t1, 1f
    srli    t1, t1, 1
    bne     t6, t1, 1f
    li      t1, -19
    bgeu    t3, t1, 8f
1:  SETSMALL sp, DC_ZERO, 0
    SETSMALL sp, DC_ONE, 1
    FMUL    DC_U, DC_Y, DC_Y                # u = y^2 - 1, v = d y^2 + 1
    addi    a0, sp, DC_V
    addi    a1, sp, DC_U
    lla     a2, 311f
    call    crypto_ed25519_fe_mul
    FADD    DC_V, DC_V, DC_ONE
    FSUB    DC_U, DC_U, DC_ONE
    FMUL    DC_V3, DC_V, DC_V               # v^3, v^7
    FMUL    DC_V3, DC_V3, DC_V
    FMUL    DC_V7, DC_V3, DC_V3
    FMUL    DC_V7, DC_V7, DC_V
    FMUL    DC_T, DC_U, DC_V7               # x = u v^3 (u v^7)^((p - 5) / 8)
    addi    a0, sp, DC_T
    addi    a1, sp, DC_T
    lla     a2, 301f
    call    crypto_ed25519_fe_pow
    FMUL    DC_X, DC_U, DC_V3
    FMUL    DC_X, DC_X, DC_T
    FMUL    DC_W, DC_X, DC_X                # v x^2 against u and -u
    FMUL    DC_W, DC_W, DC_V
    addi    a0, sp, DC_W
    addi    a1, sp, DC_W
    call    crypto_ed25519_fe_freeze
    addi    a0, sp, DC_U
    addi    a1, sp, DC_U
    call    crypto_ed25519_fe_freeze
    FSUB    DC_N, DC_ZERO, DC_U
    addi    a0, sp, DC_N
    addi    a1, sp, DC_N
    call    crypto_ed25519_fe_freeze
    FEQ     DC_W, DC_U
    beqz    t0, 2f
    FEQ     DC_W, DC_N
    bnez    t0, 8f
    addi    a0, sp, DC_X                    # x = x * 2^((p - 1) / 4)
    addi    a1, sp, DC_X
    lla     a2, 312f
    call    crypto_ed25519_fe_mul
2:  addi    a0, sp, DC_X
    addi    a1, sp, DC_X
    call    crypto_ed25519_fe_freeze
    FEQ     DC_X, DC_ZERO
    bnez    t0, 3f
    bnez    s1, 8f                          # x = 0 with the sign bit set
3:  ld      t0, DC_X(sp)
    andi    t0, t0, 1
    beq     t0, s1, 4f
    FSUB    DC_X, DC_ZERO, DC_X             # x = p - x
    addi    a0, sp, DC_X
    addi    a1, sp, DC_X
    call    crypto_ed25519_fe_freeze
4:  COPY32  s0, 0, sp, DC_X
    COPY32  s0, 32, sp, DC_Y
    SETSMALL s0, 64, 1
    addi    a0, s0, 96
    addi    a1, sp, DC_X
    addi    a2, sp, DC_Y
    call    crypto_ed25519_fe_mul
    li      a0, 0
    j       9f
8:  li      a0, 1
9:  LEAVE   DC_FRAME
END_FUNCTION crypto_ed25519_point_decode

/* ---------------------------------------------------------------- Field arithmetic */

/*
 * crypto_ed25519_fe_pow(result, a, exponent): a^exponent for a public
 * exponent below 2^255, by squaring and multiplying from bit 254 down.
 * s0 result, s1 bit, s2 exponent. a at sp, the running value at sp + 32.
 */
LOCAL_FUNCTION crypto_ed25519_fe_pow
    ENTER   64
    mv      s0, a0
    mv      s2, a2
    COPY32  sp, 0, a1, 0
    SETSMALL sp, 32, 1
    li      s1, 254
1:  addi    a0, sp, 32
    addi    a1, sp, 32
    addi    a2, sp, 32
    call    crypto_ed25519_fe_mul
    srli    t0, s1, 6                       # bit t of the exponent
    slli    t0, t0, 3
    add     t0, s2, t0
    ld      t0, 0(t0)
    srl     t0, t0, s1
    andi    t0, t0, 1
    beqz    t0, 2f
    addi    a0, sp, 32
    addi    a1, sp, 32
    mv      a2, sp
    call    crypto_ed25519_fe_mul
2:  addi    s1, s1, -1
    bgez    s1, 1b
    COPY32  s0, 0, sp, 32
    LEAVE   64
END_FUNCTION crypto_ed25519_fe_pow

/*
 * crypto_ed25519_fe_freeze(result, a): a mod p, below p. A leaf: folds
 * bit 255 twice, then subtracts p when the value is p or more, by a mask.
 */
LOCAL_FUNCTION crypto_ed25519_fe_freeze
    UNWIND_END_PROLOGUE
    ld      a3, 0(a1)
    ld      a4, 8(a1)
    ld      a5, 16(a1)
    ld      a6, 24(a1)
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
    sd      a3, 0(a0)
    sd      a4, 8(a0)
    sd      a5, 16(a0)
    sd      a6, 24(a0)
    ret
END_FUNCTION crypto_ed25519_fe_freeze

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
 * crypto_ed25519_fe_mul(result, a, b): a * b mod p, below 2^256, for a, b below
 * 2^256. result may be a or b. A leaf: a a3 to a6, b a7, a1, a2, t3, the
 * column t4 to t6. The 8-limb product at sp.
 */
LOCAL_FUNCTION crypto_ed25519_fe_mul
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
END_FUNCTION crypto_ed25519_fe_mul

/*
 * crypto_ed25519_fe_add(result, a, b): a + b mod p, below 2^256. A leaf:
 * the sum a3 to a6, the carry t4.
 */
LOCAL_FUNCTION crypto_ed25519_fe_add
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
END_FUNCTION crypto_ed25519_fe_add

/*
 * crypto_ed25519_fe_sub(result, a, b): a - b mod p, below 2^256. A leaf:
 * the difference a3 to a6, the borrow t4.
 */
LOCAL_FUNCTION crypto_ed25519_fe_sub
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
