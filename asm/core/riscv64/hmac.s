/*
 * HMAC-SHA-256 and HKDF-SHA-256 for RISC-V (RISC-V ELF psABI, LP64D).
 * Requirements: docs/reference/hmac.md. Layouts: include/crypto.inc, include/hmac.inc.
 *
 * Every hash goes through crypto_sha256. The inner hash input sits in the
 * caller's scratch buffer, as a ByteList at scratch + 8. The outer hash input,
 * 96 bytes, sits on the stack. Baseline RV64GC instructions only.
 */
.set ISA_RISCV64, 1
.include "crypto.inc"
.include "hmac.inc"
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

/* Write the 64 bytes at k0 XOR the pattern register xp to dst. Uses t6. */
.macro PAD dst, k0, xp
    .irp i, 0, 8, 16, 24, 32, 40, 48, 56
    ld      t6, \i(\k0)
    xor     t6, t6, \xp
    sd      t6, \i(\dst)
    .endr
.endm

/* Copy n bytes from src to dst, both 8-byte aligned. Moves src and dst; n ends at 0. Uses t6. */
.macro COPY dst, src, n
97: li      t6, 8
    bltu    \n, t6, 98f
    ld      t6, 0(\src)
    sd      t6, 0(\dst)
    addi    \src, \src, 8
    addi    \dst, \dst, 8
    addi    \n, \n, -8
    j       97b
98: beqz    \n, 99f
    lbu     t6, 0(\src)
    sb      t6, 0(\dst)
    addi    \src, \src, 1
    addi    \dst, \dst, 1
    addi    \n, \n, -1
    j       98b
99:
.endm

/*
 * crypto_hmac_sha256(key, message, scratch, mac) -> status
 * s1 key, s2 message, s3 scratch, s4 mac. K0 at sp.
 */
FUNCTION crypto_hmac_sha256
    ENTER   64
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    li      a0, CRYPTO_BUFFER_TOO_SMALL
    ld      t0, 0(s3)
    ld      t1, CRYPTO_BYTES_COUNT(s2)
    li      t2, CRYPTO_HMAC_SCRATCH
    bltu    t0, t2, 9f
    sub     t0, t0, t2
    bltu    t0, t1, 9f

    mv      a0, s1
    mv      a1, sp
    call    crypto_hmac_key

    /* The inner list: K0 ^ ipad, then the message. */
    ld      t0, 0(s3)
    addi    t0, t0, -8
    sd      t0, 8+CRYPTO_BYTES_SIZE(s3)
    li      t0, CRYPTO_BYTES_FIXED
    sd      t0, 8+CRYPTO_BYTES_OFFSET(s3)
    ld      t1, CRYPTO_BYTES_COUNT(s2)
    addi    t0, t1, CRYPTO_HMAC_BLOCK
    sd      t0, 8+CRYPTO_BYTES_COUNT(s3)
    li      t3, 0x3636363636363636
    addi    t4, s3, 32
    PAD     t4, sp, t3
    ld      t5, CRYPTO_BYTES_OFFSET(s2)
    add     t5, s2, t5
    addi    t4, s3, 96
    COPY    t4, t5, t1

    addi    a0, s3, 8
    mv      a1, sp
    mv      a2, s4
    call    crypto_hmac_finish
    li      a0, CRYPTO_OK
9:  LEAVE   64
END_FUNCTION crypto_hmac_sha256

/* crypto_hkdf_extract(salt, ikm, scratch, prk) -> status: HMAC-SHA-256 with key salt. */
FUNCTION crypto_hkdf_extract
    addi    sp, sp, -16
    UNWIND_ALLOC 16
    sd      ra, 0(sp)
    UNWIND_SAVE ra, 0
    UNWIND_END_PROLOGUE
    CALL_GLOBAL crypto_hmac_sha256
    UNWIND_BEGIN_EPILOGUE
    ld      ra, 0(sp)
    UNWIND_RESTORE ra
    addi    sp, sp, 16
    UNWIND_FREE 16
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_hkdf_extract

/*
 * crypto_hkdf_expand(prk, info, length, scratch, okm) -> status
 * s1 prk, s2 info, s3 scratch, s4 okm, s5 length, s6 block number i,
 * s7 info bytes, s8 bytes done, s9 okm bytes, s10 ipad pattern.
 * K0 at sp, T(i) at sp + 64.
 *
 * Scratch: the inner list header at 8, its bytes from 32. Block 1 puts
 * K0 ^ ipad at 64 (list offset 56); block i > 1 puts it at 32 and T(i - 1) at
 * 96 (list offset 24). The info bytes at 128 and the byte i after them stay put.
 */
FUNCTION crypto_hkdf_expand
    ENTER   96
    mv      s1, a0
    mv      s2, a1
    mv      s3, a3
    mv      s4, a4
    ld      s5, 0(a2)
    li      a0, CRYPTO_HKDF_LENGTH
    li      t0, CRYPTO_HKDF_MAX_LENGTH
    bltu    t0, s5, 9f
    li      a0, CRYPTO_BUFFER_TOO_SMALL
    ld      s7, CRYPTO_BYTES_COUNT(s2)
    ld      t0, 0(s3)
    li      t1, CRYPTO_HKDF_EXPAND_SCRATCH
    bltu    t0, t1, 9f
    sub     t0, t0, t1
    bltu    t0, s7, 9f
    ld      t0, CRYPTO_BYTES_SIZE(s4)
    li      t1, CRYPTO_BYTES_FIXED
    bltu    t0, t1, 9f
    sub     t0, t0, t1
    bltu    t0, s5, 9f

    mv      a0, s1
    mv      a1, sp
    call    crypto_hmac_key
    ld      t5, CRYPTO_BYTES_OFFSET(s2)
    add     t5, s2, t5
    addi    t4, s3, 128
    mv      t1, s7
    COPY    t4, t5, t1
    li      t0, CRYPTO_BYTES_FIXED
    sd      t0, CRYPTO_BYTES_OFFSET(s4)
    sd      s5, CRYPTO_BYTES_COUNT(s4)
    ld      t0, 0(s3)
    addi    t0, t0, -8
    sd      t0, 8+CRYPTO_BYTES_SIZE(s3)
    li      s6, 1
    li      s8, 0
    addi    s9, s4, CRYPTO_BYTES_FIXED
    li      s10, 0x3636363636363636

1:  bgeu    s8, s5, 8f
    addi    t0, s3, 128
    add     t0, t0, s7
    sb      s6, 0(t0)
    li      t1, 1
    bne     s6, t1, 2f
    li      t0, 56
    sd      t0, 8+CRYPTO_BYTES_OFFSET(s3)
    addi    t0, s7, CRYPTO_HMAC_BLOCK+1
    sd      t0, 8+CRYPTO_BYTES_COUNT(s3)
    addi    t4, s3, 64
    j       3f
2:  li      t0, CRYPTO_BYTES_FIXED
    sd      t0, 8+CRYPTO_BYTES_OFFSET(s3)
    addi    t0, s7, CRYPTO_HMAC_BLOCK+32+1
    sd      t0, 8+CRYPTO_BYTES_COUNT(s3)
    .irp i, 0, 8, 16, 24
    ld      t0, 64+\i(sp)
    sd      t0, 96+\i(s3)
    .endr
    addi    t4, s3, 32
3:  PAD     t4, sp, s10
    addi    a0, s3, 8
    mv      a1, sp
    addi    a2, sp, 64
    call    crypto_hmac_finish

    /* okm gets min(32, length - done) bytes of T(i). */
    sub     t1, s5, s8
    li      t0, 32
    bltu    t1, t0, 4f
    mv      t1, t0
4:  addi    t5, sp, 64
    add     t4, s9, s8
    COPY    t4, t5, t1
    addi    s8, s8, 32
    addi    s6, s6, 1
    j       1b
8:  li      a0, CRYPTO_OK
9:  LEAVE   96
END_FUNCTION crypto_hkdf_expand

/*
 * crypto_hmac_key(key, k0): K0 of RFC 2104 into the 64 bytes at k0. A key of
 * at most 64 bytes is copied, a longer key is hashed; zeros fill the rest.
 */
LOCAL_FUNCTION crypto_hmac_key
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    .irp i, 0, 8, 16, 24, 32, 40, 48, 56
    sd      zero, \i(s2)
    .endr
    ld      t1, CRYPTO_BYTES_COUNT(s1)
    li      t0, CRYPTO_HMAC_BLOCK
    bltu    t0, t1, 1f
    ld      t5, CRYPTO_BYTES_OFFSET(s1)
    add     t5, s1, t5
    mv      t4, s2
    COPY    t4, t5, t1
    j       2f
1:  mv      a0, s1
    mv      a1, s2
    CALL_GLOBAL crypto_sha256
2:  LEAVE   0
END_FUNCTION crypto_hmac_key

/*
 * crypto_hmac_finish(inner, k0, mac): the inner hash of the list inner, which
 * holds K0 ^ ipad and the message, then the outer hash into mac.
 * s1 k0, s2 mac. The outer list at sp: 24 bytes of header, 96 bytes.
 */
LOCAL_FUNCTION crypto_hmac_finish
    ENTER   128
    mv      s1, a1
    mv      s2, a2
    addi    a1, sp, CRYPTO_BYTES_FIXED+CRYPTO_HMAC_BLOCK
    CALL_GLOBAL crypto_sha256
    li      t0, CRYPTO_BYTES_FIXED+96
    sd      t0, CRYPTO_BYTES_SIZE(sp)
    li      t0, CRYPTO_BYTES_FIXED
    sd      t0, CRYPTO_BYTES_OFFSET(sp)
    li      t0, 96
    sd      t0, CRYPTO_BYTES_COUNT(sp)
    li      t3, 0x5C5C5C5C5C5C5C5C
    addi    t4, sp, CRYPTO_BYTES_FIXED
    PAD     t4, s1, t3
    mv      a0, sp
    mv      a1, s2
    CALL_GLOBAL crypto_sha256
    LEAVE   128
END_FUNCTION crypto_hmac_finish
