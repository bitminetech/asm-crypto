/*
 * AES-128, CTR and GCM for RISC-V (RISC-V ELF psABI, LP64D).
 * Requirements: docs/reference/aes.md. Layouts: include/crypto.inc, include/aes.inc.
 *
 * Constant time: no table lookup and no branch depends on key or data bytes.
 * Four blocks (64 bytes) go through the rounds together as 8 bit planes of
 * 8 bytes: plane i holds bit i of every byte, byte g = 16 * block + k at bit g,
 * with k = r + 4c the FIPS 197 state byte of row r and column c.
 * SubBytes computes the inverse in GF(2^8) as x^254, then the affine map.
 * GHASH multiplies one bit at a time with masks (SP 800-38D algorithm 1).
 * Baseline RV64GC instructions only. Values at addresses that may not be
 * 8-byte aligned are read and written one byte at a time.
 */
.set ISA_RISCV64, 1
.include "crypto.inc"
.include "aes.inc"
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

/* d = the 8 bytes at off(base) as a little-endian number. Uses tmp. */
.macro LOAD_LE64 d, base, off, tmp
    lbu     \d, \off+7(\base)
    .irp k, 6, 5, 4, 3, 2, 1, 0
    slli    \d, \d, 8
    lbu     \tmp, \off+\k(\base)
    or      \d, \d, \tmp
    .endr
.endm

/* The 8 bytes at off(base) = s as a little-endian number. Uses tmp. */
.macro STORE_LE64 s, base, off, tmp
    sb      \s, \off(\base)
    .irp k, 1, 2, 3, 4, 5, 6, 7
    srli    \tmp, \s, 8 * \k
    sb      \tmp, \off+\k(\base)
    .endr
.endm

/* ---------------------------------------------------------------- AES-128-CTR */

/*
 * crypto_aes128_ctr(key, counter, input, output) -> status
 * s1 key, s2 counter, s3 input, s4 output, s5 input bytes.
 * The key schedule at sp.
 */
FUNCTION crypto_aes128_ctr
    ENTER   CRYPTO_AES128_SCHEDULE_SIZE
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    li      a0, CRYPTO_BUFFER_TOO_SMALL
    ld      s5, CRYPTO_BYTES_COUNT(s3)
    ld      t0, CRYPTO_BYTES_SIZE(s4)
    li      t1, CRYPTO_BYTES_FIXED
    bltu    t0, t1, 9f
    sub     t0, t0, t1
    bltu    t0, s5, 9f
    mv      a0, s1
    mv      a1, sp
    call    crypto_aes128_expand
    li      t0, CRYPTO_BYTES_FIXED
    sd      t0, CRYPTO_BYTES_OFFSET(s4)
    sd      s5, CRYPTO_BYTES_COUNT(s4)
    mv      a0, sp
    mv      a1, s2
    ld      a2, CRYPTO_BYTES_OFFSET(s3)
    add     a2, s3, a2
    addi    a3, s4, CRYPTO_BYTES_FIXED
    mv      a4, s5
    li      a5, 0
    call    crypto_aes128_ctr_xor
    li      a0, CRYPTO_OK
9:  LEAVE   CRYPTO_AES128_SCHEDULE_SIZE
END_FUNCTION crypto_aes128_ctr

/* ---------------------------------------------------------------- AES-128-GCM */

/* GCM locals, after the key schedule at sp. */
.set G_BLOCKS, CRYPTO_AES128_SCHEDULE_SIZE  /* E(0^128) = H, then E(J0) */
.set G_Y, G_BLOCKS + 64                     /* the GHASH value */
.set G_LENGTHS, G_Y + 16                    /* len(A) || len(C), in bits */
.set G_COUNTER, G_LENGTHS + 16              /* inc32(J0), the first counter block of the data */
.set G_FRAME, G_COUNTER + 16

/*
 * The key schedule from key s1, then H and E(J0) from iv s2, the counter
 * block inc32(J0), and Y = 0. J0 = IV || 0^31 || 1.
 */
.macro GCM_START
    mv      a0, s1
    mv      a1, sp
    call    crypto_aes128_expand
    addi    t0, sp, G_BLOCKS
    .irp i, 0, 8, 16, 24, 32, 40, 48, 56
    sd      zero, \i(t0)
    .endr
    ld      t1, 0(s2)
    lwu     t2, 8(s2)
    sd      t1, 16(t0)
    sw      t2, 24(t0)
    li      t3, 0x01000000
    sw      t3, 28(t0)
    addi    t4, sp, G_COUNTER
    sd      t1, 0(t4)
    sw      t2, 8(t4)
    li      t3, 0x02000000
    sw      t3, 12(t4)
    addi    t4, sp, G_Y
    sd      zero, 0(t4)
    sd      zero, 8(t4)
    mv      a0, sp
    addi    a1, sp, G_BLOCKS
    call    crypto_aes128_encrypt4
.endm

/* GHASH of the n bytes at data into Y, with zeros padding the last block. data and n are not a0 or a1. */
.macro GHASH data, n
    mv      a2, \data
    mv      a3, \n
    addi    a0, sp, G_Y
    addi    a1, sp, G_BLOCKS
    call    crypto_aes128_ghash
.endm

/* GHASH of the lengths block, then t0, t1 = the tag E(J0) ^ Y, as little-endian words. */
.macro GCM_TAG abytes, cbytes
    slli    t0, \abytes, 3
    slli    t1, \cbytes, 3
    addi    t2, sp, G_LENGTHS
    STORE_BE64 t0, t2, 0, t6
    STORE_BE64 t1, t2, 8, t6
    li      t3, 16
    GHASH   t2, t3
    ld      t0, G_Y(sp)
    ld      t1, G_Y+8(sp)
    ld      t2, G_BLOCKS+16(sp)
    ld      t3, G_BLOCKS+24(sp)
    xor     t0, t0, t2
    xor     t1, t1, t3
.endm

/*
 * crypto_aes128_gcm_ae(key, iv, plaintext, aad, sealed) -> status
 * s1 key, s2 iv, s3 plaintext, s4 aad, s5 sealed, s6 plaintext bytes,
 * s7 sealed bytes.
 */
FUNCTION crypto_aes128_gcm_ae
    ENTER   G_FRAME
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      s5, a4
    li      a0, CRYPTO_BUFFER_TOO_SMALL
    ld      s6, CRYPTO_BYTES_COUNT(s3)
    ld      t0, CRYPTO_BYTES_SIZE(s5)
    li      t1, CRYPTO_BYTES_FIXED + CRYPTO_GCM_TAG_SIZE
    bltu    t0, t1, 9f
    sub     t0, t0, t1
    bltu    t0, s6, 9f
    GCM_START
    addi    s7, s5, CRYPTO_BYTES_FIXED
    mv      a0, sp
    addi    a1, sp, G_COUNTER
    ld      a2, CRYPTO_BYTES_OFFSET(s3)
    add     a2, s3, a2
    mv      a3, s7
    mv      a4, s6
    li      a5, 1
    call    crypto_aes128_ctr_xor
    ld      t4, CRYPTO_BYTES_OFFSET(s4)
    add     t4, s4, t4
    ld      t5, CRYPTO_BYTES_COUNT(s4)
    GHASH   t4, t5
    GHASH   s7, s6
    ld      t4, CRYPTO_BYTES_COUNT(s4)
    GCM_TAG t4, s6
    add     t2, s7, s6
    STORE_LE64 t0, t2, 0, t6
    STORE_LE64 t1, t2, 8, t6
    li      t0, CRYPTO_BYTES_FIXED
    sd      t0, CRYPTO_BYTES_OFFSET(s5)
    addi    t0, s6, CRYPTO_GCM_TAG_SIZE
    sd      t0, CRYPTO_BYTES_COUNT(s5)
    li      a0, CRYPTO_OK
9:  LEAVE   G_FRAME
END_FUNCTION crypto_aes128_gcm_ae

/*
 * crypto_aes128_gcm_ad(key, iv, sealed, aad, plaintext) -> status
 * s1 key, s2 iv, s3 sealed, s4 aad, s5 plaintext, s6 ciphertext bytes,
 * s7 sealed bytes. The tag is checked before any plaintext is written.
 */
FUNCTION crypto_aes128_gcm_ad
    ENTER   G_FRAME
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      s5, a4
    li      a0, CRYPTO_GCM_FAIL
    ld      s6, CRYPTO_BYTES_COUNT(s3)
    li      t1, CRYPTO_GCM_TAG_SIZE
    bltu    s6, t1, 9f
    sub     s6, s6, t1
    li      a0, CRYPTO_BUFFER_TOO_SMALL
    ld      t0, CRYPTO_BYTES_SIZE(s5)
    li      t1, CRYPTO_BYTES_FIXED
    bltu    t0, t1, 9f
    sub     t0, t0, t1
    bltu    t0, s6, 9f
    GCM_START
    ld      s7, CRYPTO_BYTES_OFFSET(s3)
    add     s7, s3, s7
    ld      t4, CRYPTO_BYTES_OFFSET(s4)
    add     t4, s4, t4
    ld      t5, CRYPTO_BYTES_COUNT(s4)
    GHASH   t4, t5
    GHASH   s7, s6
    ld      t4, CRYPTO_BYTES_COUNT(s4)
    GCM_TAG t4, s6
    add     t2, s7, s6
    LOAD_LE64 t3, t2, 0, t6
    xor     t0, t0, t3
    LOAD_LE64 t3, t2, 8, t6
    xor     t1, t1, t3
    or      t0, t0, t1
    li      a0, CRYPTO_GCM_FAIL
    bnez    t0, 9f
    mv      a0, sp
    addi    a1, sp, G_COUNTER
    mv      a2, s7
    addi    a3, s5, CRYPTO_BYTES_FIXED
    mv      a4, s6
    li      a5, 1
    call    crypto_aes128_ctr_xor
    li      t0, CRYPTO_BYTES_FIXED
    sd      t0, CRYPTO_BYTES_OFFSET(s5)
    sd      s6, CRYPTO_BYTES_COUNT(s5)
    li      a0, CRYPTO_OK
9:  LEAVE   G_FRAME
END_FUNCTION crypto_aes128_gcm_ad

/* ---------------------------------------------------------------- Helpers */

/*
 * crypto_aes128_expand(key, schedule): KeyExpansion of FIPS 197 section 5.2,
 * then each round key repeated 4 times and turned into planes.
 * s1 key, s2 schedule, s3 word i, s4 Rcon, s5 temp.
 * w[0..43] at sp (176 bytes), the SubWord block at sp + 176 (64 bytes).
 */
LOCAL_FUNCTION crypto_aes128_expand
    ENTER   240
    mv      s1, a0
    mv      s2, a1
    ld      t0, 0(s1)
    sd      t0, 0(sp)
    ld      t0, 8(s1)
    sd      t0, 8(sp)
    li      s3, 4
    lla     s4, 312f
1:  slli    t0, s3, 2
    add     t0, sp, t0
    lwu     s5, -4(t0)
    andi    t1, s3, 3
    bnez    t1, 2f
    srli    t1, s5, 8                       # RotWord
    slli    t2, s5, 24
    or      s5, t1, t2
    slli    s5, s5, 32
    srli    s5, s5, 32
    .irp i, 0, 8, 16, 24, 32, 40, 48, 56    # SubWord: the S-box on the 4 bytes
    sd      zero, 176+\i(sp)
    .endr
    sw      s5, 176(sp)
    addi    a0, sp, 176
    li      a1, 0
    call    crypto_aes128_bitslice
    addi    a0, sp, 176
    call    crypto_aes128_sbox
    addi    a0, sp, 176
    li      a1, 1
    call    crypto_aes128_bitslice
    lwu     s5, 176(sp)
    lbu     t1, 0(s4)                       # Rcon
    addi    s4, s4, 1
    xor     s5, s5, t1
2:  slli    t0, s3, 2
    add     t0, sp, t0
    lwu     t1, -16(t0)
    xor     s5, s5, t1
    sw      s5, 0(t0)
    addi    s3, s3, 1
    li      t1, 44
    bltu    s3, t1, 1b
    li      s3, 0
3:  slli    t0, s3, 4
    add     t0, sp, t0
    ld      t1, 0(t0)
    ld      t2, 8(t0)
    slli    a0, s3, 6
    add     a0, s2, a0
    .irp i, 0, 16, 32, 48
    sd      t1, \i(a0)
    sd      t2, \i+8(a0)
    .endr
    li      a1, 0
    call    crypto_aes128_bitslice
    addi    s3, s3, 1
    li      t1, 11
    bltu    s3, t1, 3b
    LEAVE   240
END_FUNCTION crypto_aes128_expand

/*
 * crypto_aes128_ctr_xor(schedule, counter, source, target, count, mode):
 * target = source XOR the key stream, count bytes. The key stream is
 * E(counter), E(counter + 1), ... Mode 0 adds 1 to the whole block as a
 * 128-bit big-endian number, mode 1 to its last 32 bits only (inc32).
 * s1 schedule, s2 source, s3 target, s4 bytes left, s5 mode,
 * s6:s7 the counter as a 128-bit number, s8 block offset. Four counter blocks at sp.
 */
LOCAL_FUNCTION crypto_aes128_ctr_xor
    ENTER   64
    mv      s1, a0
    mv      s2, a2
    mv      s3, a3
    mv      s4, a4
    mv      s5, a5
    LOAD_BE64 s6, a1, 0, t6
    LOAD_BE64 s7, a1, 8, t6
1:  beqz    s4, 9f
    li      s8, 0
2:  add     t0, sp, s8
    STORE_BE64 s6, t0, 0, t6
    STORE_BE64 s7, t0, 8, t6
    bnez    s5, 3f
    addi    s7, s7, 1
    seqz    t1, s7
    add     s6, s6, t1
    j       4f
3:  addiw   t1, s7, 1
    slli    t1, t1, 32
    srli    t1, t1, 32
    srli    t2, s7, 32
    slli    t2, t2, 32
    or      s7, t2, t1
4:  addi    s8, s8, 16
    li      t0, 64
    bltu    s8, t0, 2b
    mv      a0, s1
    mv      a1, sp
    call    crypto_aes128_encrypt4
    li      t0, 64
    mv      t1, s4
    bltu    s4, t0, 5f
    mv      t1, t0
5:  sub     s4, s4, t1
    mv      t2, sp
6:  li      t0, 8
    bltu    t1, t0, 7f
    ld      t3, 0(s2)
    ld      t4, 0(t2)
    xor     t3, t3, t4
    sd      t3, 0(s3)
    addi    s2, s2, 8
    addi    t2, t2, 8
    addi    s3, s3, 8
    addi    t1, t1, -8
    j       6b
7:  beqz    t1, 1b
    lbu     t3, 0(s2)
    lbu     t4, 0(t2)
    xor     t3, t3, t4
    sb      t3, 0(s3)
    addi    s2, s2, 1
    addi    t2, t2, 1
    addi    s3, s3, 1
    addi    t1, t1, -1
    j       7b
9:  LEAVE   64
END_FUNCTION crypto_aes128_ctr_xor

/*
 * crypto_aes128_encrypt4(schedule, blocks): the cipher of FIPS 197 section
 * 5.1 on the 4 blocks of 16 bytes at blocks, in place.
 * s1 schedule, s2 blocks, s3 round.
 */
LOCAL_FUNCTION crypto_aes128_encrypt4
    ENTER   0
    mv      s1, a0
    mv      s2, a1
    mv      a0, s2
    li      a1, 0
    call    crypto_aes128_bitslice
    li      t0, 0
1:  add     t1, s2, t0
    ld      t2, 0(t1)
    add     t3, s1, t0
    ld      t4, 0(t3)
    xor     t2, t2, t4
    sd      t2, 0(t1)
    addi    t0, t0, 8
    li      t5, 64
    bltu    t0, t5, 1b
    li      s3, 1
2:  mv      a0, s2
    call    crypto_aes128_sbox
    mv      a0, s2
    slli    a1, s3, 6
    add     a1, s1, a1
    addi    a2, s3, -10
    snez    a2, a2
    call    crypto_aes128_mix
    addi    s3, s3, 1
    li      t0, 10
    bleu    s3, t0, 2b
    mv      a0, s2
    li      a1, 1
    call    crypto_aes128_bitslice
    LEAVE   0
END_FUNCTION crypto_aes128_encrypt4

/* SWAPMOVE: swap the bits of b at mask with the bits of a at mask << n. Uses s1. */
.macro SWAPMOVE a, b, mask, n
    srli    s1, \a, \n
    xor     s1, s1, \b
    and     s1, s1, \mask
    xor     \b, \b, s1
    slli    s1, s1, \n
    xor     \a, \a, s1
.endm

/* Swap byte i of word j with byte j of word i, for the words in t0 to t6 and a7. Masks a4, a5, a6. */
.macro BYTE_TRANSPOSE
    SWAPMOVE t0, t4, a4, 32
    SWAPMOVE t1, t5, a4, 32
    SWAPMOVE t2, t6, a4, 32
    SWAPMOVE t3, a7, a4, 32
    SWAPMOVE t0, t2, a5, 16
    SWAPMOVE t1, t3, a5, 16
    SWAPMOVE t4, t6, a5, 16
    SWAPMOVE t5, a7, a5, 16
    SWAPMOVE t0, t1, a6, 8
    SWAPMOVE t2, t3, a6, 8
    SWAPMOVE t4, t5, a6, 8
    SWAPMOVE t6, a7, a6, 8
.endm

/* In word w, swap bit i of byte j with bit j of byte i. Masks a2, a3, s0. Uses s1. */
.macro BIT_TRANSPOSE w
    srli    s1, \w, 7
    xor     s1, s1, \w
    and     s1, s1, a2
    xor     \w, \w, s1
    slli    s1, s1, 7
    xor     \w, \w, s1
    srli    s1, \w, 14
    xor     s1, s1, \w
    and     s1, s1, a3
    xor     \w, \w, s1
    slli    s1, s1, 14
    xor     \w, \w, s1
    srli    s1, \w, 28
    xor     s1, s1, \w
    and     s1, s1, s0
    xor     \w, \w, s1
    slli    s1, s1, 28
    xor     \w, \w, s1
.endm

/*
 * crypto_aes128_bitslice(blocks, inverse): turn the 64 bytes at blocks into
 * the 8 planes in place (inverse 0), or the planes back into bytes (inverse 1).
 * Forward is the bit transpose in each word, then the byte transpose across
 * the words; inverse is the same two steps in the other order.
 */
LOCAL_FUNCTION crypto_aes128_bitslice
    addi    sp, sp, -16
    UNWIND_ALLOC 16
    sd      s0, 0(sp)
    UNWIND_SAVE s0, 0
    sd      s1, 8(sp)
    UNWIND_SAVE s1, 8
    UNWIND_END_PROLOGUE
    li      a2, 0x00AA00AA00AA00AA
    li      a3, 0x0000CCCC0000CCCC
    li      s0, 0x00000000F0F0F0F0
    li      a4, 0x00000000FFFFFFFF
    li      a5, 0x0000FFFF0000FFFF
    li      a6, 0x00FF00FF00FF00FF
    ld      t0, 0(a0)
    ld      t1, 8(a0)
    ld      t2, 16(a0)
    ld      t3, 24(a0)
    ld      t4, 32(a0)
    ld      t5, 40(a0)
    ld      t6, 48(a0)
    ld      a7, 56(a0)
    beqz    a1, 1f
    BYTE_TRANSPOSE
1:  .irp w, t0, t1, t2, t3, t4, t5, t6, a7
    BIT_TRANSPOSE \w
    .endr
    bnez    a1, 2f
    BYTE_TRANSPOSE
2:  sd      t0, 0(a0)
    sd      t1, 8(a0)
    sd      t2, 16(a0)
    sd      t3, 24(a0)
    sd      t4, 32(a0)
    sd      t5, 40(a0)
    sd      t6, 48(a0)
    sd      a7, 56(a0)
    UNWIND_BEGIN_EPILOGUE
    ld      s0, 0(sp)
    UNWIND_RESTORE s0
    ld      s1, 8(sp)
    UNWIND_RESTORE s1
    addi    sp, sp, 16
    UNWIND_FREE 16
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_aes128_bitslice

/* S-box stack: x, x^2, x^3, x^12, then s0 to s7. */
.set SB_X, 0
.set SB_X2, 64
.set SB_X3, 128
.set SB_X12, 192
.set SB_SAVE, 256
.set SB_FRAME, 320

/* Store a (s0 to s7) or r (t0 to t6, a7) at sp + off. */
.macro STORE_A off
    .irp k, 0, 1, 2, 3, 4, 5, 6, 7
    sd      s\k, \off+8*\k(sp)
    .endr
.endm

.macro STORE_R off
    sd      t0, \off(sp)
    sd      t1, \off+8(sp)
    sd      t2, \off+16(sp)
    sd      t3, \off+24(sp)
    sd      t4, \off+32(sp)
    sd      t5, \off+40(sp)
    sd      t6, \off+48(sp)
    sd      a7, \off+56(sp)
.endm

.macro R_TO_A
    mv      s0, t0
    mv      s1, t1
    mv      s2, t2
    mv      s3, t3
    mv      s4, t4
    mv      s5, t5
    mv      s6, t6
    mv      s7, a7
.endm

/* r = a^2 in GF(2^8), a linear map of the planes. a: s0 to s7, r: t0 to t6, a7. */
.macro SQUARE
    xor     t0, s0, s4
    xor     t0, t0, s6
    xor     t1, s4, s6
    xor     t1, t1, s7
    xor     t2, s1, s5
    xor     t3, s4, s5
    xor     t3, t3, s6
    xor     t3, t3, s7
    xor     t4, s2, s4
    xor     t4, t4, s7
    xor     t5, s5, s6
    xor     t6, s3, s5
    xor     a7, s6, s7
.endm

/*
 * r = a * b in GF(2^8), b the 8 planes at sp + off. Horner on the planes of
 * b from 7 down to 0: r = r * x, then r ^= a & b_i. Times x maps the planes
 * r0..r7 to r7, r0 ^ r7, r1, r2 ^ r7, r3 ^ r7, r4, r5, r6.
 * Uses a1 to a5.
 */
.macro MULTIPLY off
    li      t0, 0
    li      t1, 0
    li      t2, 0
    li      t3, 0
    li      t4, 0
    li      t5, 0
    li      t6, 0
    li      a7, 0
    addi    a4, sp, \off
    li      a3, 56
1:  mv      a5, a7
    mv      a7, t6
    mv      t6, t5
    mv      t5, t4
    xor     t4, t3, a5
    xor     t3, t2, a5
    mv      t2, t1
    xor     t1, t0, a5
    mv      t0, a5
    add     a1, a4, a3
    ld      a1, 0(a1)
    and     a2, s0, a1
    xor     t0, t0, a2
    and     a2, s1, a1
    xor     t1, t1, a2
    and     a2, s2, a1
    xor     t2, t2, a2
    and     a2, s3, a1
    xor     t3, t3, a2
    and     a2, s4, a1
    xor     t4, t4, a2
    and     a2, s5, a1
    xor     t5, t5, a2
    and     a2, s6, a1
    xor     t6, t6, a2
    and     a2, s7, a1
    xor     a7, a7, a2
    addi    a3, a3, -8
    bgez    a3, 1b
.endm

/* Plane at off(a0) = r_i ^ r_(i+4) ^ r_(i+5) ^ r_(i+6) ^ r_(i+7), inverted when flip is 1. */
.macro AFFINE off, i, j, k, l, m, flip
    xor     a1, \i, \j
    xor     a1, a1, \k
    xor     a1, a1, \l
    xor     a1, a1, \m
    .if \flip
    not     a1, a1
    .endif
    sd      a1, \off(a0)
.endm

/*
 * crypto_aes128_sbox(planes): SubBytes on the 8 planes at planes, in place:
 * x^254 = x^-1 in GF(2^8) by x^2, x^3, x^6, x^12, x^15, x^30, x^60, x^120,
 * x^240, x^252, x^254, then the affine map with c = 0x63.
 */
LOCAL_FUNCTION crypto_aes128_sbox
    addi    sp, sp, -SB_FRAME
    UNWIND_ALLOC SB_FRAME
    .irp k, 0, 1, 2, 3, 4, 5, 6, 7
    sd      s\k, SB_SAVE+8*\k(sp)
    UNWIND_SAVE s\k, SB_SAVE+8*\k
    .endr
    UNWIND_END_PROLOGUE
    .irp k, 0, 1, 2, 3, 4, 5, 6, 7
    ld      s\k, 8*\k(a0)
    .endr
    STORE_A SB_X
    SQUARE                                  # x^2
    STORE_R SB_X2
    R_TO_A
    MULTIPLY SB_X                           # x^3
    STORE_R SB_X3
    R_TO_A
    SQUARE                                  # x^6
    R_TO_A
    SQUARE                                  # x^12
    STORE_R SB_X12
    R_TO_A
    MULTIPLY SB_X3                          # x^15
    R_TO_A
    SQUARE                                  # x^30
    R_TO_A
    SQUARE                                  # x^60
    R_TO_A
    SQUARE                                  # x^120
    R_TO_A
    SQUARE                                  # x^240
    R_TO_A
    MULTIPLY SB_X12                         # x^252
    R_TO_A
    MULTIPLY SB_X2                          # x^254
    AFFINE  0, t0, t4, t5, t6, a7, 1        # c = 0x63: bits 0, 1, 5 and 6
    AFFINE  8, t1, t5, t6, a7, t0, 1
    AFFINE  16, t2, t6, a7, t0, t1, 0
    AFFINE  24, t3, a7, t0, t1, t2, 0
    AFFINE  32, t4, t0, t1, t2, t3, 0
    AFFINE  40, t5, t1, t2, t3, t4, 1
    AFFINE  48, t6, t2, t3, t4, t5, 1
    AFFINE  56, a7, t3, t4, t5, t6, 0
    UNWIND_BEGIN_EPILOGUE
    .irp k, 0, 1, 2, 3, 4, 5, 6, 7
    ld      s\k, SB_SAVE+8*\k(sp)
    UNWIND_RESTORE s\k
    .endr
    addi    sp, sp, SB_FRAME
    UNWIND_FREE SB_FRAME
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_aes128_sbox

/*
 * crypto_aes128_mix(planes, round_key, columns): ShiftRows, then MixColumns
 * when columns is 1, then AddRoundKey with the 8 planes at round_key.
 * ShiftRows moves row r of each block 4r bits down in its 16-bit lane.
 * MixColumns: with u = rot1(a) and t = a ^ u, out = xtime(t) ^ u ^ rot2(t),
 * where rotk takes row r + k of the column to row r.
 * The planes of u ^ rot2(t) at sp, then s0 to s5.
 */
LOCAL_FUNCTION crypto_aes128_mix
    addi    sp, sp, -112
    UNWIND_ALLOC 112
    .irp k, 0, 1, 2, 3, 4, 5
    sd      s\k, 64+8*\k(sp)
    UNWIND_SAVE s\k, 64+8*\k
    .endr
    UNWIND_END_PROLOGUE
    li      a3, 0x0222022202220222
    li      a4, 0x2000200020002000
    li      a5, 0x0044004400440044
    li      a6, 0x4400440044004400
    li      a7, 0x0008000800080008
    li      s0, 0x8880888088808880
    li      s1, 0x1111111111111111
    li      s2, 0x7777777777777777
    li      s3, 0x8888888888888888
    li      s4, 0x3333333333333333
    li      s5, 0xCCCCCCCCCCCCCCCC
    li      t0, 0
1:  add     t3, a0, t0
    ld      t1, 0(t3)
    and     t2, t1, s1                      # row 0
    srli    t3, t1, 4                       # row 1
    and     t3, t3, a3
    or      t2, t2, t3
    slli    t3, t1, 12
    and     t3, t3, a4
    or      t2, t2, t3
    srli    t3, t1, 8                       # row 2
    and     t3, t3, a5
    or      t2, t2, t3
    slli    t3, t1, 8
    and     t3, t3, a6
    or      t2, t2, t3
    srli    t3, t1, 12                      # row 3
    and     t3, t3, a7
    or      t2, t2, t3
    slli    t3, t1, 4
    and     t3, t3, s0
    or      t2, t2, t3
    beqz    a2, 2f
    srli    t3, t2, 1                       # u = rot1(a)
    and     t3, t3, s2
    slli    t4, t2, 3
    and     t4, t4, s3
    or      t3, t3, t4
    xor     t2, t2, t3                      # t = a ^ u
    srli    t4, t2, 2                       # rot2(t)
    and     t4, t4, s4
    slli    t5, t2, 2
    and     t5, t5, s5
    or      t4, t4, t5
    xor     t3, t3, t4
    add     t4, sp, t0
    sd      t3, 0(t4)
2:  add     t3, a0, t0
    sd      t2, 0(t3)
    addi    t0, t0, 8
    li      t3, 64
    bltu    t0, t3, 1b
    beqz    a2, 3f
    ld      t6, 56(a0)                      # xtime(t) = t7, t0 ^ t7, t1, t2 ^ t7, t3 ^ t7, t4, t5, t6
    ld      t0, 0(sp)
    xor     t0, t0, t6
    ld      t1, 8(sp)
    ld      t2, 0(a0)
    xor     t1, t1, t2
    xor     t1, t1, t6
    ld      t2, 16(sp)
    ld      t3, 8(a0)
    xor     t2, t2, t3
    ld      t3, 24(sp)
    ld      t4, 16(a0)
    xor     t3, t3, t4
    xor     t3, t3, t6
    ld      t4, 32(sp)
    ld      t5, 24(a0)
    xor     t4, t4, t5
    xor     t4, t4, t6
    ld      t5, 40(sp)
    ld      a3, 32(a0)
    xor     t5, t5, a3
    ld      a3, 48(sp)
    ld      a4, 40(a0)
    xor     a3, a3, a4
    ld      a4, 56(sp)
    ld      a5, 48(a0)
    xor     a4, a4, a5
    sd      t0, 0(a0)
    sd      t1, 8(a0)
    sd      t2, 16(a0)
    sd      t3, 24(a0)
    sd      t4, 32(a0)
    sd      t5, 40(a0)
    sd      a3, 48(a0)
    sd      a4, 56(a0)
3:  li      t0, 0
4:  add     t1, a0, t0
    ld      t2, 0(t1)
    add     t3, a1, t0
    ld      t4, 0(t3)
    xor     t2, t2, t4
    sd      t2, 0(t1)
    addi    t0, t0, 8
    li      t3, 64
    bltu    t0, t3, 4b
    UNWIND_BEGIN_EPILOGUE
    .irp k, 0, 1, 2, 3, 4, 5
    ld      s\k, 64+8*\k(sp)
    UNWIND_RESTORE s\k
    .endr
    addi    sp, sp, 112
    UNWIND_FREE 112
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_aes128_mix

/*
 * crypto_aes128_ghash(y, h, data, count): for each 16-byte block X of the
 * count bytes at data, Y = (Y ^ X) * H in GF(2^128); zeros pad the last
 * block. Blocks are big-endian 128-bit numbers, bit 0 of GCM the top bit.
 * a4:a5 X, a6:a7 H, t1:t2 Z, t3:t4 V, s0 bits left, s1 R. The padded block at sp.
 */
LOCAL_FUNCTION crypto_aes128_ghash
    addi    sp, sp, -32
    UNWIND_ALLOC 32
    sd      s0, 16(sp)
    UNWIND_SAVE s0, 16
    sd      s1, 24(sp)
    UNWIND_SAVE s1, 24
    UNWIND_END_PROLOGUE
    LOAD_BE64 a4, a0, 0, t6
    LOAD_BE64 a5, a0, 8, t6
    LOAD_BE64 a6, a1, 0, t6
    LOAD_BE64 a7, a1, 8, t6
    li      s1, 0xE100000000000000
1:  beqz    a3, 8f
    li      t0, 16
    bgeu    a3, t0, 3f
    sd      zero, 0(sp)
    sd      zero, 8(sp)
    li      t0, 0
2:  add     t1, a2, t0
    lbu     t2, 0(t1)
    add     t1, sp, t0
    sb      t2, 0(t1)
    addi    t0, t0, 1
    bltu    t0, a3, 2b
    mv      a2, sp
    li      a3, 16
3:  LOAD_BE64 t0, a2, 0, t6
    xor     a4, a4, t0
    LOAD_BE64 t0, a2, 8, t6
    xor     a5, a5, t0
    addi    a2, a2, 16
    addi    a3, a3, -16
    li      t1, 0
    li      t2, 0
    mv      t3, a6
    mv      t4, a7
    li      s0, 128
4:  srai    t5, a4, 63                      /* all ones when the next bit of X is 1 */
    slli    a4, a4, 1
    srli    t0, a5, 63
    or      a4, a4, t0
    slli    a5, a5, 1
    and     t0, t3, t5
    xor     t1, t1, t0
    and     t0, t4, t5
    xor     t2, t2, t0
    andi    t5, t4, 1                       # all ones when the last bit of V is 1
    neg     t5, t5
    slli    t0, t3, 63
    srli    t4, t4, 1
    or      t4, t4, t0
    srli    t3, t3, 1
    and     t0, s1, t5
    xor     t3, t3, t0
    addi    s0, s0, -1
    bnez    s0, 4b
    mv      a4, t1
    mv      a5, t2
    j       1b
8:  STORE_BE64 a4, a0, 0, t6
    STORE_BE64 a5, a0, 8, t6
    UNWIND_BEGIN_EPILOGUE
    ld      s0, 16(sp)
    UNWIND_RESTORE s0
    ld      s1, 24(sp)
    UNWIND_RESTORE s1
    addi    sp, sp, 32
    UNWIND_FREE 32
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_aes128_ghash

/* Rcon[1] to Rcon[10], the first byte of each. */
312:
    .byte   0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36
