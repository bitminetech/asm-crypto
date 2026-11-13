/*
 * ChaCha20, Poly1305 and the ChaCha20-Poly1305 AEAD (RFC 8439) for RISC-V
 * (RISC-V ELF psABI, LP64D). Baseline RV64GC instructions only: carries come
 * from sltu, and rotations from slliw, srliw and or. Values at addresses
 * that may not be 8-byte aligned are read and written one byte at a time.
 * Requirements: docs/reference/chacha20.md, docs/reference/poly1305.md and
 * docs/reference/chacha20-poly1305.md. Layouts: include/chacha20.inc.
 *
 * The functions and their steps follow the ARM64 file one for one. The
 * ChaCha20 block keeps its 16 state words in s0 to s11 and a4 to a7; only
 * the low 32 bits of each register count. Poly1305 works in base 2^64 with
 * five 64 x 64 products for each block. Nothing branches on key or data
 * bytes; only the result of the whole tag comparison decides a branch.
 */
.set ISA_RISCV64, 1
.include "crypto.inc"
.include "chacha20.inc"
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

/* ---------------------------------------------------------------- AEAD */

.set A_BLOCK, 0                     # the first key stream block: the Poly1305 key
.set A_POLY, 64                     # the Poly1305 state
.set A_LENGTHS, 128                 # le64(aad bytes) || le64(ciphertext bytes)
.set A_TAG, 144                     # the computed tag
.set A_FRAME, 160

/* The Poly1305 key and state from block 0 of the key stream. Uses s1 key, s2 nonce. */
.macro POLY_KEY unused=0
.if \unused
.endif
    mv      a0, s1
    li      a1, 0
    mv      a2, s2
    addi    a3, sp, A_BLOCK
    call    crypto_chacha20_block
    addi    a0, sp, A_POLY
    addi    a1, sp, A_BLOCK
    call    crypto_poly1305_init
.endm

/* The tag over aad (s4), then the ciphertext (bytes at s7, count at s6), into sp + A_TAG. */
.macro POLY_TAG unused=0
.if \unused
.endif
    addi    a0, sp, A_POLY
    ld      a1, CRYPTO_BYTES_OFFSET(s4)
    add     a1, s4, a1
    ld      a2, CRYPTO_BYTES_COUNT(s4)
    li      a3, 1
    call    crypto_poly1305_blocks
    addi    a0, sp, A_POLY
    mv      a1, s7
    mv      a2, s6
    li      a3, 1
    call    crypto_poly1305_blocks
    ld      t0, CRYPTO_BYTES_COUNT(s4)
    sd      t0, A_LENGTHS(sp)
    sd      s6, A_LENGTHS+8(sp)
    addi    a0, sp, A_POLY
    addi    a1, sp, A_LENGTHS
    li      a2, 16
    li      a3, 1
    call    crypto_poly1305_blocks
    addi    a0, sp, A_POLY
    addi    a1, sp, A_TAG
    call    crypto_poly1305_emit
.endm

/*
 * crypto_chacha20_aead_encrypt(key, nonce, plaintext, aad, sealed) -> status
 * s1 key, s2 nonce, s3 plaintext, s4 aad, s5 sealed, s6 plaintext bytes,
 * s7 the ciphertext in sealed.
 */
FUNCTION crypto_chacha20_aead_encrypt
    ENTER   A_FRAME
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      s5, a4
    li      a0, CRYPTO_BUFFER_TOO_SMALL
    ld      s6, CRYPTO_BYTES_COUNT(s3)
    ld      t0, CRYPTO_BYTES_SIZE(s5)
    li      t1, CRYPTO_BYTES_FIXED + CRYPTO_POLY1305_TAG_SIZE
    bltu    t0, t1, 9f
    sub     t0, t0, t1
    bltu    t0, s6, 9f
    POLY_KEY
    addi    s7, s5, CRYPTO_BYTES_FIXED
    mv      a0, s1                          # C = P ^ the key stream from block 1
    mv      a1, s2
    li      a2, 1
    ld      a3, CRYPTO_BYTES_OFFSET(s3)
    add     a3, s3, a3
    mv      a4, s7
    mv      a5, s6
    call    crypto_chacha20_xor
    POLY_TAG
    add     t1, s7, s6                      # the tag, a byte at a time
    li      t2, 0
1:  add     t3, sp, t2
    lbu     t3, A_TAG(t3)
    add     t4, t1, t2
    sb      t3, 0(t4)
    addi    t2, t2, 1
    li      t3, 16
    bltu    t2, t3, 1b
    li      t0, CRYPTO_BYTES_FIXED
    sd      t0, CRYPTO_BYTES_OFFSET(s5)
    addi    t0, s6, CRYPTO_POLY1305_TAG_SIZE
    sd      t0, CRYPTO_BYTES_COUNT(s5)
    li      a0, CRYPTO_OK
9:  LEAVE   A_FRAME
END_FUNCTION crypto_chacha20_aead_encrypt

/*
 * crypto_chacha20_aead_decrypt(key, nonce, sealed, aad, plaintext) -> status
 * s1 key, s2 nonce, s3 sealed, s4 aad, s5 plaintext, s6 ciphertext bytes,
 * s7 the ciphertext in sealed. The tag is checked before any plaintext is
 * written.
 */
FUNCTION crypto_chacha20_aead_decrypt
    ENTER   A_FRAME
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      s5, a4
    li      a0, CRYPTO_CHACHA20_POLY1305_FAIL
    ld      s6, CRYPTO_BYTES_COUNT(s3)
    li      t0, CRYPTO_POLY1305_TAG_SIZE
    bltu    s6, t0, 9f
    sub     s6, s6, t0
    li      a0, CRYPTO_BUFFER_TOO_SMALL
    ld      t0, CRYPTO_BYTES_SIZE(s5)
    li      t1, CRYPTO_BYTES_FIXED
    bltu    t0, t1, 9f
    sub     t0, t0, t1
    bltu    t0, s6, 9f
    POLY_KEY
    ld      s7, CRYPTO_BYTES_OFFSET(s3)
    add     s7, s3, s7
    POLY_TAG
    add     t1, s7, s6                      # compare all 16 bytes
    li      t2, 0
    li      t5, 0
1:  add     t3, sp, t2
    lbu     t3, A_TAG(t3)
    add     t4, t1, t2
    lbu     t4, 0(t4)
    xor     t3, t3, t4
    or      t5, t5, t3
    addi    t2, t2, 1
    li      t3, 16
    bltu    t2, t3, 1b
    li      a0, CRYPTO_CHACHA20_POLY1305_FAIL
    bnez    t5, 9f
    mv      a0, s1
    mv      a1, s2
    li      a2, 1
    mv      a3, s7
    addi    a4, s5, CRYPTO_BYTES_FIXED
    mv      a5, s6
    call    crypto_chacha20_xor
    li      t0, CRYPTO_BYTES_FIXED
    sd      t0, CRYPTO_BYTES_OFFSET(s5)
    sd      s6, CRYPTO_BYTES_COUNT(s5)
    li      a0, CRYPTO_OK
9:  LEAVE   A_FRAME
END_FUNCTION crypto_chacha20_aead_decrypt

/* ---------------------------------------------------------------- ChaCha20 */

/* d = d rotated left by n, on the low 32 bits. Uses t0. */
.macro ROTL d, n
    slliw   t0, \d, \n
    srliw   \d, \d, 32 - \n
    or      \d, \d, t0
.endm

/* The quarter round of RFC 8439 section 2.1 on state words a, b, c, d. */
.macro QR a, b, c, d
    addw    \a, \a, \b
    xor     \d, \d, \a
    ROTL    \d, 16
    addw    \c, \c, \d
    xor     \b, \b, \c
    ROTL    \b, 12
    addw    \a, \a, \b
    xor     \d, \d, \a
    ROTL    \d, 8
    addw    \c, \c, \d
    xor     \b, \b, \c
    ROTL    \b, 7
.endm

/*
 * crypto_chacha20_block(key, counter, nonce, block): the ChaCha20 block
 * function of RFC 8439 section 2.3, with the 32-bit block counter in a
 * register. A leaf: the state words 0 to 11 in s0 to s11 and 12 to 15 in
 * a4 to a7, t1 the round count; s0 to s11 saved at sp.
 */
LOCAL_FUNCTION crypto_chacha20_block
    addi    sp, sp, -96
    UNWIND_ALLOC 96
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
    sd      s9, 72(sp)
    UNWIND_SAVE s9, 72
    sd      s10, 80(sp)
    UNWIND_SAVE s10, 80
    sd      s11, 88(sp)
    UNWIND_SAVE s11, 88
    UNWIND_END_PROLOGUE
    li      s0, 0x61707865
    li      s1, 0x3320646e
    li      s2, 0x79622d32
    li      s3, 0x6b206574
    lw      s4, 0(a0)
    lw      s5, 4(a0)
    lw      s6, 8(a0)
    lw      s7, 12(a0)
    lw      s8, 16(a0)
    lw      s9, 20(a0)
    lw      s10, 24(a0)
    lw      s11, 28(a0)
    mv      a4, a1
    lw      a5, 0(a2)
    lw      a6, 4(a2)
    lw      a7, 8(a2)
    li      t1, 10
1:  QR      s0, s4, s8, a4                  # column rounds
    QR      s1, s5, s9, a5
    QR      s2, s6, s10, a6
    QR      s3, s7, s11, a7
    QR      s0, s5, s10, a7                 # diagonal rounds
    QR      s1, s6, s11, a4
    QR      s2, s7, s8, a5
    QR      s3, s4, s9, a6
    addi    t1, t1, -1
    bnez    t1, 1b
    li      t2, 0x61707865                  # add the input state, store little endian
    addw    s0, s0, t2
    sw      s0, 0(a3)
    li      t2, 0x3320646e
    addw    s1, s1, t2
    sw      s1, 4(a3)
    li      t2, 0x79622d32
    addw    s2, s2, t2
    sw      s2, 8(a3)
    li      t2, 0x6b206574
    addw    s3, s3, t2
    sw      s3, 12(a3)
    lw      t2, 0(a0)
    addw    s4, s4, t2
    sw      s4, 16(a3)
    lw      t2, 4(a0)
    addw    s5, s5, t2
    sw      s5, 20(a3)
    lw      t2, 8(a0)
    addw    s6, s6, t2
    sw      s6, 24(a3)
    lw      t2, 12(a0)
    addw    s7, s7, t2
    sw      s7, 28(a3)
    lw      t2, 16(a0)
    addw    s8, s8, t2
    sw      s8, 32(a3)
    lw      t2, 20(a0)
    addw    s9, s9, t2
    sw      s9, 36(a3)
    lw      t2, 24(a0)
    addw    s10, s10, t2
    sw      s10, 40(a3)
    lw      t2, 28(a0)
    addw    s11, s11, t2
    sw      s11, 44(a3)
    addw    a4, a4, a1
    sw      a4, 48(a3)
    lw      t2, 0(a2)
    addw    a5, a5, t2
    sw      a5, 52(a3)
    lw      t2, 4(a2)
    addw    a6, a6, t2
    sw      a6, 56(a3)
    lw      t2, 8(a2)
    addw    a7, a7, t2
    sw      a7, 60(a3)
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
    ld      s9, 72(sp)
    UNWIND_RESTORE s9
    ld      s10, 80(sp)
    UNWIND_RESTORE s10
    ld      s11, 88(sp)
    UNWIND_RESTORE s11
    addi    sp, sp, 96
    UNWIND_FREE 96
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_chacha20_block

/*
 * crypto_chacha20_xor(key, nonce, counter, source, target, count): target =
 * source ^ the key stream from block counter on (RFC 8439 section 2.4), for
 * count bytes. s1 key, s2 nonce, s3 counter, s4 source, s5 target, s6 bytes
 * left. The key stream block at sp.
 */
LOCAL_FUNCTION crypto_chacha20_xor
    ENTER   64
    mv      s1, a0
    mv      s2, a1
    mv      s3, a2
    mv      s4, a3
    mv      s5, a4
    mv      s6, a5
1:  beqz    s6, 9f
    mv      a0, s1
    mv      a1, s3
    mv      a2, s2
    mv      a3, sp
    call    crypto_chacha20_block
    addiw   s3, s3, 1
    li      t0, 64
    mv      t1, s6
    bltu    s6, t0, 2f
    mv      t1, t0
2:  sub     s6, s6, t1
    mv      t2, sp
3:  li      t0, 8
    bltu    t1, t0, 4f
    ld      t3, 0(s4)
    ld      t4, 0(t2)
    xor     t3, t3, t4
    sd      t3, 0(s5)
    addi    s4, s4, 8
    addi    t2, t2, 8
    addi    s5, s5, 8
    addi    t1, t1, -8
    j       3b
4:  beqz    t1, 1b
    lbu     t3, 0(s4)
    lbu     t4, 0(t2)
    xor     t3, t3, t4
    sb      t3, 0(s5)
    addi    s4, s4, 1
    addi    t2, t2, 1
    addi    s5, s5, 1
    addi    t1, t1, -1
    j       4b
9:  LEAVE   64
END_FUNCTION crypto_chacha20_xor

/* ---------------------------------------------------------------- Poly1305 */

/*
 * crypto_poly1305_mac(key, message, tag) -> status: poly1305_mac of RFC 8439
 * section 2.5.1. The full blocks carry the 2^128 bit; a last part block
 * gets a 0x01 byte after it, then zeros. s1 key, s2 message bytes, s3 tag,
 * s4 count, s5 the bytes of the last part block. The state at sp, the last
 * block at sp + 64.
 */
FUNCTION crypto_poly1305_mac
    ENTER   80
    mv      s1, a0
    ld      t0, CRYPTO_BYTES_OFFSET(a1)
    add     s2, a1, t0
    ld      s4, CRYPTO_BYTES_COUNT(a1)
    mv      s3, a2
    mv      a0, sp
    mv      a1, s1
    call    crypto_poly1305_init
    mv      a0, sp
    mv      a1, s2
    andi    a2, s4, -16
    li      a3, 1
    call    crypto_poly1305_blocks
    andi    s5, s4, 15
    beqz    s5, 2f
    sd      zero, 64(sp)                    # the last part block, 0x01, zeros
    sd      zero, 72(sp)
    andi    t1, s4, -16
    add     t1, s2, t1
    li      t2, 0
1:  add     t3, t1, t2
    lbu     t3, 0(t3)
    add     t4, sp, t2
    sb      t3, 64(t4)
    addi    t2, t2, 1
    bltu    t2, s5, 1b
    add     t4, sp, s5
    li      t3, 1
    sb      t3, 64(t4)
    mv      a0, sp
    addi    a1, sp, 64
    li      a2, 16
    li      a3, 0
    call    crypto_poly1305_blocks
2:  mv      a0, sp
    mv      a1, s3
    call    crypto_poly1305_emit
    li      a0, CRYPTO_OK
    LEAVE   80
END_FUNCTION crypto_poly1305_mac

/* d = the 8 bytes at off(base) as a little-endian number. Uses tmp. */
.macro LOAD_LE64 d, base, off, tmp
    lbu     \d, \off+7(\base)
    .irp k, 6, 5, 4, 3, 2, 1, 0
    slli    \d, \d, 8
    lbu     \tmp, \off+\k(\base)
    or      \d, \d, \tmp
    .endr
.endm

/*
 * crypto_poly1305_init(state, key): h = 0, r = the first 16 key bytes
 * clamped (RFC 8439 section 2.5), s1 = r1 + r1 / 4, s = the last 16 bytes.
 * A leaf.
 */
LOCAL_FUNCTION crypto_poly1305_init
    UNWIND_END_PROLOGUE
    LOAD_LE64 a2, a1, 0, t6
    LOAD_LE64 a3, a1, 8, t6
    LOAD_LE64 a4, a1, 16, t6
    LOAD_LE64 a5, a1, 24, t6
    li      t0, 0x0FFFFFFC0FFFFFFF
    and     a2, a2, t0
    li      t0, 0x0FFFFFFC0FFFFFFC
    and     a3, a3, t0
    srli    t0, a3, 2
    add     t0, a3, t0
    sd      zero, CRYPTO_POLY1305_H0(a0)
    sd      zero, CRYPTO_POLY1305_H1(a0)
    sd      zero, CRYPTO_POLY1305_H2(a0)
    sd      a2, CRYPTO_POLY1305_R0(a0)
    sd      a3, CRYPTO_POLY1305_R1(a0)
    sd      t0, CRYPTO_POLY1305_S1(a0)
    sd      a4, CRYPTO_POLY1305_S(a0)
    sd      a5, CRYPTO_POLY1305_S+8(a0)
    ret
END_FUNCTION crypto_poly1305_init

/*
 * crypto_poly1305_blocks(state, data, count, pad): h = (h + block + pad *
 * 2^128) * r mod 2^130 - 5 for each 16-byte block of the count bytes.
 * Zeros pad the last block to 16 bytes (pad16 of RFC 8439 section 2.8).
 * A leaf: h0 a3, h1 a4, h2 a5, r0 a6, r1 a7, s1 t0; d0 t2:t1, d1 t4:t3;
 * t5, t6 carries. The padded block at sp, pad at sp + 16.
 */
LOCAL_FUNCTION crypto_poly1305_blocks
    addi    sp, sp, -32
    UNWIND_ALLOC 32
    UNWIND_END_PROLOGUE
    sd      a3, 16(sp)
    ld      a3, CRYPTO_POLY1305_H0(a0)
    ld      a4, CRYPTO_POLY1305_H1(a0)
    ld      a5, CRYPTO_POLY1305_H2(a0)
    ld      a6, CRYPTO_POLY1305_R0(a0)
    ld      a7, CRYPTO_POLY1305_R1(a0)
    ld      t0, CRYPTO_POLY1305_S1(a0)
1:  beqz    a2, 8f
    li      t1, 16
    bgeu    a2, t1, 3f
    sd      zero, 0(sp)                     # the last part block, padded
    sd      zero, 8(sp)
    li      t1, 0
2:  add     t2, a1, t1
    lbu     t2, 0(t2)
    add     t3, sp, t1
    sb      t2, 0(t3)
    addi    t1, t1, 1
    bltu    t1, a2, 2b
    mv      a1, sp
    li      a2, 16
3:  ld      t1, 0(a1)
    ld      t2, 8(a1)
    addi    a1, a1, 16
    addi    a2, a2, -16
    add     a3, a3, t1                      # h += m + pad * 2^128
    sltu    t3, a3, t1
    add     a4, a4, t2
    sltu    t4, a4, t2
    add     a4, a4, t3
    sltu    t5, a4, t3
    or      t4, t4, t5
    add     a5, a5, t4
    ld      t5, 16(sp)
    add     a5, a5, t5
    mul     t1, a3, a6                      # d0 = h0 r0 + h1 s1
    mulhu   t2, a3, a6
    mul     t3, a4, t0
    mulhu   t4, a4, t0
    add     t1, t1, t3
    sltu    t3, t1, t3
    add     t2, t2, t4
    add     t2, t2, t3
    mul     t3, a3, a7                      # d1 = h0 r1 + h1 r0 + h2 s1
    mulhu   t4, a3, a7
    mul     t5, a4, a6
    mulhu   t6, a4, a6
    add     t3, t3, t5
    sltu    t5, t3, t5
    add     t4, t4, t6
    add     t4, t4, t5
    mul     t5, a5, t0
    add     t3, t3, t5
    sltu    t5, t3, t5
    add     t4, t4, t5
    mul     a5, a5, a6                      # d2 = h2 r0
    add     t3, t3, t2                      # h1 = d1 + d0 / 2^64
    sltu    t2, t3, t2
    add     t4, t4, t2
    add     a5, a5, t4                      # h2 = d2 + d1 / 2^64
    andi    t5, a5, -4                      # c = 5 * (h2 / 4)
    srli    t6, a5, 2
    add     t5, t5, t6
    andi    a5, a5, 3
    add     a3, t1, t5
    sltu    t6, a3, t5
    add     a4, t3, t6
    sltu    t6, a4, t6
    add     a5, a5, t6
    j       1b
8:  sd      a3, CRYPTO_POLY1305_H0(a0)
    sd      a4, CRYPTO_POLY1305_H1(a0)
    sd      a5, CRYPTO_POLY1305_H2(a0)
    UNWIND_BEGIN_EPILOGUE
    addi    sp, sp, 32
    UNWIND_FREE 32
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_poly1305_blocks

/*
 * crypto_poly1305_emit(state, tag): tag = (h mod 2^130 - 5) + s mod 2^128,
 * 16 bytes little endian. h - p is taken when h + 5 reaches 2^130. A leaf:
 * tag is 8-byte aligned.
 */
LOCAL_FUNCTION crypto_poly1305_emit
    UNWIND_END_PROLOGUE
    ld      a2, CRYPTO_POLY1305_H0(a0)
    ld      a3, CRYPTO_POLY1305_H1(a0)
    ld      a4, CRYPTO_POLY1305_H2(a0)
    addi    a5, a2, 5                       # g = h + 5
    sltu    t0, a5, a2
    add     a6, a3, t0
    sltu    t0, a6, t0
    add     a7, a4, t0
    srli    a7, a7, 2                       # g reaches 2^130: h - p is g - 2^130
    snez    a7, a7
    neg     a7, a7
    xor     t0, a2, a5
    and     t0, t0, a7
    xor     a2, a2, t0
    xor     t0, a3, a6
    and     t0, t0, a7
    xor     a3, a3, t0
    ld      t1, CRYPTO_POLY1305_S(a0)
    ld      t2, CRYPTO_POLY1305_S+8(a0)
    add     a2, a2, t1
    sltu    t0, a2, t1
    add     a3, a3, t2
    add     a3, a3, t0
    sd      a2, 0(a1)
    sd      a3, 8(a1)
    ret
END_FUNCTION crypto_poly1305_emit
