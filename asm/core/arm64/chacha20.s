/*
 * ChaCha20, Poly1305 and the ChaCha20-Poly1305 AEAD (RFC 8439) for ARM64
 * (AAPCS64). Requirements: docs/reference/chacha20.md,
 * docs/reference/poly1305.md and docs/reference/chacha20-poly1305.md.
 * Layouts: include/chacha20.inc.
 *
 * ChaCha20 keeps its 16 state words in w0 to w15 and rotates with ror.
 * Poly1305 works in base 2^64: h is three limbs, r two clamped limbs, and
 * each block costs five 64 x 64 products, as in OpenSSL's poly1305_blocks.
 * Nothing branches on key or data bytes; only the result of the whole tag
 * comparison decides a branch. x18 is never used. Every function that calls
 * keeps an x29 frame record.
 */
.set ISA_ARM64, 1
.include "crypto.inc"
.include "chacha20.inc"
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

/* ---------------------------------------------------------------- AEAD */

.set A_BLOCK, 0                     /* the first key stream block: the Poly1305 key */
.set A_POLY, 64                     /* the Poly1305 state */
.set A_LENGTHS, 128                 /* le64(aad bytes) || le64(ciphertext bytes) */
.set A_TAG, 144                     /* the computed tag */
.set A_FRAME, 160

/*
 * The Poly1305 key and state from block 0 of the key stream (RFC 8439
 * section 2.6). Uses x19 key, x20 nonce.
 */
.macro POLY_KEY
    mov     x0, x19
    mov     x1, #0
    mov     x2, x20
    add     x3, sp, #A_BLOCK
    bl      crypto_chacha20_block
    add     x0, sp, #A_POLY
    add     x1, sp, #A_BLOCK
    bl      crypto_poly1305_init
.endm

/* The tag over aad (x22), then the ciphertext (bytes at ct, count at n), into sp + A_TAG. */
.macro POLY_TAG ct, n
    add     x0, sp, #A_POLY
    ldr     x1, [x22, #CRYPTO_BYTES_OFFSET]
    add     x1, x22, x1
    ldr     x2, [x22, #CRYPTO_BYTES_COUNT]
    mov     x3, #1
    bl      crypto_poly1305_blocks
    add     x0, sp, #A_POLY
    mov     x1, \ct
    mov     x2, \n
    mov     x3, #1
    bl      crypto_poly1305_blocks
    ldr     x9, [x22, #CRYPTO_BYTES_COUNT]
    add     x10, sp, #A_LENGTHS
    stp     x9, \n, [x10]
    add     x0, sp, #A_POLY
    add     x1, sp, #A_LENGTHS
    mov     x2, #16
    mov     x3, #1
    bl      crypto_poly1305_blocks
    add     x0, sp, #A_POLY
    add     x1, sp, #A_TAG
    bl      crypto_poly1305_emit
.endm

/*
 * crypto_chacha20_aead_encrypt(key, nonce, plaintext, aad, sealed) -> status
 * x19 key, x20 nonce, x21 plaintext, x22 aad, x23 sealed, x24 plaintext
 * bytes, x25 the ciphertext in sealed.
 */
FUNCTION crypto_chacha20_aead_encrypt
    ENTER   0, A_FRAME
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x23, x4
    mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    ldr     x24, [x21, #CRYPTO_BYTES_COUNT]
    ldr     x9, [x23, #CRYPTO_BYTES_SIZE]
    subs    x9, x9, #(CRYPTO_BYTES_FIXED + CRYPTO_POLY1305_TAG_SIZE)
    b.lo    9f
    cmp     x9, x24
    b.lo    9f
    POLY_KEY
    add     x25, x23, #CRYPTO_BYTES_FIXED
    mov     x0, x19                         /* C = P ^ the key stream from block 1 */
    mov     x1, x20
    mov     x2, #1
    ldr     x3, [x21, #CRYPTO_BYTES_OFFSET]
    add     x3, x21, x3
    mov     x4, x25
    mov     x5, x24
    bl      crypto_chacha20_xor
    POLY_TAG x25, x24
    add     x9, sp, #A_TAG
    ldp     x9, x10, [x9]
    add     x11, x25, x24
    str     x9, [x11]
    str     x10, [x11, #8]
    mov     x9, #CRYPTO_BYTES_FIXED
    str     x9, [x23, #CRYPTO_BYTES_OFFSET]
    add     x9, x24, #CRYPTO_POLY1305_TAG_SIZE
    str     x9, [x23, #CRYPTO_BYTES_COUNT]
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, A_FRAME
END_FUNCTION crypto_chacha20_aead_encrypt

/*
 * crypto_chacha20_aead_decrypt(key, nonce, sealed, aad, plaintext) -> status
 * x19 key, x20 nonce, x21 sealed, x22 aad, x23 plaintext, x24 ciphertext
 * bytes, x25 the ciphertext in sealed. The tag is checked before any
 * plaintext is written.
 */
FUNCTION crypto_chacha20_aead_decrypt
    ENTER   0, A_FRAME
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x23, x4
    mov     x0, #CRYPTO_CHACHA20_POLY1305_FAIL
    ldr     x24, [x21, #CRYPTO_BYTES_COUNT]
    subs    x24, x24, #CRYPTO_POLY1305_TAG_SIZE
    b.lo    9f
    mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    ldr     x9, [x23, #CRYPTO_BYTES_SIZE]
    subs    x9, x9, #CRYPTO_BYTES_FIXED
    b.lo    9f
    cmp     x9, x24
    b.lo    9f
    POLY_KEY
    ldr     x25, [x21, #CRYPTO_BYTES_OFFSET]
    add     x25, x21, x25
    POLY_TAG x25, x24
    add     x9, sp, #A_TAG                  /* compare all 16 bytes */
    ldp     x9, x10, [x9]
    add     x11, x25, x24
    ldr     x12, [x11]
    ldr     x13, [x11, #8]
    eor     x9, x9, x12
    eor     x10, x10, x13
    orr     x9, x9, x10
    mov     x0, #CRYPTO_CHACHA20_POLY1305_FAIL
    cbnz    x9, 9f
    mov     x0, x19
    mov     x1, x20
    mov     x2, #1
    mov     x3, x25
    add     x4, x23, #CRYPTO_BYTES_FIXED
    mov     x5, x24
    bl      crypto_chacha20_xor
    mov     x9, #CRYPTO_BYTES_FIXED
    str     x9, [x23, #CRYPTO_BYTES_OFFSET]
    str     x24, [x23, #CRYPTO_BYTES_COUNT]
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, A_FRAME
END_FUNCTION crypto_chacha20_aead_decrypt

/* ---------------------------------------------------------------- ChaCha20 */

/* The quarter round of RFC 8439 section 2.1 on state words a, b, c, d. */
.macro QR a, b, c, d
    add     \a, \a, \b
    eor     \d, \d, \a
    ror     \d, \d, #16
    add     \c, \c, \d
    eor     \b, \b, \c
    ror     \b, \b, #20
    add     \a, \a, \b
    eor     \d, \d, \a
    ror     \d, \d, #24
    add     \c, \c, \d
    eor     \b, \b, \c
    ror     \b, \b, #25
.endm

/* reg = the 64-bit constant v. */
.macro MOV64 reg, v
    movz    \reg, #((\v) & 0xFFFF)
    movk    \reg, #(((\v) >> 16) & 0xFFFF), lsl #16
    movk    \reg, #(((\v) >> 32) & 0xFFFF), lsl #32
    movk    \reg, #(((\v) >> 48) & 0xFFFF), lsl #48
.endm

/* w = the 32-bit constant v. */
.macro MOV32 w, v
    movz    \w, #((\v) & 0xFFFF)
    movk    \w, #(((\v) >> 16) & 0xFFFF), lsl #16
.endm

/*
 * crypto_chacha20_block(key, counter, nonce, block): the ChaCha20 block
 * function of RFC 8439 section 2.3, with the 32-bit block counter in a
 * register. A leaf: the state in w0 to w15, the round count in x16, the
 * arguments at sp (key, counter, nonce, block).
 */
LOCAL_FUNCTION crypto_chacha20_block
    sub     sp, sp, #32
    UNWIND_ALLOC 32
    UNWIND_END_PROLOGUE
    stp     x0, x1, [sp]
    stp     x2, x3, [sp, #16]
    mov     x17, x0
    mov     x16, x2
    mov     w12, w1
    ldp     w4, w5, [x17]
    ldp     w6, w7, [x17, #8]
    ldp     w8, w9, [x17, #16]
    ldp     w10, w11, [x17, #24]
    ldr     w13, [x16]
    ldp     w14, w15, [x16, #4]
    MOV32   w0, 0x61707865
    MOV32   w1, 0x3320646e
    MOV32   w2, 0x79622d32
    MOV32   w3, 0x6b206574
    mov     x16, #10
1:  QR      w0, w4, w8, w12                 /* column rounds */
    QR      w1, w5, w9, w13
    QR      w2, w6, w10, w14
    QR      w3, w7, w11, w15
    QR      w0, w5, w10, w15                /* diagonal rounds */
    QR      w1, w6, w11, w12
    QR      w2, w7, w8, w13
    QR      w3, w4, w9, w14
    subs    x16, x16, #1
    b.ne    1b
    MOV32   w17, 0x61707865                 /* add the input state */
    add     w0, w0, w17
    MOV32   w17, 0x3320646e
    add     w1, w1, w17
    MOV32   w17, 0x79622d32
    add     w2, w2, w17
    MOV32   w17, 0x6b206574
    add     w3, w3, w17
    ldr     x16, [sp]
    ldr     w17, [x16]
    add     w4, w4, w17
    ldr     w17, [x16, #4]
    add     w5, w5, w17
    ldr     w17, [x16, #8]
    add     w6, w6, w17
    ldr     w17, [x16, #12]
    add     w7, w7, w17
    ldr     w17, [x16, #16]
    add     w8, w8, w17
    ldr     w17, [x16, #20]
    add     w9, w9, w17
    ldr     w17, [x16, #24]
    add     w10, w10, w17
    ldr     w17, [x16, #28]
    add     w11, w11, w17
    ldr     x17, [sp, #8]
    add     w12, w12, w17
    ldr     x16, [sp, #16]
    ldr     w17, [x16]
    add     w13, w13, w17
    ldr     w17, [x16, #4]
    add     w14, w14, w17
    ldr     w17, [x16, #8]
    add     w15, w15, w17
    ldr     x16, [sp, #24]                  /* the words, little endian */
    stp     w0, w1, [x16]
    stp     w2, w3, [x16, #8]
    stp     w4, w5, [x16, #16]
    stp     w6, w7, [x16, #24]
    stp     w8, w9, [x16, #32]
    stp     w10, w11, [x16, #40]
    stp     w12, w13, [x16, #48]
    stp     w14, w15, [x16, #56]
    UNWIND_BEGIN_EPILOGUE
    add     sp, sp, #32
    UNWIND_FREE 32
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_chacha20_block

/*
 * crypto_chacha20_xor(key, nonce, counter, source, target, count): target =
 * source ^ the key stream from block counter on (RFC 8439 section 2.4), for
 * count bytes. x19 key, x20 nonce, w21 counter, x22 source, x23 target,
 * x24 bytes left. The key stream block at sp.
 */
LOCAL_FUNCTION crypto_chacha20_xor
    ENTER   0, 64
    mov     x19, x0
    mov     x20, x1
    mov     w21, w2
    mov     x22, x3
    mov     x23, x4
    mov     x24, x5
1:  cbz     x24, 9f
    mov     x0, x19
    mov     w1, w21
    mov     x2, x20
    mov     x3, sp
    bl      crypto_chacha20_block
    add     w21, w21, #1
    cmp     x24, #64
    b.lo    3f
    mov     x9, #0
2:  ldr     x10, [x22, x9]
    ldr     x11, [sp, x9]
    eor     x10, x10, x11
    str     x10, [x23, x9]
    add     x9, x9, #8
    cmp     x9, #64
    b.lo    2b
    add     x22, x22, #64
    add     x23, x23, #64
    sub     x24, x24, #64
    b       1b
3:  mov     x9, #0                          /* the last part block */
4:  ldrb    w10, [x22, x9]
    ldrb    w11, [sp, x9]
    eor     w10, w10, w11
    strb    w10, [x23, x9]
    add     x9, x9, #1
    cmp     x9, x24
    b.lo    4b
9:  LEAVE   0, 64
END_FUNCTION crypto_chacha20_xor

/* ---------------------------------------------------------------- Poly1305 */

/*
 * crypto_poly1305_mac(key, message, tag) -> status: poly1305_mac of RFC 8439
 * section 2.5.1. The full blocks carry the 2^128 bit; a last part block
 * gets a 0x01 byte after it, then zeros. x19 key, x20 message bytes,
 * x21 tag, x22 count. The state at sp, the last block at sp + 64.
 */
FUNCTION crypto_poly1305_mac
    ENTER   0, 80
    mov     x19, x0
    ldr     x9, [x1, #CRYPTO_BYTES_OFFSET]
    add     x20, x1, x9
    ldr     x22, [x1, #CRYPTO_BYTES_COUNT]
    mov     x21, x2
    mov     x0, sp
    mov     x1, x19
    bl      crypto_poly1305_init
    mov     x0, sp
    mov     x1, x20
    and     x2, x22, #0xFFFFFFFFFFFFFFF0
    mov     x3, #1
    bl      crypto_poly1305_blocks
    ands    x9, x22, #15
    b.eq    2f
    stp     xzr, xzr, [sp, #64]             /* the last part block, 0x01, zeros */
    and     x10, x22, #0xFFFFFFFFFFFFFFF0
    add     x10, x20, x10
    add     x13, sp, #64
    mov     x11, #0
1:  ldrb    w12, [x10, x11]
    strb    w12, [x13, x11]
    add     x11, x11, #1
    cmp     x11, x9
    b.lo    1b
    mov     w12, #1
    strb    w12, [x13, x9]
    mov     x0, sp
    mov     x1, x13
    mov     x2, #16
    mov     x3, #0
    bl      crypto_poly1305_blocks
2:  mov     x0, sp
    mov     x1, x21
    bl      crypto_poly1305_emit
    mov     x0, #CRYPTO_OK
    LEAVE   0, 80
END_FUNCTION crypto_poly1305_mac

/*
 * crypto_poly1305_init(state, key): h = 0, r = the first 16 key bytes
 * clamped (RFC 8439 section 2.5), s1 = r1 + r1 / 4, s = the last 16 bytes.
 * A leaf.
 */
LOCAL_FUNCTION crypto_poly1305_init
    UNWIND_END_PROLOGUE
    ldp     x2, x3, [x1]
    ldp     x4, x5, [x1, #16]
    MOV64   x6, 0x0FFFFFFC0FFFFFFF
    and     x2, x2, x6
    MOV64   x6, 0x0FFFFFFC0FFFFFFC
    and     x3, x3, x6
    add     x6, x3, x3, lsr #2
    stp     xzr, xzr, [x0, #CRYPTO_POLY1305_H0]
    str     xzr, [x0, #CRYPTO_POLY1305_H2]
    stp     x2, x3, [x0, #CRYPTO_POLY1305_R0]
    str     x6, [x0, #CRYPTO_POLY1305_S1]
    stp     x4, x5, [x0, #CRYPTO_POLY1305_S]
    ret
END_FUNCTION crypto_poly1305_init

/*
 * crypto_poly1305_blocks(state, data, count, pad): h = (h + block + pad *
 * 2^128) * r mod 2^130 - 5 for each 16-byte block of the count bytes.
 * Zeros pad the last block to 16 bytes (pad16 of RFC 8439 section 2.8).
 * A leaf: h0 x4, h1 x5, h2 x6, r0 x7, r1 x8, s1 x13, pad x15; x9 to x12,
 * x14, x16, x17 products. The padded block at sp.
 */
LOCAL_FUNCTION crypto_poly1305_blocks
    sub     sp, sp, #16
    UNWIND_ALLOC 16
    UNWIND_END_PROLOGUE
    ldp     x4, x5, [x0, #CRYPTO_POLY1305_H0]
    ldr     x6, [x0, #CRYPTO_POLY1305_H2]
    ldp     x7, x8, [x0, #CRYPTO_POLY1305_R0]
    ldr     x13, [x0, #CRYPTO_POLY1305_S1]
    mov     x15, x3
1:  cbz     x2, 8f
    cmp     x2, #16
    b.hs    3f
    stp     xzr, xzr, [sp]                  /* the last part block, padded */
    mov     x9, #0
2:  ldrb    w10, [x1, x9]
    strb    w10, [sp, x9]
    add     x9, x9, #1
    cmp     x9, x2
    b.lo    2b
    mov     x1, sp
    mov     x2, #16
3:  ldr     x9, [x1]
    ldr     x10, [x1, #8]
    add     x1, x1, #16
    sub     x2, x2, #16
    adds    x4, x4, x9                      /* h += m + pad * 2^128 */
    adcs    x5, x5, x10
    adc     x6, x6, x15
    mul     x9, x4, x7                      /* d0 = h0 r0 + h1 s1 */
    umulh   x10, x4, x7
    mul     x11, x5, x13
    umulh   x12, x5, x13
    adds    x9, x9, x11
    adc     x10, x10, x12
    mul     x11, x4, x8                     /* d1 = h0 r1 + h1 r0 + h2 s1 */
    umulh   x12, x4, x8
    mul     x14, x5, x7
    umulh   x16, x5, x7
    adds    x11, x11, x14
    adc     x12, x12, x16
    mul     x14, x6, x13
    adds    x11, x11, x14
    adc     x12, x12, xzr
    mul     x14, x6, x7                     /* d2 = h2 r0 */
    adds    x11, x11, x10                   /* h1 = d1 + d0 / 2^64 */
    adc     x12, x12, xzr
    add     x14, x14, x12                   /* h2 = d2 + d1 / 2^64 */
    and     x16, x14, #0xFFFFFFFFFFFFFFFC   /* c = 5 * (h2 / 4) */
    add     x16, x16, x14, lsr #2
    and     x6, x14, #3
    adds    x4, x9, x16
    adcs    x5, x11, xzr
    adc     x6, x6, xzr
    b       1b
8:  stp     x4, x5, [x0, #CRYPTO_POLY1305_H0]
    str     x6, [x0, #CRYPTO_POLY1305_H2]
    UNWIND_BEGIN_EPILOGUE
    add     sp, sp, #16
    UNWIND_FREE 16
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_poly1305_blocks

/*
 * crypto_poly1305_emit(state, tag): tag = (h mod 2^130 - 5) + s mod 2^128,
 * 16 bytes little endian. h - p is taken when h + 5 reaches 2^130. A leaf.
 */
LOCAL_FUNCTION crypto_poly1305_emit
    UNWIND_END_PROLOGUE
    ldp     x2, x3, [x0, #CRYPTO_POLY1305_H0]
    ldr     x4, [x0, #CRYPTO_POLY1305_H2]
    adds    x5, x2, #5                      /* g = h + 5 */
    adcs    x6, x3, xzr
    adc     x7, x4, xzr
    tst     x7, #0xFFFFFFFFFFFFFFFC         /* g reaches 2^130: h - p is g - 2^130 */
    csel    x2, x5, x2, ne
    csel    x3, x6, x3, ne
    ldp     x5, x6, [x0, #CRYPTO_POLY1305_S]
    adds    x2, x2, x5
    adc     x3, x3, x6
    stp     x2, x3, [x1]
    ret
END_FUNCTION crypto_poly1305_emit
