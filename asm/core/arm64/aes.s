/*
 * AES-128, CTR and GCM for ARM64 (AAPCS64).
 * Requirements: docs/reference/aes.md. Layouts: include/crypto.inc, include/aes.inc.
 *
 * Constant time: no table lookup and no branch depends on key or data bytes.
 * Four blocks (64 bytes) go through the rounds together as 8 bit planes of
 * 8 bytes: plane i holds bit i of every byte, byte g = 16 * block + k at bit g,
 * with k = r + 4c the FIPS 197 state byte of row r and column c.
 * SubBytes computes the inverse in GF(2^8) as x^254, then the affine map.
 * GHASH multiplies one bit at a time with masks (SP 800-38D algorithm 1).
 * x18 is never used. Every function that calls keeps an x29 frame record.
 */
.set ISA_ARM64, 1
.include "crypto.inc"
.include "aes.inc"
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

/* ---------------------------------------------------------------- AES-128-CTR */

/*
 * crypto_aes128_ctr(key, counter, input, output) -> status
 * x19 key, x20 counter, x21 input, x22 output, x23 input bytes.
 * The key schedule at sp.
 */
FUNCTION crypto_aes128_ctr
    ENTER   0, CRYPTO_AES128_SCHEDULE_SIZE
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    ldr     x23, [x21, #CRYPTO_BYTES_COUNT]
    ldr     x9, [x22, #CRYPTO_BYTES_SIZE]
    subs    x9, x9, #CRYPTO_BYTES_FIXED
    b.lo    9f
    cmp     x9, x23
    b.lo    9f
    mov     x0, x19
    mov     x1, sp
    bl      crypto_aes128_expand
    mov     x9, #CRYPTO_BYTES_FIXED
    str     x9, [x22, #CRYPTO_BYTES_OFFSET]
    str     x23, [x22, #CRYPTO_BYTES_COUNT]
    mov     x0, sp
    mov     x1, x20
    ldr     x2, [x21, #CRYPTO_BYTES_OFFSET]
    add     x2, x21, x2
    add     x3, x22, #CRYPTO_BYTES_FIXED
    mov     x4, x23
    mov     x5, #0
    bl      crypto_aes128_ctr_xor
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, CRYPTO_AES128_SCHEDULE_SIZE
END_FUNCTION crypto_aes128_ctr

/* ---------------------------------------------------------------- AES-128-GCM */

/* GCM locals, after the key schedule at sp. */
.set G_BLOCKS, CRYPTO_AES128_SCHEDULE_SIZE  /* E(0^128) = H, then E(J0) */
.set G_Y, G_BLOCKS + 64                     /* the GHASH value */
.set G_LENGTHS, G_Y + 16                    /* len(A) || len(C), in bits */
.set G_COUNTER, G_LENGTHS + 16              /* inc32(J0), the first counter block of the data */
.set G_FRAME, G_COUNTER + 16

/*
 * The key schedule from key x19, then H and E(J0) from iv x20, the counter
 * block inc32(J0), and Y = 0. J0 = IV || 0^31 || 1.
 */
.macro GCM_START
    mov     x0, x19
    mov     x1, sp
    bl      crypto_aes128_expand
    add     x9, sp, #G_BLOCKS
    stp     xzr, xzr, [x9]
    stp     xzr, xzr, [x9, #32]
    stp     xzr, xzr, [x9, #48]
    ldr     x10, [x20]
    ldr     w11, [x20, #8]
    mov     w12, #0x01000000
    str     x10, [x9, #16]
    str     w11, [x9, #24]
    str     w12, [x9, #28]
    add     x9, sp, #G_COUNTER
    mov     w12, #0x02000000
    str     x10, [x9]
    str     w11, [x9, #8]
    str     w12, [x9, #12]
    add     x9, sp, #G_Y
    stp     xzr, xzr, [x9]
    mov     x0, sp
    add     x1, sp, #G_BLOCKS
    bl      crypto_aes128_encrypt4
.endm

/* GHASH of the n bytes at data into Y, with zeros padding the last block. */
.macro GHASH data, n
    add     x0, sp, #G_Y
    add     x1, sp, #G_BLOCKS
    mov     x2, \data
    mov     x3, \n
    bl      crypto_aes128_ghash
.endm

/* GHASH of the lengths block, then x9, x10 = the tag E(J0) ^ Y. */
.macro GCM_TAG abytes, cbytes
    lsl     x9, \abytes, #3
    lsl     x10, \cbytes, #3
    rev     x9, x9
    rev     x10, x10
    add     x11, sp, #G_LENGTHS
    stp     x9, x10, [x11]
    mov     x10, #16
    GHASH   x11, x10
    add     x11, sp, #G_Y
    ldp     x9, x10, [x11]
    add     x11, sp, #(G_BLOCKS + 16)
    ldp     x11, x12, [x11]
    eor     x9, x9, x11
    eor     x10, x10, x12
.endm

/*
 * crypto_aes128_gcm_ae(key, iv, plaintext, aad, sealed) -> status
 * x19 key, x20 iv, x21 plaintext, x22 aad, x23 sealed, x24 plaintext bytes,
 * x25 sealed bytes.
 */
FUNCTION crypto_aes128_gcm_ae
    ENTER   0, G_FRAME
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x23, x4
    mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    ldr     x24, [x21, #CRYPTO_BYTES_COUNT]
    ldr     x9, [x23, #CRYPTO_BYTES_SIZE]
    subs    x9, x9, #(CRYPTO_BYTES_FIXED + CRYPTO_GCM_TAG_SIZE)
    b.lo    9f
    cmp     x9, x24
    b.lo    9f
    GCM_START
    add     x25, x23, #CRYPTO_BYTES_FIXED
    mov     x0, sp
    add     x1, sp, #G_COUNTER
    ldr     x2, [x21, #CRYPTO_BYTES_OFFSET]
    add     x2, x21, x2
    mov     x3, x25
    mov     x4, x24
    mov     x5, #1
    bl      crypto_aes128_ctr_xor
    ldr     x9, [x22, #CRYPTO_BYTES_OFFSET]
    add     x9, x22, x9
    ldr     x10, [x22, #CRYPTO_BYTES_COUNT]
    GHASH   x9, x10
    GHASH   x25, x24
    ldr     x11, [x22, #CRYPTO_BYTES_COUNT]
    GCM_TAG x11, x24
    add     x11, x25, x24
    stp     x9, x10, [x11]
    mov     x9, #CRYPTO_BYTES_FIXED
    str     x9, [x23, #CRYPTO_BYTES_OFFSET]
    add     x9, x24, #CRYPTO_GCM_TAG_SIZE
    str     x9, [x23, #CRYPTO_BYTES_COUNT]
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, G_FRAME
END_FUNCTION crypto_aes128_gcm_ae

/*
 * crypto_aes128_gcm_ad(key, iv, sealed, aad, plaintext) -> status
 * x19 key, x20 iv, x21 sealed, x22 aad, x23 plaintext, x24 ciphertext bytes,
 * x25 sealed bytes. The tag is checked before any plaintext is written.
 */
FUNCTION crypto_aes128_gcm_ad
    ENTER   0, G_FRAME
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x23, x4
    mov     x0, #CRYPTO_GCM_FAIL
    ldr     x24, [x21, #CRYPTO_BYTES_COUNT]
    subs    x24, x24, #CRYPTO_GCM_TAG_SIZE
    b.lo    9f
    mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    ldr     x9, [x23, #CRYPTO_BYTES_SIZE]
    subs    x9, x9, #CRYPTO_BYTES_FIXED
    b.lo    9f
    cmp     x9, x24
    b.lo    9f
    GCM_START
    ldr     x25, [x21, #CRYPTO_BYTES_OFFSET]
    add     x25, x21, x25
    ldr     x9, [x22, #CRYPTO_BYTES_OFFSET]
    add     x9, x22, x9
    ldr     x10, [x22, #CRYPTO_BYTES_COUNT]
    GHASH   x9, x10
    GHASH   x25, x24
    ldr     x11, [x22, #CRYPTO_BYTES_COUNT]
    GCM_TAG x11, x24
    add     x11, x25, x24
    ldp     x12, x13, [x11]
    eor     x9, x9, x12
    eor     x10, x10, x13
    orr     x9, x9, x10
    mov     x0, #CRYPTO_GCM_FAIL
    cbnz    x9, 9f
    mov     x0, sp
    add     x1, sp, #G_COUNTER
    mov     x2, x25
    add     x3, x23, #CRYPTO_BYTES_FIXED
    mov     x4, x24
    mov     x5, #1
    bl      crypto_aes128_ctr_xor
    mov     x9, #CRYPTO_BYTES_FIXED
    str     x9, [x23, #CRYPTO_BYTES_OFFSET]
    str     x24, [x23, #CRYPTO_BYTES_COUNT]
    mov     x0, #CRYPTO_OK
9:  LEAVE   0, G_FRAME
END_FUNCTION crypto_aes128_gcm_ad

/* ---------------------------------------------------------------- Helpers */

/*
 * crypto_aes128_expand(key, schedule): KeyExpansion of FIPS 197 section 5.2,
 * then each round key repeated 4 times and turned into planes.
 * x19 key, x20 schedule, x21 word i, x22 Rcon, w23 temp.
 * w[0..43] at sp (176 bytes), the SubWord block at sp + 176 (64 bytes).
 */
LOCAL_FUNCTION crypto_aes128_expand
    ENTER   0, 240
    mov     x19, x0
    mov     x20, x1
    ldp     x9, x10, [x19]
    stp     x9, x10, [sp]
    mov     x21, #4
    adr     x22, 312f
1:  add     x9, sp, x21, lsl #2
    ldur    w23, [x9, #-4]
    tst     x21, #3
    b.ne    2f
    ror     w23, w23, #8                    /* RotWord */
    stp     xzr, xzr, [sp, #176]            /* SubWord: the S-box on the 4 bytes */
    stp     xzr, xzr, [sp, #192]
    stp     xzr, xzr, [sp, #208]
    stp     xzr, xzr, [sp, #224]
    str     w23, [sp, #176]
    add     x0, sp, #176
    mov     x1, #0
    bl      crypto_aes128_bitslice
    add     x0, sp, #176
    bl      crypto_aes128_sbox
    add     x0, sp, #176
    mov     x1, #1
    bl      crypto_aes128_bitslice
    ldr     w23, [sp, #176]
    ldrb    w9, [x22], #1                   /* Rcon */
    eor     w23, w23, w9
2:  add     x9, sp, x21, lsl #2
    ldur    w10, [x9, #-16]
    eor     w23, w23, w10
    str     w23, [x9]
    add     x21, x21, #1
    cmp     x21, #44
    b.lo    1b
    mov     x21, #0
3:  add     x9, sp, x21, lsl #4
    ldp     x10, x11, [x9]
    add     x0, x20, x21, lsl #6
    stp     x10, x11, [x0]
    stp     x10, x11, [x0, #16]
    stp     x10, x11, [x0, #32]
    stp     x10, x11, [x0, #48]
    mov     x1, #0
    bl      crypto_aes128_bitslice
    add     x21, x21, #1
    cmp     x21, #11
    b.lo    3b
    LEAVE   0, 240
END_FUNCTION crypto_aes128_expand

/*
 * crypto_aes128_ctr_xor(schedule, counter, source, target, count, mode):
 * target = source XOR the key stream, count bytes. The key stream is
 * E(counter), E(counter + 1), ... Mode 0 adds 1 to the whole block as a
 * 128-bit big-endian number, mode 1 to its last 32 bits only (inc32).
 * x19 schedule, x20 source, x21 target, x22 bytes left, x23 mode,
 * x24:x25 the counter as a 128-bit number. Four counter blocks at sp.
 */
LOCAL_FUNCTION crypto_aes128_ctr_xor
    ENTER   0, 64
    mov     x19, x0
    mov     x20, x2
    mov     x21, x3
    mov     x22, x4
    mov     x23, x5
    ldp     x24, x25, [x1]
    rev     x24, x24
    rev     x25, x25
1:  cbz     x22, 9f
    mov     x9, #0
2:  rev     x10, x24
    rev     x11, x25
    add     x12, sp, x9
    stp     x10, x11, [x12]
    cbnz    x23, 3f
    adds    x25, x25, #1
    adc     x24, x24, xzr
    b       4f
3:  add     w10, w25, #1
    bfi     x25, x10, #0, #32
4:  add     x9, x9, #16
    cmp     x9, #64
    b.lo    2b
    mov     x0, x19
    mov     x1, sp
    bl      crypto_aes128_encrypt4
    mov     x9, #64
    cmp     x22, x9
    csel    x9, x22, x9, lo
    sub     x22, x22, x9
    mov     x10, sp
5:  cmp     x9, #8
    b.lo    6f
    ldr     x11, [x20], #8
    ldr     x12, [x10], #8
    eor     x11, x11, x12
    str     x11, [x21], #8
    sub     x9, x9, #8
    b       5b
6:  cbz     x9, 1b
    ldrb    w11, [x20], #1
    ldrb    w12, [x10], #1
    eor     w11, w11, w12
    strb    w11, [x21], #1
    sub     x9, x9, #1
    b       6b
9:  LEAVE   0, 64
END_FUNCTION crypto_aes128_ctr_xor

/*
 * crypto_aes128_encrypt4(schedule, blocks): the cipher of FIPS 197 section
 * 5.1 on the 4 blocks of 16 bytes at blocks, in place.
 * x19 schedule, x20 blocks, x21 round.
 */
LOCAL_FUNCTION crypto_aes128_encrypt4
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    mov     x0, x20
    mov     x1, #0
    bl      crypto_aes128_bitslice
    mov     x9, #0
1:  ldr     x10, [x20, x9]
    ldr     x11, [x19, x9]
    eor     x10, x10, x11
    str     x10, [x20, x9]
    add     x9, x9, #8
    cmp     x9, #64
    b.lo    1b
    mov     x21, #1
2:  mov     x0, x20
    bl      crypto_aes128_sbox
    mov     x0, x20
    add     x1, x19, x21, lsl #6
    cmp     x21, #10
    cset    x2, ne
    bl      crypto_aes128_mix
    add     x21, x21, #1
    cmp     x21, #10
    b.ls    2b
    mov     x0, x20
    mov     x1, #1
    bl      crypto_aes128_bitslice
    LEAVE   0
END_FUNCTION crypto_aes128_encrypt4

/* SWAPMOVE: swap the bits of b at mask with the bits of a at mask << n. Uses x10. */
.macro SWAPMOVE a, b, mask, n
    eor     x10, \b, \a, lsr #\n
    and     x10, x10, #\mask
    eor     \b, \b, x10
    eor     \a, \a, x10, lsl #\n
.endm

/* Swap byte i of word j with byte j of word i, for the words in x2 to x9. */
.macro BYTE_TRANSPOSE
    SWAPMOVE x2, x6, 0x00000000FFFFFFFF, 32
    SWAPMOVE x3, x7, 0x00000000FFFFFFFF, 32
    SWAPMOVE x4, x8, 0x00000000FFFFFFFF, 32
    SWAPMOVE x5, x9, 0x00000000FFFFFFFF, 32
    SWAPMOVE x2, x4, 0x0000FFFF0000FFFF, 16
    SWAPMOVE x3, x5, 0x0000FFFF0000FFFF, 16
    SWAPMOVE x6, x8, 0x0000FFFF0000FFFF, 16
    SWAPMOVE x7, x9, 0x0000FFFF0000FFFF, 16
    SWAPMOVE x2, x3, 0x00FF00FF00FF00FF, 8
    SWAPMOVE x4, x5, 0x00FF00FF00FF00FF, 8
    SWAPMOVE x6, x7, 0x00FF00FF00FF00FF, 8
    SWAPMOVE x8, x9, 0x00FF00FF00FF00FF, 8
.endm

/* In word w, swap bit i of byte j with bit j of byte i. Masks in x11, x12, x13. Uses x10. */
.macro BIT_TRANSPOSE w
    eor     x10, \w, \w, lsr #7
    and     x10, x10, x11
    eor     \w, \w, x10
    eor     \w, \w, x10, lsl #7
    eor     x10, \w, \w, lsr #14
    and     x10, x10, x12
    eor     \w, \w, x10
    eor     \w, \w, x10, lsl #14
    eor     x10, \w, \w, lsr #28
    and     x10, x10, x13
    eor     \w, \w, x10
    eor     \w, \w, x10, lsl #28
.endm

/*
 * crypto_aes128_bitslice(blocks, inverse): turn the 64 bytes at blocks into
 * the 8 planes in place (inverse 0), or the planes back into bytes (inverse 1).
 * Forward is the bit transpose in each word, then the byte transpose across
 * the words; inverse is the same two steps in the other order.
 */
LOCAL_FUNCTION crypto_aes128_bitslice
    UNWIND_END_PROLOGUE
    adr     x10, 311f
    ldp     x11, x12, [x10]
    ldr     x13, [x10, #16]
    ldp     x2, x3, [x0]
    ldp     x4, x5, [x0, #16]
    ldp     x6, x7, [x0, #32]
    ldp     x8, x9, [x0, #48]
    cbz     x1, 1f
    BYTE_TRANSPOSE
1:  .irp w, x2, x3, x4, x5, x6, x7, x8, x9
    BIT_TRANSPOSE \w
    .endr
    cbnz    x1, 2f
    BYTE_TRANSPOSE
2:  stp     x2, x3, [x0]
    stp     x4, x5, [x0, #16]
    stp     x6, x7, [x0, #32]
    stp     x8, x9, [x0, #48]
    ret
END_FUNCTION crypto_aes128_bitslice

/* S-box stack: x, x^2, x^3, x^12, then x19 to x22. */
.set SB_X, 0
.set SB_X2, 64
.set SB_X3, 128
.set SB_X12, 192
.set SB_FRAME, 288

/* a (x1 to x8) = 8 planes at ptr + off. */
.macro LOAD_A ptr, off
    ldp     x1, x2, [\ptr, #\off]
    ldp     x3, x4, [\ptr, #\off + 16]
    ldp     x5, x6, [\ptr, #\off + 32]
    ldp     x7, x8, [\ptr, #\off + 48]
.endm

.macro STORE_A off
    stp     x1, x2, [sp, #\off]
    stp     x3, x4, [sp, #\off + 16]
    stp     x5, x6, [sp, #\off + 32]
    stp     x7, x8, [sp, #\off + 48]
.endm

.macro STORE_R off
    stp     x9, x10, [sp, #\off]
    stp     x11, x12, [sp, #\off + 16]
    stp     x13, x14, [sp, #\off + 32]
    stp     x15, x16, [sp, #\off + 48]
.endm

.macro R_TO_A
    mov     x1, x9
    mov     x2, x10
    mov     x3, x11
    mov     x4, x12
    mov     x5, x13
    mov     x6, x14
    mov     x7, x15
    mov     x8, x16
.endm

/* r (x9 to x16) = a^2 in GF(2^8), a linear map of the planes. */
.macro SQUARE
    eor     x9, x1, x5
    eor     x9, x9, x7                      /* r0 = a0 ^ a4 ^ a6 */
    eor     x10, x5, x7
    eor     x10, x10, x8                    /* r1 = a4 ^ a6 ^ a7 */
    eor     x11, x2, x6                     /* r2 = a1 ^ a5 */
    eor     x12, x5, x6
    eor     x12, x12, x7
    eor     x12, x12, x8                    /* r3 = a4 ^ a5 ^ a6 ^ a7 */
    eor     x13, x3, x5
    eor     x13, x13, x8                    /* r4 = a2 ^ a4 ^ a7 */
    eor     x14, x6, x7                     /* r5 = a5 ^ a6 */
    eor     x15, x4, x6                     /* r6 = a3 ^ a5 */
    eor     x16, x7, x8                     /* r7 = a6 ^ a7 */
.endm

/*
 * r = a * b in GF(2^8), b the 8 planes at sp + off. Horner on the planes of
 * b from 7 down to 0: r = r * x, then r ^= a & b_i. Times x maps the planes
 * r0..r7 to r7, r0 ^ r7, r1, r2 ^ r7, r3 ^ r7, r4, r5, r6.
 * Uses x17, x19, x20, x21.
 */
.macro MULTIPLY off
    mov     x9, #0
    mov     x10, #0
    mov     x11, #0
    mov     x12, #0
    mov     x13, #0
    mov     x14, #0
    mov     x15, #0
    mov     x16, #0
    add     x21, sp, #\off
    mov     x20, #7
1:  mov     x19, x16
    mov     x16, x15
    mov     x15, x14
    mov     x14, x13
    eor     x13, x12, x19
    eor     x12, x11, x19
    mov     x11, x10
    eor     x10, x9, x19
    mov     x9, x19
    ldr     x17, [x21, x20, lsl #3]
    and     x19, x1, x17
    eor     x9, x9, x19
    and     x19, x2, x17
    eor     x10, x10, x19
    and     x19, x3, x17
    eor     x11, x11, x19
    and     x19, x4, x17
    eor     x12, x12, x19
    and     x19, x5, x17
    eor     x13, x13, x19
    and     x19, x6, x17
    eor     x14, x14, x19
    and     x19, x7, x17
    eor     x15, x15, x19
    and     x19, x8, x17
    eor     x16, x16, x19
    subs    x20, x20, #1
    b.ge    1b
.endm

/* Output plane o = r_i ^ r_(i+4) ^ r_(i+5) ^ r_(i+6) ^ r_(i+7), register numbers. */
.macro AFFINE o, i, j, k, l, m
    eor     x\o, x\i, x\j
    eor     x\o, x\o, x\k
    eor     x\o, x\o, x\l
    eor     x\o, x\o, x\m
.endm

/*
 * crypto_aes128_sbox(planes): SubBytes on the 8 planes at planes, in place:
 * x^254 = x^-1 in GF(2^8) by x^2, x^3, x^6, x^12, x^15, x^30, x^60, x^120,
 * x^240, x^252, x^254, then the affine map with c = 0x63.
 */
LOCAL_FUNCTION crypto_aes128_sbox
    sub     sp, sp, #SB_FRAME
    UNWIND_ALLOC SB_FRAME
    stp     x19, x20, [sp, #256]
    UNWIND_SAVE_REGP x19, x20, 256, SB_FRAME
    stp     x21, x22, [sp, #272]
    UNWIND_SAVE_REGP x21, x22, 272, SB_FRAME
    UNWIND_END_PROLOGUE
    LOAD_A  x0, 0
    STORE_A SB_X
    SQUARE                                  /* x^2 */
    STORE_R SB_X2
    R_TO_A
    MULTIPLY SB_X                           /* x^3 */
    STORE_R SB_X3
    R_TO_A
    SQUARE                                  /* x^6 */
    R_TO_A
    SQUARE                                  /* x^12 */
    STORE_R SB_X12
    R_TO_A
    MULTIPLY SB_X3                          /* x^15 */
    R_TO_A
    SQUARE                                  /* x^30 */
    R_TO_A
    SQUARE                                  /* x^60 */
    R_TO_A
    SQUARE                                  /* x^120 */
    R_TO_A
    SQUARE                                  /* x^240 */
    R_TO_A
    MULTIPLY SB_X12                         /* x^252 */
    R_TO_A
    MULTIPLY SB_X2                          /* x^254 */
    AFFINE  1, 9, 13, 14, 15, 16
    AFFINE  2, 10, 14, 15, 16, 9
    AFFINE  3, 11, 15, 16, 9, 10
    AFFINE  4, 12, 16, 9, 10, 11
    AFFINE  5, 13, 9, 10, 11, 12
    AFFINE  6, 14, 10, 11, 12, 13
    AFFINE  7, 15, 11, 12, 13, 14
    AFFINE  8, 16, 12, 13, 14, 15
    mvn     x1, x1                          /* c = 0x63: bits 0, 1, 5 and 6 */
    mvn     x2, x2
    mvn     x6, x6
    mvn     x7, x7
    stp     x1, x2, [x0]
    stp     x3, x4, [x0, #16]
    stp     x5, x6, [x0, #32]
    stp     x7, x8, [x0, #48]
    UNWIND_BEGIN_EPILOGUE
    ldp     x21, x22, [sp, #272]
    UNWIND_RESTORE_REGP x21, x22, 272
    ldp     x19, x20, [sp, #256]
    UNWIND_RESTORE_REGP x19, x20, 256
    add     sp, sp, #SB_FRAME
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
 * The 8 planes of u ^ rot2(t) at sp.
 */
LOCAL_FUNCTION crypto_aes128_mix
    sub     sp, sp, #64
    UNWIND_ALLOC 64
    UNWIND_END_PROLOGUE
    adr     x9, 310f
    ldp     x3, x4, [x9]
    ldp     x5, x6, [x9, #16]
    ldp     x7, x8, [x9, #32]
    mov     x10, #0
1:  ldr     x11, [x0, x10]
    and     x12, x11, #0x1111111111111111   /* row 0 */
    and     x13, x3, x11, lsr #4            /* row 1 */
    orr     x12, x12, x13
    and     x13, x4, x11, lsl #12
    orr     x12, x12, x13
    and     x13, x5, x11, lsr #8            /* row 2 */
    orr     x12, x12, x13
    and     x13, x6, x11, lsl #8
    orr     x12, x12, x13
    and     x13, x7, x11, lsr #12           /* row 3 */
    orr     x12, x12, x13
    and     x13, x8, x11, lsl #4
    orr     x12, x12, x13
    cbz     x2, 2f
    lsr     x13, x12, #1                    /* u = rot1(a) */
    and     x13, x13, #0x7777777777777777
    lsl     x14, x12, #3
    and     x14, x14, #0x8888888888888888
    orr     x13, x13, x14
    eor     x12, x12, x13                   /* t = a ^ u */
    lsr     x14, x12, #2                    /* rot2(t) */
    and     x14, x14, #0x3333333333333333
    lsl     x15, x12, #2
    and     x15, x15, #0xCCCCCCCCCCCCCCCC
    orr     x14, x14, x15
    eor     x13, x13, x14
    str     x13, [sp, x10]
2:  str     x12, [x0, x10]
    add     x10, x10, #8
    cmp     x10, #64
    b.lo    1b
    cbz     x2, 3f
    ldr     x9, [x0, #56]                   /* t7 */
    ldr     x3, [x0]
    ldr     x4, [sp]
    eor     x4, x4, x9                      /* t7 ^ w0 */
    ldr     x5, [sp, #8]
    eor     x5, x5, x3
    eor     x5, x5, x9                      /* t0 ^ t7 ^ w1 */
    ldr     x6, [x0, #8]
    ldr     x7, [sp, #16]
    eor     x7, x7, x6                      /* t1 ^ w2 */
    ldr     x6, [x0, #16]
    ldr     x8, [sp, #24]
    eor     x8, x8, x6
    eor     x8, x8, x9                      /* t2 ^ t7 ^ w3 */
    ldr     x6, [x0, #24]
    ldr     x10, [sp, #32]
    eor     x10, x10, x6
    eor     x10, x10, x9                    /* t3 ^ t7 ^ w4 */
    ldr     x6, [x0, #32]
    ldr     x11, [sp, #40]
    eor     x11, x11, x6                    /* t4 ^ w5 */
    ldr     x6, [x0, #40]
    ldr     x12, [sp, #48]
    eor     x12, x12, x6                    /* t5 ^ w6 */
    ldr     x6, [x0, #48]
    ldr     x13, [sp, #56]
    eor     x13, x13, x6                    /* t6 ^ w7 */
    str     x4, [x0]
    str     x5, [x0, #8]
    str     x7, [x0, #16]
    str     x8, [x0, #24]
    str     x10, [x0, #32]
    str     x11, [x0, #40]
    str     x12, [x0, #48]
    str     x13, [x0, #56]
3:  mov     x10, #0
4:  ldr     x11, [x0, x10]
    ldr     x12, [x1, x10]
    eor     x11, x11, x12
    str     x11, [x0, x10]
    add     x10, x10, #8
    cmp     x10, #64
    b.lo    4b
    UNWIND_BEGIN_EPILOGUE
    add     sp, sp, #64
    UNWIND_FREE 64
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_aes128_mix

/*
 * crypto_aes128_ghash(y, h, data, count): for each 16-byte block X of the
 * count bytes at data, Y = (Y ^ X) * H in GF(2^128); zeros pad the last
 * block. Blocks are big-endian 128-bit numbers, bit 0 of GCM the top bit.
 * x4:x5 X, x6:x7 H, x8:x9 Z, x10:x11 V, x15 R. The padded block at sp.
 */
LOCAL_FUNCTION crypto_aes128_ghash
    sub     sp, sp, #16
    UNWIND_ALLOC 16
    UNWIND_END_PROLOGUE
    ldp     x4, x5, [x0]
    rev     x4, x4
    rev     x5, x5
    ldp     x6, x7, [x1]
    rev     x6, x6
    rev     x7, x7
    mov     x15, #0xE100000000000000
1:  cbz     x3, 8f
    cmp     x3, #16
    b.hs    3f
    stp     xzr, xzr, [sp]
    mov     x9, #0
2:  ldrb    w10, [x2, x9]
    strb    w10, [sp, x9]
    add     x9, x9, #1
    cmp     x9, x3
    b.lo    2b
    mov     x2, sp
    mov     x3, #16
3:  ldp     x9, x10, [x2], #16
    rev     x9, x9
    rev     x10, x10
    eor     x4, x4, x9
    eor     x5, x5, x10
    sub     x3, x3, #16
    mov     x8, #0
    mov     x9, #0
    mov     x10, x6
    mov     x11, x7
    mov     x12, #128
4:  asr     x13, x4, #63                    /* all ones when the next bit of X is 1 */
    extr    x4, x4, x5, #63
    lsl     x5, x5, #1
    and     x14, x10, x13
    eor     x8, x8, x14
    and     x14, x11, x13
    eor     x9, x9, x14
    sbfx    x13, x11, #0, #1                /* all ones when the last bit of V is 1 */
    extr    x11, x10, x11, #1
    lsr     x10, x10, #1
    and     x14, x15, x13
    eor     x10, x10, x14
    subs    x12, x12, #1
    b.ne    4b
    mov     x4, x8
    mov     x5, x9
    b       1b
8:  rev     x4, x4
    rev     x5, x5
    stp     x4, x5, [x0]
    UNWIND_BEGIN_EPILOGUE
    add     sp, sp, #16
    UNWIND_FREE 16
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_aes128_ghash

/* ShiftRows masks: rows 1, 2 and 3, the bits moved down then the bits moved up. */
    .p2align 3
310:
    .quad   0x0222022202220222, 0x2000200020002000
    .quad   0x0044004400440044, 0x4400440044004400
    .quad   0x0008000800080008, 0x8880888088808880
/* Bit transpose masks. */
311:
    .quad   0x00AA00AA00AA00AA, 0x0000CCCC0000CCCC, 0x00000000F0F0F0F0
/* Rcon[1] to Rcon[10], the first byte of each. */
312:
    .byte   0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36
