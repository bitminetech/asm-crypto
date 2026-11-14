/*
 * SHA-512 (FIPS 180-4 sections 5.1.2, 5.2.2, 5.3.5 and 6.4) for ARM64 (AAPCS64).
 * Requirements: docs/reference/sha-512.md. Layouts: include/sha512.inc.
 *
 * v1: follows the specification steps, one 128-byte block at a time.
 * crypto_sha512_init, crypto_sha512_update and crypto_sha512_final keep a
 * Sha512State, so a message can be taken in parts; crypto_sha512 runs the
 * three on a state on its stack. x18 is never used. Every function that
 * calls keeps an x29 frame record.
 */
.set ISA_ARM64, 1
.include "crypto.inc"
.include "sha512.inc"
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

/* ---------------------------------------------------------------- crypto_sha512 */

/* crypto_sha512(message, digest) -> status. The state at sp. */
FUNCTION crypto_sha512
    ENTER   0, 208
    mov     x19, x0
    mov     x20, x1
    mov     x0, sp
    CALL_GLOBAL crypto_sha512_init
    mov     x0, sp
    mov     x1, x19
    CALL_GLOBAL crypto_sha512_update
    mov     x0, sp
    mov     x1, x20
    CALL_GLOBAL crypto_sha512_final
    mov     x0, #CRYPTO_OK
    LEAVE   0, 208
END_FUNCTION crypto_sha512

/* crypto_sha512_init(state) -> status: H = H(0) of section 5.3.5, count 0. A leaf. */
FUNCTION crypto_sha512_init
    UNWIND_END_PROLOGUE
    adr     x9, 21f
    ldp     x10, x11, [x9]
    stp     x10, x11, [x0, #CRYPTO_SHA512_STATE_H]
    ldp     x10, x11, [x9, #16]
    stp     x10, x11, [x0, #CRYPTO_SHA512_STATE_H + 16]
    ldp     x10, x11, [x9, #32]
    stp     x10, x11, [x0, #CRYPTO_SHA512_STATE_H + 32]
    ldp     x10, x11, [x9, #48]
    stp     x10, x11, [x0, #CRYPTO_SHA512_STATE_H + 48]
    str     xzr, [x0, #CRYPTO_SHA512_STATE_COUNT]
    mov     x0, #CRYPTO_OK
    ret
END_FUNCTION crypto_sha512_init

/*
 * crypto_sha512_update(state, message) -> status.
 * x19 state, x20 the next message byte, x21 bytes left, x22 fill.
 */
FUNCTION crypto_sha512_update
    ENTER   0
    mov     x19, x0
    ldr     x9, [x1, #CRYPTO_BYTES_OFFSET]
    ldr     x21, [x1, #CRYPTO_BYTES_COUNT]
    add     x20, x1, x9
    ldr     x9, [x19, #CRYPTO_SHA512_STATE_COUNT]
    and     x22, x9, #127
    add     x9, x9, x21
    str     x9, [x19, #CRYPTO_SHA512_STATE_COUNT]
    cbz     x22, 3f
    mov     x10, #128                       /* fill the buffer up to 128 bytes */
    sub     x10, x10, x22
    cmp     x21, x10
    csel    x10, x21, x10, lo
    add     x11, x19, #CRYPTO_SHA512_STATE_BUFFER
    add     x11, x11, x22
    add     x22, x22, x10
    sub     x21, x21, x10
1:  cbz     x10, 2f
    ldrb    w12, [x20], #1
    strb    w12, [x11], #1
    sub     x10, x10, #1
    b       1b
2:  cmp     x22, #128
    b.lo    9f                              /* the message ended in the buffer */
    mov     x0, x19
    add     x1, x19, #CRYPTO_SHA512_STATE_BUFFER
    mov     x2, #1
    bl      crypto_sha512_blocks
3:  lsr     x2, x21, #7                     /* full blocks straight from the message */
    cbz     x2, 4f
    mov     x0, x19
    mov     x1, x20
    add     x20, x20, x2, lsl #7
    bl      crypto_sha512_blocks
4:  and     x10, x21, #127                  /* keep the rest */
    add     x11, x19, #CRYPTO_SHA512_STATE_BUFFER
5:  cbz     x10, 9f
    ldrb    w12, [x20], #1
    strb    w12, [x11], #1
    sub     x10, x10, #1
    b       5b
9:  mov     x0, #CRYPTO_OK
    LEAVE   0
END_FUNCTION crypto_sha512_update

/*
 * crypto_sha512_final(state, digest) -> status: pads as section 5.1.2 says
 * and writes H big endian. x19 state, x20 digest, x21 the buffer.
 */
FUNCTION crypto_sha512_final
    ENTER   0
    mov     x19, x0
    mov     x20, x1
    add     x21, x19, #CRYPTO_SHA512_STATE_BUFFER
    ldr     x9, [x19, #CRYPTO_SHA512_STATE_COUNT]
    and     x10, x9, #127
    mov     w11, #0x80
    strb    w11, [x21, x10]
    add     x10, x10, #1
1:  cmp     x10, #128                       /* zeros after the 0x80 byte */
    b.hs    2f
    strb    wzr, [x21, x10]
    add     x10, x10, #1
    b       1b
2:  and     x10, x9, #127
    cmp     x10, #112
    b.lo    4f
    mov     x0, x19                         /* no room for the length: one more block */
    mov     x1, x21
    mov     x2, #1
    bl      crypto_sha512_blocks
    mov     x10, #0
3:  str     xzr, [x21, x10]
    add     x10, x10, #8
    cmp     x10, #112
    b.lo    3b
4:  ldr     x9, [x19, #CRYPTO_SHA512_STATE_COUNT]
    lsr     x10, x9, #61                    /* the length in bits, 128 bits big endian */
    lsl     x11, x9, #3
    rev     x10, x10
    rev     x11, x11
    stp     x10, x11, [x21, #112]
    mov     x0, x19
    mov     x1, x21
    mov     x2, #1
    bl      crypto_sha512_blocks
    mov     x10, #0
5:  ldr     x11, [x19, x10]
    rev     x11, x11
    str     x11, [x20, x10]
    add     x10, x10, #8
    cmp     x10, #64
    b.lo    5b
    mov     x0, #CRYPTO_OK
    LEAVE   0
END_FUNCTION crypto_sha512_final

/* ---------------------------------------------------------------- Compression */

/*
 * One round of section 6.4.2, step 3, for the working variables a to h.
 * h becomes T1 + T2 (the next a) and d becomes d + T1 (the next e).
 * x3 walks K and x4 walks W. Uses x13, x14.
 */
.macro ROUND a, b, c, d, e, f, g, h
    ldr     x13, [x3], #8
    ldr     x14, [x4], #8
    add     \h, \h, x13
    add     \h, \h, x14
    ror     x13, \e, #14                    /* Sigma1(e) */
    eor     x13, x13, \e, ror #18
    eor     x13, x13, \e, ror #41
    add     \h, \h, x13
    and     x13, \e, \f                     /* Ch(e, f, g) */
    bic     x14, \g, \e
    eor     x13, x13, x14
    add     \h, \h, x13                     /* T1 */
    add     \d, \d, \h
    ror     x13, \a, #28                    /* Sigma0(a) */
    eor     x13, x13, \a, ror #34
    eor     x13, x13, \a, ror #39
    add     \h, \h, x13
    eor     x13, \a, \b                     /* Maj(a, b, c) = ((a ^ b) & c) ^ (a & b) */
    and     x13, x13, \c
    and     x14, \a, \b
    eor     x13, x13, x14
    add     \h, \h, x13                     /* T1 + T2 */
.endm

/*
 * crypto_sha512_blocks(h, data, count): runs section 6.4.2 on count blocks
 * of 128 bytes at data, updating the 8 words at h. A leaf: x0 h, x1 data,
 * x2 blocks left, x3 K, x4 W, x5 to x12 a to h, x13 to x17 temporaries.
 * W[0..79] at sp.
 */
LOCAL_FUNCTION crypto_sha512_blocks
    sub     sp, sp, #640
    UNWIND_ALLOC 640
    UNWIND_END_PROLOGUE
    cbz     x2, 9f
1:  mov     x4, sp                          /* W[0..15]: the block as big-endian words */
    mov     x15, #16
2:  ldr     x14, [x1], #8
    rev     x14, x14
    str     x14, [x4], #8
    subs    x15, x15, #1
    b.ne    2b
    mov     x15, #64                        /* W[16..79] */
3:  ldur    x14, [x4, #-16]                 /* sigma1(W[t-2]) */
    ror     x16, x14, #19
    eor     x16, x16, x14, ror #61
    eor     x16, x16, x14, lsr #6
    ldur    x14, [x4, #-120]                /* sigma0(W[t-15]) */
    ror     x17, x14, #1
    eor     x17, x17, x14, ror #8
    eor     x17, x17, x14, lsr #7
    add     x16, x16, x17
    ldur    x14, [x4, #-56]                 /* W[t-7] */
    add     x16, x16, x14
    ldur    x14, [x4, #-128]                /* W[t-16] */
    add     x16, x16, x14
    str     x16, [x4], #8
    subs    x15, x15, #1
    b.ne    3b
    ldp     x5, x6, [x0]
    ldp     x7, x8, [x0, #16]
    ldp     x9, x10, [x0, #32]
    ldp     x11, x12, [x0, #48]
    adr     x3, 20f
    mov     x4, sp
    mov     x15, #10
4:  ROUND   x5, x6, x7, x8, x9, x10, x11, x12
    ROUND   x12, x5, x6, x7, x8, x9, x10, x11
    ROUND   x11, x12, x5, x6, x7, x8, x9, x10
    ROUND   x10, x11, x12, x5, x6, x7, x8, x9
    ROUND   x9, x10, x11, x12, x5, x6, x7, x8
    ROUND   x8, x9, x10, x11, x12, x5, x6, x7
    ROUND   x7, x8, x9, x10, x11, x12, x5, x6
    ROUND   x6, x7, x8, x9, x10, x11, x12, x5
    subs    x15, x15, #1
    b.ne    4b
    ldp     x13, x14, [x0]                  /* H += a to h */
    add     x5, x5, x13
    add     x6, x6, x14
    stp     x5, x6, [x0]
    ldp     x13, x14, [x0, #16]
    add     x7, x7, x13
    add     x8, x8, x14
    stp     x7, x8, [x0, #16]
    ldp     x13, x14, [x0, #32]
    add     x9, x9, x13
    add     x10, x10, x14
    stp     x9, x10, [x0, #32]
    ldp     x13, x14, [x0, #48]
    add     x11, x11, x13
    add     x12, x12, x14
    stp     x11, x12, [x0, #48]
    subs    x2, x2, #1
    b.ne    1b
9:  UNWIND_BEGIN_EPILOGUE
    add     sp, sp, #640
    UNWIND_FREE 640
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_sha512_blocks

/* ---------------------------------------------------------------- Constants */

/* K of section 4.2.3, then H(0) of section 5.3.5. */
    .p2align 3
20:
    .quad   0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc
    .quad   0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118
    .quad   0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2
    .quad   0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694
    .quad   0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65
    .quad   0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5
    .quad   0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4
    .quad   0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70
    .quad   0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df
    .quad   0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b
    .quad   0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30
    .quad   0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8
    .quad   0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8
    .quad   0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3
    .quad   0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec
    .quad   0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b
    .quad   0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178
    .quad   0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b
    .quad   0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c
    .quad   0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
21:
    .quad   0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1
    .quad   0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
