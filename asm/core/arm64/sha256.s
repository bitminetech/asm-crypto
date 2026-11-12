/*
 * crypto_sha256 for ARM64 (AAPCS64), FIPS 180-4 section 6.2.
 * Requirements: docs/reference/sha-256.md
 *
 * v1: follows the specification steps directly, one block at a time.
 * Uses only caller-saved registers x0-x17 (never x18) and a 416-byte frame.
 * It is a leaf function, so it builds no x29 frame record.
 *
 * Registers:
 *   x0      message, then the address of K
 *   x1      digest
 *   x2      address of the current block
 *   x3      blocks left in the current phase
 *   x4      phase: 0 for message blocks, 1 for padding blocks
 *   x5      round or word index t
 *   x6      number of padding blocks (1 or 2)
 *   w7-w14  working variables a, b, c, d, e, f, g, h
 *   x15-x17 temporaries
 *
 * Frame:
 *   sp + 0    W[0..63], 256 bytes
 *   sp + 256  H[0..7], 32 bytes
 *   sp + 288  padding blocks, 128 bytes
 *
 * Labels: 1 copy, 2 copied, 3 one padding block, 4 blocks, 5 load, 6 expand,
 * 7 round, 8 phase end, 9 done, 20 K, 21 initial H.
 */
.set ISA_ARM64, 1
.include "crypto.inc"
.include "platform.inc"

FUNCTION crypto_sha256
    sub     sp, sp, #416
    UNWIND_ALLOC 416
    UNWIND_END_PROLOGUE

    ldr     x5, [x0, #CRYPTO_BYTES_OFFSET]
    ldr     x15, [x0, #CRYPTO_BYTES_COUNT]      /* count */
    add     x2, x0, x5                          /* message bytes */

    /* Zero the 128-byte padding area. */
    add     x16, sp, #288
    stp     xzr, xzr, [x16, #0]
    stp     xzr, xzr, [x16, #16]
    stp     xzr, xzr, [x16, #32]
    stp     xzr, xzr, [x16, #48]
    stp     xzr, xzr, [x16, #64]
    stp     xzr, xzr, [x16, #80]
    stp     xzr, xzr, [x16, #96]
    stp     xzr, xzr, [x16, #112]

    /* Copy the bytes after the last full block into the padding area. */
    and     x17, x15, #63                       /* rem = count mod 64 */
    lsr     x3, x15, #6                         /* full blocks */
    add     x5, x2, x3, lsl #6                  /* first byte after them */
    mov     x6, #0
1:
    cmp     x6, x17
    b.hs    2f
    ldrb    w7, [x5, x6]
    strb    w7, [x16, x6]
    add     x6, x6, #1
    b       1b
2:
    mov     w7, #0x80
    strb    w7, [x16, x17]

    /* One padding block when rem < 56, else two. */
    mov     x6, #1
    cmp     x17, #56
    b.lo    3f
    mov     x6, #2
3:
    /* Message length in bits, big-endian, in the last 8 bytes of the padding. */
    lsl     x7, x15, #3
    rev     x7, x7
    add     x8, x16, x6, lsl #6
    stur    x7, [x8, #-8]

    /* H = initial hash value. */
    adr     x0, 21f
    ldp     x7, x8, [x0]
    ldp     x9, x10, [x0, #16]
    add     x16, sp, #256
    stp     x7, x8, [x16]
    stp     x9, x10, [x16, #16]

    adr     x0, 20f
    mov     x4, #0

4:
    cbz     x3, 8f

    /* W[0..15]: the block as big-endian words. */
    mov     x5, #0
5:
    ldr     w15, [x2, x5, lsl #2]
    rev     w15, w15
    str     w15, [sp, x5, lsl #2]
    add     x5, x5, #1
    cmp     x5, #16
    b.lo    5b

    /* W[16..63] = s1(W[t-2]) + W[t-7] + s0(W[t-15]) + W[t-16]. */
6:
    add     x17, sp, x5, lsl #2
    ldur    w15, [x17, #-60]                    /* W[t-15] */
    ror     w16, w15, #7
    eor     w16, w16, w15, ror #18
    eor     w16, w16, w15, lsr #3               /* s0 */
    ldur    w15, [x17, #-8]                     /* W[t-2] */
    ror     w7, w15, #17
    eor     w7, w7, w15, ror #19
    eor     w7, w7, w15, lsr #10                /* s1 */
    ldur    w15, [x17, #-64]                    /* W[t-16] */
    add     w16, w16, w15
    ldur    w15, [x17, #-28]                    /* W[t-7] */
    add     w16, w16, w15
    add     w16, w16, w7
    str     w16, [x17]
    add     x5, x5, #1
    cmp     x5, #64
    b.lo    6b

    /* a..h = H. */
    add     x16, sp, #256
    ldp     w7, w8, [x16]
    ldp     w9, w10, [x16, #8]
    ldp     w11, w12, [x16, #16]
    ldp     w13, w14, [x16, #24]

    mov     x5, #0
7:
    ror     w15, w11, #6
    eor     w15, w15, w11, ror #11
    eor     w15, w15, w11, ror #25              /* S1(e) */
    add     w14, w14, w15
    and     w16, w11, w12
    bic     w17, w13, w11
    orr     w16, w16, w17                       /* Ch(e, f, g) */
    add     w14, w14, w16
    ldr     w16, [x0, x5, lsl #2]               /* K[t] */
    ldr     w17, [sp, x5, lsl #2]               /* W[t] */
    add     w14, w14, w16
    add     w14, w14, w17                       /* T1 */
    add     w10, w10, w14                       /* d + T1 */
    ror     w15, w7, #2
    eor     w15, w15, w7, ror #13
    eor     w15, w15, w7, ror #22               /* S0(a) */
    add     w14, w14, w15
    orr     w16, w7, w8
    and     w16, w16, w9
    and     w17, w7, w8
    orr     w16, w16, w17                       /* Maj(a, b, c) */
    add     w15, w14, w16                       /* T1 + T2 */
    mov     w14, w13                            /* h = g */
    mov     w13, w12                            /* g = f */
    mov     w12, w11                            /* f = e */
    mov     w11, w10                            /* e = d + T1 */
    mov     w10, w9                             /* d = c */
    mov     w9, w8                              /* c = b */
    mov     w8, w7                              /* b = a */
    mov     w7, w15                             /* a = T1 + T2 */
    add     x5, x5, #1
    cmp     x5, #64
    b.lo    7b

    /* H = H + a..h. */
    add     x16, sp, #256
    ldp     w15, w17, [x16]
    add     w7, w7, w15
    add     w8, w8, w17
    stp     w7, w8, [x16]
    ldp     w15, w17, [x16, #8]
    add     w9, w9, w15
    add     w10, w10, w17
    stp     w9, w10, [x16, #8]
    ldp     w15, w17, [x16, #16]
    add     w11, w11, w15
    add     w12, w12, w17
    stp     w11, w12, [x16, #16]
    ldp     w15, w17, [x16, #24]
    add     w13, w13, w15
    add     w14, w14, w17
    stp     w13, w14, [x16, #24]

    add     x2, x2, #64
    sub     x3, x3, #1
    b       4b

8:
    /* After the message blocks, hash the padding blocks once. */
    cbnz    x4, 9f
    mov     x4, #1
    add     x2, sp, #288
    mov     x3, x6
    b       4b

9:
    /* digest = H as big-endian words. */
    add     x16, sp, #256
    ldp     w7, w8, [x16]
    ldp     w9, w10, [x16, #8]
    ldp     w11, w12, [x16, #16]
    ldp     w13, w14, [x16, #24]
    rev     w7, w7
    rev     w8, w8
    rev     w9, w9
    rev     w10, w10
    rev     w11, w11
    rev     w12, w12
    rev     w13, w13
    rev     w14, w14
    stp     w7, w8, [x1]
    stp     w9, w10, [x1, #8]
    stp     w11, w12, [x1, #16]
    stp     w13, w14, [x1, #24]

    mov     x0, #CRYPTO_OK
    UNWIND_BEGIN_EPILOGUE
    add     sp, sp, #416
    UNWIND_FREE 416
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_sha256

/* Constants: FIPS 180-4 sections 4.2.2 and 5.3.3. */
    .p2align 4
20:
    .long 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
    .long 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
    .long 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
    .long 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
    .long 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
    .long 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
    .long 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
    .long 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
21:
    .long 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
