/*
 * crypto_sha256 for ARM64 (AAPCS64), FIPS 180-4 section 6.2: the `sha` variant.
 * Requirements: docs/reference/sha-256.md. Needs FEAT_SHA256 (README, Target profile).
 *
 * The padding, the block order and the digest are those of sha256.s; the 64 rounds of a
 * block run 4 at a time: sha256h and sha256h2 do the rounds, sha256su0 and sha256su1
 * extend the schedule W. A leaf: it uses only caller-saved registers (x0-x17, never x18;
 * v0-v7 and v16-v18) and a 128-byte frame, and branches only on the message length.
 *
 * Registers:
 *   x1      digest
 *   x2      address of the current block
 *   x3      blocks left in the current run
 *   x4      address of K
 *   x6      padding blocks still to run (1 or 2, then 0)
 *   x10     K of the next 4 rounds
 *   v0      the working variables a, b, c, d (lanes 0 to 3)
 *   v1      the working variables e, f, g, h
 *   v2, v3  v0 and v1 at the start of the block
 *   v4-v7   W of the next 16 rounds, 4 words each
 *   v16     W + K of the 4 rounds
 *   v17     a, b, c, d before the 4 rounds
 *   v18     K of the 4 rounds
 *
 * Frame:
 *   sp + 0    padding blocks, 128 bytes
 *
 * Labels: 1 copy, 2 copied, 3 one padding block, 4 blocks, 6 run end, 7 done,
 * 20 K, 21 initial H.
 */
.set ISA_ARM64, 1
.include "crypto.inc"
.include "platform.inc"
.arch armv8-a+sha2

/*
 * Rounds 4g to 4g + 3, W[4g..4g+3] in w0. Before round 48, w0 then gets W[4g+16..4g+19]
 * from w1 (W[4g+4..]), w2 and w3.
 */
.macro FOUR_ROUNDS g, w0, w1, w2, w3
    ld1     {v18.4s}, [x10], #16
    add     v16.4s, \w0\().4s, v18.4s           /* W + K */
.if \g < 12
    sha256su0 \w0\().4s, \w1\().4s
    sha256su1 \w0\().4s, \w2\().4s, \w3\().4s
.endif
    mov     v17.16b, v0.16b
    sha256h q0, q1, v16.4s
    sha256h2 q1, q17, v16.4s
.endm

/* The 64 rounds of the block at ptr, and H = H + a..h. */
.macro BLOCK ptr
    ld1     {v4.16b, v5.16b, v6.16b, v7.16b}, [\ptr]
    rev32   v4.16b, v4.16b                      /* the block's words, big-endian */
    rev32   v5.16b, v5.16b
    rev32   v6.16b, v6.16b
    rev32   v7.16b, v7.16b
    mov     v2.16b, v0.16b
    mov     v3.16b, v1.16b
    mov     x10, x4
    .irp i, 0, 4, 8, 12
    FOUR_ROUNDS (\i + 0), v4, v5, v6, v7
    FOUR_ROUNDS (\i + 1), v5, v6, v7, v4
    FOUR_ROUNDS (\i + 2), v6, v7, v4, v5
    FOUR_ROUNDS (\i + 3), v7, v4, v5, v6
    .endr
    add     v0.4s, v0.4s, v2.4s
    add     v1.4s, v1.4s, v3.4s
.endm

FUNCTION crypto_sha256
    sub     sp, sp, #128
    UNWIND_ALLOC 128
    UNWIND_END_PROLOGUE

    ldr     x5, [x0, #CRYPTO_BYTES_OFFSET]
    ldr     x15, [x0, #CRYPTO_BYTES_COUNT]      /* count */
    add     x2, x0, x5                          /* message bytes */

    /* Zero the 128-byte padding area. */
    stp     xzr, xzr, [sp, #0]
    stp     xzr, xzr, [sp, #16]
    stp     xzr, xzr, [sp, #32]
    stp     xzr, xzr, [sp, #48]
    stp     xzr, xzr, [sp, #64]
    stp     xzr, xzr, [sp, #80]
    stp     xzr, xzr, [sp, #96]
    stp     xzr, xzr, [sp, #112]

    /* Copy the bytes after the last full block into the padding area. */
    and     x17, x15, #63                       /* rem = count mod 64 */
    lsr     x3, x15, #6                         /* full blocks */
    add     x5, x2, x3, lsl #6                  /* first byte after them */
    mov     x6, #0
1:
    cmp     x6, x17
    b.hs    2f
    ldrb    w7, [x5, x6]
    strb    w7, [sp, x6]
    add     x6, x6, #1
    b       1b
2:
    mov     w7, #0x80
    strb    w7, [sp, x17]

    /* One padding block when rem < 56, else two. */
    mov     x6, #1
    cmp     x17, #56
    b.lo    3f
    mov     x6, #2
3:
    /* Message length in bits, big-endian, in the last 8 bytes of the padding. */
    lsl     x7, x15, #3
    rev     x7, x7
    lsl     x8, x6, #6
    add     x8, sp, x8
    stur    x7, [x8, #-8]

    /* a..h = the initial hash value. */
    adr     x9, 21f
    ld1     {v0.4s, v1.4s}, [x9]
    adr     x4, 20f

    /* The message blocks, then the padding blocks. */
4:
    cbz     x3, 6f
    BLOCK   x2
    add     x2, x2, #64
    sub     x3, x3, #1
    b       4b
6:
    cbz     x6, 7f
    mov     x2, sp
    mov     x3, x6
    mov     x6, #0
    b       4b

7:
    /* digest = H as big-endian words. */
    rev32   v0.16b, v0.16b
    rev32   v1.16b, v1.16b
    st1     {v0.16b, v1.16b}, [x1]

    mov     x0, #CRYPTO_OK
    UNWIND_BEGIN_EPILOGUE
    add     sp, sp, #128
    UNWIND_FREE 128
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
