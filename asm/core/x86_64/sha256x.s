/*
 * crypto_sha256 for x86-64 (System V AMD64 psABI), FIPS 180-4 section 6.2: the `sha` variant.
 * Requirements: docs/reference/sha-256.md. Needs SSSE3 and SHA (sha-256.md, The sha variant).
 *
 * The padding, the block order and the digest are those of sha256.s; the 64 rounds of a
 * block run 4 at a time: sha256rnds2 does 2 rounds, sha256msg1 and sha256msg2 extend the
 * schedule W. A leaf: it uses only caller-saved registers and a 136-byte frame (144 bytes
 * in all), and branches only on the message length.
 *
 * Registers:
 *   rdx        address of the current block
 *   r8         blocks left in the current run
 *   r11        padding blocks still to run (1 or 2, then 0)
 *   rax        K + 128
 *   xmm0       W + K of the 4 rounds (the implicit operand of sha256rnds2)
 *   xmm1       the working variables a, b, e, f (lanes 3 to 0)
 *   xmm2       the working variables c, d, g, h (lanes 3 to 0)
 *   xmm3-xmm6  W of the last 16 rounds, 4 words each
 *   xmm7       a temporary
 *   xmm8       the mask that swaps the bytes of each word
 *   xmm9-xmm10 a, b, e, f and c, d, g, h at the start of the block
 *
 * Frame:
 *   rsp + 0    padding blocks, 128 bytes
 *
 * Labels: 1 copy, 2 copied, 3 one padding block, 4 blocks, 6 run end, 7 done,
 * 19 byte mask, 20 K, 21 initial H.
 */
.set ISA_X86_64, 1
.include "crypto.inc"
.include "platform.inc"

/*
 * Rounds i to i + 3 of the block at ptr, W[i..i+3] in m0. From round 12 on, m1 gets
 * W[i+4..i+7] after its sha256msg1 step: + W[i+1..i+4] parts and sha256msg2.
 */
.macro FOUR_ROUNDS i, m0, m1, m2, m3, ptr
.if \i < 16
    movdqu  (\i * 4)(\ptr), \m0                 /* W[i..i+3]: the block's words, big-endian */
    pshufb  %xmm8, \m0
.endif
    movdqa  ((\i - 32) * 4)(%rax), %xmm0
    paddd   \m0, %xmm0                          /* W + K */
    sha256rnds2 %xmm1, %xmm2                    /* rounds i, i + 1 */
.if (\i >= 12) && (\i < 60)
    movdqa  \m0, %xmm7
    palignr $4, \m3, %xmm7                      /* W[i-3..i] */
    paddd   %xmm7, \m1
    sha256msg2 \m0, \m1                         /* W[i+4..i+7] */
.endif
    punpckhqdq %xmm0, %xmm0
    sha256rnds2 %xmm2, %xmm1                    /* rounds i + 2, i + 3 */
.if (\i >= 4) && (\i < 52)
    sha256msg1 \m0, \m3
.endif
.endm

/* The 64 rounds of the block at ptr, and H = H + a..h. */
.macro BLOCK ptr
    movdqa  %xmm1, %xmm9
    movdqa  %xmm2, %xmm10
    .irp i, 0, 16, 32, 48
    FOUR_ROUNDS (\i + 0), %xmm3, %xmm4, %xmm5, %xmm6, \ptr
    FOUR_ROUNDS (\i + 4), %xmm4, %xmm5, %xmm6, %xmm3, \ptr
    FOUR_ROUNDS (\i + 8), %xmm5, %xmm6, %xmm3, %xmm4, \ptr
    FOUR_ROUNDS (\i + 12), %xmm6, %xmm3, %xmm4, %xmm5, \ptr
    .endr
    paddd   %xmm9, %xmm1
    paddd   %xmm10, %xmm2
.endm

FUNCTION crypto_sha256
    sub     $136, %rsp
    UNWIND_ALLOC 136
    UNWIND_END_PROLOGUE

    mov     CRYPTO_BYTES_OFFSET(%rdi), %rax
    mov     CRYPTO_BYTES_COUNT(%rdi), %rcx      /* count */
    lea     (%rdi,%rax), %rdx                   /* message bytes */

    /* Zero the 128-byte padding area. */
    pxor    %xmm0, %xmm0
    movdqa  %xmm0, 0(%rsp)
    movdqa  %xmm0, 16(%rsp)
    movdqa  %xmm0, 32(%rsp)
    movdqa  %xmm0, 48(%rsp)
    movdqa  %xmm0, 64(%rsp)
    movdqa  %xmm0, 80(%rsp)
    movdqa  %xmm0, 96(%rsp)
    movdqa  %xmm0, 112(%rsp)

    /* Copy the bytes after the last full block into the padding area. */
    mov     %rcx, %r8
    shr     $6, %r8                             /* full blocks */
    mov     %rcx, %r9
    and     $63, %r9                            /* rem = count mod 64 */
    mov     %r8, %r10
    shl     $6, %r10
    add     %rdx, %r10                          /* first byte after the full blocks */
    xor     %eax, %eax
1:
    cmp     %r9, %rax
    jae     2f
    movzbl  (%r10,%rax), %r11d
    mov     %r11b, (%rsp,%rax)
    inc     %rax
    jmp     1b
2:
    movb    $0x80, (%rsp,%r9)

    /* One padding block when rem < 56, else two. */
    mov     $1, %eax
    cmp     $56, %r9
    jb      3f
    mov     $2, %eax
3:
    mov     %rax, %r11
    /* Message length in bits, big-endian, in the last 8 bytes of the padding. */
    shl     $6, %rax
    shl     $3, %rcx
    bswap   %rcx
    mov     %rcx, -8(%rsp,%rax)

    /* a, b, e, f and c, d, g, h from the initial hash value. */
    movdqa  21f(%rip), %xmm1                    /* a, b, c, d in lanes 0 to 3 */
    movdqa  (21f + 16)(%rip), %xmm2             /* e, f, g, h */
    movdqa  %xmm1, %xmm7
    punpcklqdq %xmm2, %xmm1                     /* a, b, e, f in lanes 0 to 3 */
    punpckhqdq %xmm7, %xmm2                     /* g, h, c, d */
    pshufd  $0x1B, %xmm1, %xmm1                 /* f, e, b, a: a, b, e, f in lanes 3 to 0 */
    pshufd  $0xB1, %xmm2, %xmm2                 /* h, g, d, c: c, d, g, h in lanes 3 to 0 */
    movdqa  19f(%rip), %xmm8
    lea     (20f + 128)(%rip), %rax

    /* The message blocks, then the padding blocks. */
4:
    test    %r8, %r8
    jz      6f
    BLOCK   %rdx
    add     $64, %rdx
    dec     %r8
    jmp     4b
6:
    test    %r11, %r11
    jz      7f
    mov     %rsp, %rdx
    mov     %r11, %r8
    xor     %r11d, %r11d
    jmp     4b

7:
    /* digest = H as big-endian words. */
    movdqa  %xmm1, %xmm7
    punpcklqdq %xmm2, %xmm1                     /* f, e, h, g in lanes 0 to 3 */
    punpckhqdq %xmm7, %xmm2                     /* d, c, b, a */
    pshufd  $0xB1, %xmm1, %xmm1                 /* e, f, g, h */
    pshufd  $0x1B, %xmm2, %xmm2                 /* a, b, c, d */
    pshufb  %xmm8, %xmm2
    pshufb  %xmm8, %xmm1
    movdqu  %xmm2, 0(%rsi)
    movdqu  %xmm1, 16(%rsi)

    mov     $CRYPTO_OK, %eax
    UNWIND_BEGIN_EPILOGUE
    add     $136, %rsp
    UNWIND_FREE 136
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_sha256

/* Constants: the byte mask; FIPS 180-4 sections 4.2.2 and 5.3.3. */
    .p2align 4
19:
    .quad 0x0405060700010203, 0x0c0d0e0f08090a0b
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
