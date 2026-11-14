/*
 * SHA-512 (FIPS 180-4 sections 5.1.2, 5.2.2, 5.3.5 and 6.4) for x86-64
 * (System V AMD64 psABI). AT&T syntax. Baseline x86-64 instructions only.
 * Requirements: docs/reference/sha-512.md. Layouts: include/sha512.inc.
 *
 * The functions and their steps follow the ARM64 file one for one.
 *
 * Every macro has a named parameter. In a macro without one, the Mach-O
 * assembler reads $0 to $9 as positional arguments.
 */
.set ISA_X86_64, 1
.include "crypto.inc"
.include "sha512.inc"
.include "platform.inc"

/*
 * Frame: rbx, rbp, r12-r15, then bytes of locals at rsp. bytes is 8 more
 * than a multiple of 16, so rsp is 16-byte aligned at each call.
 */
.macro ENTER bytes
    push    %rbx
    UNWIND_PUSH %rbx
    push    %rbp
    UNWIND_PUSH %rbp
    push    %r12
    UNWIND_PUSH %r12
    push    %r13
    UNWIND_PUSH %r13
    push    %r14
    UNWIND_PUSH %r14
    push    %r15
    UNWIND_PUSH %r15
    sub     $\bytes, %rsp
    UNWIND_ALLOC \bytes
    UNWIND_END_PROLOGUE
.endm

.macro LEAVE bytes
    UNWIND_BEGIN_EPILOGUE
    add     $\bytes, %rsp
    UNWIND_FREE \bytes
    pop     %r15
    UNWIND_POP %r15
    pop     %r14
    UNWIND_POP %r14
    pop     %r13
    UNWIND_POP %r13
    pop     %r12
    UNWIND_POP %r12
    pop     %rbp
    UNWIND_POP %rbp
    pop     %rbx
    UNWIND_POP %rbx
    UNWIND_END_EPILOGUE
    ret
.endm

/* ---------------------------------------------------------------- crypto_sha512 */

/* crypto_sha512(message, digest) -> status. rbx message, rbp digest, the state at rsp. */
FUNCTION crypto_sha512
    ENTER   216
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rsp, %rdi
    CALL_GLOBAL crypto_sha512_init
    mov     %rsp, %rdi
    mov     %rbx, %rsi
    CALL_GLOBAL crypto_sha512_update
    mov     %rsp, %rdi
    mov     %rbp, %rsi
    CALL_GLOBAL crypto_sha512_final
    mov     $CRYPTO_OK, %eax
    LEAVE   216
END_FUNCTION crypto_sha512

/* crypto_sha512_init(state) -> status: H = H(0) of section 5.3.5, count 0. A leaf. */
FUNCTION crypto_sha512_init
    UNWIND_END_PROLOGUE
    lea     21f(%rip), %rsi
    .irp off, 0, 8, 16, 24, 32, 40, 48, 56
    mov     \off(%rsi), %rax
    mov     %rax, (CRYPTO_SHA512_STATE_H + \off)(%rdi)
    .endr
    movq    $0, CRYPTO_SHA512_STATE_COUNT(%rdi)
    mov     $CRYPTO_OK, %eax
    ret
END_FUNCTION crypto_sha512_init

/*
 * crypto_sha512_update(state, message) -> status.
 * rbx state, rbp the next message byte, r12 bytes left, r13 fill.
 */
FUNCTION crypto_sha512_update
    ENTER   8
    mov     %rdi, %rbx
    mov     CRYPTO_BYTES_OFFSET(%rsi), %rax
    mov     CRYPTO_BYTES_COUNT(%rsi), %r12
    lea     (%rsi,%rax), %rbp
    mov     CRYPTO_SHA512_STATE_COUNT(%rbx), %rax
    mov     %rax, %r13
    and     $127, %r13
    add     %r12, %rax
    mov     %rax, CRYPTO_SHA512_STATE_COUNT(%rbx)
    test    %r13, %r13
    jz      3f
    mov     $128, %ecx                      /* fill the buffer up to 128 bytes */
    sub     %r13, %rcx
    cmp     %rcx, %r12
    cmovb   %r12, %rcx
    lea     CRYPTO_SHA512_STATE_BUFFER(%rbx,%r13), %rdi
    add     %rcx, %r13
    sub     %rcx, %r12
1:  test    %rcx, %rcx
    jz      2f
    movzbl  (%rbp), %eax
    mov     %al, (%rdi)
    inc     %rbp
    inc     %rdi
    dec     %rcx
    jmp     1b
2:  cmp     $128, %r13
    jb      9f                              /* the message ended in the buffer */
    mov     %rbx, %rdi
    lea     CRYPTO_SHA512_STATE_BUFFER(%rbx), %rsi
    mov     $1, %edx
    call    crypto_sha512_blocks
3:  mov     %r12, %rdx                      /* full blocks straight from the message */
    shr     $7, %rdx
    jz      4f
    mov     %rbx, %rdi
    mov     %rbp, %rsi
    mov     %rdx, %rax
    shl     $7, %rax
    add     %rax, %rbp
    call    crypto_sha512_blocks
4:  mov     %r12, %rcx                      /* keep the rest */
    and     $127, %rcx
    lea     CRYPTO_SHA512_STATE_BUFFER(%rbx), %rdi
5:  test    %rcx, %rcx
    jz      9f
    movzbl  (%rbp), %eax
    mov     %al, (%rdi)
    inc     %rbp
    inc     %rdi
    dec     %rcx
    jmp     5b
9:  mov     $CRYPTO_OK, %eax
    LEAVE   8
END_FUNCTION crypto_sha512_update

/*
 * crypto_sha512_final(state, digest) -> status: pads as section 5.1.2 says
 * and writes H big endian. rbx state, rbp digest, r12 the buffer.
 */
FUNCTION crypto_sha512_final
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    lea     CRYPTO_SHA512_STATE_BUFFER(%rbx), %r12
    mov     CRYPTO_SHA512_STATE_COUNT(%rbx), %rcx
    and     $127, %rcx
    movb    $0x80, (%r12,%rcx)
    inc     %rcx
1:  cmp     $128, %rcx                      /* zeros after the 0x80 byte */
    jae     2f
    movb    $0, (%r12,%rcx)
    inc     %rcx
    jmp     1b
2:  mov     CRYPTO_SHA512_STATE_COUNT(%rbx), %rcx
    and     $127, %rcx
    cmp     $112, %rcx
    jb      4f
    mov     %rbx, %rdi                      /* no room for the length: one more block */
    mov     %r12, %rsi
    mov     $1, %edx
    call    crypto_sha512_blocks
    xor     %ecx, %ecx
3:  movq    $0, (%r12,%rcx)
    add     $8, %rcx
    cmp     $112, %rcx
    jb      3b
4:  mov     CRYPTO_SHA512_STATE_COUNT(%rbx), %rax
    mov     %rax, %rdx                      /* the length in bits, 128 bits big endian */
    shr     $61, %rdx
    shl     $3, %rax
    bswap   %rdx
    bswap   %rax
    mov     %rdx, 112(%r12)
    mov     %rax, 120(%r12)
    mov     %rbx, %rdi
    mov     %r12, %rsi
    mov     $1, %edx
    call    crypto_sha512_blocks
    .irp off, 0, 8, 16, 24, 32, 40, 48, 56
    mov     \off(%rbx), %rax
    bswap   %rax
    mov     %rax, \off(%rbp)
    .endr
    mov     $CRYPTO_OK, %eax
    LEAVE   8
END_FUNCTION crypto_sha512_final

/* ---------------------------------------------------------------- Compression */

/*
 * One round of section 6.4.2, step 3, for the working variables a to h and
 * word t = rbp + i. h becomes T1 + T2 (the next a) and d becomes d + T1
 * (the next e). rcx holds K and W is at rsp. Uses rax, rbx.
 */
.macro ROUND a, b, c, d, e, f, g, h, i
    add     (8 * \i)(%rcx,%rbp,8), \h
    add     (8 * \i)(%rsp,%rbp,8), \h
    mov     \e, %rax                        /* Sigma1(e) */
    ror     $14, %rax
    mov     \e, %rbx
    ror     $18, %rbx
    xor     %rbx, %rax
    mov     \e, %rbx
    ror     $41, %rbx
    xor     %rbx, %rax
    add     %rax, \h
    mov     \f, %rax                        /* Ch(e, f, g) = ((f ^ g) & e) ^ g */
    xor     \g, %rax
    and     \e, %rax
    xor     \g, %rax
    add     %rax, \h                        /* T1 */
    add     \h, \d
    mov     \a, %rax                        /* Sigma0(a) */
    ror     $28, %rax
    mov     \a, %rbx
    ror     $34, %rbx
    xor     %rbx, %rax
    mov     \a, %rbx
    ror     $39, %rbx
    xor     %rbx, %rax
    add     %rax, \h
    mov     \a, %rax                        /* Maj(a, b, c) = ((a ^ b) & c) ^ (a & b) */
    xor     \b, %rax
    and     \c, %rax
    mov     \a, %rbx
    and     \b, %rbx
    xor     %rbx, %rax
    add     %rax, \h                        /* T1 + T2 */
.endm

/*
 * crypto_sha512_blocks(h, data, count): runs section 6.4.2 on count blocks
 * of 128 bytes at data, updating the 8 words at h. rdi h, rsi data, rcx K,
 * rbp the word index t, r8 to r15 a to h, rax, rbx, rdx temporaries
 * (and rcx, before it holds K).
 * W[0..79] at rsp, the blocks left at rsp + 640.
 */
LOCAL_FUNCTION crypto_sha512_blocks
    ENTER   648
    test    %rdx, %rdx
    jz      9f
    mov     %rdx, 640(%rsp)
1:  xor     %ebp, %ebp                      /* W[0..15]: the block as big-endian words */
2:  mov     (%rsi,%rbp,8), %rax
    bswap   %rax
    mov     %rax, (%rsp,%rbp,8)
    inc     %rbp
    cmp     $16, %rbp
    jb      2b
3:  mov     -16(%rsp,%rbp,8), %rax          /* W[16..79]: sigma1(W[t-2]) */
    mov     %rax, %rdx
    ror     $19, %rdx
    mov     %rax, %rbx
    ror     $61, %rbx
    xor     %rbx, %rdx
    shr     $6, %rax
    xor     %rax, %rdx
    mov     -120(%rsp,%rbp,8), %rax         /* sigma0(W[t-15]) */
    mov     %rax, %rcx
    ror     $1, %rcx
    mov     %rax, %rbx
    ror     $8, %rbx
    xor     %rbx, %rcx
    shr     $7, %rax
    xor     %rax, %rcx
    add     %rcx, %rdx
    add     -56(%rsp,%rbp,8), %rdx          /* W[t-7] */
    add     -128(%rsp,%rbp,8), %rdx         /* W[t-16] */
    mov     %rdx, (%rsp,%rbp,8)
    inc     %rbp
    cmp     $80, %rbp
    jb      3b
    mov     (%rdi), %r8
    mov     8(%rdi), %r9
    mov     16(%rdi), %r10
    mov     24(%rdi), %r11
    mov     32(%rdi), %r12
    mov     40(%rdi), %r13
    mov     48(%rdi), %r14
    mov     56(%rdi), %r15
    lea     20f(%rip), %rcx
    xor     %ebp, %ebp
4:  ROUND   %r8, %r9, %r10, %r11, %r12, %r13, %r14, %r15, 0
    ROUND   %r15, %r8, %r9, %r10, %r11, %r12, %r13, %r14, 1
    ROUND   %r14, %r15, %r8, %r9, %r10, %r11, %r12, %r13, 2
    ROUND   %r13, %r14, %r15, %r8, %r9, %r10, %r11, %r12, 3
    ROUND   %r12, %r13, %r14, %r15, %r8, %r9, %r10, %r11, 4
    ROUND   %r11, %r12, %r13, %r14, %r15, %r8, %r9, %r10, 5
    ROUND   %r10, %r11, %r12, %r13, %r14, %r15, %r8, %r9, 6
    ROUND   %r9, %r10, %r11, %r12, %r13, %r14, %r15, %r8, 7
    add     $8, %rbp
    cmp     $80, %rbp
    jb      4b
    add     %r8, (%rdi)                     /* H += a to h */
    add     %r9, 8(%rdi)
    add     %r10, 16(%rdi)
    add     %r11, 24(%rdi)
    add     %r12, 32(%rdi)
    add     %r13, 40(%rdi)
    add     %r14, 48(%rdi)
    add     %r15, 56(%rdi)
    sub     $-128, %rsi
    decq    640(%rsp)
    jnz     1b
9:  LEAVE   648
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
