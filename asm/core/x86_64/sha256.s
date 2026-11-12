/*
 * crypto_sha256 for x86-64 (System V AMD64 psABI), FIPS 180-4 section 6.2.
 * Requirements: docs/reference/sha-256.md
 *
 * v1: follows the specification steps directly, one block at a time.
 * Baseline x86-64 general-purpose instructions only. AT&T syntax.
 * Saves rbx, rbp and r12-r15, then uses a 456-byte frame (512 bytes in all).
 *
 * Registers:
 *   rdi        message, then the address of K
 *   rbp        address of the current block
 *   rbx        round or word index t
 *   r8d-r15d   working variables a, b, c, d, e, f, g, h
 *   eax, ecx, edx  temporaries
 *
 * Frame:
 *   rsp + 0    W[0..63], 256 bytes
 *   rsp + 256  H[0..7], 32 bytes
 *   rsp + 288  padding blocks, 128 bytes
 *   rsp + 416  digest pointer
 *   rsp + 424  blocks left in the current phase
 *   rsp + 432  phase: 0 for message blocks, 1 for padding blocks
 *   rsp + 440  number of padding blocks (1 or 2)
 *
 * Labels: 1 copy, 2 copied, 3 one padding block, 4 blocks, 5 load, 6 expand,
 * 7 round, 8 phase end, 9 done, 20 K, 21 initial H.
 */
.set ISA_X86_64, 1
.include "crypto.inc"
.include "platform.inc"

FUNCTION crypto_sha256
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
    sub     $456, %rsp
    UNWIND_ALLOC 456
    UNWIND_END_PROLOGUE

    mov     %rsi, 416(%rsp)                     /* digest */
    mov     CRYPTO_BYTES_OFFSET(%rdi), %rax
    mov     CRYPTO_BYTES_COUNT(%rdi), %rcx      /* count */
    lea     (%rdi,%rax), %rbp                   /* message bytes */

    /* Zero the 128-byte padding area. */
    xor     %eax, %eax
    mov     %rax, 288(%rsp)
    mov     %rax, 296(%rsp)
    mov     %rax, 304(%rsp)
    mov     %rax, 312(%rsp)
    mov     %rax, 320(%rsp)
    mov     %rax, 328(%rsp)
    mov     %rax, 336(%rsp)
    mov     %rax, 344(%rsp)
    mov     %rax, 352(%rsp)
    mov     %rax, 360(%rsp)
    mov     %rax, 368(%rsp)
    mov     %rax, 376(%rsp)
    mov     %rax, 384(%rsp)
    mov     %rax, 392(%rsp)
    mov     %rax, 400(%rsp)
    mov     %rax, 408(%rsp)

    /* Copy the bytes after the last full block into the padding area. */
    mov     %rcx, %rdx
    shr     $6, %rdx                            /* full blocks */
    mov     %rdx, 424(%rsp)
    mov     %rcx, %r8
    and     $63, %r8                            /* rem = count mod 64 */
    mov     %rdx, %r9
    shl     $6, %r9
    add     %rbp, %r9                           /* first byte after the full blocks */
    xor     %ebx, %ebx
1:
    cmp     %r8, %rbx
    jae     2f
    movzbl  (%r9,%rbx), %eax
    mov     %al, 288(%rsp,%rbx)
    inc     %rbx
    jmp     1b
2:
    movb    $0x80, 288(%rsp,%r8)

    /* One padding block when rem < 56, else two. */
    mov     $1, %eax
    cmp     $56, %r8
    jb      3f
    mov     $2, %eax
3:
    mov     %rax, 440(%rsp)
    /* Message length in bits, big-endian, in the last 8 bytes of the padding. */
    shl     $6, %rax
    shl     $3, %rcx
    bswap   %rcx
    mov     %rcx, 280(%rsp,%rax)

    /* H = initial hash value. */
    lea     21f(%rip), %rax
    mov     (%rax), %rcx
    mov     %rcx, 256(%rsp)
    mov     8(%rax), %rcx
    mov     %rcx, 264(%rsp)
    mov     16(%rax), %rcx
    mov     %rcx, 272(%rsp)
    mov     24(%rax), %rcx
    mov     %rcx, 280(%rsp)

    lea     20f(%rip), %rdi
    movq    $0, 432(%rsp)

4:
    cmpq    $0, 424(%rsp)
    je      8f

    /* W[0..15]: the block as big-endian words. */
    xor     %ebx, %ebx
5:
    mov     (%rbp,%rbx,4), %ecx
    bswap   %ecx
    mov     %ecx, (%rsp,%rbx,4)
    inc     %rbx
    cmp     $16, %rbx
    jb      5b

    /* W[16..63] = s1(W[t-2]) + W[t-7] + s0(W[t-15]) + W[t-16]. */
6:
    mov     -60(%rsp,%rbx,4), %ecx              /* W[t-15] */
    mov     %ecx, %eax
    ror     $7, %eax
    mov     %ecx, %edx
    ror     $18, %edx
    xor     %edx, %eax
    shr     $3, %ecx
    xor     %ecx, %eax                          /* s0 */
    mov     -8(%rsp,%rbx,4), %ecx               /* W[t-2] */
    mov     %ecx, %edx
    ror     $17, %edx
    mov     %ecx, %r8d
    ror     $19, %r8d
    xor     %r8d, %edx
    shr     $10, %ecx
    xor     %ecx, %edx                          /* s1 */
    add     -64(%rsp,%rbx,4), %eax              /* + W[t-16] */
    add     -28(%rsp,%rbx,4), %eax              /* + W[t-7] */
    add     %edx, %eax
    mov     %eax, (%rsp,%rbx,4)
    inc     %rbx
    cmp     $64, %rbx
    jb      6b

    /* a..h = H. */
    mov     256(%rsp), %r8d
    mov     260(%rsp), %r9d
    mov     264(%rsp), %r10d
    mov     268(%rsp), %r11d
    mov     272(%rsp), %r12d
    mov     276(%rsp), %r13d
    mov     280(%rsp), %r14d
    mov     284(%rsp), %r15d

    xor     %ebx, %ebx
7:
    mov     %r12d, %ecx
    ror     $6, %ecx
    mov     %r12d, %edx
    ror     $11, %edx
    xor     %edx, %ecx
    ror     $14, %edx
    xor     %edx, %ecx                          /* S1(e) */
    add     %ecx, %r15d
    mov     %r13d, %ecx
    xor     %r14d, %ecx
    and     %r12d, %ecx
    xor     %r14d, %ecx                         /* Ch(e, f, g) */
    add     %ecx, %r15d
    add     (%rdi,%rbx,4), %r15d                /* + K[t] */
    add     (%rsp,%rbx,4), %r15d                /* + W[t] = T1 */
    add     %r15d, %r11d                        /* d + T1 */
    mov     %r8d, %ecx
    ror     $2, %ecx
    mov     %r8d, %edx
    ror     $13, %edx
    xor     %edx, %ecx
    ror     $9, %edx
    xor     %edx, %ecx                          /* S0(a) */
    add     %ecx, %r15d
    mov     %r8d, %ecx
    or      %r9d, %ecx
    and     %r10d, %ecx
    mov     %r8d, %edx
    and     %r9d, %edx
    or      %edx, %ecx                          /* Maj(a, b, c) */
    add     %ecx, %r15d                         /* T1 + T2 */
    mov     %r15d, %ecx
    mov     %r14d, %r15d                        /* h = g */
    mov     %r13d, %r14d                        /* g = f */
    mov     %r12d, %r13d                        /* f = e */
    mov     %r11d, %r12d                        /* e = d + T1 */
    mov     %r10d, %r11d                        /* d = c */
    mov     %r9d, %r10d                         /* c = b */
    mov     %r8d, %r9d                          /* b = a */
    mov     %ecx, %r8d                          /* a = T1 + T2 */
    inc     %rbx
    cmp     $64, %rbx
    jb      7b

    /* H = H + a..h. */
    add     %r8d, 256(%rsp)
    add     %r9d, 260(%rsp)
    add     %r10d, 264(%rsp)
    add     %r11d, 268(%rsp)
    add     %r12d, 272(%rsp)
    add     %r13d, 276(%rsp)
    add     %r14d, 280(%rsp)
    add     %r15d, 284(%rsp)

    add     $64, %rbp
    decq    424(%rsp)
    jmp     4b

8:
    /* After the message blocks, hash the padding blocks once. */
    cmpq    $0, 432(%rsp)
    jne     9f
    movq    $1, 432(%rsp)
    lea     288(%rsp), %rbp
    mov     440(%rsp), %rax
    mov     %rax, 424(%rsp)
    jmp     4b

9:
    /* digest = H as big-endian words. */
    mov     416(%rsp), %rsi
    mov     256(%rsp), %eax
    bswap   %eax
    mov     %eax, 0(%rsi)
    mov     260(%rsp), %eax
    bswap   %eax
    mov     %eax, 4(%rsi)
    mov     264(%rsp), %eax
    bswap   %eax
    mov     %eax, 8(%rsi)
    mov     268(%rsp), %eax
    bswap   %eax
    mov     %eax, 12(%rsi)
    mov     272(%rsp), %eax
    bswap   %eax
    mov     %eax, 16(%rsi)
    mov     276(%rsp), %eax
    bswap   %eax
    mov     %eax, 20(%rsi)
    mov     280(%rsp), %eax
    bswap   %eax
    mov     %eax, 24(%rsi)
    mov     284(%rsp), %eax
    bswap   %eax
    mov     %eax, 28(%rsi)

    mov     $CRYPTO_OK, %eax
    UNWIND_BEGIN_EPILOGUE
    add     $456, %rsp
    UNWIND_FREE 456
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
