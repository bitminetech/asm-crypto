/*
 * Keccak-256 for x86-64 (System V AMD64 psABI). AT&T syntax.
 * Requirements: docs/reference/keccak-256.md. Layouts: include/crypto.inc.
 *
 * The state is 25 lanes of 8 bytes on the stack, lane x + 5y at 8 * (x + 5y).
 * The 200 bytes after it hold B, the lanes after rho and pi, and before that
 * the last block with its padding. Baseline x86-64 instructions only.
 *
 * Every macro has a named parameter. In a macro without one, the Mach-O
 * assembler reads $0 to $9 as positional arguments.
 */
.set ISA_X86_64, 1
.include "crypto.inc"
.include "keccak.inc"
.include "platform.inc"

.set STATE, 0
.set B, 200
.set DATA, 400          /* next input bytes */
.set LEFT, 408          /* bytes left */
.set LAST, 416          /* 1 on the last block */
.set DIGEST, 424        /* the digest pointer */
.set FRAME, 440

.macro SAVE6 unused=0
.if \unused
.endif
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
.endm

.macro RESTORE6 unused=0
.if \unused
.endif
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
.endm

/* theta: register c = C[x], the XOR of column x. */
.macro COLUMN c, x
    mov     8*\x(%rsp), \c
    xor     8*\x+40(%rsp), \c
    xor     8*\x+80(%rsp), \c
    xor     8*\x+120(%rsp), \c
    xor     8*\x+160(%rsp), \c
.endm

/* theta: XOR D[0] to D[4] into the row that starts at byte row. */
.macro MIX row
    xor     %r13, \row(%rsp)
    xor     %r14, \row+8(%rsp)
    xor     %r15, \row+16(%rsp)
    xor     %rbx, \row+24(%rsp)
    xor     %rbp, \row+32(%rsp)
.endm

/* rho and pi: B[dst] = A[src] rotated left by rot. */
.macro RHO_PI src, dst, rot
    mov     8*\src(%rsp), %rax
    rol     $\rot, %rax
    mov     %rax, B+8*\dst(%rsp)
.endm

/* chi for row y: A[x + 5y] = B[x + 5y] ^ (~B[x + 1 + 5y] & B[x + 2 + 5y]). */
.macro CHI_LANE out, b0, b1, b2
    mov     \b1, %rax
    not     %rax
    and     \b2, %rax
    xor     \b0, %rax
    mov     %rax, \out(%rsp)
.endm

.macro CHI y
    mov     B+40*\y(%rsp), %r8
    mov     B+40*\y+8(%rsp), %r9
    mov     B+40*\y+16(%rsp), %r10
    mov     B+40*\y+24(%rsp), %r11
    mov     B+40*\y+32(%rsp), %r12
    CHI_LANE 40*\y, %r8, %r9, %r10
    CHI_LANE 40*\y+8, %r9, %r10, %r11
    CHI_LANE 40*\y+16, %r10, %r11, %r12
    CHI_LANE 40*\y+24, %r11, %r12, %r8
    CHI_LANE 40*\y+32, %r12, %r8, %r9
.endm

/*
 * crypto_keccak256(message, digest) -> status
 * rsi: the round constant; ecx: rounds left. r8 to r12 C, r13, r14, r15,
 * rbx, rbp D in theta.
 */
FUNCTION crypto_keccak256
    SAVE6
    sub     $FRAME, %rsp
    UNWIND_ALLOC FRAME
    UNWIND_END_PROLOGUE
    mov     %rsi, DIGEST(%rsp)
    mov     CRYPTO_BYTES_OFFSET(%rdi), %rax
    mov     CRYPTO_BYTES_COUNT(%rdi), %rcx
    add     %rdi, %rax
    mov     %rax, DATA(%rsp)
    mov     %rcx, LEFT(%rsp)
    movq    $0, LAST(%rsp)
    xor     %eax, %eax
    mov     %rsp, %rdi
    mov     $25, %ecx
    rep stosq

    /* Take a full block, or build the last one: the bytes left, 0x01, zeros, 0x80. */
1:  mov     LEFT(%rsp), %rcx
    mov     DATA(%rsp), %rsi
    cmp     $CRYPTO_KECCAK256_RATE, %rcx
    jae     3f
    lea     B(%rsp), %rdi
    xor     %eax, %eax
    mov     $(CRYPTO_KECCAK256_RATE / 8), %ecx
    rep stosq
    lea     B(%rsp), %rdi
    mov     LEFT(%rsp), %rcx
    rep movsb
    lea     B(%rsp), %rsi
    mov     LEFT(%rsp), %rcx
    xorb    $0x01, (%rsi,%rcx)
    xorb    $0x80, CRYPTO_KECCAK256_RATE-1(%rsi)
    movq    $CRYPTO_KECCAK256_RATE, LEFT(%rsp)
    movq    $1, LAST(%rsp)

    /* Absorb: XOR the 17 lanes of the block into the state. */
3:  xor     %ecx, %ecx
4:  mov     (%rsi,%rcx,8), %rax
    xor     %rax, (%rsp,%rcx,8)
    inc     %ecx
    cmp     $(CRYPTO_KECCAK256_RATE / 8), %ecx
    jb      4b
    add     $CRYPTO_KECCAK256_RATE, %rsi
    mov     %rsi, DATA(%rsp)
    subq    $CRYPTO_KECCAK256_RATE, LEFT(%rsp)

    /* Keccak-f[1600]: 24 rounds of theta, rho, pi, chi and iota. */
    lea     300f(%rip), %rsi
    mov     $24, %ecx
5:  COLUMN  %r8, 0
    COLUMN  %r9, 1
    COLUMN  %r10, 2
    COLUMN  %r11, 3
    COLUMN  %r12, 4
    mov     %r9, %r13                       /* D[0] = C[4] ^ rotl(C[1], 1) */
    rol     $1, %r13
    xor     %r12, %r13
    mov     %r10, %r14                      /* D[1] = C[0] ^ rotl(C[2], 1) */
    rol     $1, %r14
    xor     %r8, %r14
    mov     %r11, %r15                      /* D[2] = C[1] ^ rotl(C[3], 1) */
    rol     $1, %r15
    xor     %r9, %r15
    mov     %r12, %rbx                      /* D[3] = C[2] ^ rotl(C[4], 1) */
    rol     $1, %rbx
    xor     %r10, %rbx
    mov     %r8, %rbp                       /* D[4] = C[3] ^ rotl(C[0], 1) */
    rol     $1, %rbp
    xor     %r11, %rbp
    MIX     0
    MIX     40
    MIX     80
    MIX     120
    MIX     160
    RHO_PI  0, 0, 0
    RHO_PI  1, 10, 1
    RHO_PI  2, 20, 62
    RHO_PI  3, 5, 28
    RHO_PI  4, 15, 27
    RHO_PI  5, 16, 36
    RHO_PI  6, 1, 44
    RHO_PI  7, 11, 6
    RHO_PI  8, 21, 55
    RHO_PI  9, 6, 20
    RHO_PI  10, 7, 3
    RHO_PI  11, 17, 10
    RHO_PI  12, 2, 43
    RHO_PI  13, 12, 25
    RHO_PI  14, 22, 39
    RHO_PI  15, 23, 41
    RHO_PI  16, 8, 45
    RHO_PI  17, 18, 15
    RHO_PI  18, 3, 21
    RHO_PI  19, 13, 8
    RHO_PI  20, 14, 18
    RHO_PI  21, 24, 2
    RHO_PI  22, 9, 61
    RHO_PI  23, 19, 56
    RHO_PI  24, 4, 14
    CHI     0
    CHI     1
    CHI     2
    CHI     3
    CHI     4
    mov     (%rsi), %rax                    /* iota */
    xor     %rax, (%rsp)
    add     $8, %rsi
    dec     %ecx
    jnz     5b
    cmpq    $0, LAST(%rsp)
    je      1b

    /* The digest is the first 32 bytes of the state. */
    mov     DIGEST(%rsp), %rdi
    mov     (%rsp), %rax
    mov     %rax, (%rdi)
    mov     8(%rsp), %rax
    mov     %rax, 8(%rdi)
    mov     16(%rsp), %rax
    mov     %rax, 16(%rdi)
    mov     24(%rsp), %rax
    mov     %rax, 24(%rdi)
    mov     $CRYPTO_OK, %eax
    UNWIND_BEGIN_EPILOGUE
    add     $FRAME, %rsp
    UNWIND_FREE FRAME
    RESTORE6
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_keccak256

/* Round constants RC[0] to RC[23] of FIPS 202 algorithm 6. */
    .p2align 3
300:
    .quad   0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000
    .quad   0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009
    .quad   0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A
    .quad   0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003
    .quad   0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A
    .quad   0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
