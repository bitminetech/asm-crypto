/*
 * ChaCha20, Poly1305 and the ChaCha20-Poly1305 AEAD (RFC 8439) for x86-64
 * (System V AMD64 psABI). AT&T syntax. Baseline x86-64 instructions only,
 * SSE2 included. Requirements: docs/reference/chacha20.md,
 * docs/reference/poly1305.md and docs/reference/chacha20-poly1305.md.
 * Layouts: include/chacha20.inc.
 *
 * The functions and their steps follow the ARM64 file one for one, except
 * that the ChaCha20 block keeps its 4 rows in xmm0 to xmm3 and works on 4
 * columns at once, turning the rows for the diagonal rounds with pshufd. It
 * uses only xmm0 to xmm5. Poly1305 works in base 2^64 with five 64 x 64
 * products for each block. Nothing branches on key or data bytes; only the
 * result of the whole tag comparison decides a branch.
 *
 * Every macro has a named parameter. In a macro without one, the Mach-O
 * assembler reads $0 to $9 as positional arguments.
 */
.set ISA_X86_64, 1
.include "crypto.inc"
.include "chacha20.inc"
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

/* ---------------------------------------------------------------- AEAD */

.set A_BLOCK, 0                     /* the first key stream block: the Poly1305 key */
.set A_POLY, 64                     /* the Poly1305 state */
.set A_LENGTHS, 128                 /* le64(aad bytes) || le64(ciphertext bytes) */
.set A_TAG, 144                     /* the computed tag */
.set A_CT, 160                      /* the address of the ciphertext */
.set A_FRAME, 168

/* The Poly1305 key and state from block 0 of the key stream. Uses rbx key, rbp nonce. */
.macro POLY_KEY unused=0
.if \unused
.endif
    mov     %rbx, %rdi
    xor     %esi, %esi
    mov     %rbp, %rdx
    lea     A_BLOCK(%rsp), %rcx
    call    crypto_chacha20_block
    lea     A_POLY(%rsp), %rdi
    lea     A_BLOCK(%rsp), %rsi
    call    crypto_poly1305_init
.endm

/* The tag over aad (r13), then the ciphertext (address at rsp + A_CT, count at n), into rsp + A_TAG. */
.macro POLY_TAG n
    lea     A_POLY(%rsp), %rdi
    mov     CRYPTO_BYTES_OFFSET(%r13), %rsi
    add     %r13, %rsi
    mov     CRYPTO_BYTES_COUNT(%r13), %rdx
    mov     $1, %ecx
    call    crypto_poly1305_blocks
    lea     A_POLY(%rsp), %rdi
    mov     A_CT(%rsp), %rsi
    mov     \n, %rdx
    mov     $1, %ecx
    call    crypto_poly1305_blocks
    mov     CRYPTO_BYTES_COUNT(%r13), %rax
    mov     %rax, A_LENGTHS(%rsp)
    mov     \n, %rax
    mov     %rax, A_LENGTHS+8(%rsp)
    lea     A_POLY(%rsp), %rdi
    lea     A_LENGTHS(%rsp), %rsi
    mov     $16, %edx
    mov     $1, %ecx
    call    crypto_poly1305_blocks
    lea     A_POLY(%rsp), %rdi
    lea     A_TAG(%rsp), %rsi
    call    crypto_poly1305_emit
.endm

/*
 * crypto_chacha20_aead_encrypt(key, nonce, plaintext, aad, sealed) -> status
 * rbx key, rbp nonce, r12 plaintext, r13 aad, r14 sealed, r15 plaintext bytes.
 */
FUNCTION crypto_chacha20_aead_encrypt
    ENTER   A_FRAME
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     %r8, %r14
    mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    mov     CRYPTO_BYTES_COUNT(%r12), %r15
    mov     CRYPTO_BYTES_SIZE(%r14), %rcx
    sub     $(CRYPTO_BYTES_FIXED + CRYPTO_POLY1305_TAG_SIZE), %rcx
    jb      9f
    cmp     %r15, %rcx
    jb      9f
    POLY_KEY
    mov     %rbx, %rdi                      /* C = P ^ the key stream from block 1 */
    mov     %rbp, %rsi
    mov     $1, %edx
    mov     CRYPTO_BYTES_OFFSET(%r12), %rcx
    add     %r12, %rcx
    lea     CRYPTO_BYTES_FIXED(%r14), %r8
    mov     %r15, %r9
    call    crypto_chacha20_xor
    lea     CRYPTO_BYTES_FIXED(%r14), %rax
    mov     %rax, A_CT(%rsp)
    POLY_TAG %r15
    lea     CRYPTO_BYTES_FIXED(%r14,%r15), %rcx
    mov     A_TAG(%rsp), %rax
    mov     %rax, (%rcx)
    mov     A_TAG+8(%rsp), %rax
    mov     %rax, 8(%rcx)
    movq    $CRYPTO_BYTES_FIXED, CRYPTO_BYTES_OFFSET(%r14)
    lea     CRYPTO_POLY1305_TAG_SIZE(%r15), %rax
    mov     %rax, CRYPTO_BYTES_COUNT(%r14)
    mov     $CRYPTO_OK, %eax
9:  LEAVE   A_FRAME
END_FUNCTION crypto_chacha20_aead_encrypt

/*
 * crypto_chacha20_aead_decrypt(key, nonce, sealed, aad, plaintext) -> status
 * rbx key, rbp nonce, r12 sealed, r13 aad, r14 plaintext, r15 ciphertext
 * bytes. The tag is checked before any plaintext is written.
 */
FUNCTION crypto_chacha20_aead_decrypt
    ENTER   A_FRAME
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     %r8, %r14
    mov     $CRYPTO_CHACHA20_POLY1305_FAIL, %eax
    mov     CRYPTO_BYTES_COUNT(%r12), %r15
    sub     $CRYPTO_POLY1305_TAG_SIZE, %r15
    jb      9f
    mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    mov     CRYPTO_BYTES_SIZE(%r14), %rcx
    sub     $CRYPTO_BYTES_FIXED, %rcx
    jb      9f
    cmp     %r15, %rcx
    jb      9f
    POLY_KEY
    mov     CRYPTO_BYTES_OFFSET(%r12), %rax
    add     %r12, %rax
    mov     %rax, A_CT(%rsp)
    POLY_TAG %r15
    mov     A_CT(%rsp), %rcx                /* compare all 16 bytes */
    add     %r15, %rcx
    mov     A_TAG(%rsp), %rax
    xor     (%rcx), %rax
    mov     A_TAG+8(%rsp), %rdx
    xor     8(%rcx), %rdx
    or      %rdx, %rax
    mov     $CRYPTO_CHACHA20_POLY1305_FAIL, %eax
    jnz     9f
    mov     %rbx, %rdi
    mov     %rbp, %rsi
    mov     $1, %edx
    mov     A_CT(%rsp), %rcx
    lea     CRYPTO_BYTES_FIXED(%r14), %r8
    mov     %r15, %r9
    call    crypto_chacha20_xor
    movq    $CRYPTO_BYTES_FIXED, CRYPTO_BYTES_OFFSET(%r14)
    mov     %r15, CRYPTO_BYTES_COUNT(%r14)
    mov     $CRYPTO_OK, %eax
9:  LEAVE   A_FRAME
END_FUNCTION crypto_chacha20_aead_decrypt

/* ---------------------------------------------------------------- ChaCha20 */

/* x = x rotated left by n, 32-bit lanes. Uses xmm4. */
.macro ROTL x, n
    movdqa  \x, %xmm4
    pslld   $\n, \x
    psrld   $(32 - \n), %xmm4
    por     %xmm4, \x
.endm

/* The quarter round of RFC 8439 section 2.1 on the 4 columns of the rows xmm0 to xmm3. */
.macro QR4 unused=0
.if \unused
.endif
    paddd   %xmm1, %xmm0
    pxor    %xmm0, %xmm3
    ROTL    %xmm3, 16
    paddd   %xmm3, %xmm2
    pxor    %xmm2, %xmm1
    ROTL    %xmm1, 12
    paddd   %xmm1, %xmm0
    pxor    %xmm0, %xmm3
    ROTL    %xmm3, 8
    paddd   %xmm3, %xmm2
    pxor    %xmm2, %xmm1
    ROTL    %xmm1, 7
.endm

/* x = row 3: the counter (esi), then the 3 nonce words (at rdx). Uses xmm5. */
.macro ROW3 x
    movd    %esi, \x
    movq    (%rdx), %xmm5
    pslldq  $4, %xmm5
    por     %xmm5, \x
    movd    8(%rdx), %xmm5
    pslldq  $12, %xmm5
    por     %xmm5, \x
.endm

/*
 * crypto_chacha20_block(key, counter, nonce, block): the ChaCha20 block
 * function of RFC 8439 section 2.3, with the 32-bit block counter in a
 * register. A leaf: the rows in xmm0 to xmm3, eax the round count.
 */
LOCAL_FUNCTION crypto_chacha20_block
    UNWIND_END_PROLOGUE
    movdqu  300f(%rip), %xmm0
    movdqu  (%rdi), %xmm1
    movdqu  16(%rdi), %xmm2
    ROW3    %xmm3
    mov     $10, %eax
1:  QR4                                     /* column rounds */
    pshufd  $0x39, %xmm1, %xmm1             /* diagonals into columns */
    pshufd  $0x4E, %xmm2, %xmm2
    pshufd  $0x93, %xmm3, %xmm3
    QR4                                     /* diagonal rounds */
    pshufd  $0x93, %xmm1, %xmm1
    pshufd  $0x4E, %xmm2, %xmm2
    pshufd  $0x39, %xmm3, %xmm3
    dec     %eax
    jnz     1b
    movdqu  300f(%rip), %xmm4               /* add the input state */
    paddd   %xmm4, %xmm0
    movdqu  (%rdi), %xmm4
    paddd   %xmm4, %xmm1
    movdqu  16(%rdi), %xmm4
    paddd   %xmm4, %xmm2
    ROW3    %xmm4
    paddd   %xmm4, %xmm3
    movdqu  %xmm0, (%rcx)
    movdqu  %xmm1, 16(%rcx)
    movdqu  %xmm2, 32(%rcx)
    movdqu  %xmm3, 48(%rcx)
    ret
END_FUNCTION crypto_chacha20_block

/*
 * crypto_chacha20_xor(key, nonce, counter, source, target, count): target =
 * source ^ the key stream from block counter on (RFC 8439 section 2.4), for
 * count bytes. rbx key, rbp nonce, r12d counter, r13 source, r14 target,
 * r15 bytes left. The key stream block at rsp.
 */
LOCAL_FUNCTION crypto_chacha20_xor
    ENTER   72
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %edx, %r12d
    mov     %rcx, %r13
    mov     %r8, %r14
    mov     %r9, %r15
1:  test    %r15, %r15
    jz      9f
    mov     %rbx, %rdi
    mov     %r12d, %esi
    mov     %rbp, %rdx
    mov     %rsp, %rcx
    call    crypto_chacha20_block
    inc     %r12d
    cmp     $64, %r15
    jb      3f
    xor     %ecx, %ecx
2:  mov     (%r13,%rcx), %rax
    xor     (%rsp,%rcx), %rax
    mov     %rax, (%r14,%rcx)
    add     $8, %rcx
    cmp     $64, %rcx
    jb      2b
    add     $64, %r13
    add     $64, %r14
    sub     $64, %r15
    jmp     1b
3:  xor     %ecx, %ecx                      /* the last part block */
4:  movzbl  (%r13,%rcx), %eax
    xor     (%rsp,%rcx), %al
    mov     %al, (%r14,%rcx)
    inc     %rcx
    cmp     %r15, %rcx
    jb      4b
9:  LEAVE   72
END_FUNCTION crypto_chacha20_xor

/* ---------------------------------------------------------------- Poly1305 */

/*
 * crypto_poly1305_mac(key, message, tag) -> status: poly1305_mac of RFC 8439
 * section 2.5.1. The full blocks carry the 2^128 bit; a last part block
 * gets a 0x01 byte after it, then zeros. rbx key, rbp message bytes,
 * r12 tag, r13 count. The state at rsp, the last block at rsp + 64.
 */
FUNCTION crypto_poly1305_mac
    ENTER   88
    mov     %rdi, %rbx
    mov     CRYPTO_BYTES_OFFSET(%rsi), %rbp
    add     %rsi, %rbp
    mov     CRYPTO_BYTES_COUNT(%rsi), %r13
    mov     %rdx, %r12
    mov     %rsp, %rdi
    mov     %rbx, %rsi
    call    crypto_poly1305_init
    mov     %rsp, %rdi
    mov     %rbp, %rsi
    mov     %r13, %rdx
    and     $-16, %rdx
    mov     $1, %ecx
    call    crypto_poly1305_blocks
    mov     %r13, %r14
    and     $15, %r14
    jz      2f
    movq    $0, 64(%rsp)                    /* the last part block, 0x01, zeros */
    movq    $0, 72(%rsp)
    mov     %r13, %rsi
    and     $-16, %rsi
    add     %rbp, %rsi
    xor     %ecx, %ecx
1:  movzbl  (%rsi,%rcx), %eax
    mov     %al, 64(%rsp,%rcx)
    inc     %rcx
    cmp     %r14, %rcx
    jb      1b
    movb    $1, 64(%rsp,%r14)
    mov     %rsp, %rdi
    lea     64(%rsp), %rsi
    mov     $16, %edx
    xor     %ecx, %ecx
    call    crypto_poly1305_blocks
2:  mov     %rsp, %rdi
    mov     %r12, %rsi
    call    crypto_poly1305_emit
    mov     $CRYPTO_OK, %eax
    LEAVE   88
END_FUNCTION crypto_poly1305_mac

/*
 * crypto_poly1305_init(state, key): h = 0, r = the first 16 key bytes
 * clamped (RFC 8439 section 2.5), s1 = r1 + r1 / 4, s = the last 16 bytes.
 * A leaf.
 */
LOCAL_FUNCTION crypto_poly1305_init
    UNWIND_END_PROLOGUE
    mov     (%rsi), %rax
    movabs  $0x0FFFFFFC0FFFFFFF, %rcx
    and     %rcx, %rax
    mov     %rax, CRYPTO_POLY1305_R0(%rdi)
    mov     8(%rsi), %rax
    movabs  $0x0FFFFFFC0FFFFFFC, %rcx
    and     %rcx, %rax
    mov     %rax, CRYPTO_POLY1305_R1(%rdi)
    mov     %rax, %rcx
    shr     $2, %rcx
    add     %rcx, %rax
    mov     %rax, CRYPTO_POLY1305_S1(%rdi)
    mov     16(%rsi), %rax
    mov     %rax, CRYPTO_POLY1305_S(%rdi)
    mov     24(%rsi), %rax
    mov     %rax, CRYPTO_POLY1305_S+8(%rdi)
    movq    $0, CRYPTO_POLY1305_H0(%rdi)
    movq    $0, CRYPTO_POLY1305_H1(%rdi)
    movq    $0, CRYPTO_POLY1305_H2(%rdi)
    ret
END_FUNCTION crypto_poly1305_init

/*
 * crypto_poly1305_blocks(state, data, count, pad): h = (h + block + pad *
 * 2^128) * r mod 2^130 - 5 for each 16-byte block of the count bytes.
 * Zeros pad the last block to 16 bytes (pad16 of RFC 8439 section 2.8).
 * h0 r8, h1 r9, h2 r10, r0 r11, r1 rbx, s1 rbp, rcx bytes left;
 * d0 r12:r13, d1 r14:r15. The padded block at rsp, pad at rsp + 16.
 */
LOCAL_FUNCTION crypto_poly1305_blocks
    ENTER   24
    mov     %rcx, 16(%rsp)
    mov     %rdx, %rcx
    mov     CRYPTO_POLY1305_H0(%rdi), %r8
    mov     CRYPTO_POLY1305_H1(%rdi), %r9
    mov     CRYPTO_POLY1305_H2(%rdi), %r10
    mov     CRYPTO_POLY1305_R0(%rdi), %r11
    mov     CRYPTO_POLY1305_R1(%rdi), %rbx
    mov     CRYPTO_POLY1305_S1(%rdi), %rbp
1:  test    %rcx, %rcx
    jz      8f
    cmp     $16, %rcx
    jae     3f
    movq    $0, (%rsp)                      /* the last part block, padded */
    movq    $0, 8(%rsp)
    xor     %edx, %edx
2:  movzbl  (%rsi,%rdx), %eax
    mov     %al, (%rsp,%rdx)
    inc     %rdx
    cmp     %rcx, %rdx
    jb      2b
    mov     %rsp, %rsi
    mov     $16, %ecx
3:  add     (%rsi), %r8                     /* h += m + pad * 2^128 */
    adc     8(%rsi), %r9
    adc     16(%rsp), %r10
    add     $16, %rsi
    sub     $16, %rcx
    mov     %r8, %rax                       /* d0 = h0 r0 + h1 s1 */
    mul     %r11
    mov     %rax, %r12
    mov     %rdx, %r13
    mov     %r9, %rax
    mul     %rbp
    add     %rax, %r12
    adc     %rdx, %r13
    mov     %r8, %rax                       /* d1 = h0 r1 + h1 r0 + h2 s1 */
    mul     %rbx
    mov     %rax, %r14
    mov     %rdx, %r15
    mov     %r9, %rax
    mul     %r11
    add     %rax, %r14
    adc     %rdx, %r15
    mov     %r10, %rax
    imul    %rbp, %rax
    add     %rax, %r14
    adc     $0, %r15
    imul    %r11, %r10                      /* d2 = h2 r0 */
    add     %r13, %r14                      /* h1 = d1 + d0 / 2^64 */
    adc     $0, %r15
    add     %r15, %r10                      /* h2 = d2 + d1 / 2^64 */
    mov     %r10, %rax                      /* c = 5 * (h2 / 4) */
    and     $-4, %rax
    mov     %r10, %rdx
    shr     $2, %rdx
    add     %rdx, %rax
    and     $3, %r10
    add     %rax, %r12
    adc     $0, %r14
    adc     $0, %r10
    mov     %r12, %r8
    mov     %r14, %r9
    jmp     1b
8:  mov     %r8, CRYPTO_POLY1305_H0(%rdi)
    mov     %r9, CRYPTO_POLY1305_H1(%rdi)
    mov     %r10, CRYPTO_POLY1305_H2(%rdi)
    LEAVE   24
END_FUNCTION crypto_poly1305_blocks

/*
 * crypto_poly1305_emit(state, tag): tag = (h mod 2^130 - 5) + s mod 2^128,
 * 16 bytes little endian. h - p is taken when h + 5 reaches 2^130. A leaf.
 */
LOCAL_FUNCTION crypto_poly1305_emit
    UNWIND_END_PROLOGUE
    mov     CRYPTO_POLY1305_H0(%rdi), %rax
    mov     CRYPTO_POLY1305_H1(%rdi), %rdx
    mov     CRYPTO_POLY1305_H2(%rdi), %rcx
    mov     %rax, %r8                       /* g = h + 5 */
    mov     %rdx, %r9
    add     $5, %r8
    adc     $0, %r9
    adc     $0, %rcx
    test    $-4, %rcx                       /* g reaches 2^130: h - p is g - 2^130 */
    cmovnz  %r8, %rax
    cmovnz  %r9, %rdx
    add     CRYPTO_POLY1305_S(%rdi), %rax
    adc     CRYPTO_POLY1305_S+8(%rdi), %rdx
    mov     %rax, (%rsi)
    mov     %rdx, 8(%rsi)
    ret
END_FUNCTION crypto_poly1305_emit

/* ---------------------------------------------------------------- Constants */

    .p2align 4
/* "expand 32-byte k" as 4 little-endian words. */
300:
    .long   0x61707865, 0x3320646e, 0x79622d32, 0x6b206574
