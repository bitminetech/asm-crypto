/*
 * AES-128, CTR and GCM for x86-64 (System V AMD64 psABI). AT&T syntax.
 * Requirements: docs/reference/aes.md. Layouts: include/crypto.inc, include/aes.inc.
 *
 * Constant time: no table lookup and no branch depends on key or data bytes.
 * Four blocks (64 bytes) go through the rounds together as 8 bit planes of
 * 8 bytes: plane i holds bit i of every byte, byte g = 16 * block + k at bit g,
 * with k = r + 4c the FIPS 197 state byte of row r and column c.
 * SubBytes computes the inverse in GF(2^8) as x^254, then the affine map.
 * GHASH multiplies one bit at a time with masks (SP 800-38D algorithm 1).
 * Baseline x86-64 instructions only.
 *
 * Every macro has a named parameter. In a macro without one, the Mach-O
 * assembler reads $0 to $9 as positional arguments.
 */
.set ISA_X86_64, 1
.include "crypto.inc"
.include "aes.inc"
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

/* Save r12 to r15 in a leaf, then bytes of locals at rsp. */
.macro LEAF_ENTER bytes
    push    %r12
    UNWIND_PUSH %r12
    push    %r13
    UNWIND_PUSH %r13
    push    %r14
    UNWIND_PUSH %r14
    push    %r15
    UNWIND_PUSH %r15
    .if \bytes
    sub     $\bytes, %rsp
    UNWIND_ALLOC \bytes
    .endif
    UNWIND_END_PROLOGUE
.endm

.macro LEAF_LEAVE bytes
    UNWIND_BEGIN_EPILOGUE
    .if \bytes
    add     $\bytes, %rsp
    UNWIND_FREE \bytes
    .endif
    pop     %r15
    UNWIND_POP %r15
    pop     %r14
    UNWIND_POP %r14
    pop     %r13
    UNWIND_POP %r13
    pop     %r12
    UNWIND_POP %r12
    UNWIND_END_EPILOGUE
    ret
.endm

/* ---------------------------------------------------------------- AES-128-CTR */

/*
 * crypto_aes128_ctr(key, counter, input, output) -> status
 * rbx key, rbp counter, r12 input, r13 output, r14 input bytes.
 * The key schedule at rsp.
 */
FUNCTION crypto_aes128_ctr
    ENTER   CRYPTO_AES128_SCHEDULE_SIZE+8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    mov     CRYPTO_BYTES_COUNT(%r12), %r14
    mov     CRYPTO_BYTES_SIZE(%r13), %rcx
    sub     $CRYPTO_BYTES_FIXED, %rcx
    jb      9f
    cmp     %r14, %rcx
    jb      9f
    mov     %rbx, %rdi
    mov     %rsp, %rsi
    call    crypto_aes128_expand
    movq    $CRYPTO_BYTES_FIXED, CRYPTO_BYTES_OFFSET(%r13)
    mov     %r14, CRYPTO_BYTES_COUNT(%r13)
    mov     %rsp, %rdi
    mov     %rbp, %rsi
    mov     CRYPTO_BYTES_OFFSET(%r12), %rdx
    add     %r12, %rdx
    lea     CRYPTO_BYTES_FIXED(%r13), %rcx
    mov     %r14, %r8
    xor     %r9d, %r9d
    call    crypto_aes128_ctr_xor
    mov     $CRYPTO_OK, %eax
9:  LEAVE   CRYPTO_AES128_SCHEDULE_SIZE+8
END_FUNCTION crypto_aes128_ctr

/* ---------------------------------------------------------------- AES-128-GCM */

/* GCM locals, after the key schedule at rsp. */
.set G_BLOCKS, CRYPTO_AES128_SCHEDULE_SIZE  /* E(0^128) = H, then E(J0) */
.set G_Y, G_BLOCKS + 64                     /* the GHASH value */
.set G_LENGTHS, G_Y + 16                    /* len(A) || len(C), in bits */
.set G_COUNTER, G_LENGTHS + 16              /* inc32(J0), the first counter block of the data */
.set G_FRAME, G_COUNTER + 16 + 8

/*
 * The key schedule from key rbx, then H and E(J0) from iv rbp, the counter
 * block inc32(J0), and Y = 0. J0 = IV || 0^31 || 1.
 */
.macro GCM_START unused=0
.if \unused
.endif
    mov     %rbx, %rdi
    mov     %rsp, %rsi
    call    crypto_aes128_expand
    .irp i, 0, 8, 16, 24, 32, 40, 48, 56
    movq    $0, G_BLOCKS+\i(%rsp)
    .endr
    mov     (%rbp), %rax
    mov     8(%rbp), %edx
    mov     %rax, G_BLOCKS+16(%rsp)
    mov     %edx, G_BLOCKS+24(%rsp)
    movl    $0x01000000, G_BLOCKS+28(%rsp)
    mov     %rax, G_COUNTER(%rsp)
    mov     %edx, G_COUNTER+8(%rsp)
    movl    $0x02000000, G_COUNTER+12(%rsp)
    movq    $0, G_Y(%rsp)
    movq    $0, G_Y+8(%rsp)
    mov     %rsp, %rdi
    lea     G_BLOCKS(%rsp), %rsi
    call    crypto_aes128_encrypt4
.endm

/* GHASH of the n bytes at data into Y, with zeros padding the last block. n is not rdx. */
.macro GHASH data, n
    mov     \data, %rdx
    mov     \n, %rcx
    lea     G_Y(%rsp), %rdi
    lea     G_BLOCKS(%rsp), %rsi
    call    crypto_aes128_ghash
.endm

/* GHASH of the lengths block, then rax, rdx = the tag E(J0) ^ Y. */
.macro GCM_TAG abytes, cbytes
    mov     \abytes, %rax
    shl     $3, %rax
    bswap   %rax
    mov     %rax, G_LENGTHS(%rsp)
    mov     \cbytes, %rax
    shl     $3, %rax
    bswap   %rax
    mov     %rax, G_LENGTHS+8(%rsp)
    lea     G_LENGTHS(%rsp), %rax
    GHASH   %rax, $16
    mov     G_Y(%rsp), %rax
    xor     G_BLOCKS+16(%rsp), %rax
    mov     G_Y+8(%rsp), %rdx
    xor     G_BLOCKS+24(%rsp), %rdx
.endm

/*
 * crypto_aes128_gcm_ae(key, iv, plaintext, aad, sealed) -> status
 * rbx key, rbp iv, r12 plaintext, r13 aad, r14 sealed, r15 plaintext bytes.
 */
FUNCTION crypto_aes128_gcm_ae
    ENTER   G_FRAME
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     %r8, %r14
    mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    mov     CRYPTO_BYTES_COUNT(%r12), %r15
    mov     CRYPTO_BYTES_SIZE(%r14), %rcx
    sub     $(CRYPTO_BYTES_FIXED + CRYPTO_GCM_TAG_SIZE), %rcx
    jb      9f
    cmp     %r15, %rcx
    jb      9f
    GCM_START
    mov     %rsp, %rdi
    lea     G_COUNTER(%rsp), %rsi
    mov     CRYPTO_BYTES_OFFSET(%r12), %rdx
    add     %r12, %rdx
    lea     CRYPTO_BYTES_FIXED(%r14), %rcx
    mov     %r15, %r8
    mov     $1, %r9d
    call    crypto_aes128_ctr_xor
    mov     CRYPTO_BYTES_OFFSET(%r13), %rax
    add     %r13, %rax
    GHASH   %rax, CRYPTO_BYTES_COUNT(%r13)
    lea     CRYPTO_BYTES_FIXED(%r14), %rax
    GHASH   %rax, %r15
    GCM_TAG CRYPTO_BYTES_COUNT(%r13), %r15
    lea     CRYPTO_BYTES_FIXED(%r14,%r15), %rcx
    mov     %rax, (%rcx)
    mov     %rdx, 8(%rcx)
    movq    $CRYPTO_BYTES_FIXED, CRYPTO_BYTES_OFFSET(%r14)
    lea     CRYPTO_GCM_TAG_SIZE(%r15), %rax
    mov     %rax, CRYPTO_BYTES_COUNT(%r14)
    mov     $CRYPTO_OK, %eax
9:  LEAVE   G_FRAME
END_FUNCTION crypto_aes128_gcm_ae

/*
 * crypto_aes128_gcm_ad(key, iv, sealed, aad, plaintext) -> status
 * rbx key, rbp iv, r12 sealed, r13 aad, r14 plaintext, r15 ciphertext bytes.
 * The tag is checked before any plaintext is written.
 */
FUNCTION crypto_aes128_gcm_ad
    ENTER   G_FRAME
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     %r8, %r14
    mov     $CRYPTO_GCM_FAIL, %eax
    mov     CRYPTO_BYTES_COUNT(%r12), %r15
    sub     $CRYPTO_GCM_TAG_SIZE, %r15
    jb      9f
    mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    mov     CRYPTO_BYTES_SIZE(%r14), %rcx
    sub     $CRYPTO_BYTES_FIXED, %rcx
    jb      9f
    cmp     %r15, %rcx
    jb      9f
    GCM_START
    mov     CRYPTO_BYTES_OFFSET(%r13), %rax
    add     %r13, %rax
    GHASH   %rax, CRYPTO_BYTES_COUNT(%r13)
    mov     CRYPTO_BYTES_OFFSET(%r12), %rax
    add     %r12, %rax
    GHASH   %rax, %r15
    GCM_TAG CRYPTO_BYTES_COUNT(%r13), %r15
    mov     CRYPTO_BYTES_OFFSET(%r12), %rcx
    add     %r12, %rcx
    xor     (%rcx,%r15), %rax
    xor     8(%rcx,%r15), %rdx
    or      %rdx, %rax
    mov     $CRYPTO_GCM_FAIL, %eax
    jnz     9f
    mov     %rsp, %rdi
    lea     G_COUNTER(%rsp), %rsi
    mov     %rcx, %rdx
    lea     CRYPTO_BYTES_FIXED(%r14), %rcx
    mov     %r15, %r8
    mov     $1, %r9d
    call    crypto_aes128_ctr_xor
    movq    $CRYPTO_BYTES_FIXED, CRYPTO_BYTES_OFFSET(%r14)
    mov     %r15, CRYPTO_BYTES_COUNT(%r14)
    mov     $CRYPTO_OK, %eax
9:  LEAVE   G_FRAME
END_FUNCTION crypto_aes128_gcm_ad

/* ---------------------------------------------------------------- Helpers */

/*
 * crypto_aes128_expand(key, schedule): KeyExpansion of FIPS 197 section 5.2,
 * then each round key repeated 4 times and turned into planes.
 * rbx key, rbp schedule, r12 word i, r13 Rcon, r14d temp.
 * w[0..43] at rsp (176 bytes), the SubWord block at rsp + 176 (64 bytes).
 */
LOCAL_FUNCTION crypto_aes128_expand
    ENTER   248
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     (%rbx), %rax
    mov     %rax, (%rsp)
    mov     8(%rbx), %rax
    mov     %rax, 8(%rsp)
    mov     $4, %r12d
    lea     312f(%rip), %r13
1:  mov     -4(%rsp,%r12,4), %r14d
    test    $3, %r12
    jnz     2f
    ror     $8, %r14d                       /* RotWord */
    .irp i, 0, 8, 16, 24, 32, 40, 48, 56    /* SubWord: the S-box on the 4 bytes */
    movq    $0, 176+\i(%rsp)
    .endr
    mov     %r14d, 176(%rsp)
    lea     176(%rsp), %rdi
    xor     %esi, %esi
    call    crypto_aes128_bitslice
    lea     176(%rsp), %rdi
    call    crypto_aes128_sbox
    lea     176(%rsp), %rdi
    mov     $1, %esi
    call    crypto_aes128_bitslice
    mov     176(%rsp), %r14d
    movzbl  (%r13), %eax                    /* Rcon */
    inc     %r13
    xor     %eax, %r14d
2:  xor     -16(%rsp,%r12,4), %r14d
    mov     %r14d, (%rsp,%r12,4)
    inc     %r12
    cmp     $44, %r12
    jb      1b
    xor     %r12d, %r12d
3:  mov     %r12, %rax
    shl     $4, %rax
    mov     (%rsp,%rax), %rcx
    mov     8(%rsp,%rax), %rdx
    mov     %r12, %rdi
    shl     $6, %rdi
    add     %rbp, %rdi
    .irp i, 0, 16, 32, 48
    mov     %rcx, \i(%rdi)
    mov     %rdx, \i+8(%rdi)
    .endr
    xor     %esi, %esi
    call    crypto_aes128_bitslice
    inc     %r12
    cmp     $11, %r12
    jb      3b
    LEAVE   248
END_FUNCTION crypto_aes128_expand

/*
 * crypto_aes128_ctr_xor(schedule, counter, source, target, count, mode):
 * target = source XOR the key stream, count bytes. The key stream is
 * E(counter), E(counter + 1), ... Mode 0 adds 1 to the whole block as a
 * 128-bit big-endian number, mode 1 to its last 32 bits only (inc32).
 * rbx schedule, rbp source, r12 target, r13 bytes left, r14:r15 the counter
 * as a 128-bit number. Four counter blocks at rsp, the mode at rsp + 64.
 */
LOCAL_FUNCTION crypto_aes128_ctr_xor
    ENTER   72
    mov     %rdi, %rbx
    mov     %rdx, %rbp
    mov     %rcx, %r12
    mov     %r8, %r13
    mov     %r9, 64(%rsp)
    mov     (%rsi), %r14
    bswap   %r14
    mov     8(%rsi), %r15
    bswap   %r15
1:  test    %r13, %r13
    jz      9f
    xor     %ecx, %ecx
2:  mov     %r14, %rax
    bswap   %rax
    mov     %rax, (%rsp,%rcx)
    mov     %r15, %rax
    bswap   %rax
    mov     %rax, 8(%rsp,%rcx)
    cmpq    $0, 64(%rsp)
    jne     3f
    add     $1, %r15
    adc     $0, %r14
    jmp     4f
3:  mov     %r15, %rdx
    shr     $32, %rdx
    shl     $32, %rdx
    inc     %r15d
    or      %rdx, %r15
4:  add     $16, %ecx
    cmp     $64, %ecx
    jb      2b
    mov     %rbx, %rdi
    mov     %rsp, %rsi
    call    crypto_aes128_encrypt4
    mov     $64, %ecx
    cmp     %rcx, %r13
    cmovb   %r13, %rcx
    sub     %rcx, %r13
    xor     %edx, %edx
5:  cmp     $8, %rcx
    jb      6f
    mov     (%rbp), %rax
    xor     (%rsp,%rdx), %rax
    mov     %rax, (%r12)
    add     $8, %rbp
    add     $8, %r12
    add     $8, %rdx
    sub     $8, %rcx
    jmp     5b
6:  test    %rcx, %rcx
    jz      1b
    movzbl  (%rbp), %eax
    xor     (%rsp,%rdx), %al
    mov     %al, (%r12)
    inc     %rbp
    inc     %r12
    inc     %rdx
    dec     %rcx
    jmp     6b
9:  LEAVE   72
END_FUNCTION crypto_aes128_ctr_xor

/*
 * crypto_aes128_encrypt4(schedule, blocks): the cipher of FIPS 197 section
 * 5.1 on the 4 blocks of 16 bytes at blocks, in place.
 * rbx schedule, rbp blocks, r12 round.
 */
LOCAL_FUNCTION crypto_aes128_encrypt4
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rbp, %rdi
    xor     %esi, %esi
    call    crypto_aes128_bitslice
    xor     %ecx, %ecx
1:  mov     (%rbx,%rcx,8), %rax
    xor     %rax, (%rbp,%rcx,8)
    inc     %ecx
    cmp     $8, %ecx
    jb      1b
    mov     $1, %r12d
2:  mov     %rbp, %rdi
    call    crypto_aes128_sbox
    mov     %rbp, %rdi
    mov     %r12, %rsi
    shl     $6, %rsi
    add     %rbx, %rsi
    xor     %edx, %edx
    cmp     $10, %r12
    setne   %dl
    call    crypto_aes128_mix
    inc     %r12
    cmp     $10, %r12
    jbe     2b
    mov     %rbp, %rdi
    mov     $1, %esi
    call    crypto_aes128_bitslice
    LEAVE   8
END_FUNCTION crypto_aes128_encrypt4

/* SWAPMOVE: swap the bits of b at the mask with the bits of a at mask << n. Uses rax. */
.macro SWAPMOVE a, b, mask, n
    mov     \a, %rax
    shr     $\n, %rax
    xor     \b, %rax
    and     \mask(%rip), %rax
    xor     %rax, \b
    shl     $\n, %rax
    xor     %rax, \a
.endm

/* Swap byte i of word j with byte j of word i, for the words in r8 to r15. */
.macro BYTE_TRANSPOSE unused=0
.if \unused
.endif
    SWAPMOVE %r8, %r12, 311f+24, 32
    SWAPMOVE %r9, %r13, 311f+24, 32
    SWAPMOVE %r10, %r14, 311f+24, 32
    SWAPMOVE %r11, %r15, 311f+24, 32
    SWAPMOVE %r8, %r10, 311f+32, 16
    SWAPMOVE %r9, %r11, 311f+32, 16
    SWAPMOVE %r12, %r14, 311f+32, 16
    SWAPMOVE %r13, %r15, 311f+32, 16
    SWAPMOVE %r8, %r9, 311f+40, 8
    SWAPMOVE %r10, %r11, 311f+40, 8
    SWAPMOVE %r12, %r13, 311f+40, 8
    SWAPMOVE %r14, %r15, 311f+40, 8
.endm

/* In word w, swap bit i of byte j with bit j of byte i. Uses rax. */
.macro BIT_TRANSPOSE w
    mov     \w, %rax
    shr     $7, %rax
    xor     \w, %rax
    and     311f(%rip), %rax
    xor     %rax, \w
    shl     $7, %rax
    xor     %rax, \w
    mov     \w, %rax
    shr     $14, %rax
    xor     \w, %rax
    and     311f+8(%rip), %rax
    xor     %rax, \w
    shl     $14, %rax
    xor     %rax, \w
    mov     \w, %rax
    shr     $28, %rax
    xor     \w, %rax
    and     311f+16(%rip), %rax
    xor     %rax, \w
    shl     $28, %rax
    xor     %rax, \w
.endm

/*
 * crypto_aes128_bitslice(blocks, inverse): turn the 64 bytes at blocks into
 * the 8 planes in place (inverse 0), or the planes back into bytes (inverse 1).
 * Forward is the bit transpose in each word, then the byte transpose across
 * the words; inverse is the same two steps in the other order.
 */
LOCAL_FUNCTION crypto_aes128_bitslice
    LEAF_ENTER 0
    mov     (%rdi), %r8
    mov     8(%rdi), %r9
    mov     16(%rdi), %r10
    mov     24(%rdi), %r11
    mov     32(%rdi), %r12
    mov     40(%rdi), %r13
    mov     48(%rdi), %r14
    mov     56(%rdi), %r15
    test    %rsi, %rsi
    jz      1f
    BYTE_TRANSPOSE
1:  .irp w, %r8, %r9, %r10, %r11, %r12, %r13, %r14, %r15
    BIT_TRANSPOSE \w
    .endr
    test    %rsi, %rsi
    jnz     2f
    BYTE_TRANSPOSE
2:  mov     %r8, (%rdi)
    mov     %r9, 8(%rdi)
    mov     %r10, 16(%rdi)
    mov     %r11, 24(%rdi)
    mov     %r12, 32(%rdi)
    mov     %r13, 40(%rdi)
    mov     %r14, 48(%rdi)
    mov     %r15, 56(%rdi)
    LEAF_LEAVE 0
END_FUNCTION crypto_aes128_bitslice

/* S-box stack: a, x, x^2, x^3, x^12. */
.set SB_A, 0
.set SB_X, 64
.set SB_X2, 128
.set SB_X3, 192
.set SB_X12, 256
.set SB_FRAME, 320

/* Store r (r8 to r15) at rsp + off. */
.macro STORE_R off
    mov     %r8, \off(%rsp)
    mov     %r9, \off+8(%rsp)
    mov     %r10, \off+16(%rsp)
    mov     %r11, \off+24(%rsp)
    mov     %r12, \off+32(%rsp)
    mov     %r13, \off+40(%rsp)
    mov     %r14, \off+48(%rsp)
    mov     %r15, \off+56(%rsp)
.endm

/* r = a^2 in GF(2^8), a at rsp + SB_A: a linear map of the planes. */
.macro SQUARE unused=0
.if \unused
.endif
    mov     SB_A(%rsp), %r8
    xor     SB_A+32(%rsp), %r8
    xor     SB_A+48(%rsp), %r8              /* r0 = a0 ^ a4 ^ a6 */
    mov     SB_A+32(%rsp), %r9
    xor     SB_A+48(%rsp), %r9
    xor     SB_A+56(%rsp), %r9              /* r1 = a4 ^ a6 ^ a7 */
    mov     SB_A+8(%rsp), %r10
    xor     SB_A+40(%rsp), %r10             /* r2 = a1 ^ a5 */
    mov     SB_A+32(%rsp), %r11
    xor     SB_A+40(%rsp), %r11
    xor     SB_A+48(%rsp), %r11
    xor     SB_A+56(%rsp), %r11             /* r3 = a4 ^ a5 ^ a6 ^ a7 */
    mov     SB_A+16(%rsp), %r12
    xor     SB_A+32(%rsp), %r12
    xor     SB_A+56(%rsp), %r12             /* r4 = a2 ^ a4 ^ a7 */
    mov     SB_A+40(%rsp), %r13
    xor     SB_A+48(%rsp), %r13             /* r5 = a5 ^ a6 */
    mov     SB_A+24(%rsp), %r14
    xor     SB_A+40(%rsp), %r14             /* r6 = a3 ^ a5 */
    mov     SB_A+48(%rsp), %r15
    xor     SB_A+56(%rsp), %r15             /* r7 = a6 ^ a7 */
.endm

/*
 * r = a * b in GF(2^8), a at rsp + SB_A and b at rsp + off. Horner on the
 * planes of b from 7 down to 0: r = r * x, then r ^= a & b_i. Times x maps
 * the planes r0..r7 to r7, r0 ^ r7, r1, r2 ^ r7, r3 ^ r7, r4, r5, r6.
 * Uses rax, rcx, rdx.
 */
.macro MULTIPLY off
    xor     %r8d, %r8d
    xor     %r9d, %r9d
    xor     %r10d, %r10d
    xor     %r11d, %r11d
    xor     %r12d, %r12d
    xor     %r13d, %r13d
    xor     %r14d, %r14d
    xor     %r15d, %r15d
    mov     $7, %ecx
1:  mov     %r15, %rdx
    mov     %r14, %r15
    mov     %r13, %r14
    mov     %r12, %r13
    mov     %r11, %r12
    xor     %rdx, %r12
    mov     %r10, %r11
    xor     %rdx, %r11
    mov     %r9, %r10
    mov     %r8, %r9
    xor     %rdx, %r9
    mov     %rdx, %r8
    mov     \off(%rsp,%rcx,8), %rax
    .irp p, 8, 9, 10, 11, 12, 13, 14, 15
    mov     %rax, %rdx
    and     SB_A+8*(\p-8)(%rsp), %rdx
    xor     %rdx, %r\p
    .endr
    dec     %rcx
    jns     1b
.endm

/* Plane i of the result = r_i ^ r_(i+4) ^ r_(i+5) ^ r_(i+6) ^ r_(i+7), register numbers, to off(rdi). */
.macro AFFINE off, i, j, k, l, m, flip
    mov     %r\i, %rax
    xor     %r\j, %rax
    xor     %r\k, %rax
    xor     %r\l, %rax
    xor     %r\m, %rax
    .if \flip
    not     %rax
    .endif
    mov     %rax, \off(%rdi)
.endm

/*
 * crypto_aes128_sbox(planes): SubBytes on the 8 planes at planes, in place:
 * x^254 = x^-1 in GF(2^8) by x^2, x^3, x^6, x^12, x^15, x^30, x^60, x^120,
 * x^240, x^252, x^254, then the affine map with c = 0x63.
 */
LOCAL_FUNCTION crypto_aes128_sbox
    LEAF_ENTER SB_FRAME
    .irp i, 0, 8, 16, 24, 32, 40, 48, 56
    mov     \i(%rdi), %rax
    mov     %rax, SB_A+\i(%rsp)
    mov     %rax, SB_X+\i(%rsp)
    .endr
    SQUARE                                  /* x^2 */
    STORE_R SB_X2
    STORE_R SB_A
    MULTIPLY SB_X                           /* x^3 */
    STORE_R SB_X3
    STORE_R SB_A
    SQUARE                                  /* x^6 */
    STORE_R SB_A
    SQUARE                                  /* x^12 */
    STORE_R SB_X12
    STORE_R SB_A
    MULTIPLY SB_X3                          /* x^15 */
    STORE_R SB_A
    SQUARE                                  /* x^30 */
    STORE_R SB_A
    SQUARE                                  /* x^60 */
    STORE_R SB_A
    SQUARE                                  /* x^120 */
    STORE_R SB_A
    SQUARE                                  /* x^240 */
    STORE_R SB_A
    MULTIPLY SB_X12                         /* x^252 */
    STORE_R SB_A
    MULTIPLY SB_X2                          /* x^254 */
    AFFINE  0, 8, 12, 13, 14, 15, 1         /* c = 0x63: bits 0, 1, 5 and 6 */
    AFFINE  8, 9, 13, 14, 15, 8, 1
    AFFINE  16, 10, 14, 15, 8, 9, 0
    AFFINE  24, 11, 15, 8, 9, 10, 0
    AFFINE  32, 12, 8, 9, 10, 11, 0
    AFFINE  40, 13, 9, 10, 11, 12, 1
    AFFINE  48, 14, 10, 11, 12, 13, 1
    AFFINE  56, 15, 11, 12, 13, 14, 0
    LEAF_LEAVE SB_FRAME
END_FUNCTION crypto_aes128_sbox

/* ShiftRows of one plane: x to y. Uses rax. */
.macro SHIFT_ROWS x, y
    mov     313f(%rip), \y
    and     \x, \y                          /* row 0 */
    .irp k, 0, 1, 2
    mov     \x, %rax
    shr     $(4 + 4 * \k), %rax
    and     310f+16*\k(%rip), %rax
    or      %rax, \y
    mov     \x, %rax
    shl     $(12 - 4 * \k), %rax
    and     310f+16*\k+8(%rip), %rax
    or      %rax, \y
    .endr
.endm

/*
 * crypto_aes128_mix(planes, round_key, columns): ShiftRows, then MixColumns
 * when columns is 1, then AddRoundKey with the 8 planes at round_key.
 * ShiftRows moves row r of each block 4r bits down in its 16-bit lane.
 * MixColumns: with u = rot1(a) and t = a ^ u, out = xtime(t) ^ u ^ rot2(t),
 * where rotk takes row r + k of the column to row r.
 * The planes of u ^ rot2(t), then the output planes, at rsp.
 */
LOCAL_FUNCTION crypto_aes128_mix
    sub     $72, %rsp
    UNWIND_ALLOC 72
    UNWIND_END_PROLOGUE
    xor     %ecx, %ecx
1:  mov     (%rdi,%rcx,8), %r8
    SHIFT_ROWS %r8, %r9
    test    %rdx, %rdx
    jz      2f
    mov     %r9, %r10                       /* u = rot1(a) */
    shr     $1, %r10
    and     313f+8(%rip), %r10
    mov     %r9, %rax
    shl     $3, %rax
    and     313f+16(%rip), %rax
    or      %rax, %r10
    xor     %r10, %r9                       /* t = a ^ u */
    mov     %r9, %r11                       /* rot2(t) */
    shr     $2, %r11
    and     313f+24(%rip), %r11
    mov     %r9, %rax
    shl     $2, %rax
    and     313f+32(%rip), %rax
    or      %rax, %r11
    xor     %r11, %r10
    mov     %r10, (%rsp,%rcx,8)
2:  mov     %r9, (%rdi,%rcx,8)
    inc     %ecx
    cmp     $8, %ecx
    jb      1b
    test    %rdx, %rdx
    jz      4f
    mov     56(%rdi), %r9                   /* xtime(t) = t7, t0 ^ t7, t1, t2 ^ t7, t3 ^ t7, t4, t5, t6 */
    xor     %r9, (%rsp)
    mov     (%rdi), %rax
    xor     %rax, 8(%rsp)
    xor     %r9, 8(%rsp)
    mov     8(%rdi), %rax
    xor     %rax, 16(%rsp)
    mov     16(%rdi), %rax
    xor     %rax, 24(%rsp)
    xor     %r9, 24(%rsp)
    mov     24(%rdi), %rax
    xor     %rax, 32(%rsp)
    xor     %r9, 32(%rsp)
    mov     32(%rdi), %rax
    xor     %rax, 40(%rsp)
    mov     40(%rdi), %rax
    xor     %rax, 48(%rsp)
    mov     48(%rdi), %rax
    xor     %rax, 56(%rsp)
    xor     %ecx, %ecx
3:  mov     (%rsp,%rcx,8), %rax
    mov     %rax, (%rdi,%rcx,8)
    inc     %ecx
    cmp     $8, %ecx
    jb      3b
4:  xor     %ecx, %ecx
5:  mov     (%rsi,%rcx,8), %rax
    xor     %rax, (%rdi,%rcx,8)
    inc     %ecx
    cmp     $8, %ecx
    jb      5b
    UNWIND_BEGIN_EPILOGUE
    add     $72, %rsp
    UNWIND_FREE 72
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_aes128_mix

/*
 * crypto_aes128_ghash(y, h, data, count): for each 16-byte block X of the
 * count bytes at data, Y = (Y ^ X) * H in GF(2^128); zeros pad the last
 * block. Blocks are big-endian 128-bit numbers, bit 0 of GCM the top bit.
 * r8:r9 X, r10:r11 H, r12:r13 Z, r14:r15 V, rbp y, ebx bits left.
 * The padded block at rsp.
 */
LOCAL_FUNCTION crypto_aes128_ghash
    ENTER   24
    mov     %rdi, %rbp
    mov     (%rdi), %r8
    bswap   %r8
    mov     8(%rdi), %r9
    bswap   %r9
    mov     (%rsi), %r10
    bswap   %r10
    mov     8(%rsi), %r11
    bswap   %r11
1:  test    %rcx, %rcx
    jz      8f
    cmp     $16, %rcx
    jae     3f
    movq    $0, (%rsp)
    movq    $0, 8(%rsp)
    mov     %rdx, %rsi
    mov     %rsp, %rdi
    rep movsb
    mov     %rsp, %rdx
    mov     $16, %ecx
3:  mov     (%rdx), %rax
    bswap   %rax
    xor     %rax, %r8
    mov     8(%rdx), %rax
    bswap   %rax
    xor     %rax, %r9
    add     $16, %rdx
    sub     $16, %rcx
    xor     %r12d, %r12d
    xor     %r13d, %r13d
    mov     %r10, %r14
    mov     %r11, %r15
    mov     $128, %ebx
4:  mov     %r8, %rax                       /* all ones when the next bit of X is 1 */
    sar     $63, %rax
    shld    $1, %r9, %r8
    shl     $1, %r9
    mov     %r14, %rsi
    and     %rax, %rsi
    xor     %rsi, %r12
    mov     %r15, %rsi
    and     %rax, %rsi
    xor     %rsi, %r13
    mov     %r15, %rax                      /* all ones when the last bit of V is 1 */
    and     $1, %eax
    neg     %rax
    shrd    $1, %r14, %r15
    shr     $1, %r14
    movabs  $0xE100000000000000, %rsi
    and     %rax, %rsi
    xor     %rsi, %r14
    dec     %ebx
    jnz     4b
    mov     %r12, %r8
    mov     %r13, %r9
    jmp     1b
8:  bswap   %r8
    bswap   %r9
    mov     %r8, (%rbp)
    mov     %r9, 8(%rbp)
    LEAVE   24
END_FUNCTION crypto_aes128_ghash

/* ShiftRows masks: rows 1, 2 and 3, the bits moved down then the bits moved up. */
    .p2align 3
310:
    .quad   0x0222022202220222, 0x2000200020002000
    .quad   0x0044004400440044, 0x4400440044004400
    .quad   0x0008000800080008, 0x8880888088808880
/* Transpose masks: bits (7, 14, 28), then bytes (32, 16, 8). */
311:
    .quad   0x00AA00AA00AA00AA, 0x0000CCCC0000CCCC, 0x00000000F0F0F0F0
    .quad   0x00000000FFFFFFFF, 0x0000FFFF0000FFFF, 0x00FF00FF00FF00FF
/* Row 0, then the MixColumns rotation masks. */
313:
    .quad   0x1111111111111111, 0x7777777777777777, 0x8888888888888888
    .quad   0x3333333333333333, 0xCCCCCCCCCCCCCCCC
/* Rcon[1] to Rcon[10], the first byte of each. */
312:
    .byte   0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36
