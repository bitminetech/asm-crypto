/*
 * HMAC-SHA-256 and HKDF-SHA-256 for x86-64 (System V AMD64 psABI). AT&T syntax.
 * Requirements: docs/reference/hmac.md. Layouts: include/crypto.inc, include/hmac.inc.
 *
 * Every hash goes through crypto_sha256. The inner hash input sits in the
 * caller's scratch buffer, as a ByteList at scratch + 8. The outer hash input,
 * 96 bytes, sits on the stack. Baseline x86-64 instructions only.
 *
 * Every macro has a named parameter. In a macro without one, the Mach-O
 * assembler reads $0 to $9 as positional arguments.
 */
.set ISA_X86_64, 1
.include "crypto.inc"
.include "hmac.inc"
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

/* Write the 64 bytes at koff(k0) XOR the pattern register xp to doff(dst). Uses rax. */
.macro PAD dst, doff, k0, koff, xp
    .irp i, 0, 8, 16, 24, 32, 40, 48, 56
    mov     \koff+\i(\k0), %rax
    xor     \xp, %rax
    mov     %rax, \doff+\i(\dst)
    .endr
.endm

/*
 * crypto_hmac_sha256(key, message, scratch, mac) -> status
 * rbx key, rbp message, r12 scratch, r13 mac. K0 at rsp.
 */
FUNCTION crypto_hmac_sha256
    ENTER   72
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    mov     (%r12), %rcx
    mov     CRYPTO_BYTES_COUNT(%rbp), %rdx
    sub     $CRYPTO_HMAC_SCRATCH, %rcx
    jb      9f
    cmp     %rdx, %rcx
    jb      9f

    mov     %rbx, %rdi
    mov     %rsp, %rsi
    call    crypto_hmac_key

    /* The inner list: K0 ^ ipad, then the message. */
    mov     (%r12), %rax
    sub     $8, %rax
    mov     %rax, 8+CRYPTO_BYTES_SIZE(%r12)
    movq    $CRYPTO_BYTES_FIXED, 8+CRYPTO_BYTES_OFFSET(%r12)
    mov     CRYPTO_BYTES_COUNT(%rbp), %rax
    add     $CRYPTO_HMAC_BLOCK, %rax
    mov     %rax, 8+CRYPTO_BYTES_COUNT(%r12)
    movabs  $0x3636363636363636, %r8
    PAD     %r12, 32, %rsp, 0, %r8
    mov     CRYPTO_BYTES_OFFSET(%rbp), %rsi
    add     %rbp, %rsi
    lea     96(%r12), %rdi
    mov     CRYPTO_BYTES_COUNT(%rbp), %rcx
    rep movsb

    lea     8(%r12), %rdi
    mov     %rsp, %rsi
    mov     %r13, %rdx
    call    crypto_hmac_finish
    mov     $CRYPTO_OK, %eax
9:  LEAVE   72
END_FUNCTION crypto_hmac_sha256

/* crypto_hkdf_extract(salt, ikm, scratch, prk) -> status: HMAC-SHA-256 with key salt. */
FUNCTION crypto_hkdf_extract
    sub     $8, %rsp
    UNWIND_ALLOC 8
    UNWIND_END_PROLOGUE
    CALL_GLOBAL crypto_hmac_sha256
    UNWIND_BEGIN_EPILOGUE
    add     $8, %rsp
    UNWIND_FREE 8
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_hkdf_extract

/*
 * crypto_hkdf_expand(prk, info, length, scratch, okm) -> status
 * rbp info, r12 scratch, r13 okm, r14 length, r15 block number i, rbx info bytes.
 * K0 at rsp, T(i) at rsp + 64, bytes done at rsp + 96.
 *
 * Scratch: the inner list header at 8, its bytes from 32. Block 1 puts
 * K0 ^ ipad at 64 (list offset 56); block i > 1 puts it at 32 and T(i - 1) at
 * 96 (list offset 24). The info bytes at 128 and the byte i after them stay put.
 */
FUNCTION crypto_hkdf_expand
    ENTER   104
    mov     (%rdx), %r14
    mov     $CRYPTO_HKDF_LENGTH, %eax
    cmp     $CRYPTO_HKDF_MAX_LENGTH, %r14
    ja      9f
    mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    mov     %rsi, %rbp
    mov     %rcx, %r12
    mov     %r8, %r13
    mov     CRYPTO_BYTES_COUNT(%rbp), %rbx
    mov     (%r12), %rcx
    sub     $CRYPTO_HKDF_EXPAND_SCRATCH, %rcx
    jb      9f
    cmp     %rbx, %rcx
    jb      9f
    mov     CRYPTO_BYTES_SIZE(%r13), %rcx
    sub     $CRYPTO_BYTES_FIXED, %rcx
    jb      9f
    cmp     %r14, %rcx
    jb      9f

    mov     %rsp, %rsi
    call    crypto_hmac_key
    mov     CRYPTO_BYTES_OFFSET(%rbp), %rsi
    add     %rbp, %rsi
    lea     128(%r12), %rdi
    mov     %rbx, %rcx
    rep movsb
    movq    $CRYPTO_BYTES_FIXED, CRYPTO_BYTES_OFFSET(%r13)
    mov     %r14, CRYPTO_BYTES_COUNT(%r13)
    mov     (%r12), %rax
    sub     $8, %rax
    mov     %rax, 8+CRYPTO_BYTES_SIZE(%r12)
    mov     $1, %r15d
    movq    $0, 96(%rsp)

1:  cmp     %r14, 96(%rsp)
    jae     8f
    lea     128(%r12), %rax
    mov     %r15b, (%rax,%rbx)
    cmp     $1, %r15
    jne     2f
    movq    $56, 8+CRYPTO_BYTES_OFFSET(%r12)
    lea     CRYPTO_HMAC_BLOCK+1(%rbx), %rax
    mov     %rax, 8+CRYPTO_BYTES_COUNT(%r12)
    lea     64(%r12), %rdi
    jmp     3f
2:  movq    $CRYPTO_BYTES_FIXED, 8+CRYPTO_BYTES_OFFSET(%r12)
    lea     CRYPTO_HMAC_BLOCK+32+1(%rbx), %rax
    mov     %rax, 8+CRYPTO_BYTES_COUNT(%r12)
    .irp i, 0, 8, 16, 24
    mov     64+\i(%rsp), %rax
    mov     %rax, 96+\i(%r12)
    .endr
    lea     32(%r12), %rdi
3:  movabs  $0x3636363636363636, %r8
    PAD     %rdi, 0, %rsp, 0, %r8
    lea     8(%r12), %rdi
    mov     %rsp, %rsi
    lea     64(%rsp), %rdx
    call    crypto_hmac_finish

    /* okm gets min(32, length - done) bytes of T(i). */
    mov     %r14, %rcx
    sub     96(%rsp), %rcx
    mov     $32, %eax
    cmp     %rax, %rcx
    cmova   %rax, %rcx
    lea     64(%rsp), %rsi
    lea     CRYPTO_BYTES_FIXED(%r13), %rdi
    add     96(%rsp), %rdi
    rep movsb
    addq    $32, 96(%rsp)
    inc     %r15
    jmp     1b
8:  mov     $CRYPTO_OK, %eax
9:  LEAVE   104
END_FUNCTION crypto_hkdf_expand

/*
 * crypto_hmac_key(key, k0): K0 of RFC 2104 into the 64 bytes at k0. A key of
 * at most 64 bytes is copied, a longer key is hashed; zeros fill the rest.
 */
LOCAL_FUNCTION crypto_hmac_key
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    xor     %eax, %eax
    mov     %rsi, %rdi
    mov     $8, %ecx
    rep stosq
    mov     CRYPTO_BYTES_COUNT(%rbx), %rcx
    cmp     $CRYPTO_HMAC_BLOCK, %rcx
    ja      1f
    mov     CRYPTO_BYTES_OFFSET(%rbx), %rsi
    add     %rbx, %rsi
    mov     %rbp, %rdi
    rep movsb
    jmp     2f
1:  mov     %rbx, %rdi
    mov     %rbp, %rsi
    CALL_GLOBAL crypto_sha256
2:  LEAVE   8
END_FUNCTION crypto_hmac_key

/*
 * crypto_hmac_finish(inner, k0, mac): the inner hash of the list inner, which
 * holds K0 ^ ipad and the message, then the outer hash into mac.
 * rbx k0, rbp mac. The outer list at rsp: 24 bytes of header, 96 bytes.
 */
LOCAL_FUNCTION crypto_hmac_finish
    ENTER   136
    mov     %rsi, %rbx
    mov     %rdx, %rbp
    lea     CRYPTO_BYTES_FIXED+CRYPTO_HMAC_BLOCK(%rsp), %rsi
    CALL_GLOBAL crypto_sha256
    movq    $(CRYPTO_BYTES_FIXED + 96), CRYPTO_BYTES_SIZE(%rsp)
    movq    $CRYPTO_BYTES_FIXED, CRYPTO_BYTES_OFFSET(%rsp)
    movq    $96, CRYPTO_BYTES_COUNT(%rsp)
    movabs  $0x5C5C5C5C5C5C5C5C, %r8
    PAD     %rsp, CRYPTO_BYTES_FIXED, %rbx, 0, %r8
    mov     %rsp, %rdi
    mov     %rbp, %rsi
    CALL_GLOBAL crypto_sha256
    LEAVE   136
END_FUNCTION crypto_hmac_finish
