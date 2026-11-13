/*
 * X25519 (RFC 7748) for x86-64 (System V AMD64 psABI). AT&T syntax.
 * Baseline x86-64 instructions only.
 * Requirements: docs/reference/x25519.md. Layouts: include/x25519.inc.
 *
 * The functions and their steps follow the ARM64 file one for one. Field
 * elements are 4 limbs of 64 bits, any number below 2^256 that stands for
 * its value mod p = 2^255 - 19; 2^256 = 38 mod p folds the high bits back.
 * The ladder runs all 255 steps and swaps with a mask, and the inverse uses
 * the public exponent p - 2, so no branch or address depends on the scalar
 * or the point.
 *
 * Every macro has a named parameter. In a macro without one, the Mach-O
 * assembler reads $0 to $9 as positional arguments.
 */
.set ISA_X86_64, 1
.include "crypto.inc"
.include "x25519.inc"
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

/* fn(rsp + d, rsp + a, rsp + b). */
.macro OP fn, d, a, b
    lea     \d(%rsp), %rdi
    lea     \a(%rsp), %rsi
    lea     \b(%rsp), %rdx
    call    \fn
.endm

.macro FMUL d, a, b
    OP      crypto_x25519_mul, \d, \a, \b
.endm

.macro FADD d, a, b
    OP      crypto_x25519_add, \d, \a, \b
.endm

.macro FSUB d, a, b
    OP      crypto_x25519_sub, \d, \a, \b
.endm

/* crypto_x25519_cswap(rsp + a, rsp + b, mask rbx). */
.macro CSWAP a, b
    lea     \a(%rsp), %rdi
    lea     \b(%rsp), %rsi
    mov     %rbx, %rdx
    call    crypto_x25519_cswap
.endm

/* ---------------------------------------------------------------- X25519 */

.set X_K, 0                         /* the clamped scalar */
.set X_X1, 32                       /* u */
.set X_X2, 64
.set X_Z2, 96
.set X_X3, 128
.set X_Z3, 160
.set X_A, 192
.set X_AA, 224
.set X_B, 256
.set X_BB, 288
.set X_E, 320
.set X_C, 352
.set X_D, 384
.set X_DA, 416
.set X_CB, 448
.set X_T, 480
.set X_FRAME, 520

/* r8 to r11: fold bit 255 back, since 2^255 = 19 mod p. Uses rax. */
.macro FOLD255 unused=0
.if \unused
.endif
    mov     %r11, %rax
    shr     $63, %rax
    btr     $63, %r11
    imul    $19, %rax, %rax
    add     %rax, %r8
    adc     $0, %r9
    adc     $0, %r10
    adc     $0, %r11
.endm

/*
 * crypto_x25519(scalar, u, result) -> status
 * rbx swap mask, rbp result, r12 bit t, r13 swap, r14 k_t.
 */
FUNCTION crypto_x25519
    ENTER   X_FRAME
    mov     %rdx, %rbp
    mov     (%rdi), %rax                    /* decodeScalar25519 */
    and     $-8, %rax
    mov     %rax, X_K(%rsp)
    mov     8(%rdi), %rax
    mov     %rax, X_K+8(%rsp)
    mov     16(%rdi), %rax
    mov     %rax, X_K+16(%rsp)
    mov     24(%rdi), %rax
    btr     $63, %rax
    bts     $62, %rax
    mov     %rax, X_K+24(%rsp)
    mov     (%rsi), %rax                    /* decodeUCoordinate: the top bit is masked */
    mov     %rax, X_X1(%rsp)
    mov     %rax, X_X3(%rsp)                /* x3 = u, z3 = 1, x2 = 1, z2 = 0 */
    mov     8(%rsi), %rax
    mov     %rax, X_X1+8(%rsp)
    mov     %rax, X_X3+8(%rsp)
    mov     16(%rsi), %rax
    mov     %rax, X_X1+16(%rsp)
    mov     %rax, X_X3+16(%rsp)
    mov     24(%rsi), %rax
    btr     $63, %rax
    mov     %rax, X_X1+24(%rsp)
    mov     %rax, X_X3+24(%rsp)
    xor     %eax, %eax
    movq    $1, X_Z3(%rsp)
    mov     %rax, X_Z3+8(%rsp)
    mov     %rax, X_Z3+16(%rsp)
    mov     %rax, X_Z3+24(%rsp)
    movq    $1, X_X2(%rsp)
    mov     %rax, X_X2+8(%rsp)
    mov     %rax, X_X2+16(%rsp)
    mov     %rax, X_X2+24(%rsp)
    mov     %rax, X_Z2(%rsp)
    mov     %rax, X_Z2+8(%rsp)
    mov     %rax, X_Z2+16(%rsp)
    mov     %rax, X_Z2+24(%rsp)
    xor     %r13d, %r13d
    mov     $254, %r12d
1:  mov     %r12, %rax                      /* k_t */
    shr     $6, %rax
    mov     X_K(%rsp,%rax,8), %r14
    mov     %r12d, %ecx
    shr     %cl, %r14
    and     $1, %r14d
    xor     %r14, %r13
    mov     %r13, %rbx
    neg     %rbx
    CSWAP   X_X2, X_X3
    CSWAP   X_Z2, X_Z3
    mov     %r14, %r13
    FADD    X_A, X_X2, X_Z2
    FMUL    X_AA, X_A, X_A
    FSUB    X_B, X_X2, X_Z2
    FMUL    X_BB, X_B, X_B
    FSUB    X_E, X_AA, X_BB
    FADD    X_C, X_X3, X_Z3
    FSUB    X_D, X_X3, X_Z3
    FMUL    X_DA, X_D, X_A
    FMUL    X_CB, X_C, X_B
    FADD    X_T, X_DA, X_CB                 /* x3 = (DA + CB)^2 */
    FMUL    X_X3, X_T, X_T
    FSUB    X_T, X_DA, X_CB                 /* z3 = x1 * (DA - CB)^2 */
    FMUL    X_T, X_T, X_T
    FMUL    X_Z3, X_X1, X_T
    FMUL    X_X2, X_AA, X_BB                /* x2 = AA * BB */
    lea     X_T(%rsp), %rdi                 /* z2 = E * (AA + a24 * E) */
    lea     X_E(%rsp), %rsi
    call    crypto_x25519_mul_a24
    FADD    X_T, X_AA, X_T
    FMUL    X_Z2, X_E, X_T
    sub     $1, %r12
    jge     1b
    mov     %r13, %rbx
    neg     %rbx
    CSWAP   X_X2, X_X3
    CSWAP   X_Z2, X_Z3
    lea     X_T(%rsp), %rdi                 /* x2 / z2 */
    lea     X_Z2(%rsp), %rsi
    call    crypto_x25519_invert
    FMUL    X_T, X_X2, X_T
    mov     X_T(%rsp), %r8                  /* reduce below p, then check for zero */
    mov     X_T+8(%rsp), %r9
    mov     X_T+16(%rsp), %r10
    mov     X_T+24(%rsp), %r11
    FOLD255
    FOLD255
    mov     %r8, %rax                       /* v + 19 reaches 2^255 when v >= p */
    mov     %r9, %rcx
    mov     %r10, %rdx
    mov     %r11, %rsi
    add     $19, %rax
    adc     $0, %rcx
    adc     $0, %rdx
    adc     $0, %rsi
    btr     $63, %rsi
    cmovc   %rax, %r8
    cmovc   %rcx, %r9
    cmovc   %rdx, %r10
    cmovc   %rsi, %r11
    mov     %r8, %rax
    or      %r9, %rax
    or      %r10, %rax
    or      %r11, %rax
    mov     $CRYPTO_X25519_ZERO, %eax
    jz      9f
    mov     %r8, (%rbp)
    mov     %r9, 8(%rbp)
    mov     %r10, 16(%rbp)
    mov     %r11, 24(%rbp)
    mov     $CRYPTO_OK, %eax
9:  LEAVE   X_FRAME
END_FUNCTION crypto_x25519

/*
 * crypto_x25519_invert(result, a): a^(p - 2), by squaring and multiplying
 * from bit 254 down. The exponent is public. rbx result, r12 bit.
 * a at rsp, the running value at rsp + 32.
 */
LOCAL_FUNCTION crypto_x25519_invert
    ENTER   72
    mov     %rdi, %rbx
    mov     (%rsi), %rax
    mov     %rax, (%rsp)
    mov     8(%rsi), %rax
    mov     %rax, 8(%rsp)
    mov     16(%rsi), %rax
    mov     %rax, 16(%rsp)
    mov     24(%rsi), %rax
    mov     %rax, 24(%rsp)
    movq    $1, 32(%rsp)
    movq    $0, 40(%rsp)
    movq    $0, 48(%rsp)
    movq    $0, 56(%rsp)
    mov     $254, %r12d
1:  lea     32(%rsp), %rdi
    lea     32(%rsp), %rsi
    lea     32(%rsp), %rdx
    call    crypto_x25519_mul
    mov     %r12, %rax                      /* bit t of p - 2 */
    shr     $6, %rax
    lea     300f(%rip), %rdx
    mov     (%rdx,%rax,8), %rax
    mov     %r12d, %ecx
    shr     %cl, %rax
    test    $1, %al
    jz      2f
    lea     32(%rsp), %rdi
    lea     32(%rsp), %rsi
    mov     %rsp, %rdx
    call    crypto_x25519_mul
2:  sub     $1, %r12
    jge     1b
    mov     32(%rsp), %rax
    mov     %rax, (%rbx)
    mov     40(%rsp), %rax
    mov     %rax, 8(%rbx)
    mov     48(%rsp), %rax
    mov     %rax, 16(%rbx)
    mov     56(%rsp), %rax
    mov     %rax, 24(%rbx)
    LEAVE   72
END_FUNCTION crypto_x25519_invert

/* ---------------------------------------------------------------- Field arithmetic */

/* One column of the product: r8, r9, r10 += a_i * b_j. Uses rax, rdx. */
.macro MULACC i, j
    mov     (8 * \i)(%rsi), %rax
    mulq    (8 * \j)(%rcx)
    add     %rax, %r8
    adc     %rdx, %r9
    adc     $0, %r10
.endm

/* Store the low word of the column at rsp + off and shift the column down. */
.macro COLUMN off
    mov     %r8, \off(%rsp)
    mov     %r9, %r8
    mov     %r10, %r9
    xor     %r10d, %r10d
.endm

/*
 * Store at rdi the low half at rsp plus 38 times the high half at rsp + 32,
 * folded below 2^256. Uses rax, rcx, rdx, r8 to r11.
 */
.macro REDUCE38 unused=0
.if \unused
.endif
    mov     $38, %r11d
    mov     32(%rsp), %rax                  /* 38 * high, 5 limbs: r8, r9, r10, rcx, rdx */
    mul     %r11
    mov     %rax, %r8
    mov     %rdx, %r9
    mov     40(%rsp), %rax
    mul     %r11
    add     %r9, %rax
    adc     $0, %rdx
    mov     %rax, %r9
    mov     %rdx, %r10
    mov     48(%rsp), %rax
    mul     %r11
    add     %r10, %rax
    adc     $0, %rdx
    mov     %rax, %r10
    mov     %rdx, %rcx
    mov     56(%rsp), %rax
    mul     %r11
    add     %rcx, %rax
    adc     $0, %rdx
    mov     %rax, %rcx
    add     (%rsp), %r8                     /* + low */
    adc     8(%rsp), %r9
    adc     16(%rsp), %r10
    adc     24(%rsp), %rcx
    adc     $0, %rdx                        /* the top, below 39 */
    imul    $38, %rdx, %rax
    add     %rax, %r8
    adc     $0, %r9
    adc     $0, %r10
    adc     $0, %rcx
    sbb     %rax, %rax
    and     $38, %eax
    add     %rax, %r8                       /* no carry: the sum wrapped, so it is small */
    mov     %r8, (%rdi)
    mov     %r9, 8(%rdi)
    mov     %r10, 16(%rdi)
    mov     %rcx, 24(%rdi)
.endm

/*
 * crypto_x25519_mul(result, a, b): a * b mod p, below 2^256, for a, b below
 * 2^256. result may be a or b. A leaf: b at rcx, the column r8 to r10.
 * The 8-limb product at rsp.
 */
LOCAL_FUNCTION crypto_x25519_mul
    sub     $72, %rsp
    UNWIND_ALLOC 72
    UNWIND_END_PROLOGUE
    mov     %rdx, %rcx
    xor     %r8d, %r8d
    xor     %r9d, %r9d
    xor     %r10d, %r10d
    MULACC  0, 0
    COLUMN  0
    MULACC  0, 1
    MULACC  1, 0
    COLUMN  8
    MULACC  0, 2
    MULACC  1, 1
    MULACC  2, 0
    COLUMN  16
    MULACC  0, 3
    MULACC  1, 2
    MULACC  2, 1
    MULACC  3, 0
    COLUMN  24
    MULACC  1, 3
    MULACC  2, 2
    MULACC  3, 1
    COLUMN  32
    MULACC  2, 3
    MULACC  3, 2
    COLUMN  40
    MULACC  3, 3
    mov     %r8, 48(%rsp)
    mov     %r9, 56(%rsp)
    REDUCE38
    UNWIND_BEGIN_EPILOGUE
    add     $72, %rsp
    UNWIND_FREE 72
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_x25519_mul

/*
 * crypto_x25519_mul_a24(result, a): a * 121665 mod p (a24 of RFC 7748
 * section 5), below 2^256. A leaf: the product r8, r9, r10, r11, the top rcx.
 */
LOCAL_FUNCTION crypto_x25519_mul_a24
    UNWIND_END_PROLOGUE
    mov     $121665, %ecx
    mov     (%rsi), %rax
    mul     %rcx
    mov     %rax, %r8
    mov     %rdx, %r9
    mov     8(%rsi), %rax
    mul     %rcx
    add     %rax, %r9
    adc     $0, %rdx
    mov     %rdx, %r10
    mov     16(%rsi), %rax
    mul     %rcx
    add     %rax, %r10
    adc     $0, %rdx
    mov     %rdx, %r11
    mov     24(%rsi), %rax
    mul     %rcx
    add     %rax, %r11
    adc     $0, %rdx
    imul    $38, %rdx, %rax
    add     %rax, %r8
    adc     $0, %r9
    adc     $0, %r10
    adc     $0, %r11
    sbb     %rax, %rax
    and     $38, %eax
    add     %rax, %r8
    mov     %r8, (%rdi)
    mov     %r9, 8(%rdi)
    mov     %r10, 16(%rdi)
    mov     %r11, 24(%rdi)
    ret
END_FUNCTION crypto_x25519_mul_a24

/*
 * crypto_x25519_add(result, a, b): a + b mod p, below 2^256. A leaf:
 * the sum r8 to r11.
 */
LOCAL_FUNCTION crypto_x25519_add
    UNWIND_END_PROLOGUE
    mov     (%rsi), %r8
    mov     8(%rsi), %r9
    mov     16(%rsi), %r10
    mov     24(%rsi), %r11
    add     (%rdx), %r8
    adc     8(%rdx), %r9
    adc     16(%rdx), %r10
    adc     24(%rdx), %r11
    sbb     %rax, %rax                      /* 2^256 = 38 */
    and     $38, %eax
    add     %rax, %r8
    adc     $0, %r9
    adc     $0, %r10
    adc     $0, %r11
    sbb     %rax, %rax
    and     $38, %eax
    add     %rax, %r8
    mov     %r8, (%rdi)
    mov     %r9, 8(%rdi)
    mov     %r10, 16(%rdi)
    mov     %r11, 24(%rdi)
    ret
END_FUNCTION crypto_x25519_add

/*
 * crypto_x25519_sub(result, a, b): a - b mod p, below 2^256. A leaf:
 * the difference r8 to r11.
 */
LOCAL_FUNCTION crypto_x25519_sub
    UNWIND_END_PROLOGUE
    mov     (%rsi), %r8
    mov     8(%rsi), %r9
    mov     16(%rsi), %r10
    mov     24(%rsi), %r11
    sub     (%rdx), %r8
    sbb     8(%rdx), %r9
    sbb     16(%rdx), %r10
    sbb     24(%rdx), %r11
    sbb     %rax, %rax                      /* a borrow of 2^256 = 38 */
    and     $38, %eax
    sub     %rax, %r8
    sbb     $0, %r9
    sbb     $0, %r10
    sbb     $0, %r11
    sbb     %rax, %rax
    and     $38, %eax
    sub     %rax, %r8
    mov     %r8, (%rdi)
    mov     %r9, 8(%rdi)
    mov     %r10, 16(%rdi)
    mov     %r11, 24(%rdi)
    ret
END_FUNCTION crypto_x25519_sub

/*
 * crypto_x25519_cswap(a, b, mask): swaps the 32 bytes at a and b when mask
 * is all ones, and keeps them when it is 0, with the same instructions.
 * A leaf.
 */
LOCAL_FUNCTION crypto_x25519_cswap
    UNWIND_END_PROLOGUE
    .irp off, 0, 8, 16, 24
    mov     \off(%rdi), %rax
    mov     \off(%rsi), %rcx
    mov     %rax, %r8
    xor     %rcx, %r8
    and     %rdx, %r8
    xor     %r8, %rax
    xor     %r8, %rcx
    mov     %rax, \off(%rdi)
    mov     %rcx, \off(%rsi)
    .endr
    ret
END_FUNCTION crypto_x25519_cswap

/* ---------------------------------------------------------------- Constants */

    .p2align 3
/* p - 2 = 2^255 - 21: the exponent of 1 / a mod p. */
300:
    .quad   0xFFFFFFFFFFFFFFEB, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF
