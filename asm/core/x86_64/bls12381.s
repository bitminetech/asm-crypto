/*
 * BLS12-381 for x86-64 (System V AMD64 psABI): the field tower, the groups
 * G1 and G2, the optimal ate pairing, hash to G2 (RFC 9380) and the BLS
 * signatures of the proof of possession scheme, then the KZG commitments of
 * blobs and cells over it, as cryptography-specs v0.3.0 defines them
 * (EthLib/Cryptography/Bls and Kzg). AT&T syntax. Baseline x86-64
 * instructions only.
 * Requirements: docs/reference/bls12-381.md, docs/reference/hash-to-curve.md,
 * docs/reference/bls-signatures.md, docs/reference/kzg.md,
 * docs/reference/kzg-cells.md. Layouts: include/bls12381.inc,
 * include/kzg.inc.
 *
 * The functions and their steps follow the ARM64 file one for one. The
 * pointers that ARM64 keeps in x19 to x24 are in rbx, rbp, r12, r13, r14
 * and r15.
 *
 * Every macro has a named parameter. In a macro without one, the Mach-O
 * assembler reads $0 to $9 as positional arguments.
 */
.set ISA_X86_64, 1
.include "crypto.inc"
.include "bls12381.inc"
.include "kzg.inc"
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

/* ---------------------------------------------------------------- Macros */

/* rdi = oa(ra), rsi = ob(rb), rdx = oc(rc); then call fn. */
.macro C3 fn, ra, oa, rb, ob, rc, oc
    lea     \oa(\ra), %rdi
    lea     \ob(\rb), %rsi
    lea     \oc(\rc), %rdx
    call    \fn
.endm

.macro C2 fn, ra, oa, rb, ob
    lea     \oa(\ra), %rdi
    lea     \ob(\rb), %rsi
    call    \fn
.endm

/* The same with a global function of this library. */
.macro G3 fn, ra, oa, rb, ob, rc, oc
    lea     \oa(\ra), %rdi
    lea     \ob(\rb), %rsi
    lea     \oc(\rc), %rdx
    CALL_GLOBAL \fn
.endm

.macro G2 fn, ra, oa, rb, ob
    lea     \oa(\ra), %rdi
    lea     \ob(\rb), %rsi
    CALL_GLOBAL \fn
.endm

.macro FMUL ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp_mul, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro FADD ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp_add, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro FSUB ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp_sub, \ra, \oa, \rb, \ob, \rc, \oc
.endm

/*
 * The .rept bodies below take no immediates: a .rept body has no named
 * parameter, so the Mach-O assembler would read $0 to $9 in it.
 */

/* Copy n bytes (a multiple of 8) from os(rs) to od(rd). Uses rax, rcx, rdx. */
.macro COPY rd, od, rs, os, n
    lea     \os(\rs), %rcx
    lea     \od(\rd), %rdx
    .rept   (\n) / 8
    mov     (%rcx), %rax
    mov     %rax, (%rdx)
    lea     8(%rcx), %rcx
    lea     8(%rdx), %rdx
    .endr
.endm

/* Zero n bytes (a multiple of 8) at od(rd). Uses rax, rcx. */
.macro ZERO rd, od, n
    lea     \od(\rd), %rcx
    xor     %eax, %eax
    .rept   (\n) / 8
    mov     %rax, (%rcx)
    lea     8(%rcx), %rcx
    .endr
.endm

/* ZF set when the n bytes (a multiple of 8) at os(rs) are all zero. Uses rax, rcx. */
.macro IS_ZERO rs, os, n
    lea     \os(\rs), %rcx
    xor     %eax, %eax
    .rept   (\n) / 8
    or      (%rcx), %rax
    lea     8(%rcx), %rcx
    .endr
    test    %rax, %rax
.endm

/* ZF set when the n bytes (a multiple of 8) at oa(ra) equal those at ob(rb). Uses rax, rcx, rdx, r8. */
.macro EQUAL ra, oa, rb, ob, n
    lea     \oa(\ra), %rcx
    lea     \ob(\rb), %rdx
    xor     %eax, %eax
    .rept   (\n) / 8
    mov     (%rcx), %r8
    xor     (%rdx), %r8
    or      %r8, %rax
    lea     8(%rcx), %rcx
    lea     8(%rdx), %rdx
    .endr
    test    %rax, %rax
.endm

/* The Fp element 1 (Montgomery form) at od(rd). Uses rax, rcx, rdx. */
.macro SET_ONE rd, od
    lea     900f+BLS_FP_RECORD_ONE(%rip), %rcx
    lea     \od(\rd), %rdx
    .irp i, 0, 8, 16, 24, 32, 40
    mov     \i(%rcx), %rax
    mov     %rax, \i(%rdx)
    .endr
.endm

/* ---------------------------------------------------------------- Fp */

/*
 * crypto_bls_fp_mul(result, a, b): a * b / 2^384 mod p, for a, b < p (CIOS).
 * result may be a or b. rsi a, rbx b, T r8 to r15, b_i and q rcx, rbp the
 * carry limb; the limbs of p are read from the record; result is kept on
 * the stack.
 */
LOCAL_FUNCTION crypto_bls_fp_mul
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
    push    %rdi
    UNWIND_PUSH %rdi
    UNWIND_END_PROLOGUE
    mov     %rdx, %rbx
    xor     %r8d, %r8d
    xor     %r9d, %r9d
    xor     %r10d, %r10d
    xor     %r11d, %r11d
    xor     %r12d, %r12d
    xor     %r13d, %r13d
    xor     %r14d, %r14d
    .irp off, 0, 8, 16, 24, 32, 40
    xor     %r15d, %r15d
    mov     \off(%rbx), %rcx                /* T += a * b_i */
    mov     (%rsi), %rax
    mul     %rcx
    add     %rax, %r8
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     8(%rsi), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %rax, %r9
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     16(%rsi), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %rax, %r10
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     24(%rsi), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %rax, %r11
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     32(%rsi), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %rax, %r12
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     40(%rsi), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %rax, %r13
    adc     $0, %rdx
    add     %rdx, %r14
    adc     $0, %r15
    mov     %r8, %rcx                       /* q = T0 * -p^-1 mod 2^64 */
    imul    900f+BLS_FP_RECORD_INVERSE(%rip), %rcx
    mov     900f(%rip), %rax                /* T = (T + q * p) / 2^64 */
    mul     %rcx
    add     %rax, %r8
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     900f+8(%rip), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %r9, %rax
    adc     $0, %rdx
    mov     %rax, %r8
    mov     %rdx, %rbp
    mov     900f+16(%rip), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %r10, %rax
    adc     $0, %rdx
    mov     %rax, %r9
    mov     %rdx, %rbp
    mov     900f+24(%rip), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %r11, %rax
    adc     $0, %rdx
    mov     %rax, %r10
    mov     %rdx, %rbp
    mov     900f+32(%rip), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %r12, %rax
    adc     $0, %rdx
    mov     %rax, %r11
    mov     %rdx, %rbp
    mov     900f+40(%rip), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %r13, %rax
    adc     $0, %rdx
    mov     %rax, %r12
    mov     %r14, %r13
    add     %rdx, %r13
    adc     $0, %r15
    mov     %r15, %r14
    .endr
    mov     %r8, %rax                       /* T - p when T >= p */
    sub     900f(%rip), %rax
    mov     %r9, %rcx
    sbb     900f+8(%rip), %rcx
    mov     %r10, %rdx
    sbb     900f+16(%rip), %rdx
    mov     %r11, %rsi
    sbb     900f+24(%rip), %rsi
    mov     %r12, %rbx
    sbb     900f+32(%rip), %rbx
    mov     %r13, %rbp
    sbb     900f+40(%rip), %rbp
    sbb     $0, %r14
    cmovae  %rax, %r8
    cmovae  %rcx, %r9
    cmovae  %rdx, %r10
    cmovae  %rsi, %r11
    cmovae  %rbx, %r12
    cmovae  %rbp, %r13
    mov     (%rsp), %rdi                    /* result */
    mov     %r8, (%rdi)
    mov     %r9, 8(%rdi)
    mov     %r10, 16(%rdi)
    mov     %r11, 24(%rdi)
    mov     %r12, 32(%rdi)
    mov     %r13, 40(%rdi)
    UNWIND_BEGIN_EPILOGUE
    pop     %rdi
    UNWIND_POP %rdi
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
END_FUNCTION crypto_bls_fp_mul

/* crypto_bls_fp_add(result, a, b): a + b mod p, for a, b < p. result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp_add
    UNWIND_END_PROLOGUE
    mov     (%rsi), %rax
    mov     8(%rsi), %rcx
    mov     16(%rsi), %r8
    mov     24(%rsi), %r9
    mov     32(%rsi), %r10
    mov     40(%rsi), %r11
    add     (%rdx), %rax
    adc     8(%rdx), %rcx
    adc     16(%rdx), %r8
    adc     24(%rdx), %r9
    adc     32(%rdx), %r10
    adc     40(%rdx), %r11
    sbb     %rsi, %rsi                      /* -1 on a carry out */
    mov     %rax, (%rdi)                    /* the sum, then the sum - p when it is p or more */
    mov     %rcx, 8(%rdi)
    mov     %r8, 16(%rdi)
    mov     %r9, 24(%rdi)
    mov     %r10, 32(%rdi)
    mov     %r11, 40(%rdi)
    sub     900f(%rip), %rax
    sbb     900f+8(%rip), %rcx
    sbb     900f+16(%rip), %r8
    sbb     900f+24(%rip), %r9
    sbb     900f+32(%rip), %r10
    sbb     900f+40(%rip), %r11
    sbb     $0, %rsi                        /* borrow when sum < p and no carry out */
    jc      1f
    mov     %rax, (%rdi)
    mov     %rcx, 8(%rdi)
    mov     %r8, 16(%rdi)
    mov     %r9, 24(%rdi)
    mov     %r10, 32(%rdi)
    mov     %r11, 40(%rdi)
1:  ret
END_FUNCTION crypto_bls_fp_add

/* crypto_bls_fp_sub(result, a, b): a - b mod p, for a, b < p. result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp_sub
    UNWIND_END_PROLOGUE
    mov     (%rsi), %rax
    mov     8(%rsi), %rcx
    mov     16(%rsi), %r8
    mov     24(%rsi), %r9
    mov     32(%rsi), %r10
    mov     40(%rsi), %r11
    sub     (%rdx), %rax
    sbb     8(%rdx), %rcx
    sbb     16(%rdx), %r8
    sbb     24(%rdx), %r9
    sbb     32(%rdx), %r10
    sbb     40(%rdx), %r11
    jnc     1f
    add     900f(%rip), %rax                /* a borrow: add p */
    adc     900f+8(%rip), %rcx
    adc     900f+16(%rip), %r8
    adc     900f+24(%rip), %r9
    adc     900f+32(%rip), %r10
    adc     900f+40(%rip), %r11
1:  mov     %rax, (%rdi)
    mov     %rcx, 8(%rdi)
    mov     %r8, 16(%rdi)
    mov     %r9, 24(%rdi)
    mov     %r10, 32(%rdi)
    mov     %r11, 40(%rdi)
    ret
END_FUNCTION crypto_bls_fp_sub

/* crypto_bls_fp_neg(result, a): -a mod p, for a < p; 0 stays 0. result may be a. */
LOCAL_FUNCTION crypto_bls_fp_neg
    UNWIND_END_PROLOGUE
    mov     (%rsi), %rax
    or      8(%rsi), %rax
    or      16(%rsi), %rax
    or      24(%rsi), %rax
    or      32(%rsi), %rax
    or      40(%rsi), %rax
    jz      1f
    mov     900f(%rip), %rax
    mov     900f+8(%rip), %rcx
    mov     900f+16(%rip), %r8
    mov     900f+24(%rip), %r9
    mov     900f+32(%rip), %r10
    mov     900f+40(%rip), %r11
    sub     (%rsi), %rax
    sbb     8(%rsi), %rcx
    sbb     16(%rsi), %r8
    sbb     24(%rsi), %r9
    sbb     32(%rsi), %r10
    sbb     40(%rsi), %r11
    mov     %rax, (%rdi)
    mov     %rcx, 8(%rdi)
    mov     %r8, 16(%rdi)
    mov     %r9, 24(%rdi)
    mov     %r10, 32(%rdi)
    mov     %r11, 40(%rdi)
    ret
1:  mov     %rax, (%rdi)                    /* rax is 0 */
    mov     %rax, 8(%rdi)
    mov     %rax, 16(%rdi)
    mov     %rax, 24(%rdi)
    mov     %rax, 32(%rdi)
    mov     %rax, 40(%rdi)
    ret
END_FUNCTION crypto_bls_fp_neg

/*
 * crypto_bls_fp_pow(result, base, exponent): base^e (Fp.powNat), with e the
 * 6 little-endian limbs at exponent, a public value. result may be base.
 * rbx result, rbp exponent, r12 bit index.
 */
.set FW_ACC, 0
.set FW_BASE, 48
.set FW_SIZE, 104
LOCAL_FUNCTION crypto_bls_fp_pow
    ENTER   FW_SIZE
    mov     %rdi, %rbx
    mov     %rdx, %rbp
    COPY    %rsp, FW_BASE, %rsi, 0, 48
    SET_ONE %rsp, FW_ACC
    mov     $383, %r12d
1:  mov     %r12, %rcx                      /* skip the zero bits above the top set bit */
    shr     $6, %rcx
    mov     (%rbp,%rcx,8), %rax
    mov     %r12, %rcx
    shr     %cl, %rax
    test    $1, %al
    jnz     2f
    sub     $1, %r12
    jns     1b
    jmp     4f
2:  FMUL    %rsp, FW_ACC, %rsp, FW_ACC, %rsp, FW_ACC
    mov     %r12, %rcx
    shr     $6, %rcx
    mov     (%rbp,%rcx,8), %rax
    mov     %r12, %rcx
    shr     %cl, %rax
    test    $1, %al
    jz      3f
    FMUL    %rsp, FW_ACC, %rsp, FW_ACC, %rsp, FW_BASE
3:  sub     $1, %r12
    jns     2b
4:  COPY    %rbx, 0, %rsp, FW_ACC, 48
    LEAVE   FW_SIZE
END_FUNCTION crypto_bls_fp_pow

/* crypto_bls_fp_inverse(result, a): a^(p - 2) (Fp.inverse); 0 gives 0. result may be a. */
LOCAL_FUNCTION crypto_bls_fp_inverse
    ENTER   8
    lea     917f(%rip), %rdx
    call    crypto_bls_fp_pow
    LEAVE   8
END_FUNCTION crypto_bls_fp_inverse

/*
 * crypto_bls_fp_sqrt(result, a) -> status: c = a^((p + 1) / 4) (Fp.sqrt).
 * CRYPTO_OK and c when c * c = a; CRYPTO_INVALID_ENCODING when a is not a
 * square, and nothing is written. result may be a.
 */
.set FS_C, 0
.set FS_CC, 48
.set FS_SIZE, 104
LOCAL_FUNCTION crypto_bls_fp_sqrt
    ENTER   FS_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    lea     FS_C(%rsp), %rdi
    lea     918f(%rip), %rdx
    call    crypto_bls_fp_pow
    FMUL    %rsp, FS_CC, %rsp, FS_C, %rsp, FS_C
    EQUAL   %rsp, FS_CC, %rbp, 0, 48
    jne     9f
    COPY    %rbx, 0, %rsp, FS_C, 48
    mov     $CRYPTO_OK, %eax
    LEAVE   FS_SIZE
9:  mov     $CRYPTO_INVALID_ENCODING, %eax
    LEAVE   FS_SIZE
END_FUNCTION crypto_bls_fp_sqrt

/*
 * crypto_bls_fp_from_bytes(result, bytes) -> status: the 48 big-endian bytes
 * as an element of Fp, in Montgomery form (Fp.fromBytesBE).
 * CRYPTO_INVALID_ENCODING when the number is p or more; nothing is written.
 */
.set FB_N, 0
.set FB_SIZE, 56
LOCAL_FUNCTION crypto_bls_fp_from_bytes
    ENTER   FB_SIZE
    mov     %rdi, %rbx
    .irp i, 0, 1, 2, 3, 4, 5
    mov     40-8*\i(%rsi), %rax
    bswap   %rax
    mov     %rax, FB_N+8*\i(%rsp)
    .endr
    mov     FB_N(%rsp), %rax                /* below p? */
    sub     900f(%rip), %rax
    mov     FB_N+8(%rsp), %rax
    sbb     900f+8(%rip), %rax
    mov     FB_N+16(%rsp), %rax
    sbb     900f+16(%rip), %rax
    mov     FB_N+24(%rsp), %rax
    sbb     900f+24(%rip), %rax
    mov     FB_N+32(%rsp), %rax
    sbb     900f+32(%rip), %rax
    mov     FB_N+40(%rsp), %rax
    sbb     900f+40(%rip), %rax
    jnc     9f
    mov     %rbx, %rdi                      /* result = n * 2^768 / 2^384 */
    lea     FB_N(%rsp), %rsi
    lea     900f+BLS_FP_RECORD_R2(%rip), %rdx
    call    crypto_bls_fp_mul
    mov     $CRYPTO_OK, %eax
    LEAVE   FB_SIZE
9:  mov     $CRYPTO_INVALID_ENCODING, %eax
    LEAVE   FB_SIZE
END_FUNCTION crypto_bls_fp_from_bytes

/* crypto_bls_fp_canonical(result, a): the value of a (Montgomery form) as 6 little-endian limbs. */
.set FN_ONE, 0
.set FN_SIZE, 56
LOCAL_FUNCTION crypto_bls_fp_canonical
    ENTER   FN_SIZE
    movq    $1, FN_ONE(%rsp)
    movq    $0, FN_ONE+8(%rsp)
    movq    $0, FN_ONE+16(%rsp)
    movq    $0, FN_ONE+24(%rsp)
    movq    $0, FN_ONE+32(%rsp)
    movq    $0, FN_ONE+40(%rsp)
    lea     FN_ONE(%rsp), %rdx              /* a * 1 / 2^384 */
    call    crypto_bls_fp_mul
    LEAVE   FN_SIZE
END_FUNCTION crypto_bls_fp_canonical

/* crypto_bls_fp_to_bytes(bytes, a): the 48 big-endian bytes of a (Fp.toBytesBE). */
.set FT_N, 0
.set FT_SIZE, 56
LOCAL_FUNCTION crypto_bls_fp_to_bytes
    ENTER   FT_SIZE
    mov     %rdi, %rbx
    lea     FT_N(%rsp), %rdi
    call    crypto_bls_fp_canonical
    .irp i, 0, 1, 2, 3, 4, 5
    mov     FT_N+8*\i(%rsp), %rax
    bswap   %rax
    mov     %rax, 40-8*\i(%rbx)
    .endr
    LEAVE   FT_SIZE
END_FUNCTION crypto_bls_fp_to_bytes

/*
 * crypto_bls_fp_sign_bit(bit, a): the u64 1 when the value y of a satisfies
 * y > p - y (Fp.signBit), else 0.
 */
.set FG_Y, 0
.set FG_SIZE, 56
LOCAL_FUNCTION crypto_bls_fp_sign_bit
    ENTER   FG_SIZE
    mov     %rdi, %rbx
    lea     FG_Y(%rsp), %rdi
    call    crypto_bls_fp_canonical
    mov     900f(%rip), %rax                /* d = p - y */
    sub     FG_Y(%rsp), %rax
    mov     900f+8(%rip), %rcx
    sbb     FG_Y+8(%rsp), %rcx
    mov     900f+16(%rip), %rdx
    sbb     FG_Y+16(%rsp), %rdx
    mov     900f+24(%rip), %r8
    sbb     FG_Y+24(%rsp), %r8
    mov     900f+32(%rip), %r9
    sbb     FG_Y+32(%rsp), %r9
    mov     900f+40(%rip), %r10
    sbb     FG_Y+40(%rsp), %r10
    sub     FG_Y(%rsp), %rax                /* d - y borrows when y > d */
    sbb     FG_Y+8(%rsp), %rcx
    sbb     FG_Y+16(%rsp), %rdx
    sbb     FG_Y+24(%rsp), %r8
    sbb     FG_Y+32(%rsp), %r9
    sbb     FG_Y+40(%rsp), %r10
    setc    %al
    movzbl  %al, %eax
    mov     %rax, (%rbx)
    LEAVE   FG_SIZE
END_FUNCTION crypto_bls_fp_sign_bit

/* ---------------------------------------------------------------- G1 */

/* crypto_bls_g1_double(result, point): 2 * point (G1.double). result may be point. */
.set GD_A, 0
.set GD_B, 48
.set GD_C, 96
.set GD_D, 144
.set GD_E, 192
.set GD_F, 240
.set GD_T, 288
.set GD_X, 336
.set GD_Y, 384
.set GD_Z, 432
.set GD_SIZE, 488
LOCAL_FUNCTION crypto_bls_g1_double
    ENTER   GD_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    IS_ZERO %rbp, 96, 48
    jnz     1f
    COPY    %rbx, 0, %rbp, 0, 144
    LEAVE   GD_SIZE
1:  FMUL    %rsp, GD_A, %rbp, 0, %rbp, 0
    FMUL    %rsp, GD_B, %rbp, 48, %rbp, 48
    FMUL    %rsp, GD_C, %rsp, GD_B, %rsp, GD_B
    FADD    %rsp, GD_T, %rbp, 0, %rsp, GD_B
    FMUL    %rsp, GD_T, %rsp, GD_T, %rsp, GD_T
    FSUB    %rsp, GD_T, %rsp, GD_T, %rsp, GD_A
    FSUB    %rsp, GD_T, %rsp, GD_T, %rsp, GD_C
    FADD    %rsp, GD_D, %rsp, GD_T, %rsp, GD_T
    FADD    %rsp, GD_E, %rsp, GD_A, %rsp, GD_A
    FADD    %rsp, GD_E, %rsp, GD_E, %rsp, GD_A
    FMUL    %rsp, GD_F, %rsp, GD_E, %rsp, GD_E
    FADD    %rsp, GD_T, %rsp, GD_D, %rsp, GD_D
    FSUB    %rsp, GD_X, %rsp, GD_F, %rsp, GD_T
    FSUB    %rsp, GD_T, %rsp, GD_D, %rsp, GD_X
    FMUL    %rsp, GD_Y, %rsp, GD_E, %rsp, GD_T
    FADD    %rsp, GD_T, %rsp, GD_C, %rsp, GD_C
    FADD    %rsp, GD_T, %rsp, GD_T, %rsp, GD_T
    FADD    %rsp, GD_T, %rsp, GD_T, %rsp, GD_T
    FSUB    %rsp, GD_Y, %rsp, GD_Y, %rsp, GD_T
    FADD    %rsp, GD_T, %rbp, 48, %rbp, 48
    FMUL    %rsp, GD_Z, %rsp, GD_T, %rbp, 96
    COPY    %rbx, 0, %rsp, GD_X, 144
    LEAVE   GD_SIZE
END_FUNCTION crypto_bls_g1_double

/* crypto_bls_g1_add(first, second, point) -> status: first + second (G1.add). point may be first or second. */
.set GA_Z1Z1, 0
.set GA_Z2Z2, 48
.set GA_U1, 96
.set GA_U2, 144
.set GA_S1, 192
.set GA_S2, 240
.set GA_H, 288
.set GA_I, 336
.set GA_J, 384
.set GA_R, 432
.set GA_V, 480
.set GA_T, 528
.set GA_X, 576
.set GA_Y, 624
.set GA_Z, 672
.set GA_SIZE, 728
FUNCTION crypto_bls_g1_add
    ENTER   GA_SIZE
    mov     %rdi, %rbx                      /* first */
    mov     %rsi, %rbp                      /* second */
    mov     %rdx, %r12                      /* point */
    IS_ZERO %rbx, 96, 48
    jnz     1f
    COPY    %r12, 0, %rbp, 0, 144
    jmp     9f
1:  IS_ZERO %rbp, 96, 48
    jnz     2f
    COPY    %r12, 0, %rbx, 0, 144
    jmp     9f
2:  FMUL    %rsp, GA_Z1Z1, %rbx, 96, %rbx, 96
    FMUL    %rsp, GA_Z2Z2, %rbp, 96, %rbp, 96
    FMUL    %rsp, GA_U1, %rbx, 0, %rsp, GA_Z2Z2
    FMUL    %rsp, GA_U2, %rbp, 0, %rsp, GA_Z1Z1
    FMUL    %rsp, GA_S1, %rbx, 48, %rbp, 96
    FMUL    %rsp, GA_S1, %rsp, GA_S1, %rsp, GA_Z2Z2
    FMUL    %rsp, GA_S2, %rbp, 48, %rbx, 96
    FMUL    %rsp, GA_S2, %rsp, GA_S2, %rsp, GA_Z1Z1
    EQUAL   %rsp, GA_U1, %rsp, GA_U2, 48
    jne     4f
    EQUAL   %rsp, GA_S1, %rsp, GA_S2, 48
    jne     3f
    mov     %r12, %rdi
    mov     %rbx, %rsi
    call    crypto_bls_g1_double
    jmp     9f
3:  SET_ONE %r12, 0
    SET_ONE %r12, 48
    ZERO    %r12, 96, 48
    jmp     9f
4:  FSUB    %rsp, GA_H, %rsp, GA_U2, %rsp, GA_U1
    FADD    %rsp, GA_T, %rsp, GA_H, %rsp, GA_H
    FMUL    %rsp, GA_I, %rsp, GA_T, %rsp, GA_T
    FMUL    %rsp, GA_J, %rsp, GA_H, %rsp, GA_I
    FSUB    %rsp, GA_T, %rsp, GA_S2, %rsp, GA_S1
    FADD    %rsp, GA_R, %rsp, GA_T, %rsp, GA_T
    FMUL    %rsp, GA_V, %rsp, GA_U1, %rsp, GA_I
    FMUL    %rsp, GA_X, %rsp, GA_R, %rsp, GA_R
    FSUB    %rsp, GA_X, %rsp, GA_X, %rsp, GA_J
    FSUB    %rsp, GA_X, %rsp, GA_X, %rsp, GA_V
    FSUB    %rsp, GA_X, %rsp, GA_X, %rsp, GA_V
    FSUB    %rsp, GA_T, %rsp, GA_V, %rsp, GA_X
    FMUL    %rsp, GA_Y, %rsp, GA_R, %rsp, GA_T
    FADD    %rsp, GA_T, %rsp, GA_S1, %rsp, GA_S1
    FMUL    %rsp, GA_T, %rsp, GA_T, %rsp, GA_J
    FSUB    %rsp, GA_Y, %rsp, GA_Y, %rsp, GA_T
    FADD    %rsp, GA_T, %rbx, 96, %rbp, 96
    FMUL    %rsp, GA_T, %rsp, GA_T, %rsp, GA_T
    FSUB    %rsp, GA_T, %rsp, GA_T, %rsp, GA_Z1Z1
    FSUB    %rsp, GA_T, %rsp, GA_T, %rsp, GA_Z2Z2
    FMUL    %rsp, GA_Z, %rsp, GA_T, %rsp, GA_H
    COPY    %r12, 0, %rsp, GA_X, 144
9:  mov     $CRYPTO_OK, %eax
    LEAVE   GA_SIZE
END_FUNCTION crypto_bls_g1_add

/* crypto_bls_g1_neg(point, negated) -> status: (X, -Y, Z) (G1.neg). */
FUNCTION crypto_bls_g1_neg
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    COPY    %rbp, 0, %rbx, 0, 48
    COPY    %rbp, 96, %rbx, 96, 48
    C2      crypto_bls_fp_neg, %rbp, 48, %rbx, 48
    mov     $CRYPTO_OK, %eax
    LEAVE   8
END_FUNCTION crypto_bls_g1_neg

/* crypto_bls_g1_mul(result, point, scalar): k * point (G1.mulNat), k the 4 limbs at scalar. result may be point. */
.set GM_ACC, 0
.set GM_P, 144
.set GM_SIZE, 296
LOCAL_FUNCTION crypto_bls_g1_mul
    ENTER   GM_SIZE
    mov     %rdi, %rbx
    mov     %rdx, %rbp
    COPY    %rsp, GM_P, %rsi, 0, 144
    SET_ONE %rsp, GM_ACC
    SET_ONE %rsp, GM_ACC + 48
    ZERO    %rsp, GM_ACC + 96, 48
    mov     $255, %r12d
1:  C2      crypto_bls_g1_double, %rsp, GM_ACC, %rsp, GM_ACC
    mov     %r12, %rcx
    shr     $6, %rcx
    mov     (%rbp,%rcx,8), %rax
    mov     %r12, %rcx
    shr     %cl, %rax
    test    $1, %al
    jz      2f
    G3      crypto_bls_g1_add, %rsp, GM_ACC, %rsp, GM_P, %rsp, GM_ACC
2:  sub     $1, %r12
    jns     1b
    COPY    %rbx, 0, %rsp, GM_ACC, 144
    LEAVE   GM_SIZE
END_FUNCTION crypto_bls_g1_mul

/* crypto_bls_g1_affine(xy, point): x = X / Z^2, y = Y / Z^3 (G1.toAffine); 0 and 0 at infinity. */
.set GF_ZI, 0
.set GF_ZI2, 48
.set GF_ZI3, 96
.set GF_SIZE, 152
LOCAL_FUNCTION crypto_bls_g1_affine
    ENTER   GF_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    IS_ZERO %rbp, 96, 48
    jnz     1f
    ZERO    %rbx, 0, 96
    LEAVE   GF_SIZE
1:  C2      crypto_bls_fp_inverse, %rsp, GF_ZI, %rbp, 96
    FMUL    %rsp, GF_ZI2, %rsp, GF_ZI, %rsp, GF_ZI
    FMUL    %rsp, GF_ZI3, %rsp, GF_ZI2, %rsp, GF_ZI
    FMUL    %rbx, 0, %rbp, 0, %rsp, GF_ZI2
    FMUL    %rbx, 48, %rbp, 48, %rsp, GF_ZI3
    LEAVE   GF_SIZE
END_FUNCTION crypto_bls_g1_affine

/* crypto_bls_g1_in_subgroup(point, valid): the u64 1 when r * point is the point at infinity, or point is, else 0. */
.set GS_T, 0
.set GS_SIZE, 152
LOCAL_FUNCTION crypto_bls_g1_in_subgroup
    ENTER   GS_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    IS_ZERO %rbx, 96, 48
    jz      1f
    lea     GS_T(%rsp), %rdi
    mov     %rbx, %rsi
    lea     924f(%rip), %rdx
    call    crypto_bls_g1_mul
    IS_ZERO %rsp, GS_T + 96, 48
1:  setz    %al
    movzbl  %al, %eax
    mov     %rax, (%rbp)
    LEAVE   GS_SIZE
END_FUNCTION crypto_bls_g1_in_subgroup

/* ZF set when bytes 1 to n - 1 at rs are all zero. Uses rax, rcx. */
.macro TAIL_ZERO rs, n
    movzbl  1(\rs), %eax
    movzwl  2(\rs), %ecx
    or      %rcx, %rax
    mov     4(\rs), %ecx
    or      %rcx, %rax
    .irp i, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88
    .if \i < \n
    or      \i(\rs), %rax
    .endif
    .endr
    test    %rax, %rax
.endm

/*
 * crypto_bls_g1_uncompress(bytes, point) -> status: the point of a
 * compressed form (G1.uncompress), without the subgroup check.
 * CRYPTO_INVALID_ENCODING otherwise; nothing is written then.
 */
.set GU_X, 0
.set GU_Y, 48
.set GU_Z, 96
.set GU_RHS, 144
.set GU_BIT, 192
.set GU_SIZE, 216
LOCAL_FUNCTION crypto_bls_g1_uncompress
    ENTER   GU_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    movzbl  (%rbx), %r12d
    test    $0x80, %r12d
    jz      8f
    test    $0x40, %r12d
    jz      2f
    cmp     $0xC0, %r12d
    jne     8f
    TAIL_ZERO %rbx, 48
    jnz     8f
    SET_ONE %rbp, 0
    SET_ONE %rbp, 48
    ZERO    %rbp, 96, 48
    jmp     9f
2:  COPY    %rsp, GU_RHS, %rbx, 0, 48
    andb    $0x1F, GU_RHS(%rsp)
    C2      crypto_bls_fp_from_bytes, %rsp, GU_X, %rsp, GU_RHS
    test    %rax, %rax
    jnz     8f
    FMUL    %rsp, GU_RHS, %rsp, GU_X, %rsp, GU_X
    FMUL    %rsp, GU_RHS, %rsp, GU_RHS, %rsp, GU_X
    lea     GU_RHS(%rsp), %rdi
    lea     GU_RHS(%rsp), %rsi
    lea     923f(%rip), %rdx
    call    crypto_bls_fp_add
    C2      crypto_bls_fp_sqrt, %rsp, GU_Y, %rsp, GU_RHS
    test    %rax, %rax
    jnz     8f
    C2      crypto_bls_fp_sign_bit, %rsp, GU_BIT, %rsp, GU_Y
    mov     %r12d, %eax
    shr     $5, %eax
    and     $1, %eax
    cmp     GU_BIT(%rsp), %rax
    je      3f
    C2      crypto_bls_fp_neg, %rsp, GU_Y, %rsp, GU_Y
3:  SET_ONE %rsp, GU_Z
    COPY    %rbp, 0, %rsp, GU_X, 144
9:  mov     $CRYPTO_OK, %eax
    LEAVE   GU_SIZE
8:  mov     $CRYPTO_INVALID_ENCODING, %eax
    LEAVE   GU_SIZE
END_FUNCTION crypto_bls_g1_uncompress

/* crypto_bls_g1_decode(bytes, point) -> status: G1.uncompress, then the subgroup check (decodeG1Export). */
.set GE_P, 0
.set GE_V, 144
.set GE_SIZE, 168
FUNCTION crypto_bls_g1_decode
    ENTER   GE_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    lea     GE_P(%rsp), %rsi
    call    crypto_bls_g1_uncompress
    test    %rax, %rax
    jnz     8f
    C2      crypto_bls_g1_in_subgroup, %rsp, GE_P, %rsp, GE_V
    cmpq    $0, GE_V(%rsp)
    je      8f
    COPY    %rbp, 0, %rsp, GE_P, 144
    mov     $CRYPTO_OK, %eax
    LEAVE   GE_SIZE
8:  mov     $CRYPTO_INVALID_ENCODING, %eax
    LEAVE   GE_SIZE
END_FUNCTION crypto_bls_g1_decode

/* crypto_bls_g1_compress(point, bytes) -> status: G1.compress. */
.set GC_XY, 0
.set GC_BIT, 96
.set GC_SIZE, 120
FUNCTION crypto_bls_g1_compress
    ENTER   GC_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    IS_ZERO %rbx, 96, 48
    jnz     1f
    ZERO    %rbp, 0, 48
    movb    $0xC0, (%rbp)
    jmp     9f
1:  C2      crypto_bls_g1_affine, %rsp, GC_XY, %rbx, 0
    C2      crypto_bls_fp_to_bytes, %rbp, 0, %rsp, GC_XY
    C2      crypto_bls_fp_sign_bit, %rsp, GC_BIT, %rsp, GC_XY + 48
    mov     GC_BIT(%rsp), %rax
    shl     $5, %eax
    or      $0x80, %eax
    or      %al, (%rbp)
9:  mov     $CRYPTO_OK, %eax
    LEAVE   GC_SIZE
END_FUNCTION crypto_bls_g1_compress

/* ---------------------------------------------------------------- Fp2 */

.macro F2MUL ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp2_mul, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro F2ADD ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp2_add, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro F2SUB ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp2_sub, \ra, \oa, \rb, \ob, \rc, \oc
.endm

/* crypto_bls_fp2_add(result, a, b): a + b (Fp2.add). result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp2_add
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    FADD    %rbx, 0, %rbp, 0, %r12, 0
    FADD    %rbx, 48, %rbp, 48, %r12, 48
    LEAVE   8
END_FUNCTION crypto_bls_fp2_add

/* crypto_bls_fp2_sub(result, a, b): a - b (Fp2.sub). result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp2_sub
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    FSUB    %rbx, 0, %rbp, 0, %r12, 0
    FSUB    %rbx, 48, %rbp, 48, %r12, 48
    LEAVE   8
END_FUNCTION crypto_bls_fp2_sub

/* crypto_bls_fp2_neg(result, a): -a (Fp2.neg). result may be a. */
LOCAL_FUNCTION crypto_bls_fp2_neg
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    C2      crypto_bls_fp_neg, %rbx, 0, %rbp, 0
    C2      crypto_bls_fp_neg, %rbx, 48, %rbp, 48
    LEAVE   8
END_FUNCTION crypto_bls_fp2_neg

/* crypto_bls_fp2_mul(result, a, b): (a0 b0 - a1 b1, a0 b1 + a1 b0) (Fp2.mul). result may be a or b. */
.set M2_T0, 0
.set M2_T1, 48
.set M2_T2, 96
.set M2_T3, 144
.set M2_SIZE, 200
LOCAL_FUNCTION crypto_bls_fp2_mul
    ENTER   M2_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    FMUL    %rsp, M2_T0, %rbp, 0, %r12, 0
    FMUL    %rsp, M2_T1, %rbp, 48, %r12, 48
    FMUL    %rsp, M2_T2, %rbp, 0, %r12, 48
    FMUL    %rsp, M2_T3, %rbp, 48, %r12, 0
    FSUB    %rbx, 0, %rsp, M2_T0, %rsp, M2_T1
    FADD    %rbx, 48, %rsp, M2_T2, %rsp, M2_T3
    LEAVE   M2_SIZE
END_FUNCTION crypto_bls_fp2_mul

/* crypto_bls_fp2_mul_fp(result, a, k): (a0 k, a1 k), for k in Fp. result may be a. */
LOCAL_FUNCTION crypto_bls_fp2_mul_fp
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    FMUL    %rbx, 0, %rbp, 0, %r12, 0
    FMUL    %rbx, 48, %rbp, 48, %r12, 0
    LEAVE   8
END_FUNCTION crypto_bls_fp2_mul_fp

/* crypto_bls_fp2_mul_nr(result, a): a (1 + u) = (a0 - a1, a0 + a1) (Fp2.mulByOnePlusI). result may be a. */
.set MN_T, 0
.set MN_SIZE, 56
LOCAL_FUNCTION crypto_bls_fp2_mul_nr
    ENTER   MN_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    FSUB    %rsp, MN_T, %rbp, 0, %rbp, 48
    FADD    %rbx, 48, %rbp, 0, %rbp, 48
    COPY    %rbx, 0, %rsp, MN_T, 48
    LEAVE   MN_SIZE
END_FUNCTION crypto_bls_fp2_mul_nr

/* crypto_bls_fp2_inverse(result, a): (a0 / n, -a1 / n), n = a0^2 + a1^2 (Fp2.inverse). result may be a. */
.set I2_N, 0
.set I2_T, 48
.set I2_SIZE, 104
LOCAL_FUNCTION crypto_bls_fp2_inverse
    ENTER   I2_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    FMUL    %rsp, I2_N, %rbp, 0, %rbp, 0
    FMUL    %rsp, I2_T, %rbp, 48, %rbp, 48
    FADD    %rsp, I2_N, %rsp, I2_N, %rsp, I2_T
    C2      crypto_bls_fp_inverse, %rsp, I2_N, %rsp, I2_N
    FMUL    %rbx, 0, %rbp, 0, %rsp, I2_N
    FMUL    %rsp, I2_T, %rbp, 48, %rsp, I2_N
    C2      crypto_bls_fp_neg, %rbx, 48, %rsp, I2_T
    LEAVE   I2_SIZE
END_FUNCTION crypto_bls_fp2_inverse

/*
 * crypto_bls_fp2_sqrt(result, a) -> status: a square root of a, by the steps
 * of Fp2.sqrt. CRYPTO_INVALID_ENCODING when a is not a square; nothing is
 * written then. result may be a.
 */
.set Q2_S, 0
.set Q2_T, 48
.set Q2_C0, 96
.set Q2_C1, 144
.set Q2_SIZE, 200
LOCAL_FUNCTION crypto_bls_fp2_sqrt
    ENTER   Q2_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    IS_ZERO %rbp, 48, 48
    jnz     3f
    C2      crypto_bls_fp_sqrt, %rsp, Q2_C0, %rbp, 0
    test    %rax, %rax
    jnz     1f
    ZERO    %rsp, Q2_C1, 48
    jmp     7f
1:  C2      crypto_bls_fp_neg, %rsp, Q2_T, %rbp, 0
    C2      crypto_bls_fp_sqrt, %rsp, Q2_C1, %rsp, Q2_T
    test    %rax, %rax
    jnz     8f
    ZERO    %rsp, Q2_C0, 48
    jmp     7f
3:  FMUL    %rsp, Q2_S, %rbp, 0, %rbp, 0
    FMUL    %rsp, Q2_T, %rbp, 48, %rbp, 48
    FADD    %rsp, Q2_S, %rsp, Q2_S, %rsp, Q2_T
    C2      crypto_bls_fp_sqrt, %rsp, Q2_S, %rsp, Q2_S
    test    %rax, %rax
    jnz     8f
    FADD    %rsp, Q2_T, %rbp, 0, %rsp, Q2_S
    lea     Q2_T(%rsp), %rdi
    lea     Q2_T(%rsp), %rsi
    lea     903f(%rip), %rdx
    call    crypto_bls_fp_mul
    C2      crypto_bls_fp_sqrt, %rsp, Q2_C0, %rsp, Q2_T
    test    %rax, %rax
    jz      4f
    FSUB    %rsp, Q2_T, %rbp, 0, %rsp, Q2_S
    lea     Q2_T(%rsp), %rdi
    lea     Q2_T(%rsp), %rsi
    lea     903f(%rip), %rdx
    call    crypto_bls_fp_mul
    C2      crypto_bls_fp_sqrt, %rsp, Q2_C0, %rsp, Q2_T
    test    %rax, %rax
    jnz     8f
4:  FADD    %rsp, Q2_T, %rsp, Q2_C0, %rsp, Q2_C0
    C2      crypto_bls_fp_inverse, %rsp, Q2_T, %rsp, Q2_T
    FMUL    %rsp, Q2_C1, %rbp, 48, %rsp, Q2_T
7:  COPY    %rbx, 0, %rsp, Q2_C0, 96
    mov     $CRYPTO_OK, %eax
    LEAVE   Q2_SIZE
8:  mov     $CRYPTO_INVALID_ENCODING, %eax
    LEAVE   Q2_SIZE
END_FUNCTION crypto_bls_fp2_sqrt

/* crypto_bls_fp2_sign_bit(bit, a): Fp2.signBit: that of c1 when c1 is not 0, else that of c0. */
LOCAL_FUNCTION crypto_bls_fp2_sign_bit
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    IS_ZERO %rbp, 48, 48
    jz      1f
    C2      crypto_bls_fp_sign_bit, %rbx, 0, %rbp, 48
    LEAVE   8
1:  C2      crypto_bls_fp_sign_bit, %rbx, 0, %rbp, 0
    LEAVE   8
END_FUNCTION crypto_bls_fp2_sign_bit

/* ---------------------------------------------------------------- G2 */

/* crypto_bls_g2_double(result, point): 2 * point (G2.double). result may be point. */
.set HD_A, 0
.set HD_B, 96
.set HD_C, 192
.set HD_D, 288
.set HD_E, 384
.set HD_F, 480
.set HD_T, 576
.set HD_X, 672
.set HD_Y, 768
.set HD_Z, 864
.set HD_SIZE, 968
LOCAL_FUNCTION crypto_bls_g2_double
    ENTER   HD_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    IS_ZERO %rbp, 192, 96
    jnz     1f
    COPY    %rbx, 0, %rbp, 0, 288
    LEAVE   HD_SIZE
1:  F2MUL   %rsp, HD_A, %rbp, 0, %rbp, 0
    F2MUL   %rsp, HD_B, %rbp, 96, %rbp, 96
    F2MUL   %rsp, HD_C, %rsp, HD_B, %rsp, HD_B
    F2ADD   %rsp, HD_T, %rbp, 0, %rsp, HD_B
    F2MUL   %rsp, HD_T, %rsp, HD_T, %rsp, HD_T
    F2SUB   %rsp, HD_T, %rsp, HD_T, %rsp, HD_A
    F2SUB   %rsp, HD_T, %rsp, HD_T, %rsp, HD_C
    F2ADD   %rsp, HD_D, %rsp, HD_T, %rsp, HD_T
    F2ADD   %rsp, HD_E, %rsp, HD_A, %rsp, HD_A
    F2ADD   %rsp, HD_E, %rsp, HD_E, %rsp, HD_A
    F2MUL   %rsp, HD_F, %rsp, HD_E, %rsp, HD_E
    F2ADD   %rsp, HD_T, %rsp, HD_D, %rsp, HD_D
    F2SUB   %rsp, HD_X, %rsp, HD_F, %rsp, HD_T
    F2SUB   %rsp, HD_T, %rsp, HD_D, %rsp, HD_X
    F2MUL   %rsp, HD_Y, %rsp, HD_E, %rsp, HD_T
    F2ADD   %rsp, HD_T, %rsp, HD_C, %rsp, HD_C
    F2ADD   %rsp, HD_T, %rsp, HD_T, %rsp, HD_T
    F2ADD   %rsp, HD_T, %rsp, HD_T, %rsp, HD_T
    F2SUB   %rsp, HD_Y, %rsp, HD_Y, %rsp, HD_T
    F2ADD   %rsp, HD_T, %rbp, 96, %rbp, 96
    F2MUL   %rsp, HD_Z, %rsp, HD_T, %rbp, 192
    COPY    %rbx, 0, %rsp, HD_X, 288
    LEAVE   HD_SIZE
END_FUNCTION crypto_bls_g2_double

/* crypto_bls_g2_add(result, first, second): first + second (G2.add). result may be first or second. */
.set HA_Z1Z1, 0
.set HA_Z2Z2, 96
.set HA_U1, 192
.set HA_U2, 288
.set HA_S1, 384
.set HA_S2, 480
.set HA_I, 576
.set HA_J, 672
.set HA_X, 768
.set HA_Y, 864
.set HA_Z, 960
.set HA_SIZE, 1064
LOCAL_FUNCTION crypto_bls_g2_add
    ENTER   HA_SIZE
    mov     %rdi, %r12                      /* result */
    mov     %rsi, %rbx                      /* first */
    mov     %rdx, %rbp                      /* second */
    IS_ZERO %rbx, 192, 96
    jnz     1f
    COPY    %r12, 0, %rbp, 0, 288
    jmp     9f
1:  IS_ZERO %rbp, 192, 96
    jnz     2f
    COPY    %r12, 0, %rbx, 0, 288
    jmp     9f
2:  F2MUL   %rsp, HA_Z1Z1, %rbx, 192, %rbx, 192
    F2MUL   %rsp, HA_Z2Z2, %rbp, 192, %rbp, 192
    F2MUL   %rsp, HA_U1, %rbx, 0, %rsp, HA_Z2Z2
    F2MUL   %rsp, HA_U2, %rbp, 0, %rsp, HA_Z1Z1
    F2MUL   %rsp, HA_S1, %rbx, 96, %rbp, 192
    F2MUL   %rsp, HA_S1, %rsp, HA_S1, %rsp, HA_Z2Z2
    F2MUL   %rsp, HA_S2, %rbp, 96, %rbx, 192
    F2MUL   %rsp, HA_S2, %rsp, HA_S2, %rsp, HA_Z1Z1
    EQUAL   %rsp, HA_U1, %rsp, HA_U2, 96
    jne     4f
    EQUAL   %rsp, HA_S1, %rsp, HA_S2, 96
    jne     3f
    mov     %r12, %rdi
    mov     %rbx, %rsi
    call    crypto_bls_g2_double
    jmp     9f
3:  SET_ONE %r12, 0
    ZERO    %r12, 48, 48
    SET_ONE %r12, 96
    ZERO    %r12, 144, 144
    jmp     9f
4:  F2SUB   %rsp, HA_U2, %rsp, HA_U2, %rsp, HA_U1
    F2ADD   %rsp, HA_I, %rsp, HA_U2, %rsp, HA_U2
    F2MUL   %rsp, HA_I, %rsp, HA_I, %rsp, HA_I
    F2MUL   %rsp, HA_J, %rsp, HA_U2, %rsp, HA_I
    F2SUB   %rsp, HA_S2, %rsp, HA_S2, %rsp, HA_S1
    F2ADD   %rsp, HA_S2, %rsp, HA_S2, %rsp, HA_S2
    F2MUL   %rsp, HA_U1, %rsp, HA_U1, %rsp, HA_I
    F2MUL   %rsp, HA_X, %rsp, HA_S2, %rsp, HA_S2
    F2SUB   %rsp, HA_X, %rsp, HA_X, %rsp, HA_J
    F2SUB   %rsp, HA_X, %rsp, HA_X, %rsp, HA_U1
    F2SUB   %rsp, HA_X, %rsp, HA_X, %rsp, HA_U1
    F2SUB   %rsp, HA_I, %rsp, HA_U1, %rsp, HA_X
    F2MUL   %rsp, HA_Y, %rsp, HA_S2, %rsp, HA_I
    F2ADD   %rsp, HA_S1, %rsp, HA_S1, %rsp, HA_S1
    F2MUL   %rsp, HA_S1, %rsp, HA_S1, %rsp, HA_J
    F2SUB   %rsp, HA_Y, %rsp, HA_Y, %rsp, HA_S1
    F2ADD   %rsp, HA_I, %rbx, 192, %rbp, 192
    F2MUL   %rsp, HA_I, %rsp, HA_I, %rsp, HA_I
    F2SUB   %rsp, HA_I, %rsp, HA_I, %rsp, HA_Z1Z1
    F2SUB   %rsp, HA_I, %rsp, HA_I, %rsp, HA_Z2Z2
    F2MUL   %rsp, HA_Z, %rsp, HA_I, %rsp, HA_U2
    COPY    %r12, 0, %rsp, HA_X, 288
9:  LEAVE   HA_SIZE
END_FUNCTION crypto_bls_g2_add

/* crypto_bls_g2_neg(result, point): (X, -Y, Z) (G2.neg). result may be point. */
LOCAL_FUNCTION crypto_bls_g2_neg
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    COPY    %rbx, 0, %rbp, 0, 96
    COPY    %rbx, 192, %rbp, 192, 96
    C2      crypto_bls_fp2_neg, %rbx, 96, %rbp, 96
    LEAVE   8
END_FUNCTION crypto_bls_g2_neg

/* crypto_bls_g2_mul(result, point, scalar): k * point (G2.mulNat). result may be point. */
.set HM_ACC, 0
.set HM_P, 288
.set HM_SIZE, 584
LOCAL_FUNCTION crypto_bls_g2_mul
    ENTER   HM_SIZE
    mov     %rdi, %rbx
    mov     %rdx, %rbp
    COPY    %rsp, HM_P, %rsi, 0, 288
    SET_ONE %rsp, HM_ACC
    ZERO    %rsp, HM_ACC + 48, 48
    SET_ONE %rsp, HM_ACC + 96
    ZERO    %rsp, HM_ACC + 144, 144
    mov     $255, %r12d
1:  C2      crypto_bls_g2_double, %rsp, HM_ACC, %rsp, HM_ACC
    mov     %r12, %rcx
    shr     $6, %rcx
    mov     (%rbp,%rcx,8), %rax
    mov     %r12, %rcx
    shr     %cl, %rax
    test    $1, %al
    jz      2f
    C3      crypto_bls_g2_add, %rsp, HM_ACC, %rsp, HM_ACC, %rsp, HM_P
2:  sub     $1, %r12
    jns     1b
    COPY    %rbx, 0, %rsp, HM_ACC, 288
    LEAVE   HM_SIZE
END_FUNCTION crypto_bls_g2_mul

/* crypto_bls_g2_affine(xy, point): x = X / Z^2, y = Y / Z^3 (G2.toAffine); 0 and 0 at infinity. */
.set HF_ZI, 0
.set HF_ZI2, 96
.set HF_ZI3, 192
.set HF_SIZE, 296
LOCAL_FUNCTION crypto_bls_g2_affine
    ENTER   HF_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    IS_ZERO %rbp, 192, 96
    jnz     1f
    ZERO    %rbx, 0, 192
    LEAVE   HF_SIZE
1:  C2      crypto_bls_fp2_inverse, %rsp, HF_ZI, %rbp, 192
    F2MUL   %rsp, HF_ZI2, %rsp, HF_ZI, %rsp, HF_ZI
    F2MUL   %rsp, HF_ZI3, %rsp, HF_ZI2, %rsp, HF_ZI
    F2MUL   %rbx, 0, %rbp, 0, %rsp, HF_ZI2
    F2MUL   %rbx, 96, %rbp, 96, %rsp, HF_ZI3
    LEAVE   HF_SIZE
END_FUNCTION crypto_bls_g2_affine

/* crypto_bls_g2_in_subgroup(point, valid): the u64 1 when r * point is the point at infinity, or point is, else 0. */
.set HS_T, 0
.set HS_SIZE, 296
LOCAL_FUNCTION crypto_bls_g2_in_subgroup
    ENTER   HS_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    IS_ZERO %rbx, 192, 96
    jz      1f
    lea     HS_T(%rsp), %rdi
    mov     %rbx, %rsi
    lea     924f(%rip), %rdx
    call    crypto_bls_g2_mul
    IS_ZERO %rsp, HS_T + 192, 96
1:  setz    %al
    movzbl  %al, %eax
    mov     %rax, (%rbp)
    LEAVE   HS_SIZE
END_FUNCTION crypto_bls_g2_in_subgroup

/*
 * crypto_bls_g2_uncompress(bytes, point) -> status: the point of a
 * compressed form (G2.uncompress), without the subgroup check.
 * CRYPTO_INVALID_ENCODING otherwise; nothing is written then.
 */
.set HU_X, 0
.set HU_Y, 96
.set HU_Z, 192
.set HU_RHS, 288
.set HU_BIT, 384
.set HU_SIZE, 408
LOCAL_FUNCTION crypto_bls_g2_uncompress
    ENTER   HU_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    movzbl  (%rbx), %r12d
    test    $0x80, %r12d
    jz      8f
    test    $0x40, %r12d
    jz      2f
    cmp     $0xC0, %r12d
    jne     8f
    TAIL_ZERO %rbx, 96
    jnz     8f
    SET_ONE %rbp, 0
    ZERO    %rbp, 48, 48
    SET_ONE %rbp, 96
    ZERO    %rbp, 144, 144
    jmp     9f
2:  COPY    %rsp, HU_RHS, %rbx, 0, 96
    andb    $0x1F, HU_RHS(%rsp)
    C2      crypto_bls_fp_from_bytes, %rsp, HU_X + 48, %rsp, HU_RHS
    test    %rax, %rax
    jnz     8f
    C2      crypto_bls_fp_from_bytes, %rsp, HU_X, %rsp, HU_RHS + 48
    test    %rax, %rax
    jnz     8f
    F2MUL   %rsp, HU_RHS, %rsp, HU_X, %rsp, HU_X
    F2MUL   %rsp, HU_RHS, %rsp, HU_RHS, %rsp, HU_X
    lea     HU_RHS(%rsp), %rdi
    lea     HU_RHS(%rsp), %rsi
    lea     901f(%rip), %rdx
    call    crypto_bls_fp2_add
    C2      crypto_bls_fp2_sqrt, %rsp, HU_Y, %rsp, HU_RHS
    test    %rax, %rax
    jnz     8f
    C2      crypto_bls_fp2_sign_bit, %rsp, HU_BIT, %rsp, HU_Y
    mov     %r12d, %eax
    shr     $5, %eax
    and     $1, %eax
    cmp     HU_BIT(%rsp), %rax
    je      3f
    C2      crypto_bls_fp2_neg, %rsp, HU_Y, %rsp, HU_Y
3:  SET_ONE %rsp, HU_Z
    ZERO    %rsp, HU_Z + 48, 48
    COPY    %rbp, 0, %rsp, HU_X, 288
9:  mov     $CRYPTO_OK, %eax
    LEAVE   HU_SIZE
8:  mov     $CRYPTO_INVALID_ENCODING, %eax
    LEAVE   HU_SIZE
END_FUNCTION crypto_bls_g2_uncompress

/* crypto_bls_g2_decode(bytes, point) -> status: G2.uncompress, then the subgroup check (decodeG2Export). */
.set HE_P, 0
.set HE_V, 288
.set HE_SIZE, 312
FUNCTION crypto_bls_g2_decode
    ENTER   HE_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    lea     HE_P(%rsp), %rsi
    call    crypto_bls_g2_uncompress
    test    %rax, %rax
    jnz     8f
    C2      crypto_bls_g2_in_subgroup, %rsp, HE_P, %rsp, HE_V
    cmpq    $0, HE_V(%rsp)
    je      8f
    COPY    %rbp, 0, %rsp, HE_P, 288
    mov     $CRYPTO_OK, %eax
    LEAVE   HE_SIZE
8:  mov     $CRYPTO_INVALID_ENCODING, %eax
    LEAVE   HE_SIZE
END_FUNCTION crypto_bls_g2_decode

/* crypto_bls_g2_compress(point, bytes) -> status: G2.compress. */
.set HC_XY, 0
.set HC_BIT, 192
.set HC_SIZE, 216
FUNCTION crypto_bls_g2_compress
    ENTER   HC_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    IS_ZERO %rbx, 192, 96
    jnz     1f
    ZERO    %rbp, 0, 96
    movb    $0xC0, (%rbp)
    jmp     9f
1:  C2      crypto_bls_g2_affine, %rsp, HC_XY, %rbx, 0
    C2      crypto_bls_fp_to_bytes, %rbp, 0, %rsp, HC_XY + 48
    C2      crypto_bls_fp_to_bytes, %rbp, 48, %rsp, HC_XY
    C2      crypto_bls_fp2_sign_bit, %rsp, HC_BIT, %rsp, HC_XY + 96
    mov     HC_BIT(%rsp), %rax
    shl     $5, %eax
    or      $0x80, %eax
    or      %al, (%rbp)
9:  mov     $CRYPTO_OK, %eax
    LEAVE   HC_SIZE
END_FUNCTION crypto_bls_g2_compress

/* ---------------------------------------------------------------- Hash to G2 (HashToCurve.lean) */

/*
 * crypto_bls_xmd(message, dst, length, work, uniform): the first length
 * bytes of expand_message_xmd (expandMessageXmd), for length at most 8160,
 * written at uniform. work holds at least 360 + max(323 + count of
 * message, 17 + count of dst) bytes. Bytes are copied with rep movsb:
 * rcx bytes from rsi to rdi, which both end past the bytes.
 */
.set XW_B0, 0
.set XW_BI, 32
.set XW_DSTP, 64
.set XW_DPLEN, 328
.set XW_BUF, 336
.set XW_DATA, 360
/* SHA-256 of the nreg bytes of the BUF data of work r13, digest at r13 + dig. */
.macro XHASH nreg, dig
    lea     XW_BUF(%r13), %rdi
    lea     24(\nreg), %rax
    mov     %rax, (%rdi)                    /* size */
    movq    $24, 8(%rdi)                    /* offset */
    mov     \nreg, 16(%rdi)                 /* count */
    lea     \dig(%r13), %rsi
    CALL_GLOBAL crypto_sha256
.endm

.set XF_I, 0
.set XF_W, 8
.set XF_SIZE, 24
LOCAL_FUNCTION crypto_bls_xmd
    ENTER   XF_SIZE
    mov     %rdi, %rbx                      /* message */
    mov     %rsi, %rbp                      /* dst */
    mov     (%rdx), %r12                    /* length */
    mov     %rcx, %r13                      /* work */
    mov     %r8, %r14                       /* uniform */
    mov     8(%rbp), %r15                   /* dst offset, count */
    add     %rbp, %r15
    mov     16(%rbp), %r8
    cmp     $255, %r8
    jbe     1f
    lea     XW_DATA(%r13), %rdi             /* a long DST: SHA-256("H2C-OVERSIZE-DST-" || DST) */
    lea     930f(%rip), %rsi
    mov     $17, %ecx
    rep movsb
    mov     %r15, %rsi
    mov     %r8, %rcx
    rep movsb
    lea     17(%r8), %rdx
    XHASH   %rdx, XW_DSTP
    mov     $32, %r8d
    jmp     2f
1:  lea     XW_DSTP(%r13), %rdi
    mov     %r15, %rsi
    mov     %r8, %rcx
    rep movsb
2:  movb    %r8b, XW_DSTP(%r13,%r8)         /* DST' = DST || I2OSP(len(DST), 1) */
    add     $1, %r8
    mov     %r8, XW_DPLEN(%r13)
    /* b_0 = H(Z_pad || msg || I2OSP(length, 2) || I2OSP(0, 1) || DST') */
    ZERO    %r13, XW_DATA, 64
    lea     XW_DATA + 64(%r13), %rdi
    mov     8(%rbx), %rsi
    add     %rbx, %rsi
    mov     16(%rbx), %rcx
    rep movsb
    mov     %r12d, %eax
    shr     $8, %eax
    movb    %al, (%rdi)
    movb    %r12b, 1(%rdi)
    movb    $0, 2(%rdi)
    add     $3, %rdi
    lea     XW_DSTP(%r13), %rsi
    mov     XW_DPLEN(%r13), %rcx
    rep movsb
    lea     XW_DATA(%r13), %rax
    mov     %rdi, %rdx
    sub     %rax, %rdx
    XHASH   %rdx, XW_B0
    /* b_1 = H(b_0 || I2OSP(1, 1) || DST'); b_i = H((b_0 xor b_(i-1)) || I2OSP(i, 1) || DST') */
    COPY    %r13, XW_DATA, %r13, XW_B0, 32
    movq    $1, XF_I(%rsp)                  /* i */
    movq    $0, XF_W(%rsp)                  /* bytes written */
3:  lea     XW_DATA + 32(%r13), %rdi
    mov     XF_I(%rsp), %rax
    movb    %al, (%rdi)
    add     $1, %rdi
    lea     XW_DSTP(%r13), %rsi
    mov     XW_DPLEN(%r13), %rcx
    rep movsb
    lea     XW_DATA(%r13), %rax
    mov     %rdi, %rdx
    sub     %rax, %rdx
    XHASH   %rdx, XW_BI
    mov     %r12, %rcx                      /* copy min(32, length - written) bytes */
    sub     XF_W(%rsp), %rcx
    mov     $32, %eax
    cmp     %rax, %rcx
    cmova   %rax, %rcx
    mov     XF_W(%rsp), %rdi
    add     %r14, %rdi
    lea     XW_BI(%r13), %rsi
    add     %rcx, XF_W(%rsp)
    rep movsb
    cmp     %r12, XF_W(%rsp)
    jae     9f
    addq    $1, XF_I(%rsp)
    .irp off, 0, 8, 16, 24
    mov     XW_B0+\off(%r13), %rax
    xor     XW_BI+\off(%r13), %rax
    mov     %rax, XW_DATA+\off(%r13)
    .endr
    jmp     3b
9:  mov     $CRYPTO_OK, %eax
    LEAVE   XF_SIZE
END_FUNCTION crypto_bls_xmd

/*
 * crypto_bls_fp_from_bytes64(result, bytes): the 64 big-endian bytes, a
 * number n below 2^512, as n mod p in Montgomery form (fpFromBytesL).
 * n = hi 2^384 + lo: result = lo * R^2 / R + hi * R^3 / R, with R = 2^384.
 */
.set F64_LO, 0
.set F64_HI, 48
.set F64_A, 96
.set F64_SIZE, 152
LOCAL_FUNCTION crypto_bls_fp_from_bytes64
    ENTER   F64_SIZE
    mov     %rdi, %rbx
    .irp i, 0, 1, 2, 3, 4, 5
    mov     56-8*\i(%rsi), %rax             /* lo: bytes 16 to 63, least significant last */
    bswap   %rax
    mov     %rax, F64_LO+8*\i(%rsp)
    .endr
    mov     8(%rsi), %rax                   /* hi: bytes 0 to 15 */
    bswap   %rax
    mov     %rax, F64_HI(%rsp)
    mov     (%rsi), %rax
    bswap   %rax
    mov     %rax, F64_HI+8(%rsp)
    ZERO    %rsp, F64_HI + 16, 32
    lea     F64_A(%rsp), %rdi
    lea     F64_LO(%rsp), %rsi
    lea     900f+BLS_FP_RECORD_R2(%rip), %rdx
    call    crypto_bls_fp_mul
    lea     F64_LO(%rsp), %rdi
    lea     F64_HI(%rsp), %rsi
    lea     925f(%rip), %rdx
    call    crypto_bls_fp_mul
    FADD    %rbx, 0, %rsp, F64_A, %rsp, F64_LO
    LEAVE   F64_SIZE
END_FUNCTION crypto_bls_fp_from_bytes64

/*
 * crypto_bls_fp2_sgn0(bit, a): sgn0 of RFC 9380 section 4.1 for Fp2
 * (sgn0Fp2): s0 or (c0 = 0 and s1), with si the parity of ci, as the u64 1 or 0.
 */
.set SG_C, 0
.set SG_SIZE, 56
LOCAL_FUNCTION crypto_bls_fp2_sgn0
    ENTER   SG_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    C2      crypto_bls_fp_canonical, %rsp, SG_C, %rbp, 0
    mov     SG_C(%rsp), %r12
    and     $1, %r12d                       /* s0 */
    IS_ZERO %rsp, SG_C, 48
    setz    %al
    movzbl  %al, %r13d                      /* z0 */
    C2      crypto_bls_fp_canonical, %rsp, SG_C, %rbp, 48
    mov     SG_C(%rsp), %rax
    and     %r13, %rax                      /* z0 and s1 */
    or      %r12, %rax
    mov     %rax, (%rbx)
    LEAVE   SG_SIZE
END_FUNCTION crypto_bls_fp2_sgn0

/*
 * crypto_bls_simple_swu(xy, u) -> status: the point (x, y) of E2' for u, by
 * the steps of simpleSwu (RFC 9380 section 6.6.2). CRYPTO_INVALID_ENCODING
 * when neither g(x1) nor g(x2) is a square, which the RFC excludes.
 */
.set SW_U2, 0
.set SW_ZU2, 96
.set SW_DEN, 192
.set SW_X1, 288
.set SW_GX, 384
.set SW_X, 480
.set SW_Y, 576
.set SW_T, 672
.set SW_S, 768
.set SW_BIT, 864
.set SW_SIZE, 888
LOCAL_FUNCTION crypto_bls_simple_swu
    ENTER   SW_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    lea     910f(%rip), %r12                /* A', then B', then Z */
    F2MUL   %rsp, SW_U2, %rbp, 0, %rbp, 0   /* u2 = u u */
    F2MUL   %rsp, SW_ZU2, %r12, 192, %rsp, SW_U2    /* zu2 = Z u2 */
    F2MUL   %rsp, SW_DEN, %rsp, SW_ZU2, %rsp, SW_ZU2
    F2ADD   %rsp, SW_DEN, %rsp, SW_DEN, %rsp, SW_ZU2
    IS_ZERO %rsp, SW_DEN, 96
    jnz     1f
    F2MUL   %rsp, SW_T, %r12, 192, %r12, 0  /* x1 = B' / (Z A') */
    C2      crypto_bls_fp2_inverse, %rsp, SW_T, %rsp, SW_T
    F2MUL   %rsp, SW_X1, %r12, 96, %rsp, SW_T
    jmp     2f
1:  C2      crypto_bls_fp2_neg, %rsp, SW_S, %r12, 96   /* x1 = (-B' / A') (1 + 1 / denom) */
    C2      crypto_bls_fp2_inverse, %rsp, SW_T, %r12, 0
    F2MUL   %rsp, SW_S, %rsp, SW_S, %rsp, SW_T
    C2      crypto_bls_fp2_inverse, %rsp, SW_T, %rsp, SW_DEN
    lea     SW_T(%rsp), %rdi
    lea     SW_T(%rsp), %rsi
    lea     900f+BLS_FP_RECORD_ONE(%rip), %rdx
    call    crypto_bls_fp_add               /* 1 + c0; c1 unchanged */
    F2MUL   %rsp, SW_X1, %rsp, SW_S, %rsp, SW_T
2:  COPY    %rsp, SW_X, %rsp, SW_X1, 96
    C2      crypto_bls_swu_g, %rsp, SW_GX, %rsp, SW_X  /* gx1 = x1^3 + A' x1 + B' */
    C2      crypto_bls_fp2_sqrt, %rsp, SW_Y, %rsp, SW_GX
    test    %rax, %rax
    jz      3f
    F2MUL   %rsp, SW_X, %rsp, SW_ZU2, %rsp, SW_X1      /* x2 = zu2 x1 */
    C2      crypto_bls_swu_g, %rsp, SW_GX, %rsp, SW_X
    C2      crypto_bls_fp2_sqrt, %rsp, SW_Y, %rsp, SW_GX
    test    %rax, %rax
    jnz     8f
3:  C2      crypto_bls_fp2_sgn0, %rsp, SW_BIT, %rbp, 0
    C2      crypto_bls_fp2_sgn0, %rsp, SW_BIT + 8, %rsp, SW_Y
    mov     SW_BIT(%rsp), %rax
    cmp     SW_BIT+8(%rsp), %rax
    je      4f
    C2      crypto_bls_fp2_neg, %rsp, SW_Y, %rsp, SW_Y
4:  COPY    %rbx, 0, %rsp, SW_X, 192
    mov     $CRYPTO_OK, %eax
    LEAVE   SW_SIZE
8:  mov     $CRYPTO_INVALID_ENCODING, %eax
    LEAVE   SW_SIZE
END_FUNCTION crypto_bls_simple_swu

/* crypto_bls_swu_g(result, x): x^3 + A' x + B' on E2'. */
.set SV_T, 0
.set SV_SIZE, 104
LOCAL_FUNCTION crypto_bls_swu_g
    ENTER   SV_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    lea     910f(%rip), %r12
    F2MUL   %rbx, 0, %rbp, 0, %rbp, 0
    F2MUL   %rbx, 0, %rbx, 0, %rbp, 0
    F2MUL   %rsp, SV_T, %r12, 0, %rbp, 0
    F2ADD   %rbx, 0, %rbx, 0, %rsp, SV_T
    F2ADD   %rbx, 0, %rbx, 0, %r12, 96
    LEAVE   SV_SIZE
END_FUNCTION crypto_bls_swu_g

/*
 * crypto_bls_iso_map_g2(point, xy): the 3-isogeny of RFC 9380 appendix E.3
 * (isoMapG2): (x_num / x_den, y' y_num / y_den, 1), or the point at
 * infinity when a denominator is 0.
 */
.set IM_X2, 0
.set IM_X3, 96
.set IM_XN, 192
.set IM_XD, 288
.set IM_YN, 384
.set IM_YD, 480
.set IM_T, 576
.set IM_SIZE, 680
LOCAL_FUNCTION crypto_bls_iso_map_g2
    ENTER   IM_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    lea     913f(%rip), %r12                /* k10..k13, then k20, k21, then k30..k33, then k40..k42 */
    F2MUL   %rsp, IM_X2, %rbp, 0, %rbp, 0
    F2MUL   %rsp, IM_X3, %rsp, IM_X2, %rbp, 0
    F2MUL   %rsp, IM_XN, %r12, 288, %rsp, IM_X3     /* x_num = k13 x^3 + k12 x^2 + k11 x + k10 */
    F2MUL   %rsp, IM_T, %r12, 192, %rsp, IM_X2
    F2ADD   %rsp, IM_XN, %rsp, IM_XN, %rsp, IM_T
    F2MUL   %rsp, IM_T, %r12, 96, %rbp, 0
    F2ADD   %rsp, IM_XN, %rsp, IM_XN, %rsp, IM_T
    F2ADD   %rsp, IM_XN, %rsp, IM_XN, %r12, 0
    F2MUL   %rsp, IM_T, %r12, 480, %rbp, 0  /* x_den = x^2 + k21 x + k20 */
    F2ADD   %rsp, IM_XD, %rsp, IM_X2, %rsp, IM_T
    F2ADD   %rsp, IM_XD, %rsp, IM_XD, %r12, 384
    lea     576(%r12), %r13
    F2MUL   %rsp, IM_YN, %r13, 288, %rsp, IM_X3     /* y_num = k33 x^3 + k32 x^2 + k31 x + k30 */
    F2MUL   %rsp, IM_T, %r13, 192, %rsp, IM_X2
    F2ADD   %rsp, IM_YN, %rsp, IM_YN, %rsp, IM_T
    F2MUL   %rsp, IM_T, %r13, 96, %rbp, 0
    F2ADD   %rsp, IM_YN, %rsp, IM_YN, %rsp, IM_T
    F2ADD   %rsp, IM_YN, %rsp, IM_YN, %r13, 0
    lea     960(%r12), %r13
    F2MUL   %rsp, IM_T, %r13, 192, %rsp, IM_X2      /* y_den = x^3 + k42 x^2 + k41 x + k40 */
    F2ADD   %rsp, IM_YD, %rsp, IM_X3, %rsp, IM_T
    F2MUL   %rsp, IM_T, %r13, 96, %rbp, 0
    F2ADD   %rsp, IM_YD, %rsp, IM_YD, %rsp, IM_T
    F2ADD   %rsp, IM_YD, %rsp, IM_YD, %r13, 0
    IS_ZERO %rsp, IM_XD, 96
    jz      1f
    IS_ZERO %rsp, IM_YD, 96
    jz      1f
    C2      crypto_bls_fp2_inverse, %rsp, IM_T, %rsp, IM_XD
    F2MUL   %rbx, 0, %rsp, IM_XN, %rsp, IM_T
    F2MUL   %rsp, IM_YN, %rbp, 96, %rsp, IM_YN
    C2      crypto_bls_fp2_inverse, %rsp, IM_T, %rsp, IM_YD
    F2MUL   %rbx, 96, %rsp, IM_YN, %rsp, IM_T
    SET_ONE %rbx, 192
    ZERO    %rbx, 240, 48
    LEAVE   IM_SIZE
1:  SET_ONE %rbx, 0                         /* the point at infinity */
    ZERO    %rbx, 48, 48
    SET_ONE %rbx, 96
    ZERO    %rbx, 144, 144
    LEAVE   IM_SIZE
END_FUNCTION crypto_bls_iso_map_g2

/*
 * crypto_bls_psi(result, point): psi of RFC 9380 appendix G.3 (psi): the
 * affine (c1Psi conj(x), c2Psi conj(y), 1); the point at infinity stays.
 * result may be point.
 */
.set PS_XY, 0
.set PS_T, 192
.set PS_SIZE, 296
LOCAL_FUNCTION crypto_bls_psi
    ENTER   PS_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    IS_ZERO %rbp, 192, 96
    jnz     1f
    COPY    %rbx, 0, %rbp, 0, 288
    LEAVE   PS_SIZE
1:  C2      crypto_bls_g2_affine, %rsp, PS_XY, %rbp, 0
    lea     907f(%rip), %r12                /* c1Psi, then c2Psi */
    COPY    %rsp, PS_T, %rsp, PS_XY, 48     /* conj(x) */
    C2      crypto_bls_fp_neg, %rsp, PS_T + 48, %rsp, PS_XY + 48
    F2MUL   %rbx, 0, %r12, 0, %rsp, PS_T
    COPY    %rsp, PS_T, %rsp, PS_XY + 96, 48        /* conj(y) */
    C2      crypto_bls_fp_neg, %rsp, PS_T + 48, %rsp, PS_XY + 144
    F2MUL   %rbx, 96, %r12, 96, %rsp, PS_T
    SET_ONE %rbx, 192
    ZERO    %rbx, 240, 48
    LEAVE   PS_SIZE
END_FUNCTION crypto_bls_psi

/*
 * crypto_bls_psi2(result, point): psi2 of RFC 9380 appendix G.3 (psi2):
 * the affine (c1Psi2 x, -y, 1); the point at infinity stays. result may be
 * point.
 */
.set P2_XY, 0
.set P2_SIZE, 200
LOCAL_FUNCTION crypto_bls_psi2
    ENTER   P2_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    IS_ZERO %rbp, 192, 96
    jnz     1f
    COPY    %rbx, 0, %rbp, 0, 288
    LEAVE   P2_SIZE
1:  C2      crypto_bls_g2_affine, %rsp, P2_XY, %rbp, 0
    mov     %rbx, %rdi
    lea     P2_XY(%rsp), %rsi
    lea     908f(%rip), %rdx                /* c1Psi2, in Fp */
    call    crypto_bls_fp2_mul_fp
    C2      crypto_bls_fp2_neg, %rbx, 96, %rsp, P2_XY + 96
    SET_ONE %rbx, 192
    ZERO    %rbx, 240, 48
    LEAVE   P2_SIZE
END_FUNCTION crypto_bls_psi2

/* crypto_bls_g2_mul_neg_x(result, point): x * point, with the negative BLS parameter x = -|x| (mulNegX). */
LOCAL_FUNCTION crypto_bls_g2_mul_neg_x
    ENTER   8
    mov     %rdi, %rbx
    lea     926f(%rip), %rdx
    call    crypto_bls_g2_mul
    C2      crypto_bls_g2_neg, %rbx, 0, %rbx, 0
    LEAVE   8
END_FUNCTION crypto_bls_g2_mul_neg_x

/*
 * crypto_bls_clear_cofactor(result, point, work): clear_cofactor of RFC 9380
 * appendix G.3 (clearCofactor). work holds 1152 bytes: t1, t2, t3 and t4.
 * result may be point.
 */
.set CC_T1, 0
.set CC_T2, 288
.set CC_T3, 576
.set CC_T4, 864
LOCAL_FUNCTION crypto_bls_clear_cofactor
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    C2      crypto_bls_g2_mul_neg_x, %r12, CC_T1, %rbp, 0   /* t1 = x P */
    C2      crypto_bls_psi, %r12, CC_T2, %rbp, 0            /* t2 = psi(P) */
    C2      crypto_bls_g2_double, %r12, CC_T3, %rbp, 0      /* t3 = psi2(2 P) */
    C2      crypto_bls_psi2, %r12, CC_T3, %r12, CC_T3
    C2      crypto_bls_g2_neg, %r12, CC_T4, %r12, CC_T2     /* t3 = t3 - t2 */
    C3      crypto_bls_g2_add, %r12, CC_T3, %r12, CC_T3, %r12, CC_T4
    C3      crypto_bls_g2_add, %r12, CC_T2, %r12, CC_T1, %r12, CC_T2   /* t2 = t1 + t2 */
    C2      crypto_bls_g2_mul_neg_x, %r12, CC_T2, %r12, CC_T2         /* t2 = x t2 */
    C3      crypto_bls_g2_add, %r12, CC_T3, %r12, CC_T3, %r12, CC_T2   /* t3 = t3 + t2 */
    C2      crypto_bls_g2_neg, %r12, CC_T1, %r12, CC_T1     /* t3 = t3 - t1 */
    C3      crypto_bls_g2_add, %r12, CC_T3, %r12, CC_T3, %r12, CC_T1
    C2      crypto_bls_g2_neg, %r12, CC_T4, %rbp, 0         /* result = t3 - P */
    C3      crypto_bls_g2_add, %rbx, 0, %r12, CC_T3, %r12, CC_T4
    LEAVE   8
END_FUNCTION crypto_bls_clear_cofactor

/*
 * crypto_bls_hash_to_g2_point(message, dst, work, point): hashToG2 into a
 * point of G2. work holds the H2C work area of include/bls12381.inc.
 */
.set HW_U, 0
.set HW_U0, 256
.set HW_U1, 352
.set HW_XY0, 448
.set HW_XY1, 640
.set HW_Q0, 832
.set HW_Q1, 1120
.set HW_LEN, 1408
.set HW_P, 1416
.set HW_CC, 1704
.set HW_XMD, 2856
LOCAL_FUNCTION crypto_bls_hash_to_g2_point
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12                      /* work */
    mov     %rcx, %r13                      /* point */
    movq    $256, HW_LEN(%r12)
    mov     %rbx, %rdi                      /* uniform = expand_message_xmd(msg, DST, 256) */
    mov     %rbp, %rsi
    lea     HW_LEN(%r12), %rdx
    lea     HW_XMD(%r12), %rcx
    lea     HW_U(%r12), %r8
    call    crypto_bls_xmd
    C2      crypto_bls_fp_from_bytes64, %r12, HW_U0, %r12, HW_U       /* hash_to_field: u0, u1 */
    C2      crypto_bls_fp_from_bytes64, %r12, HW_U0 + 48, %r12, HW_U + 64
    C2      crypto_bls_fp_from_bytes64, %r12, HW_U1, %r12, HW_U + 128
    C2      crypto_bls_fp_from_bytes64, %r12, HW_U1 + 48, %r12, HW_U + 192
    C2      crypto_bls_simple_swu, %r12, HW_XY0, %r12, HW_U0
    test    %rax, %rax
    jnz     9f
    C2      crypto_bls_simple_swu, %r12, HW_XY1, %r12, HW_U1
    test    %rax, %rax
    jnz     9f
    C2      crypto_bls_iso_map_g2, %r12, HW_Q0, %r12, HW_XY0
    C2      crypto_bls_iso_map_g2, %r12, HW_Q1, %r12, HW_XY1
    C3      crypto_bls_g2_add, %r12, HW_Q0, %r12, HW_Q0, %r12, HW_Q1
    C3      crypto_bls_clear_cofactor, %r13, 0, %r12, HW_Q0, %r12, HW_CC
    mov     $CRYPTO_OK, %eax
9:  LEAVE   8
END_FUNCTION crypto_bls_hash_to_g2_point

/*
 * crypto_bls_expand_message_xmd(message, dst, length, scratch, uniform) ->
 * status: checks length, scratch and uniform, then crypto_bls_xmd.
 */
FUNCTION crypto_bls_expand_message_xmd
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     %r8, %r14
    mov     (%r12), %r15                    /* length */
    cmp     $CRYPTO_BLS_XMD_MAX_LENGTH, %r15
    ja      7f
    mov     CRYPTO_BYTES_COUNT(%rbx), %rax  /* scratch: CRYPTO_BLS_H2C_SCRATCH + message + dst */
    add     CRYPTO_BYTES_COUNT(%rbp), %rax
    add     $CRYPTO_BLS_H2C_SCRATCH, %rax
    cmp     %rax, (%r13)
    jb      8f
    lea     CRYPTO_BYTES_FIXED(%r15), %rax  /* uniform: 24 + length */
    cmp     %rax, (%r14)
    jb      8f
    mov     %rbx, %rdi
    mov     %rbp, %rsi
    mov     %r12, %rdx
    lea     8(%r13), %rcx
    lea     CRYPTO_BYTES_FIXED(%r14), %r8
    call    crypto_bls_xmd
    movq    $CRYPTO_BYTES_FIXED, CRYPTO_BYTES_OFFSET(%r14)
    mov     %r15, CRYPTO_BYTES_COUNT(%r14)
    mov     $CRYPTO_OK, %eax
    LEAVE   8
7:  mov     $CRYPTO_BLS_XMD_LENGTH, %eax
    LEAVE   8
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   8
END_FUNCTION crypto_bls_expand_message_xmd

/*
 * crypto_bls_hash_to_g2(message, dst, scratch, point) -> status: checks
 * scratch, hashes, and writes the affine coordinates (hashToG2Export).
 */
.set HG_XY, 0
.set HG_SIZE, 200
FUNCTION crypto_bls_hash_to_g2
    ENTER   HG_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     CRYPTO_BYTES_COUNT(%rbx), %rax
    add     CRYPTO_BYTES_COUNT(%rbp), %rax
    add     $CRYPTO_BLS_H2C_SCRATCH, %rax
    cmp     %rax, (%r12)
    jb      8f
    lea     8(%r12), %r14                   /* work */
    mov     %rbx, %rdi
    mov     %rbp, %rsi
    mov     %r14, %rdx
    lea     HW_P(%r14), %rcx
    call    crypto_bls_hash_to_g2_point
    test    %rax, %rax
    jnz     9f
    IS_ZERO %r14, HW_P + 192, 96
    jz      7f
    C2      crypto_bls_g2_affine, %rsp, HG_XY, %r14, HW_P
    C2      crypto_bls_fp_to_bytes, %r13, 0, %rsp, HG_XY
    C2      crypto_bls_fp_to_bytes, %r13, 48, %rsp, HG_XY + 48
    C2      crypto_bls_fp_to_bytes, %r13, 96, %rsp, HG_XY + 96
    C2      crypto_bls_fp_to_bytes, %r13, 144, %rsp, HG_XY + 144
    mov     $CRYPTO_OK, %eax
9:  LEAVE   HG_SIZE
7:  mov     $CRYPTO_BLS_POINT_AT_INFINITY, %eax
    LEAVE   HG_SIZE
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   HG_SIZE
END_FUNCTION crypto_bls_hash_to_g2

/* ---------------------------------------------------------------- Signatures (Signatures.lean) */

/*
 * crypto_bls_secret_key(scalar, secret_key) -> status: the 32 big-endian
 * bytes as 4 little-endian limbs (SecretKey.fromBytes).
 * CRYPTO_INVALID_PRIVATE_KEY when the key is 0, or r or more; nothing is
 * written then.
 */
LOCAL_FUNCTION crypto_bls_secret_key
    UNWIND_END_PROLOGUE
    mov     24(%rsi), %rax
    bswap   %rax
    mov     16(%rsi), %rcx
    bswap   %rcx
    mov     8(%rsi), %rdx
    bswap   %rdx
    mov     (%rsi), %r8
    bswap   %r8
    mov     %rax, %r9
    or      %rcx, %r9
    or      %rdx, %r9
    or      %r8, %r9
    jz      8f
    mov     %rax, %r9                       /* below r? */
    sub     924f(%rip), %r9
    mov     %rcx, %r9
    sbb     924f+8(%rip), %r9
    mov     %rdx, %r9
    sbb     924f+16(%rip), %r9
    mov     %r8, %r9
    sbb     924f+24(%rip), %r9
    jnc     8f
    mov     %rax, (%rdi)
    mov     %rcx, 8(%rdi)
    mov     %rdx, 16(%rdi)
    mov     %r8, 24(%rdi)
    mov     $CRYPTO_OK, %eax
    ret
8:  mov     $CRYPTO_INVALID_PRIVATE_KEY, %eax
    ret
END_FUNCTION crypto_bls_secret_key

/* crypto_bls_sk_to_pk(secret_key, public_key) -> status: skToPk. */
.set SP_K, 0
.set SP_P, 32
.set SP_SIZE, 184
FUNCTION crypto_bls_sk_to_pk
    ENTER   SP_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    lea     SP_K(%rsp), %rdi
    mov     %rbx, %rsi
    call    crypto_bls_secret_key
    test    %rax, %rax
    jnz     9f
    lea     904f(%rip), %r12                /* the generator of G1: (x, y, 1) */
    COPY    %rsp, SP_P, %r12, 0, 96
    SET_ONE %rsp, SP_P + 96
    C3      crypto_bls_g1_mul, %rsp, SP_P, %rsp, SP_P, %rsp, SP_K
    G2      crypto_bls_g1_compress, %rsp, SP_P, %rbp, 0
    mov     $CRYPTO_OK, %eax
9:  LEAVE   SP_SIZE
END_FUNCTION crypto_bls_sk_to_pk

/*
 * crypto_bls_sign(secret_key, message, scratch, signature) -> status: sign:
 * the compressed SK * H(message), H the hash to G2 under the DST.
 * scratch: Q at work + 0, the hash work at work + 288.
 */
.set SN_K, 0
.set SN_SIZE, 40
FUNCTION crypto_bls_sign
    ENTER   SN_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    lea     SN_K(%rsp), %rdi
    mov     %rbx, %rsi
    call    crypto_bls_secret_key
    test    %rax, %rax
    jnz     9f
    mov     CRYPTO_BYTES_COUNT(%rbp), %rax
    add     $CRYPTO_BLS_SCRATCH, %rax
    cmp     %rax, (%r12)
    jb      8f
    lea     8(%r12), %r14                   /* work */
    mov     %rbp, %rdi
    lea     931f(%rip), %rsi                /* the DST, as a ByteList */
    lea     288(%r14), %rdx
    mov     %r14, %rcx
    call    crypto_bls_hash_to_g2_point
    test    %rax, %rax
    jnz     9f
    mov     %r14, %rdi
    mov     %r14, %rsi
    lea     SN_K(%rsp), %rdx
    call    crypto_bls_g2_mul
    G2      crypto_bls_g2_compress, %r14, 0, %r13, 0
    mov     $CRYPTO_OK, %eax
9:  LEAVE   SN_SIZE
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   SN_SIZE
END_FUNCTION crypto_bls_sign

/*
 * crypto_bls_key_validate_point(public_key, point) -> status: G1.keyValidatePoint:
 * decompression, not the point at infinity, in the subgroup.
 * CRYPTO_INVALID_PUBLIC_KEY otherwise; nothing is written then.
 */
.set KV_P, 0
.set KV_V, 144
.set KV_SIZE, 168
LOCAL_FUNCTION crypto_bls_key_validate_point
    ENTER   KV_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    lea     KV_P(%rsp), %rsi
    call    crypto_bls_g1_uncompress
    test    %rax, %rax
    jnz     8f
    IS_ZERO %rsp, KV_P + 96, 48
    jz      8f
    C2      crypto_bls_g1_in_subgroup, %rsp, KV_P, %rsp, KV_V
    cmpq    $0, KV_V(%rsp)
    je      8f
    COPY    %rbp, 0, %rsp, KV_P, 144
    mov     $CRYPTO_OK, %eax
    LEAVE   KV_SIZE
8:  mov     $CRYPTO_INVALID_PUBLIC_KEY, %eax
    LEAVE   KV_SIZE
END_FUNCTION crypto_bls_key_validate_point

/* crypto_bls_key_validate(public_key, valid) -> status: keyValidate, as 1 or 0. */
.set KW_P, 0
.set KW_SIZE, 152
FUNCTION crypto_bls_key_validate
    ENTER   KW_SIZE
    mov     %rsi, %rbp
    lea     KW_P(%rsp), %rsi
    call    crypto_bls_key_validate_point
    cmp     $CRYPTO_OK, %rax
    sete    %al
    movzbl  %al, %eax
    mov     %rax, (%rbp)
    mov     $CRYPTO_OK, %eax
    LEAVE   KW_SIZE
END_FUNCTION crypto_bls_key_validate

/* crypto_bls_aggregate(signatures, signature) -> status: aggregate. */
.set AG_ACC, 0
.set AG_P, 288
.set AG_SIZE, 584
FUNCTION crypto_bls_aggregate
    ENTER   AG_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     CRYPTO_BLS_LIST_OFFSET(%rbx), %r12
    mov     CRYPTO_BLS_LIST_COUNT(%rbx), %r13
    test    %r13, %r13
    jz      7f
    add     %rbx, %r12
    SET_ONE %rsp, AG_ACC                    /* the point at infinity */
    ZERO    %rsp, AG_ACC + 48, 48
    SET_ONE %rsp, AG_ACC + 96
    ZERO    %rsp, AG_ACC + 144, 144
1:  mov     %r12, %rdi
    lea     AG_P(%rsp), %rsi
    call    crypto_bls_g2_uncompress
    test    %rax, %rax
    jnz     8f
    C3      crypto_bls_g2_add, %rsp, AG_ACC, %rsp, AG_ACC, %rsp, AG_P
    add     $96, %r12
    sub     $1, %r13
    jnz     1b
    G2      crypto_bls_g2_compress, %rsp, AG_ACC, %rbp, 0
    mov     $CRYPTO_OK, %eax
    LEAVE   AG_SIZE
7:  mov     $CRYPTO_EMPTY_LIST, %eax
    LEAVE   AG_SIZE
8:  mov     $CRYPTO_INVALID_SIGNATURE, %eax
    LEAVE   AG_SIZE
END_FUNCTION crypto_bls_aggregate

/*
 * crypto_bls_aggregate_keys(public_keys, point) -> status: the sum of the
 * keys, each through crypto_bls_key_validate_point, from the point at
 * infinity. CRYPTO_EMPTY_LIST or CRYPTO_INVALID_PUBLIC_KEY otherwise.
 */
.set AK_ACC, 0
.set AK_P, 144
.set AK_SIZE, 296
LOCAL_FUNCTION crypto_bls_aggregate_keys
    ENTER   AK_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     CRYPTO_BLS_LIST_OFFSET(%rbx), %r12
    mov     CRYPTO_BLS_LIST_COUNT(%rbx), %r13
    test    %r13, %r13
    jz      7f
    add     %rbx, %r12
    SET_ONE %rsp, AK_ACC
    SET_ONE %rsp, AK_ACC + 48
    ZERO    %rsp, AK_ACC + 96, 48
1:  mov     %r12, %rdi
    lea     AK_P(%rsp), %rsi
    call    crypto_bls_key_validate_point
    test    %rax, %rax
    jnz     9f
    G3      crypto_bls_g1_add, %rsp, AK_ACC, %rsp, AK_P, %rsp, AK_ACC
    add     $48, %r12
    sub     $1, %r13
    jnz     1b
    COPY    %rbp, 0, %rsp, AK_ACC, 144
    mov     $CRYPTO_OK, %eax
9:  LEAVE   AK_SIZE
7:  mov     $CRYPTO_EMPTY_LIST, %eax
    LEAVE   AK_SIZE
END_FUNCTION crypto_bls_aggregate_keys

/* crypto_bls_eth_aggregate_pubkeys(public_keys, public_key) -> status: ethAggregatePubkeys. */
.set EA_P, 0
.set EA_SIZE, 152
FUNCTION crypto_bls_eth_aggregate_pubkeys
    ENTER   EA_SIZE
    mov     %rsi, %rbp
    lea     EA_P(%rsp), %rsi
    call    crypto_bls_aggregate_keys
    test    %rax, %rax
    jnz     9f
    G2      crypto_bls_g1_compress, %rsp, EA_P, %rbp, 0
    mov     $CRYPTO_OK, %eax
9:  LEAVE   EA_SIZE
END_FUNCTION crypto_bls_eth_aggregate_pubkeys

/* ---------------------------------------------------------------- Fp6 (Fp6.lean) */

.macro F2NR ra, oa, rb, ob
    C2      crypto_bls_fp2_mul_nr, \ra, \oa, \rb, \ob
.endm
.macro F6MUL ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp6_mul, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro F6ADD ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp6_add, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro F6SUB ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp6_sub, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro F12MUL ra, oa, rb, ob, rc, oc
    C3      crypto_bls_fp12_mul, \ra, \oa, \rb, \ob, \rc, \oc
.endm

/* crypto_bls_fp6_add(result, a, b): a + b (Fp6.add). result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp6_add
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    F2ADD   %rbx, 0, %rbp, 0, %r12, 0
    F2ADD   %rbx, 96, %rbp, 96, %r12, 96
    F2ADD   %rbx, 192, %rbp, 192, %r12, 192
    LEAVE   8
END_FUNCTION crypto_bls_fp6_add

/* crypto_bls_fp6_sub(result, a, b): a - b (Fp6.sub). result may be a or b. */
LOCAL_FUNCTION crypto_bls_fp6_sub
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    F2SUB   %rbx, 0, %rbp, 0, %r12, 0
    F2SUB   %rbx, 96, %rbp, 96, %r12, 96
    F2SUB   %rbx, 192, %rbp, 192, %r12, 192
    LEAVE   8
END_FUNCTION crypto_bls_fp6_sub

/* crypto_bls_fp6_neg(result, a): -a (Fp6.neg). result may be a. */
LOCAL_FUNCTION crypto_bls_fp6_neg
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    C2      crypto_bls_fp2_neg, %rbx, 0, %rbp, 0
    C2      crypto_bls_fp2_neg, %rbx, 96, %rbp, 96
    C2      crypto_bls_fp2_neg, %rbx, 192, %rbp, 192
    LEAVE   8
END_FUNCTION crypto_bls_fp6_neg

/*
 * crypto_bls_fp6_mul(result, a, b): a * b (Fp6.mul): with t_i = a_i b_i,
 * c0 = xi ((a1 + a2)(b1 + b2) - t1 - t2) + t0, c1 = (a0 + a1)(b0 + b1) - t0
 * - t1 + xi t2, c2 = (a0 + a2)(b0 + b2) - t0 - t2 + t1. result may be a or b.
 */
.set M6_T0, 0
.set M6_T1, 96
.set M6_T2, 192
.set M6_S, 288
.set M6_U, 384
.set M6_C0, 480
.set M6_C1, 576
.set M6_C2, 672
.set M6_SIZE, 776
LOCAL_FUNCTION crypto_bls_fp6_mul
    ENTER   M6_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    F2MUL   %rsp, M6_T0, %rbp, 0, %r12, 0
    F2MUL   %rsp, M6_T1, %rbp, 96, %r12, 96
    F2MUL   %rsp, M6_T2, %rbp, 192, %r12, 192
    F2ADD   %rsp, M6_S, %rbp, 96, %rbp, 192         /* c0 */
    F2ADD   %rsp, M6_U, %r12, 96, %r12, 192
    F2MUL   %rsp, M6_C0, %rsp, M6_S, %rsp, M6_U
    F2SUB   %rsp, M6_C0, %rsp, M6_C0, %rsp, M6_T1
    F2SUB   %rsp, M6_C0, %rsp, M6_C0, %rsp, M6_T2
    F2NR    %rsp, M6_C0, %rsp, M6_C0
    F2ADD   %rsp, M6_C0, %rsp, M6_C0, %rsp, M6_T0
    F2ADD   %rsp, M6_S, %rbp, 0, %rbp, 96           /* c1 */
    F2ADD   %rsp, M6_U, %r12, 0, %r12, 96
    F2MUL   %rsp, M6_C1, %rsp, M6_S, %rsp, M6_U
    F2SUB   %rsp, M6_C1, %rsp, M6_C1, %rsp, M6_T0
    F2SUB   %rsp, M6_C1, %rsp, M6_C1, %rsp, M6_T1
    F2NR    %rsp, M6_U, %rsp, M6_T2
    F2ADD   %rsp, M6_C1, %rsp, M6_C1, %rsp, M6_U
    F2ADD   %rsp, M6_S, %rbp, 0, %rbp, 192          /* c2 */
    F2ADD   %rsp, M6_U, %r12, 0, %r12, 192
    F2MUL   %rsp, M6_C2, %rsp, M6_S, %rsp, M6_U
    F2SUB   %rsp, M6_C2, %rsp, M6_C2, %rsp, M6_T0
    F2SUB   %rsp, M6_C2, %rsp, M6_C2, %rsp, M6_T2
    F2ADD   %rsp, M6_C2, %rsp, M6_C2, %rsp, M6_T1
    COPY    %rbx, 0, %rsp, M6_C0, 288
    LEAVE   M6_SIZE
END_FUNCTION crypto_bls_fp6_mul

/* crypto_bls_fp6_mul_v(result, a): a v = (xi a2, a0, a1) (Fp6.mulByV). result may be a. */
.set MV_T, 0
.set MV_SIZE, 104
LOCAL_FUNCTION crypto_bls_fp6_mul_v
    ENTER   MV_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    F2NR    %rsp, MV_T, %rbp, 192
    COPY    %rbx, 192, %rbp, 96, 96
    COPY    %rbx, 96, %rbp, 0, 96
    COPY    %rbx, 0, %rsp, MV_T, 96
    LEAVE   MV_SIZE
END_FUNCTION crypto_bls_fp6_mul_v

/*
 * crypto_bls_fp6_inverse(result, a): 1 / a (Fp6.inverse): t0 = a0^2 - xi
 * a1 a2, t1 = xi a2^2 - a0 a1, t2 = a1^2 - a0 a2, det = a0 t0 + xi a2 t1 +
 * xi a1 t2, and (t0, t1, t2) / det. result may be a.
 */
.set N6_T0, 0
.set N6_T1, 96
.set N6_T2, 192
.set N6_D, 288
.set N6_U, 384
.set N6_SIZE, 488
LOCAL_FUNCTION crypto_bls_fp6_inverse
    ENTER   N6_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    F2MUL   %rsp, N6_T0, %rbp, 0, %rbp, 0           /* t0 */
    F2MUL   %rsp, N6_U, %rbp, 96, %rbp, 192
    F2NR    %rsp, N6_U, %rsp, N6_U
    F2SUB   %rsp, N6_T0, %rsp, N6_T0, %rsp, N6_U
    F2MUL   %rsp, N6_T1, %rbp, 192, %rbp, 192       /* t1 */
    F2NR    %rsp, N6_T1, %rsp, N6_T1
    F2MUL   %rsp, N6_U, %rbp, 0, %rbp, 96
    F2SUB   %rsp, N6_T1, %rsp, N6_T1, %rsp, N6_U
    F2MUL   %rsp, N6_T2, %rbp, 96, %rbp, 96         /* t2 */
    F2MUL   %rsp, N6_U, %rbp, 0, %rbp, 192
    F2SUB   %rsp, N6_T2, %rsp, N6_T2, %rsp, N6_U
    F2MUL   %rsp, N6_D, %rbp, 0, %rsp, N6_T0        /* det */
    F2MUL   %rsp, N6_U, %rbp, 192, %rsp, N6_T1
    F2NR    %rsp, N6_U, %rsp, N6_U
    F2ADD   %rsp, N6_D, %rsp, N6_D, %rsp, N6_U
    F2MUL   %rsp, N6_U, %rbp, 96, %rsp, N6_T2
    F2NR    %rsp, N6_U, %rsp, N6_U
    F2ADD   %rsp, N6_D, %rsp, N6_D, %rsp, N6_U
    C2      crypto_bls_fp2_inverse, %rsp, N6_D, %rsp, N6_D
    F2MUL   %rbx, 0, %rsp, N6_T0, %rsp, N6_D
    F2MUL   %rbx, 96, %rsp, N6_T1, %rsp, N6_D
    F2MUL   %rbx, 192, %rsp, N6_T2, %rsp, N6_D
    LEAVE   N6_SIZE
END_FUNCTION crypto_bls_fp6_inverse

/* ---------------------------------------------------------------- Fp12 (Fp12.lean) */

/*
 * crypto_bls_fp12_mul(result, a, b): a * b (Fp12.mul): t0 = a0 b0, t1 = a1
 * b1, c0 = t0 + v t1, c1 = (a0 + a1)(b0 + b1) - t0 - t1. result may be a or b.
 */
.set M12_T0, 0
.set M12_T1, 288
.set M12_SA, 576
.set M12_SB, 864
.set M12_SIZE, 1160
LOCAL_FUNCTION crypto_bls_fp12_mul
    ENTER   M12_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    F6MUL   %rsp, M12_T0, %rbp, 0, %r12, 0
    F6MUL   %rsp, M12_T1, %rbp, 288, %r12, 288
    F6ADD   %rsp, M12_SA, %rbp, 0, %rbp, 288
    F6ADD   %rsp, M12_SB, %r12, 0, %r12, 288
    F6MUL   %rsp, M12_SA, %rsp, M12_SA, %rsp, M12_SB
    F6SUB   %rsp, M12_SA, %rsp, M12_SA, %rsp, M12_T0
    F6SUB   %rsp, M12_SA, %rsp, M12_SA, %rsp, M12_T1
    C2      crypto_bls_fp6_mul_v, %rsp, M12_T1, %rsp, M12_T1
    F6ADD   %rbx, 0, %rsp, M12_T0, %rsp, M12_T1
    COPY    %rbx, 288, %rsp, M12_SA, 288
    LEAVE   M12_SIZE
END_FUNCTION crypto_bls_fp12_mul

/* crypto_bls_fp12_conjugate(result, a): (a0, -a1) (Fp12.conjugate). result may be a. */
LOCAL_FUNCTION crypto_bls_fp12_conjugate
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    COPY    %rbx, 0, %rbp, 0, 288
    C2      crypto_bls_fp6_neg, %rbx, 288, %rbp, 288
    LEAVE   8
END_FUNCTION crypto_bls_fp12_conjugate

/*
 * crypto_bls_fp12_inverse(result, a): (a0 / n, -a1 / n), n = a0^2 - v a1^2
 * (Fp12.inverse). result may be a.
 */
.set N12_N, 0
.set N12_U, 288
.set N12_SIZE, 584
LOCAL_FUNCTION crypto_bls_fp12_inverse
    ENTER   N12_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    F6MUL   %rsp, N12_N, %rbp, 0, %rbp, 0
    F6MUL   %rsp, N12_U, %rbp, 288, %rbp, 288
    C2      crypto_bls_fp6_mul_v, %rsp, N12_U, %rsp, N12_U
    F6SUB   %rsp, N12_N, %rsp, N12_N, %rsp, N12_U
    C2      crypto_bls_fp6_inverse, %rsp, N12_N, %rsp, N12_N
    F6MUL   %rsp, N12_U, %rbp, 288, %rsp, N12_N
    C2      crypto_bls_fp6_neg, %rbx, 288, %rsp, N12_U
    F6MUL   %rbx, 0, %rbp, 0, %rsp, N12_N
    LEAVE   N12_SIZE
END_FUNCTION crypto_bls_fp12_inverse

/*
 * crypto_bls_fp12_frobenius(result, a): a^p (Fp12.frobenius): conj(a_k)
 * g^k, with a_k the coefficient of w^k and g the frobeniusCoeff. result may
 * be a.
 */
.set FR_T, 0
.set FR_SIZE, 104
LOCAL_FUNCTION crypto_bls_fp12_frobenius
    ENTER   FR_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    lea     909f(%rip), %r12                /* g^0, ..., g^5 */
    xor     %r13d, %r13d                    /* component: offset in a, then power of g */
1:  lea     932f(%rip), %rax
    movzwl  (%rax,%r13,4), %r14d            /* offset of a_k in a */
    movzwl  2(%rax,%r13,4), %r15d           /* k */
    lea     (%rbp,%r14), %r8                /* conj: c0, then -c1 */
    COPY    %rsp, FR_T, %r8, 0, 48
    lea     FR_T + 48(%rsp), %rdi
    lea     48(%rbp,%r14), %rsi
    call    crypto_bls_fp_neg
    imul    $96, %r15, %rdx
    add     %r12, %rdx
    lea     (%rbx,%r14), %rdi
    lea     FR_T(%rsp), %rsi
    call    crypto_bls_fp2_mul
    add     $1, %r13
    cmp     $6, %r13
    jb      1b
    LEAVE   FR_SIZE
END_FUNCTION crypto_bls_fp12_frobenius

/*
 * crypto_bls_fp12_pow(result, base, exponent): base^e (Fp12.powNat), with e
 * the u64 at exponent, a public value. result must not be base.
 */
LOCAL_FUNCTION crypto_bls_fp12_pow
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     (%rdx), %r12
    SET_ONE %rbx, 0
    ZERO    %rbx, 48, 528
    test    %r12, %r12
    jz      9f
    bsr     %r12, %r13                      /* the top set bit */
1:  F12MUL  %rbx, 0, %rbx, 0, %rbx, 0
    mov     %r12, %rax
    mov     %r13d, %ecx
    shr     %cl, %rax
    test    $1, %al
    jz      2f
    F12MUL  %rbx, 0, %rbx, 0, %rbp, 0
2:  sub     $1, %r13
    jns     1b
9:  LEAVE   8
END_FUNCTION crypto_bls_fp12_pow

/* ---------------------------------------------------------------- Pairing (Pairing.lean) */

/* The line value c0 + c2 w^2 + c3 w^3 (lineValue) at rd + od, from the Fp2 values at rs + c0, c2 and c3. */
.macro LINE rd, od, rs, c0, c2, c3
    COPY    \rd, \od, \rs, \c0, 96
    COPY    \rd, \od + 96, \rs, \c2, 96
    ZERO    \rd, \od + 192, 192
    COPY    \rd, \od + 384, \rs, \c3, 96
    ZERO    \rd, \od + 480, 96
.endm

/*
 * crypto_bls_miller_double(f, t, p, work): millerDouble: with T the G2
 * point at t and P = (xp, yp) at p, f = f^2 l with l the tangent line at T,
 * then T = 2 T. work holds 1248 bytes: the line, then the temporaries.
 */
.set MD_XX, 576
.set MD_ZZ, 672
.set MD_A, 768
.set MD_C0, 864
.set MD_C2, 960
.set MD_C3, 1056
.set MD_U, 1152
LOCAL_FUNCTION crypto_bls_miller_double
    ENTER   8
    mov     %rdi, %rbx                      /* f */
    mov     %rsi, %rbp                      /* T */
    mov     %rdx, %r12                      /* P */
    mov     %rcx, %r13                      /* work */
    F2MUL   %r13, MD_XX, %rbp, 0, %rbp, 0   /* xx = X^2, zz = Z^2 */
    F2MUL   %r13, MD_ZZ, %rbp, 192, %rbp, 192
    F2ADD   %r13, MD_A, %r13, MD_XX, %r13, MD_XX    /* 3 xx */
    F2ADD   %r13, MD_A, %r13, MD_A, %r13, MD_XX
    F2MUL   %r13, MD_C0, %r13, MD_A, %rbp, 0        /* c0 = 3 xx X - 2 Y^2 */
    F2MUL   %r13, MD_U, %rbp, 96, %rbp, 96
    F2ADD   %r13, MD_U, %r13, MD_U, %r13, MD_U
    F2SUB   %r13, MD_C0, %r13, MD_C0, %r13, MD_U
    F2MUL   %r13, MD_C2, %r13, MD_A, %r13, MD_ZZ    /* c2 = -(3 xx zz xp) */
    C3      crypto_bls_fp2_mul_fp, %r13, MD_C2, %r13, MD_C2, %r12, 0
    C2      crypto_bls_fp2_neg, %r13, MD_C2, %r13, MD_C2
    F2ADD   %r13, MD_C3, %rbp, 96, %rbp, 96         /* c3 = 2 Y zz Z yp */
    F2MUL   %r13, MD_C3, %r13, MD_C3, %r13, MD_ZZ
    F2MUL   %r13, MD_C3, %r13, MD_C3, %rbp, 192
    C3      crypto_bls_fp2_mul_fp, %r13, MD_C3, %r13, MD_C3, %r12, 48
    C2      crypto_bls_g2_double, %rbp, 0, %rbp, 0
    F12MUL  %rbx, 0, %rbx, 0, %rbx, 0
    LINE    %r13, 0, %r13, MD_C0, MD_C2, MD_C3
    F12MUL  %rbx, 0, %rbx, 0, %r13, 0
    LEAVE   8
END_FUNCTION crypto_bls_miller_double

/*
 * crypto_bls_miller_add(f, t, q, p, work): millerAdd: with Q = (xq, yq) at
 * q, f = f l with l the line through T and Q, then T = T + Q. work holds
 * 1536 bytes: the line, Q in Jacobian coordinates, then the temporaries.
 */
.set MA_ZZ, 864
.set MA_N, 960
.set MA_D, 1056
.set MA_U, 1152
.set MA_C0, 1248
.set MA_C2, 1344
.set MA_C3, 1440
LOCAL_FUNCTION crypto_bls_miller_add
    ENTER   8
    mov     %rdi, %rbx                      /* f */
    mov     %rsi, %rbp                      /* T */
    mov     %rdx, %r12                      /* Q */
    mov     %rcx, %r13                      /* P */
    mov     %r8, %r14                       /* work */
    F2MUL   %r14, MA_ZZ, %rbp, 192, %rbp, 192       /* zz = Z^2 */
    F2MUL   %r14, MA_N, %r12, 96, %r14, MA_ZZ       /* n = yq zz Z - Y */
    F2MUL   %r14, MA_N, %r14, MA_N, %rbp, 192
    F2SUB   %r14, MA_N, %r14, MA_N, %rbp, 96
    F2MUL   %r14, MA_D, %r12, 0, %r14, MA_ZZ        /* d = (xq zz - X) Z */
    F2SUB   %r14, MA_D, %r14, MA_D, %rbp, 0
    F2MUL   %r14, MA_D, %r14, MA_D, %rbp, 192
    F2MUL   %r14, MA_C0, %r14, MA_N, %r12, 0        /* c0 = n xq - d yq */
    F2MUL   %r14, MA_U, %r14, MA_D, %r12, 96
    F2SUB   %r14, MA_C0, %r14, MA_C0, %r14, MA_U
    C3      crypto_bls_fp2_mul_fp, %r14, MA_C2, %r14, MA_N, %r13, 0  /* c2 = -(n xp) */
    C2      crypto_bls_fp2_neg, %r14, MA_C2, %r14, MA_C2
    C3      crypto_bls_fp2_mul_fp, %r14, MA_C3, %r14, MA_D, %r13, 48 /* c3 = d yp */
    COPY    %r14, 576, %r12, 0, 192         /* Q = (xq, yq, 1) */
    SET_ONE %r14, 768
    ZERO    %r14, 816, 48
    C3      crypto_bls_g2_add, %rbp, 0, %rbp, 0, %r14, 576
    LINE    %r14, 0, %r14, MA_C0, MA_C2, MA_C3
    F12MUL  %rbx, 0, %rbx, 0, %r14, 0
    LEAVE   8
END_FUNCTION crypto_bls_miller_add

/*
 * crypto_bls_miller_loop(f, q, p, work): millerLoop for |x|: T = Q, f = 1,
 * then for each bit of |x| below its top bit, a double step, and an add
 * step on a set bit. work holds 1824 bytes: T, then the work of the steps.
 */
LOCAL_FUNCTION crypto_bls_miller_loop
    ENTER   8
    mov     %rdi, %rbx                      /* f */
    mov     %rsi, %rbp                      /* Q */
    mov     %rdx, %r12                      /* P */
    mov     %rcx, %r13                      /* work: T at 0, step work at 288 */
    COPY    %r13, 0, %rbp, 0, 192           /* T = (xq, yq, 1) */
    SET_ONE %r13, 192
    ZERO    %r13, 240, 48
    SET_ONE %rbx, 0                         /* f = 1 */
    ZERO    %rbx, 48, 528
    mov     927f(%rip), %r14                /* |x| */
    mov     $62, %r15d                      /* bits 62 to 0; bit 63 is the top bit */
1:  mov     %rbx, %rdi
    mov     %r13, %rsi
    mov     %r12, %rdx
    lea     288(%r13), %rcx
    call    crypto_bls_miller_double
    mov     %r14, %rax
    mov     %r15d, %ecx
    shr     %cl, %rax
    test    $1, %al
    jz      2f
    mov     %rbx, %rdi
    mov     %r13, %rsi
    mov     %rbp, %rdx
    mov     %r12, %rcx
    lea     288(%r13), %r8
    call    crypto_bls_miller_add
2:  sub     $1, %r15
    jns     1b
    LEAVE   8
END_FUNCTION crypto_bls_miller_loop

/*
 * crypto_bls_final_exponentiation(result, f, work): f^((p^12 - 1) / r) by
 * the steps of finalExponentiation. work holds 3456 bytes. result is not in
 * work.
 */
.set FE_T, 0
.set FE_M, 576
.set FE_A, 1152
.set FE_B, 1728
.set FE_C, 2304
.set FE_U, 2880
LOCAL_FUNCTION crypto_bls_final_exponentiation
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12                      /* work */
    lea     927f(%rip), %r13                /* |x|, |x| + 1, (|x| + 1) / 3 */
    C2      crypto_bls_fp12_inverse, %r12, FE_U, %rbp, 0        /* t = conj(f) / f */
    C2      crypto_bls_fp12_conjugate, %r12, FE_T, %rbp, 0
    F12MUL  %r12, FE_T, %r12, FE_T, %r12, FE_U
    C2      crypto_bls_fp12_frobenius, %r12, FE_M, %r12, FE_T   /* m = frob(frob(t)) t */
    C2      crypto_bls_fp12_frobenius, %r12, FE_M, %r12, FE_M
    F12MUL  %r12, FE_M, %r12, FE_M, %r12, FE_T
    C3      crypto_bls_fp12_pow, %r12, FE_U, %r12, FE_M, %r13, 16   /* a = (m^((|x| + 1) / 3))^(|x| + 1) */
    C3      crypto_bls_fp12_pow, %r12, FE_A, %r12, FE_U, %r13, 8
    C3      crypto_bls_fp12_pow, %r12, FE_U, %r12, FE_A, %r13, 0    /* b = frob(a) conj(a^|x|) */
    C2      crypto_bls_fp12_conjugate, %r12, FE_U, %r12, FE_U
    C2      crypto_bls_fp12_frobenius, %r12, FE_B, %r12, FE_A
    F12MUL  %r12, FE_B, %r12, FE_B, %r12, FE_U
    C3      crypto_bls_fp12_pow, %r12, FE_U, %r12, FE_B, %r13, 0    /* c = (b^|x|)^|x| frob(frob(b)) conj(b) */
    C3      crypto_bls_fp12_pow, %r12, FE_C, %r12, FE_U, %r13, 0
    C2      crypto_bls_fp12_frobenius, %r12, FE_U, %r12, FE_B
    C2      crypto_bls_fp12_frobenius, %r12, FE_U, %r12, FE_U
    F12MUL  %r12, FE_C, %r12, FE_C, %r12, FE_U
    C2      crypto_bls_fp12_conjugate, %r12, FE_U, %r12, FE_B
    F12MUL  %r12, FE_C, %r12, FE_C, %r12, FE_U
    F12MUL  %rbx, 0, %r12, FE_C, %r12, FE_M /* c m */
    LEAVE   8
END_FUNCTION crypto_bls_final_exponentiation

/*
 * crypto_bls_pairing_check(pairs, work, valid): pairingCheck: the u64 1 when
 * the product of e(P_i, Q_i) is 1, else 0. pairs holds a u64 count, then the
 * pairs, each a G1 point and a G2 point (432 bytes). A pair with a point at
 * infinity counts as 1. work holds 4608 bytes.
 */
.set PC_ACC, 0
.set PC_F, 576
.set PC_PA, 1152
.set PC_QA, 1248
.set PC_ML, 1440
.set PC_R, 576
.set PC_FE, 1152
LOCAL_FUNCTION crypto_bls_pairing_check
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp                      /* work */
    mov     %rdx, %r12                      /* valid */
    mov     (%rbx), %r13                    /* count */
    lea     8(%rbx), %r14                   /* the first pair */
    SET_ONE %rbp, PC_ACC
    ZERO    %rbp, PC_ACC + 48, 528
    test    %r13, %r13
    jz      3f
1:  IS_ZERO %r14, 96, 48                    /* skip a point at infinity */
    jz      2f
    IS_ZERO %r14, 144 + 192, 96
    jz      2f
    C2      crypto_bls_g1_affine, %rbp, PC_PA, %r14, 0
    C2      crypto_bls_g2_affine, %rbp, PC_QA, %r14, 144
    lea     PC_F(%rbp), %rdi
    lea     PC_QA(%rbp), %rsi
    lea     PC_PA(%rbp), %rdx
    lea     PC_ML(%rbp), %rcx
    call    crypto_bls_miller_loop
    C2      crypto_bls_fp12_conjugate, %rbp, PC_F, %rbp, PC_F
    F12MUL  %rbp, PC_ACC, %rbp, PC_ACC, %rbp, PC_F
2:  add     $432, %r14
    sub     $1, %r13
    jnz     1b
3:  C3      crypto_bls_final_exponentiation, %rbp, PC_R, %rbp, PC_ACC, %rbp, PC_FE
    lea     900f+BLS_FP_RECORD_ONE(%rip), %r9       /* is it 1? */
    EQUAL   %rbp, PC_R, %r9, 0, 48
    jnz     4f
    IS_ZERO %rbp, PC_R + 48, 528
4:  setz    %al
    movzbl  %al, %eax
    mov     %rax, (%r12)
    LEAVE   8
END_FUNCTION crypto_bls_pairing_check

/* ---------------------------------------------------------------- Verification (Signatures.lean) */

/*
 * crypto_bls_core_verify(public_key, message, signature, work, valid):
 * coreVerify with the DST: the u64 1 when the signature decompresses into
 * G2, the key passes KeyValidate, and e(P, R) e(-PK, H(message)) = 1, else
 * 0. work: the 2 pairs (880 bytes), then the hash work or the pairing work.
 */
.set CV_PAIRS, 0
.set CV_G1A, 8
.set CV_G2A, 152
.set CV_G1B, 440
.set CV_G2B, 584
.set CV_AREA, 880
.set CV_V, 0
.set CV_SIZE, 24
LOCAL_FUNCTION crypto_bls_core_verify
    ENTER   CV_SIZE
    mov     %rdi, %rbx                      /* public_key */
    mov     %rsi, %rbp                      /* message */
    mov     %rdx, %r12                      /* signature */
    mov     %rcx, %r13                      /* work */
    mov     %r8, %r14                       /* valid */
    movq    $0, (%r14)
    mov     %r12, %rdi                      /* R: decompress, subgroup check */
    lea     CV_G2A(%r13), %rsi
    call    crypto_bls_g2_uncompress
    test    %rax, %rax
    jnz     9f
    C2      crypto_bls_g2_in_subgroup, %r13, CV_G2A, %rsp, CV_V
    cmpq    $0, CV_V(%rsp)
    je      9f
    mov     %rbx, %rdi                      /* PK: KeyValidate */
    lea     CV_G1B(%r13), %rsi
    call    crypto_bls_key_validate_point
    test    %rax, %rax
    jnz     9f
    G2      crypto_bls_g1_neg, %r13, CV_G1B, %r13, CV_G1B
    mov     %rbp, %rdi                      /* Q = H(message) */
    lea     931f(%rip), %rsi
    lea     CV_AREA(%r13), %rdx
    lea     CV_G2B(%r13), %rcx
    call    crypto_bls_hash_to_g2_point
    test    %rax, %rax
    jnz     9f
    lea     904f(%rip), %r15                /* P: the generator of G1 */
    COPY    %r13, CV_G1A, %r15, 0, 96
    SET_ONE %r13, CV_G1A + 96
    movq    $2, CV_PAIRS(%r13)
    mov     %r13, %rdi
    lea     CV_AREA(%r13), %rsi
    mov     %r14, %rdx
    call    crypto_bls_pairing_check
9:  LEAVE   CV_SIZE
END_FUNCTION crypto_bls_core_verify

/* Jump to label when the scratch at rs is smaller than CRYPTO_BLS_SCRATCH + count of the message at rm. Uses rax. */
.macro SCRATCH_CHECK rs, rm, label
    mov     CRYPTO_BYTES_COUNT(\rm), %rax
    add     $CRYPTO_BLS_SCRATCH, %rax
    cmp     %rax, (\rs)
    jb      \label
.endm

/* crypto_bls_verify(public_key, message, signature, scratch, valid) -> status: verify. */
FUNCTION crypto_bls_verify
    ENTER   8
    SCRATCH_CHECK %rcx, %rsi, 8f
    add     $8, %rcx
    call    crypto_bls_core_verify
    mov     $CRYPTO_OK, %eax
    LEAVE   8
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   8
END_FUNCTION crypto_bls_verify

/*
 * crypto_bls_fast_verify(public_keys, message, signature, work, valid):
 * fastAggregateVerify: 0 for an empty list or a key that fails KeyValidate,
 * else crypto_bls_core_verify of the compressed sum of the keys. The sum
 * and its compressed form sit in work at 5488, after the area of
 * crypto_bls_core_verify.
 */
.set FV_AREA, 5488
.set FV_P, 0
.set FV_K, 144
LOCAL_FUNCTION crypto_bls_fast_verify
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     %r8, %r14
    movq    $0, (%r14)
    lea     FV_AREA(%r13), %r15             /* the sum, in work after the area of core_verify */
    mov     %rbx, %rdi
    lea     FV_P(%r15), %rsi
    call    crypto_bls_aggregate_keys
    test    %rax, %rax
    jnz     9f
    G2      crypto_bls_g1_compress, %r15, FV_P, %r15, FV_K
    lea     FV_K(%r15), %rdi
    mov     %rbp, %rsi
    mov     %r12, %rdx
    mov     %r13, %rcx
    mov     %r14, %r8
    call    crypto_bls_core_verify
9:  LEAVE   8
END_FUNCTION crypto_bls_fast_verify

/* crypto_bls_fast_aggregate_verify(public_keys, message, signature, scratch, valid) -> status: fastAggregateVerify. */
FUNCTION crypto_bls_fast_aggregate_verify
    ENTER   8
    SCRATCH_CHECK %rcx, %rsi, 8f
    add     $8, %rcx
    call    crypto_bls_fast_verify
    mov     $CRYPTO_OK, %eax
    LEAVE   8
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   8
END_FUNCTION crypto_bls_fast_aggregate_verify

/*
 * crypto_bls_eth_fast_aggregate_verify(public_keys, message, signature,
 * scratch, valid) -> status: ethFastAggregateVerify.
 */
FUNCTION crypto_bls_eth_fast_aggregate_verify
    ENTER   8
    SCRATCH_CHECK %rcx, %rsi, 8f
    cmpq    $0, CRYPTO_BLS_LIST_COUNT(%rdi)
    je      1f
    add     $8, %rcx
    call    crypto_bls_fast_verify
    mov     $CRYPTO_OK, %eax
    LEAVE   8
1:  cmpb    $0xC0, (%rdx)                   /* no key: 1 exactly for 0xC0 then 95 zero bytes */
    jne     2f
    TAIL_ZERO %rdx, 96
2:  sete    %al
    movzbl  %al, %eax
    mov     %rax, (%r8)
    mov     $CRYPTO_OK, %eax
    LEAVE   8
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   8
END_FUNCTION crypto_bls_eth_fast_aggregate_verify

/*
 * crypto_bls_core_verify_point(point, message, signature, work, valid):
 * crypto_bls_core_verify with the key as a point of G1 that is not the point
 * at infinity: the u64 1 when the signature decompresses into G2 and
 * e(P, R) e(-point, H(message)) = 1, else 0. work as for crypto_bls_core_verify.
 */
LOCAL_FUNCTION crypto_bls_core_verify_point
    ENTER   CV_SIZE
    mov     %rdi, %rbx                      /* point */
    mov     %rsi, %rbp                      /* message */
    mov     %rdx, %r12                      /* signature */
    mov     %rcx, %r13                      /* work */
    mov     %r8, %r14                       /* valid */
    movq    $0, (%r14)
    mov     %r12, %rdi                      /* R: decompress, subgroup check */
    lea     CV_G2A(%r13), %rsi
    call    crypto_bls_g2_uncompress
    test    %rax, %rax
    jnz     9f
    C2      crypto_bls_g2_in_subgroup, %r13, CV_G2A, %rsp, CV_V
    cmpq    $0, CV_V(%rsp)
    je      9f
    COPY    %r13, CV_G1B, %rbx, 0, 144      /* -point */
    G2      crypto_bls_g1_neg, %r13, CV_G1B, %r13, CV_G1B
    mov     %rbp, %rdi                      /* Q = H(message) */
    lea     931f(%rip), %rsi
    lea     CV_AREA(%r13), %rdx
    lea     CV_G2B(%r13), %rcx
    call    crypto_bls_hash_to_g2_point
    test    %rax, %rax
    jnz     9f
    lea     904f(%rip), %r15                /* P: the generator of G1 */
    COPY    %r13, CV_G1A, %r15, 0, 96
    SET_ONE %r13, CV_G1A + 96
    movq    $2, CV_PAIRS(%r13)
    mov     %r13, %rdi
    lea     CV_AREA(%r13), %rsi
    mov     %r14, %rdx
    call    crypto_bls_pairing_check
9:  LEAVE   CV_SIZE
END_FUNCTION crypto_bls_core_verify_point

/*
 * crypto_bls_fast_aggregate_verify_cached(keys, indices, cache, message,
 * signature, scratch, valid) -> status: fastAggregateVerify of the keys at
 * the indices, each key checked once through its cache entry. valid is the
 * 7th argument, on the stack.
 * rbx keys, rbp the next index, r12 cache, r13 work, r14 key i, r15 entry i.
 * Stack: the sum (G1Point) at 0, a point (G1Point) at 144, then message,
 * signature, valid and the indices left.
 */
.set FC_ACC, 0
.set FC_P, 144
.set FC_MSG, 288
.set FC_SIG, 296
.set FC_VALID, 304
.set FC_LEFT, 312
.set FC_SIZE, 328
FUNCTION crypto_bls_fast_aggregate_verify_cached
    ENTER   FC_SIZE
    SCRATCH_CHECK %r9, %rcx, 8f
    mov     %rdi, %rbx
    mov     %rdx, %r12
    lea     8(%r9), %r13
    mov     %rcx, FC_MSG(%rsp)
    mov     %r8, FC_SIG(%rsp)
    mov     (FC_SIZE + 56)(%rsp), %rax      /* valid: past the 6 saved registers and the return address */
    mov     %rax, FC_VALID(%rsp)
    movq    $0, (%rax)
    mov     CRYPTO_BLS_LIST_COUNT(%rsi), %rax
    test    %rax, %rax
    jz      9f                              /* no index: 0 */
    mov     %rax, FC_LEFT(%rsp)
    mov     CRYPTO_BLS_LIST_OFFSET(%rsi), %rbp
    add     %rsi, %rbp
    SET_ONE %rsp, FC_ACC                    /* the sum: the point at infinity */
    SET_ONE %rsp, FC_ACC + 48
    ZERO    %rsp, FC_ACC + 96, 48
1:  mov     (%rbp), %rax                    /* index i */
    add     $8, %rbp
    cmp     CRYPTO_BLS_CACHE_COUNT(%r12), %rax
    jae     9f                              /* at or past count: 0 */
    mov     %rax, %r14
    imul    CRYPTO_BLS_CACHE_KEY_STRIDE(%r12), %r14
    add     %rbx, %r14
    imul    $CRYPTO_BLS_ENTRY_BYTES, %rax, %r15
    add     CRYPTO_BLS_CACHE_OFFSET(%r12), %r15
    add     %r12, %r15
    cmpq    $0, CRYPTO_BLS_ENTRY_STATUS(%r15)
    je      3f                              /* empty: check the key */
    EQUAL   %r15, CRYPTO_BLS_ENTRY_KEY, %r14, 0, 48
    jnz     3f                              /* the entry of another key: check this one */
    cmpq    $2, CRYPTO_BLS_ENTRY_STATUS(%r15)
    je      9f                              /* a key that fails KeyValidate: 0 */
    COPY    %rsp, FC_P, %r15, CRYPTO_BLS_ENTRY_POINT, 96
    SET_ONE %rsp, FC_P + 96
    jmp     4f
3:  mov     %r14, %rdi                      /* KeyValidate, then the entry */
    lea     FC_P(%rsp), %rsi
    call    crypto_bls_key_validate_point
    mov     %rax, %r8
    COPY    %r15, CRYPTO_BLS_ENTRY_KEY, %r14, 0, 48
    test    %r8, %r8
    jnz     32f
    COPY    %r15, CRYPTO_BLS_ENTRY_POINT, %rsp, FC_P, 96
    movq    $1, CRYPTO_BLS_ENTRY_STATUS(%r15)
    jmp     4f
32: movq    $2, CRYPTO_BLS_ENTRY_STATUS(%r15)
    jmp     9f
4:  G3      crypto_bls_g1_add, %rsp, FC_ACC, %rsp, FC_P, %rsp, FC_ACC
    subq    $1, FC_LEFT(%rsp)
    jnz     1b
    IS_ZERO %rsp, FC_ACC + 96, 48           /* the sum at infinity: 0 */
    jz      9f
    lea     FC_ACC(%rsp), %rdi
    mov     FC_MSG(%rsp), %rsi
    mov     FC_SIG(%rsp), %rdx
    mov     %r13, %rcx
    mov     FC_VALID(%rsp), %r8
    call    crypto_bls_core_verify_point
9:  mov     $CRYPTO_OK, %eax
    LEAVE   FC_SIZE
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   FC_SIZE
END_FUNCTION crypto_bls_fast_aggregate_verify_cached

/* ---------------------------------------------------------------- Fr (Bls/Fr.lean), for KZG */

.macro RMUL ra, oa, rb, ob, rc, oc
    C3      crypto_kzg_fr_mul, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro RADD ra, oa, rb, ob, rc, oc
    C3      crypto_kzg_fr_add, \ra, \oa, \rb, \ob, \rc, \oc
.endm
.macro RSUB ra, oa, rb, ob, rc, oc
    C3      crypto_kzg_fr_sub, \ra, \oa, \rb, \ob, \rc, \oc
.endm

/* The Fr element 1 (Montgomery form) at od(rd). Uses rax, rcx, rdx. */
.macro SET_FR_ONE rd, od
    lea     940f+KZG_FR_RECORD_ONE(%rip), %rcx
    lea     \od(\rd), %rdx
    .irp i, 0, 8, 16, 24
    mov     \i(%rcx), %rax
    mov     %rax, \i(%rdx)
    .endr
.endm

/* The point at infinity of G1, (1, 1, 0), at od(rd). Uses rax, rcx, rdx. */
.macro G1_ZERO rd, od
    SET_ONE \rd, \od
    SET_ONE \rd, \od + 48
    ZERO    \rd, \od + 96, 48
.endm

/*
 * crypto_kzg_fr_mul(result, a, b): a * b / 2^256 mod r, for a < 2^256 and
 * b < r (CIOS). result may be a or b. rsi a, rbx b, T r8 to r13, b_i and q
 * rcx, rbp the carry limb; result is kept on the stack.
 */
LOCAL_FUNCTION crypto_kzg_fr_mul
    push    %rbx
    UNWIND_PUSH %rbx
    push    %rbp
    UNWIND_PUSH %rbp
    push    %r12
    UNWIND_PUSH %r12
    push    %r13
    UNWIND_PUSH %r13
    push    %rdi
    UNWIND_PUSH %rdi
    UNWIND_END_PROLOGUE
    mov     %rdx, %rbx
    xor     %r8d, %r8d
    xor     %r9d, %r9d
    xor     %r10d, %r10d
    xor     %r11d, %r11d
    xor     %r12d, %r12d
    .irp off, 0, 8, 16, 24
    xor     %r13d, %r13d
    mov     \off(%rbx), %rcx                /* T += a * b_i */
    mov     (%rsi), %rax
    mul     %rcx
    add     %rax, %r8
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     8(%rsi), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %rax, %r9
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     16(%rsi), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %rax, %r10
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     24(%rsi), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %rax, %r11
    adc     $0, %rdx
    add     %rdx, %r12
    adc     $0, %r13
    mov     %r8, %rcx                       /* q = T0 * -r^-1 mod 2^64 */
    imul    940f+KZG_FR_RECORD_INVERSE(%rip), %rcx
    mov     940f(%rip), %rax                /* T = (T + q * r) / 2^64 */
    mul     %rcx
    add     %rax, %r8
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     940f+8(%rip), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %r9, %rax
    adc     $0, %rdx
    mov     %rax, %r8
    mov     %rdx, %rbp
    mov     940f+16(%rip), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %r10, %rax
    adc     $0, %rdx
    mov     %rax, %r9
    mov     %rdx, %rbp
    mov     940f+24(%rip), %rax
    mul     %rcx
    add     %rbp, %rax
    adc     $0, %rdx
    add     %r11, %rax
    adc     $0, %rdx
    mov     %rax, %r10
    mov     %r12, %r11
    add     %rdx, %r11
    adc     $0, %r13
    mov     %r13, %r12
    .endr
    mov     %r8, %rax                       /* T - r when T >= r */
    sub     940f(%rip), %rax
    mov     %r9, %rcx
    sbb     940f+8(%rip), %rcx
    mov     %r10, %rdx
    sbb     940f+16(%rip), %rdx
    mov     %r11, %rsi
    sbb     940f+24(%rip), %rsi
    sbb     $0, %r12
    cmovae  %rax, %r8
    cmovae  %rcx, %r9
    cmovae  %rdx, %r10
    cmovae  %rsi, %r11
    mov     (%rsp), %rdi                    /* result */
    mov     %r8, (%rdi)
    mov     %r9, 8(%rdi)
    mov     %r10, 16(%rdi)
    mov     %r11, 24(%rdi)
    UNWIND_BEGIN_EPILOGUE
    pop     %rdi
    UNWIND_POP %rdi
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
END_FUNCTION crypto_kzg_fr_mul

/* crypto_kzg_fr_add(result, a, b): a + b mod r, for a, b < r. result may be a or b. A leaf. */
LOCAL_FUNCTION crypto_kzg_fr_add
    UNWIND_END_PROLOGUE
    mov     (%rsi), %rax
    mov     8(%rsi), %rcx
    mov     16(%rsi), %r8
    mov     24(%rsi), %r9
    add     (%rdx), %rax
    adc     8(%rdx), %rcx
    adc     16(%rdx), %r8
    adc     24(%rdx), %r9
    sbb     %rsi, %rsi                      /* -1 on a carry out */
    mov     %rax, (%rdi)                    /* the sum, then the sum - r when it is r or more */
    mov     %rcx, 8(%rdi)
    mov     %r8, 16(%rdi)
    mov     %r9, 24(%rdi)
    sub     940f(%rip), %rax
    sbb     940f+8(%rip), %rcx
    sbb     940f+16(%rip), %r8
    sbb     940f+24(%rip), %r9
    sbb     $0, %rsi                        /* borrow when sum < r and no carry out */
    jc      1f
    mov     %rax, (%rdi)
    mov     %rcx, 8(%rdi)
    mov     %r8, 16(%rdi)
    mov     %r9, 24(%rdi)
1:  ret
END_FUNCTION crypto_kzg_fr_add

/* crypto_kzg_fr_sub(result, a, b): a - b mod r, for a, b < r. result may be a or b. A leaf. */
LOCAL_FUNCTION crypto_kzg_fr_sub
    UNWIND_END_PROLOGUE
    mov     (%rsi), %rax
    mov     8(%rsi), %rcx
    mov     16(%rsi), %r8
    mov     24(%rsi), %r9
    sub     (%rdx), %rax
    sbb     8(%rdx), %rcx
    sbb     16(%rdx), %r8
    sbb     24(%rdx), %r9
    jnc     1f
    add     940f(%rip), %rax                /* a borrow: add r */
    adc     940f+8(%rip), %rcx
    adc     940f+16(%rip), %r8
    adc     940f+24(%rip), %r9
1:  mov     %rax, (%rdi)
    mov     %rcx, 8(%rdi)
    mov     %r8, 16(%rdi)
    mov     %r9, 24(%rdi)
    ret
END_FUNCTION crypto_kzg_fr_sub

/* crypto_kzg_fr_neg(result, a): -a mod r, for a < r; 0 stays 0. result may be a. A leaf. */
LOCAL_FUNCTION crypto_kzg_fr_neg
    UNWIND_END_PROLOGUE
    mov     (%rsi), %rax
    or      8(%rsi), %rax
    or      16(%rsi), %rax
    or      24(%rsi), %rax
    jz      1f
    mov     940f(%rip), %rax
    mov     940f+8(%rip), %rcx
    mov     940f+16(%rip), %r8
    mov     940f+24(%rip), %r9
    sub     (%rsi), %rax
    sbb     8(%rsi), %rcx
    sbb     16(%rsi), %r8
    sbb     24(%rsi), %r9
    mov     %rax, (%rdi)
    mov     %rcx, 8(%rdi)
    mov     %r8, 16(%rdi)
    mov     %r9, 24(%rdi)
    ret
1:  mov     %rax, (%rdi)                    /* rax is 0 */
    mov     %rax, 8(%rdi)
    mov     %rax, 16(%rdi)
    mov     %rax, 24(%rdi)
    ret
END_FUNCTION crypto_kzg_fr_neg

/*
 * crypto_kzg_fr_pow(result, base, exponent): base^e (Fr.powNat), with e the
 * 4 little-endian limbs at exponent, a public value. result may be base.
 */
.set RW_ACC, 0
.set RW_BASE, 32
.set RW_SIZE, 72
LOCAL_FUNCTION crypto_kzg_fr_pow
    ENTER   RW_SIZE
    mov     %rdi, %rbx
    mov     %rdx, %rbp
    COPY    %rsp, RW_BASE, %rsi, 0, 32
    SET_FR_ONE %rsp, RW_ACC
    mov     $255, %r12d                     /* bit index */
1:  mov     %r12, %rcx                      /* skip the zero bits above the top set bit */
    shr     $6, %rcx
    mov     (%rbp,%rcx,8), %rax
    mov     %r12, %rcx
    shr     %cl, %rax
    test    $1, %al
    jnz     2f
    sub     $1, %r12
    jns     1b
    jmp     4f
2:  RMUL    %rsp, RW_ACC, %rsp, RW_ACC, %rsp, RW_ACC
    mov     %r12, %rcx
    shr     $6, %rcx
    mov     (%rbp,%rcx,8), %rax
    mov     %r12, %rcx
    shr     %cl, %rax
    test    $1, %al
    jz      3f
    RMUL    %rsp, RW_ACC, %rsp, RW_ACC, %rsp, RW_BASE
3:  sub     $1, %r12
    jns     2b
4:  COPY    %rbx, 0, %rsp, RW_ACC, 32
    LEAVE   RW_SIZE
END_FUNCTION crypto_kzg_fr_pow

/* crypto_kzg_fr_inverse(result, a): a^(r - 2) (Fr.inverse); 0 gives 0. result may be a. */
LOCAL_FUNCTION crypto_kzg_fr_inverse
    ENTER   8
    lea     941f(%rip), %rdx
    call    crypto_kzg_fr_pow
    LEAVE   8
END_FUNCTION crypto_kzg_fr_inverse

/*
 * crypto_kzg_fr_from_bytes(result, bytes) -> status: the 32 big-endian bytes
 * as an element of Fr (Fr.fromBytesBE, bytesToBlsField).
 * CRYPTO_INVALID_ENCODING when the number is r or more; nothing is written.
 */
.set RB_N, 0
.set RB_SIZE, 40
LOCAL_FUNCTION crypto_kzg_fr_from_bytes
    ENTER   RB_SIZE
    mov     %rdi, %rbx
    .irp i, 0, 1, 2, 3
    mov     24-8*\i(%rsi), %rax
    bswap   %rax
    mov     %rax, RB_N+8*\i(%rsp)
    .endr
    mov     RB_N(%rsp), %rax                /* below r? */
    sub     940f(%rip), %rax
    mov     RB_N+8(%rsp), %rax
    sbb     940f+8(%rip), %rax
    mov     RB_N+16(%rsp), %rax
    sbb     940f+16(%rip), %rax
    mov     RB_N+24(%rsp), %rax
    sbb     940f+24(%rip), %rax
    jnc     9f
    mov     %rbx, %rdi                      /* result = n * 2^512 / 2^256 */
    lea     RB_N(%rsp), %rsi
    lea     940f+KZG_FR_RECORD_R2(%rip), %rdx
    call    crypto_kzg_fr_mul
    mov     $CRYPTO_OK, %eax
    LEAVE   RB_SIZE
9:  mov     $CRYPTO_INVALID_ENCODING, %eax
    LEAVE   RB_SIZE
END_FUNCTION crypto_kzg_fr_from_bytes

/*
 * crypto_kzg_fr_from_digest(result, bytes): the 32 big-endian bytes, a
 * number n below 2^256, as n mod r (Fr.ofNat in hashToBlsField).
 */
LOCAL_FUNCTION crypto_kzg_fr_from_digest
    ENTER   RB_SIZE
    .irp i, 0, 1, 2, 3
    mov     24-8*\i(%rsi), %rax
    bswap   %rax
    mov     %rax, RB_N+8*\i(%rsp)
    .endr
    lea     RB_N(%rsp), %rsi                /* n * 2^512 / 2^256, with n < 2^256 */
    lea     940f+KZG_FR_RECORD_R2(%rip), %rdx
    call    crypto_kzg_fr_mul
    LEAVE   RB_SIZE
END_FUNCTION crypto_kzg_fr_from_digest

/* crypto_kzg_fr_from_u64(result, value): the u64 value in rsi as an element of Fr (Fr.ofNat). */
LOCAL_FUNCTION crypto_kzg_fr_from_u64
    ENTER   RB_SIZE
    mov     %rsi, RB_N(%rsp)
    xor     %eax, %eax
    mov     %rax, RB_N+8(%rsp)
    mov     %rax, RB_N+16(%rsp)
    mov     %rax, RB_N+24(%rsp)
    lea     RB_N(%rsp), %rsi
    lea     940f+KZG_FR_RECORD_R2(%rip), %rdx
    call    crypto_kzg_fr_mul
    LEAVE   RB_SIZE
END_FUNCTION crypto_kzg_fr_from_u64

/* crypto_kzg_fr_canonical(result, a): the value of a (Fr.val) as 4 little-endian limbs. result may be a. */
LOCAL_FUNCTION crypto_kzg_fr_canonical
    ENTER   RB_SIZE
    xor     %eax, %eax
    mov     %rax, RB_N+8(%rsp)
    mov     %rax, RB_N+16(%rsp)
    mov     %rax, RB_N+24(%rsp)
    add     $1, %eax
    mov     %rax, RB_N(%rsp)
    lea     RB_N(%rsp), %rdx                /* a * 1 / 2^256 */
    call    crypto_kzg_fr_mul
    LEAVE   RB_SIZE
END_FUNCTION crypto_kzg_fr_canonical

/* crypto_kzg_fr_to_bytes(bytes, a): the 32 big-endian bytes of a (blsFieldToBytes). */
LOCAL_FUNCTION crypto_kzg_fr_to_bytes
    ENTER   RB_SIZE
    mov     %rdi, %rbx
    lea     RB_N(%rsp), %rdi
    call    crypto_kzg_fr_canonical
    .irp i, 0, 1, 2, 3
    mov     RB_N+8*\i(%rsp), %rax
    bswap   %rax
    mov     %rax, 24-8*\i(%rbx)
    .endr
    LEAVE   RB_SIZE
END_FUNCTION crypto_kzg_fr_to_bytes

/* ---------------------------------------------------------------- Roots of unity, bit reversal, FFT (Kzg) */

/*
 * crypto_kzg_roots_of_unity(roots, order): the powers 1, w, ..., w^(order - 1)
 * of w = 7^((r - 1) / order) (computeRootsOfUnity), for order a power of two
 * from 2 to 2^32, in rsi.
 */
.set RU_E, 0
.set RU_W, 32
.set RU_SIZE, 72
LOCAL_FUNCTION crypto_kzg_roots_of_unity
    ENTER   RU_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    bsr     %rbp, %rcx                      /* k = log2 order; e = (r - 1) >> k */
    mov     942f(%rip), %r8
    mov     942f+8(%rip), %r9
    mov     942f+16(%rip), %r10
    mov     942f+24(%rip), %r11
    shrd    %cl, %r9, %r8
    shrd    %cl, %r10, %r9
    shrd    %cl, %r11, %r10
    shr     %cl, %r11
    mov     %r8, RU_E(%rsp)
    mov     %r9, RU_E+8(%rsp)
    mov     %r10, RU_E+16(%rsp)
    mov     %r11, RU_E+24(%rsp)
    lea     RU_W(%rsp), %rdi                /* w = 7^e */
    mov     $7, %esi
    call    crypto_kzg_fr_from_u64
    C3      crypto_kzg_fr_pow, %rsp, RU_W, %rsp, RU_W, %rsp, RU_E
    SET_FR_ONE %rbx, 0                      /* computePowers */
    mov     $1, %r12d
1:  cmp     %rbp, %r12
    jae     9f
    mov     %r12, %rdi
    shl     $5, %rdi
    add     %rbx, %rdi
    lea     -32(%rdi), %rsi
    lea     RU_W(%rsp), %rdx
    call    crypto_kzg_fr_mul
    add     $1, %r12
    jmp     1b
9:  LEAVE   RU_SIZE
END_FUNCTION crypto_kzg_roots_of_unity

/*
 * crypto_kzg_bit_reversal(array, n, size): the bit-reversal permutation
 * (bitReversalPermutation) of the n entries of size bytes at array, in
 * place: entry i swaps with entry rev(i), with rev the reversal of log2 n
 * bits (reverseBits). n is a power of two from 2 up, in rsi; size is a
 * multiple of 8, in rdx.
 */
LOCAL_FUNCTION crypto_kzg_bit_reversal
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    bsr     %rbp, %r13                      /* log2 n */
    xor     %r14d, %r14d                    /* i */
1:  mov     %r14, %rax                      /* j = rev(i): reverseBitsAux */
    xor     %r15d, %r15d
    mov     %r13, %rcx
2:  test    %rcx, %rcx
    jz      3f
    shl     $1, %r15
    mov     %rax, %rdx
    and     $1, %edx
    or      %rdx, %r15
    shr     $1, %rax
    sub     $1, %rcx
    jmp     2b
3:  cmp     %r15, %r14
    jae     5f
    mov     %r14, %rsi                      /* swap entries i and j */
    imul    %r12, %rsi
    add     %rbx, %rsi
    mov     %r15, %rdi
    imul    %r12, %rdi
    add     %rbx, %rdi
    mov     %r12, %rcx
4:  mov     (%rsi), %rax
    mov     (%rdi), %rdx
    mov     %rdx, (%rsi)
    mov     %rax, (%rdi)
    add     $8, %rsi
    add     $8, %rdi
    sub     $8, %rcx
    jnz     4b
5:  add     $1, %r14
    cmp     %rbp, %r14
    jb      1b
    LEAVE   8
END_FUNCTION crypto_kzg_bit_reversal

/*
 * crypto_kzg_fft(vals, n, roots, inverse): the FFT of the n values at vals,
 * in place (fftField): the bit-reversal permutation, then the stages of
 * fftStages, each pair r < h of a block of 2 h values with the root at m r,
 * for m = n / (2 h). With inverse 1, root i is root (n - i) mod n and each
 * value is divided by n. n (a power of two) and inverse are in rsi and rcx;
 * roots holds the n-th roots of unity.
 */
.set KF_T, 0
.set KF_J, 32
.set KF_I1, 40
.set KF_I2, 48
.set KF_SIZE, 56
LOCAL_FUNCTION crypto_kzg_fft
    ENTER   KF_SIZE
    mov     %rdi, %rbx                      /* vals */
    mov     %rsi, %rbp                      /* n */
    mov     %rdx, %r12                      /* roots */
    mov     %rcx, %r13                      /* inverse */
    mov     $32, %edx
    call    crypto_kzg_bit_reversal
    xor     %r14d, %r14d                    /* log2 h */
    mov     %rbp, %r15                      /* m */
    shr     $1, %r15
1:  test    %r15, %r15
    jz      5f
    movq    $0, KF_J(%rsp)                  /* pair j < n / 2 */
2:  mov     KF_J(%rsp), %rax
    mov     %r14, %rcx
    mov     %rax, %r9
    shr     %cl, %r9                        /* block b */
    mov     $1, %r8d
    shl     %cl, %r8                        /* h */
    lea     -1(%r8), %r10
    and     %rax, %r10                      /* r = j mod h */
    add     $1, %ecx
    shl     %cl, %r9
    add     %r10, %r9                       /* i1 = 2 h b + r */
    lea     (%r9,%r8), %r11                 /* i2 = i1 + h */
    shl     $5, %r9
    add     %rbx, %r9
    mov     %r9, KF_I1(%rsp)
    shl     $5, %r11
    add     %rbx, %r11
    mov     %r11, KF_I2(%rsp)
    mov     %r15, %rax                      /* root index m r, or (n - m r) mod n */
    imul    %r10, %rax
    test    %r13, %r13
    jz      3f
    mov     %rbp, %rcx
    sub     %rax, %rcx
    lea     -1(%rbp), %rax
    and     %rcx, %rax
3:  shl     $5, %rax                        /* t = x[i2] * root */
    lea     (%r12,%rax), %rdx
    lea     KF_T(%rsp), %rdi
    mov     KF_I2(%rsp), %rsi
    call    crypto_kzg_fr_mul
    mov     KF_I2(%rsp), %rdi               /* x[i2] = x[i1] - t */
    mov     KF_I1(%rsp), %rsi
    lea     KF_T(%rsp), %rdx
    call    crypto_kzg_fr_sub
    mov     KF_I1(%rsp), %rdi               /* x[i1] = x[i1] + t */
    mov     %rdi, %rsi
    lea     KF_T(%rsp), %rdx
    call    crypto_kzg_fr_add
    mov     KF_J(%rsp), %rax
    add     $1, %rax
    mov     %rax, KF_J(%rsp)
    mov     %rbp, %rcx
    shr     $1, %rcx
    cmp     %rcx, %rax
    jb      2b
    add     $1, %r14
    shr     $1, %r15
    jmp     1b
5:  test    %r13, %r13                      /* inverse: times 1 / n */
    jz      9f
    lea     KF_T(%rsp), %rdi
    mov     %rbp, %rsi
    call    crypto_kzg_fr_from_u64
    C2      crypto_kzg_fr_inverse, %rsp, KF_T, %rsp, KF_T
    xor     %r14d, %r14d
6:  mov     %r14, %rdi
    shl     $5, %rdi
    add     %rbx, %rdi
    mov     %rdi, %rsi
    lea     KF_T(%rsp), %rdx
    call    crypto_kzg_fr_mul
    add     $1, %r14
    cmp     %rbp, %r14
    jb      6b
9:  LEAVE   KF_SIZE
END_FUNCTION crypto_kzg_fft

/* crypto_kzg_shift_vals(vals, n, factor): vals[i] times factor^i, in place (shiftVals); n in rsi. */
.set SH_S, 0
.set SH_SIZE, 40
LOCAL_FUNCTION crypto_kzg_shift_vals
    ENTER   SH_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    SET_FR_ONE %rsp, SH_S
    xor     %r13d, %r13d
1:  cmp     %rbp, %r13
    jae     9f
    mov     %r13, %rdi
    shl     $5, %rdi
    add     %rbx, %rdi
    mov     %rdi, %rsi
    lea     SH_S(%rsp), %rdx
    call    crypto_kzg_fr_mul
    C3      crypto_kzg_fr_mul, %rsp, SH_S, %rsp, SH_S, %r12, 0
    add     $1, %r13
    jmp     1b
9:  LEAVE   SH_SIZE
END_FUNCTION crypto_kzg_shift_vals

/*
 * crypto_kzg_coset_fft(vals, n, roots, inverse): cosetFftField with the shift
 * 7: shiftVals by 7 then the FFT; or the inverse FFT then shiftVals by 1 / 7.
 * n and inverse are in rsi and rcx.
 */
.set CF_F, 0
.set CF_SIZE, 40
LOCAL_FUNCTION crypto_kzg_coset_fft
    ENTER   CF_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    lea     CF_F(%rsp), %rdi
    mov     $7, %esi
    call    crypto_kzg_fr_from_u64
    test    %r13, %r13
    jnz     1f
    mov     %rbx, %rdi
    mov     %rbp, %rsi
    lea     CF_F(%rsp), %rdx
    call    crypto_kzg_shift_vals
    mov     %rbx, %rdi
    mov     %rbp, %rsi
    mov     %r12, %rdx
    xor     %ecx, %ecx
    call    crypto_kzg_fft
    LEAVE   CF_SIZE
1:  mov     %rbx, %rdi
    mov     %rbp, %rsi
    mov     %r12, %rdx
    mov     $1, %ecx
    call    crypto_kzg_fft
    C2      crypto_kzg_fr_inverse, %rsp, CF_F, %rsp, CF_F
    mov     %rbx, %rdi
    mov     %rbp, %rsi
    lea     CF_F(%rsp), %rdx
    call    crypto_kzg_shift_vals
    LEAVE   CF_SIZE
END_FUNCTION crypto_kzg_coset_fft

/*
 * crypto_kzg_batch_inverse(out, in, n): out[i] = 1 / in[i], and 0 for 0
 * (Fr.batchInverse): the products of the nonzero values before each one, one
 * inversion, then the walk back. out must not be in. n in rdx.
 */
.set BI_P, 0
.set BI_S, 32
.set BI_SIZE, 72
LOCAL_FUNCTION crypto_kzg_batch_inverse
    ENTER   BI_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    SET_FR_ONE %rsp, BI_P
    xor     %r13d, %r13d
1:  cmp     %r12, %r13                      /* out[i] = pre, the product of the nonzero values before i */
    jae     3f
    mov     %r13, %r14
    shl     $5, %r14
    lea     (%rbx,%r14), %r15
    add     %rbp, %r14
    COPY    %r15, 0, %rsp, BI_P, 32
    IS_ZERO %r14, 0, 32
    jz      2f
    C3      crypto_kzg_fr_mul, %rsp, BI_P, %rsp, BI_P, %r14, 0
2:  add     $1, %r13
    jmp     1b
3:  C2      crypto_kzg_fr_inverse, %rsp, BI_S, %rsp, BI_P  /* s = 1 / the product */
4:  test    %r13, %r13
    jz      9f
    sub     $1, %r13
    mov     %r13, %r14
    shl     $5, %r14
    lea     (%rbx,%r14), %r15
    add     %rbp, %r14
    IS_ZERO %r14, 0, 32
    jnz     5f
    ZERO    %r15, 0, 32
    jmp     4b
5:  C3      crypto_kzg_fr_mul, %r15, 0, %r15, 0, %rsp, BI_S        /* out[i] = pre s; s = s in[i] */
    C3      crypto_kzg_fr_mul, %rsp, BI_S, %rsp, BI_S, %r14, 0
    jmp     4b
9:  LEAVE   BI_SIZE
END_FUNCTION crypto_kzg_batch_inverse

/*
 * crypto_kzg_blob_to_poly(poly, bytes, count) -> status: count field
 * elements of 32 big-endian bytes (bytesToBlsFields). CRYPTO_INVALID_ENCODING
 * when one is r or more. count in rdx.
 */
LOCAL_FUNCTION crypto_kzg_blob_to_poly
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    xor     %r13d, %r13d
1:  cmp     %r12, %r13
    jae     8f
    mov     %r13, %rsi
    shl     $5, %rsi
    lea     (%rbx,%rsi), %rdi
    add     %rbp, %rsi
    call    crypto_kzg_fr_from_bytes
    test    %rax, %rax
    jnz     9f
    add     $1, %r13
    jmp     1b
8:  mov     $CRYPTO_OK, %eax
9:  LEAVE   8
END_FUNCTION crypto_kzg_blob_to_poly

/*
 * crypto_kzg_eval_to_coeff(poly, roots): the 4096 coefficients of the
 * polynomial of 4096 values, in place (polynomialEvalToCoeff): the inverse
 * FFT of the bit-reversed values. roots receives the 4096-th roots of unity.
 */
LOCAL_FUNCTION crypto_kzg_eval_to_coeff
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rbp, %rdi
    mov     $4096, %esi
    call    crypto_kzg_roots_of_unity
    mov     %rbx, %rdi
    mov     $4096, %esi
    mov     $32, %edx
    call    crypto_kzg_bit_reversal
    mov     %rbx, %rdi
    mov     $4096, %esi
    mov     %rbp, %rdx
    mov     $1, %ecx
    call    crypto_kzg_fft
    LEAVE   8
END_FUNCTION crypto_kzg_eval_to_coeff

/*
 * crypto_kzg_extended_cells(cells, coeff, work): the cells of the 4096
 * coefficients at coeff (cellsOfExtendedEvaluations of extendedEvaluations):
 * zero padding to 8192, the FFT over the 8192-th roots of unity, the
 * bit-reversal permutation, then 32 big-endian bytes per value. work holds
 * 524288 bytes: the values, then the roots.
 */
LOCAL_FUNCTION crypto_kzg_extended_cells
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12                      /* values */
    lea     262144(%r12), %r13              /* roots */
    mov     %r12, %rdi
    mov     %rbp, %rsi
    mov     $131072, %ecx
    rep movsb
    xor     %eax, %eax
    mov     $131072, %ecx
    rep stosb
    mov     %r13, %rdi
    mov     $8192, %esi
    call    crypto_kzg_roots_of_unity
    mov     %r12, %rdi
    mov     $8192, %esi
    mov     %r13, %rdx
    xor     %ecx, %ecx
    call    crypto_kzg_fft
    mov     %r12, %rdi
    mov     $8192, %esi
    mov     $32, %edx
    call    crypto_kzg_bit_reversal
    xor     %r14d, %r14d
1:  mov     %r14, %rsi
    shl     $5, %rsi
    lea     (%rbx,%rsi), %rdi
    add     %r12, %rsi
    call    crypto_kzg_fr_to_bytes
    add     $1, %r14
    cmp     $8192, %r14
    jb      1b
    LEAVE   8
END_FUNCTION crypto_kzg_extended_cells

/* Jump to label when the scratch at rs holds fewer than CRYPTO_KZG_SCRATCH + n * CRYPTO_KZG_SCRATCH_PER_ENTRY bytes. Uses rax. */
.macro KZG_SCRATCH_CHECK rs, n, label
    mov     \n, %rax
    shl     $13, %rax
    add     $CRYPTO_KZG_SCRATCH, %rax
    cmp     %rax, (\rs)
    jb      \label
.endm

/* crypto_kzg_compute_cells(blob, scratch, cells) -> status: computeCells. work: the polynomial, then 524288 bytes. */
FUNCTION crypto_kzg_compute_cells
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    KZG_SCRATCH_CHECK %rbp, $0, 8f
    lea     8(%rbp), %r13                   /* the polynomial */
    mov     %r13, %rdi
    mov     %rbx, %rsi
    mov     $4096, %edx
    call    crypto_kzg_blob_to_poly
    test    %rax, %rax
    jnz     9f
    lea     131072(%r13), %r14
    mov     %r13, %rdi
    mov     %r14, %rsi
    call    crypto_kzg_eval_to_coeff
    mov     %r12, %rdi
    mov     %r13, %rsi
    mov     %r14, %rdx
    call    crypto_kzg_extended_cells
    mov     $CRYPTO_OK, %eax
9:  LEAVE   8
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   8
END_FUNCTION crypto_kzg_compute_cells

/* ---------------------------------------------------------------- Trusted setup (TrustedSetup.lean) */

/* crypto_kzg_trusted_setup_of_bytes(g1_lagrange, g1_monomial, g2_monomial, settings) -> status: TrustedSetup.ofBytes. */
FUNCTION crypto_kzg_trusted_setup_of_bytes
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    cmpq    $CRYPTO_KZG_SETUP_G1_SIZE, CRYPTO_BYTES_COUNT(%rbx)     /* the counts */
    jne     8f
    cmpq    $CRYPTO_KZG_SETUP_G1_SIZE, CRYPTO_BYTES_COUNT(%rbp)
    jne     8f
    cmpq    $CRYPTO_KZG_SETUP_G2_SIZE, CRYPTO_BYTES_COUNT(%r12)
    jne     8f
    mov     CRYPTO_BYTES_OFFSET(%rbx), %r14         /* Lagrange point i at rev(i) */
    add     %rbx, %r14
    xor     %r15d, %r15d
1:  mov     %r15, %rax                      /* rev(i), 12 bits */
    xor     %esi, %esi
    mov     $12, %ecx
2:  shl     $1, %rsi
    mov     %rax, %rdx
    and     $1, %edx
    or      %rdx, %rsi
    shr     $1, %rax
    sub     $1, %ecx
    jnz     2b
    imul    $BLS_G1, %rsi, %rsi
    add     %r13, %rsi
    imul    $48, %r15, %rdi
    add     %r14, %rdi
    call    crypto_bls_g1_uncompress
    test    %rax, %rax
    jnz     8f
    add     $1, %r15
    cmp     $4096, %r15
    jb      1b
    mov     CRYPTO_BYTES_OFFSET(%rbp), %r14         /* the monomial points */
    add     %rbp, %r14
    xor     %r15d, %r15d
3:  imul    $BLS_G1, %r15, %rsi
    lea     CRYPTO_KZG_SETTINGS_G1_MONOMIAL(%r13,%rsi), %rsi
    imul    $48, %r15, %rdi
    add     %r14, %rdi
    call    crypto_bls_g1_uncompress
    test    %rax, %rax
    jnz     8f
    add     $1, %r15
    cmp     $4096, %r15
    jb      3b
    mov     CRYPTO_BYTES_OFFSET(%r12), %r14         /* the G2 points */
    add     %r12, %r14
    xor     %r15d, %r15d
4:  imul    $BLS_G2, %r15, %rsi
    lea     CRYPTO_KZG_SETTINGS_G2_MONOMIAL(%r13,%rsi), %rsi
    imul    $96, %r15, %rdi
    add     %r14, %rdi
    call    crypto_bls_g2_uncompress
    test    %rax, %rax
    jnz     8f
    add     $1, %r15
    cmp     $65, %r15
    jb      4b
    mov     $CRYPTO_OK, %eax
    LEAVE   8
8:  mov     $CRYPTO_KZG_INVALID_TRUSTED_SETUP, %eax
    LEAVE   8
END_FUNCTION crypto_kzg_trusted_setup_of_bytes

/* ---------------------------------------------------------------- Challenges and point checks (Core.lean) */

/*
 * crypto_kzg_validate_g1(bytes, point) -> status: validateKzgG1Point: the
 * point at infinity for 0xC0 followed by 47 zero bytes, else
 * crypto_bls_key_validate_point. CRYPTO_INVALID_PUBLIC_KEY otherwise.
 */
LOCAL_FUNCTION crypto_kzg_validate_g1
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    cmpb    $0xC0, (%rbx)
    jne     1f
    TAIL_ZERO %rbx, 48
    jnz     1f
    G1_ZERO %rbp, 0
    mov     $CRYPTO_OK, %eax
    LEAVE   8
1:  mov     %rbx, %rdi
    mov     %rbp, %rsi
    call    crypto_bls_key_validate_point
    LEAVE   8
END_FUNCTION crypto_kzg_validate_g1

/*
 * crypto_kzg_challenge(result, blob, commitment, work): computeChallenge:
 * SHA-256 of "FSBLOBVERIFY_V1_" || I2OSP(4096, 16) || blob || commitment, as
 * a number mod r. work holds 131232 bytes: the data as a ByteList, then the
 * digest.
 */
.set CH_DIGEST, 131200
LOCAL_FUNCTION crypto_kzg_challenge
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    movq    $CH_DIGEST, (%r13)              /* size, offset 24, count 131152 */
    movq    $24, 8(%r13)
    movq    $131152, 16(%r13)
    mov     945f(%rip), %rax
    mov     %rax, 24(%r13)
    mov     945f+8(%rip), %rax
    mov     %rax, 32(%r13)
    movq    $0, 40(%r13)                    /* I2OSP(4096, 16): byte 14 is 0x10 */
    movabs  $0x0010000000000000, %rax
    mov     %rax, 48(%r13)
    lea     56(%r13), %rdi                  /* the blob, then the commitment */
    mov     %rbp, %rsi
    mov     $131072, %ecx
    rep movsb
    mov     %r12, %rsi
    mov     $48, %ecx
    rep movsb
    mov     %r13, %rdi
    lea     CH_DIGEST(%r13), %rsi
    CALL_GLOBAL crypto_sha256
    mov     %rbx, %rdi
    lea     CH_DIGEST(%r13), %rsi
    call    crypto_kzg_fr_from_digest
    LEAVE   8
END_FUNCTION crypto_kzg_challenge

/*
 * crypto_kzg_compute_challenge(blob, commitment, scratch, challenge) ->
 * status: computeChallengeExport. work: the polynomial, then the point, then
 * the challenge work.
 */
.set CC_POINT, 131072
.set CC_FR, 131216
.set CC_WORK, 131248
FUNCTION crypto_kzg_compute_challenge
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    KZG_SCRATCH_CHECK %r12, $0, 7f
    lea     8(%r12), %r14                   /* work */
    mov     %r14, %rdi
    mov     %rbx, %rsi
    mov     $4096, %edx
    call    crypto_kzg_blob_to_poly
    test    %rax, %rax
    jnz     9f
    mov     %rbp, %rdi
    lea     CC_POINT(%r14), %rsi
    call    crypto_kzg_validate_g1
    test    %rax, %rax
    jnz     8f
    lea     CC_FR(%r14), %rdi
    mov     %rbx, %rsi
    mov     %rbp, %rdx
    lea     CC_WORK(%r14), %rcx
    call    crypto_kzg_challenge
    C2      crypto_kzg_fr_to_bytes, %r13, 0, %r14, CC_FR
    mov     $CRYPTO_OK, %eax
9:  LEAVE   8
7:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   8
8:  mov     $CRYPTO_KZG_INVALID_COMMITMENT, %eax
    LEAVE   8
END_FUNCTION crypto_kzg_compute_challenge

/* ---------------------------------------------------------------- Linear combinations and evaluation (Core.lean, Polynomials.lean) */

/* The generator of G1 as a G1 point at od(rd). Uses rax, rcx, rdx. */
.macro G1_GEN rd, od
    lea     904f(%rip), %rax
    COPY    \rd, \od, %rax, 0, 96
    SET_ONE \rd, \od + 96
.endm

/* The generator of G2 as a G2 point at od(rd). Uses rax, rcx, rdx. */
.macro G2_GEN rd, od
    lea     905f(%rip), %rax
    COPY    \rd, \od, %rax, 0, 192
    SET_ONE \rd, \od + 192
    ZERO    \rd, \od + 240, 48
.endm

/*
 * crypto_kzg_g1_lincomb(result, points, scalars, n, work): the sum of
 * scalars[j] times points[j] (g1LincombPoints), by the steps of G1.msm:
 * Pippenger's method with windows of 8 bits, from the top window down, the
 * point at infinity for n = 0 or all scalars 0. n in rcx. work holds 32 n +
 * 37296 bytes: the values of the scalars, the 256 buckets, then the sum,
 * the running sum and the partial sum.
 */
.set LC_NW, 0
.set LC_KK, 8
.set LC_J, 16
.set LC_SUM, 24
.set LC_SIZE, 40
LOCAL_FUNCTION crypto_kzg_g1_lincomb
    ENTER   LC_SIZE
    mov     %rdi, %rbx                      /* result */
    mov     %rsi, %rbp                      /* points */
    mov     %rdx, %r12                      /* scalars */
    mov     %rcx, %r13                      /* n */
    mov     %r8, %r14                       /* work: the values */
    test    %r13, %r13
    jz      8f
    xor     %r15d, %r15d                    /* vals = the values of the scalars */
1:  mov     %r15, %rsi
    shl     $5, %rsi
    lea     (%r14,%rsi), %rdi
    add     %r12, %rsi
    call    crypto_kzg_fr_canonical
    add     $1, %r15
    cmp     %r13, %r15
    jb      1b
    xor     %r8d, %r8d                      /* msmMaxBits */
    xor     %r15d, %r15d
2:  mov     %r15, %r9
    shl     $5, %r9
    add     %r14, %r9
    mov     $192, %r10d
    mov     24(%r9), %rax
    test    %rax, %rax
    jnz     3f
    mov     $128, %r10d
    mov     16(%r9), %rax
    test    %rax, %rax
    jnz     3f
    mov     $64, %r10d
    mov     8(%r9), %rax
    test    %rax, %rax
    jnz     3f
    xor     %r10d, %r10d
    mov     (%r9), %rax
    test    %rax, %rax
    jz      4f
3:  bsr     %rax, %rax
    lea     1(%r10,%rax), %rax
    cmp     %r8, %rax
    cmova   %rax, %r8
4:  add     $1, %r15
    cmp     %r13, %r15
    jb      2b
    test    %r8, %r8
    jz      8f
    add     $7, %r8                         /* nW */
    shr     $3, %r8
    mov     %r8, LC_NW(%rsp)
    mov     %r13, %r15                      /* the buckets */
    shl     $5, %r15
    add     %r14, %r15
    lea     256*BLS_G1(%r15), %rsi          /* the sum, then the running and partial sums */
    mov     %rsi, LC_SUM(%rsp)
    G1_ZERO %rsi, 0
    movq    $0, LC_KK(%rsp)
5:  mov     $1, %edi                        /* buckets 1 to 255 at infinity */
6:  imul    $BLS_G1, %rdi, %rsi
    add     %r15, %rsi
    G1_ZERO %rsi, 0
    add     $1, %rdi
    cmp     $256, %rdi
    jb      6b
    movq    $0, LC_J(%rsp)                  /* msmBuckets */
7:  mov     LC_J(%rsp), %rax
    mov     LC_NW(%rsp), %rcx               /* k = nW - 1 - kk */
    sub     LC_KK(%rsp), %rcx
    sub     $1, %rcx
    shl     $5, %rax
    add     %r14, %rax
    movzbl  (%rax,%rcx), %eax               /* digit k of vals[j] */
    test    %eax, %eax
    jz      70f
    imul    $BLS_G1, %rax, %rdi
    add     %r15, %rdi
    mov     %rdi, %rdx
    imul    $BLS_G1, LC_J(%rsp), %rsi
    add     %rbp, %rsi
    CALL_GLOBAL crypto_bls_g1_add
70: mov     LC_J(%rsp), %rax
    add     $1, %rax
    mov     %rax, LC_J(%rsp)
    cmp     %r13, %rax
    jb      7b
    mov     LC_SUM(%rsp), %rsi              /* msmRunning: from bucket 255 down to 1 */
    G1_ZERO %rsi, BLS_G1
    G1_ZERO %rsi, 2 * BLS_G1
    movq    $255, LC_J(%rsp)
71: mov     LC_SUM(%rsp), %rdi
    add     $BLS_G1, %rdi
    mov     %rdi, %rdx
    imul    $BLS_G1, LC_J(%rsp), %rsi
    add     %r15, %rsi
    CALL_GLOBAL crypto_bls_g1_add           /* running += B_v */
    mov     LC_SUM(%rsp), %rdi
    lea     2*BLS_G1(%rdi), %rdx
    lea     BLS_G1(%rdi), %rsi
    mov     %rdx, %rdi
    CALL_GLOBAL crypto_bls_g1_add           /* partial += running */
    subq    $1, LC_J(%rsp)
    jnz     71b
    cmpq    $0, LC_KK(%rsp)                 /* msmCombine: 8 doublings, except for the first window */
    je      73f
    movq    $8, LC_J(%rsp)
72: mov     LC_SUM(%rsp), %rdi
    mov     %rdi, %rsi
    call    crypto_bls_g1_double
    subq    $1, LC_J(%rsp)
    jnz     72b
73: mov     LC_SUM(%rsp), %rdi
    lea     2*BLS_G1(%rdi), %rsi
    mov     %rdi, %rdx
    CALL_GLOBAL crypto_bls_g1_add
    mov     LC_KK(%rsp), %rax
    add     $1, %rax
    mov     %rax, LC_KK(%rsp)
    cmp     LC_NW(%rsp), %rax
    jb      5b
    mov     LC_SUM(%rsp), %rsi
    COPY    %rbx, 0, %rsi, 0, BLS_G1
    LEAVE   LC_SIZE
8:  G1_ZERO %rbx, 0
    LEAVE   LC_SIZE
END_FUNCTION crypto_kzg_g1_lincomb

/* crypto_kzg_domain(domain): the bit-reversed 4096-th roots of unity (rootsOfUnityBrp 4096). */
LOCAL_FUNCTION crypto_kzg_domain
    ENTER   8
    mov     %rdi, %rbx
    mov     $4096, %esi
    call    crypto_kzg_roots_of_unity
    mov     %rbx, %rdi
    mov     $4096, %esi
    mov     $32, %edx
    call    crypto_kzg_bit_reversal
    LEAVE   8
END_FUNCTION crypto_kzg_domain

/*
 * crypto_kzg_evaluate(result, poly, z, work): p(z) for the 4096 values at
 * poly (evaluatePolynomialInEvaluationForm): value i when z is point i of
 * the domain, else (z^4096 - 1) / 4096 times the sum of p_i d_i / (z - d_i).
 * work holds 393216 bytes: the domain, z - d_i, then the inverses. z is not
 * in work.
 */
.set EV_ACC, 0
.set EV_T, 32
.set EV_E, 64
.set EV_I, 96
.set EV_SIZE, 104
LOCAL_FUNCTION crypto_kzg_evaluate
    ENTER   EV_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13                      /* the domain */
    lea     131072(%r13), %r14              /* z - d_i */
    lea     262144(%r13), %r15              /* the inverses */
    mov     %r13, %rdi
    call    crypto_kzg_domain
    xor     %eax, %eax                      /* z in the domain: its value */
    mov     %rax, EV_I(%rsp)
1:  mov     EV_I(%rsp), %rsi
    shl     $5, %rsi
    add     %r13, %rsi
    EQUAL   %rsi, 0, %r12, 0, 32
    jne     2f
    mov     EV_I(%rsp), %rsi
    shl     $5, %rsi
    add     %rbp, %rsi
    COPY    %rbx, 0, %rsi, 0, 32
    LEAVE   EV_SIZE
2:  mov     EV_I(%rsp), %rax
    add     $1, %rax
    mov     %rax, EV_I(%rsp)
    cmp     $4096, %rax
    jb      1b
    movq    $0, EV_I(%rsp)
3:  mov     EV_I(%rsp), %rdx
    shl     $5, %rdx
    lea     (%r14,%rdx), %rdi
    add     %r13, %rdx
    mov     %r12, %rsi
    call    crypto_kzg_fr_sub
    mov     EV_I(%rsp), %rax
    add     $1, %rax
    mov     %rax, EV_I(%rsp)
    cmp     $4096, %rax
    jb      3b
    mov     %r15, %rdi
    mov     %r14, %rsi
    mov     $4096, %edx
    call    crypto_kzg_batch_inverse
    ZERO    %rsp, EV_ACC, 32
    movq    $0, EV_I(%rsp)
4:  mov     EV_I(%rsp), %rax                /* acc += p_i d_i inv_i */
    shl     $5, %rax
    lea     EV_T(%rsp), %rdi
    lea     (%rbp,%rax), %rsi
    lea     (%r13,%rax), %rdx
    call    crypto_kzg_fr_mul
    mov     EV_I(%rsp), %rax
    shl     $5, %rax
    lea     EV_T(%rsp), %rdi
    mov     %rdi, %rsi
    lea     (%r15,%rax), %rdx
    call    crypto_kzg_fr_mul
    RADD    %rsp, EV_ACC, %rsp, EV_ACC, %rsp, EV_T
    mov     EV_I(%rsp), %rax
    add     $1, %rax
    mov     %rax, EV_I(%rsp)
    cmp     $4096, %rax
    jb      4b
    movq    $4096, EV_E(%rsp)               /* r = z^4096 - 1 */
    movq    $0, EV_E+8(%rsp)
    movq    $0, EV_E+16(%rsp)
    movq    $0, EV_E+24(%rsp)
    C3      crypto_kzg_fr_pow, %rsp, EV_T, %r12, 0, %rsp, EV_E
    SET_FR_ONE %rsp, EV_E
    RSUB    %rsp, EV_T, %rsp, EV_T, %rsp, EV_E
    RMUL    %rsp, EV_ACC, %rsp, EV_ACC, %rsp, EV_T      /* acc r / 4096 */
    lea     EV_T(%rsp), %rdi
    mov     $4096, %esi
    call    crypto_kzg_fr_from_u64
    C2      crypto_kzg_fr_inverse, %rsp, EV_T, %rsp, EV_T
    RMUL    %rbx, 0, %rsp, EV_ACC, %rsp, EV_T
    LEAVE   EV_SIZE
END_FUNCTION crypto_kzg_evaluate

/*
 * crypto_kzg_quotient_in_domain(result, z, poly, y, work): the quotient at the
 * domain point z (computeQuotientEvalWithinDomain): the sum over the points
 * d_i != z of (p_i - y) d_i / (z (z - d_i)). work holds 393216 bytes. z and
 * y are not in work.
 */
.set QD_T, 0
.set QD_I, 32
.set QD_SIZE, 40
LOCAL_FUNCTION crypto_kzg_quotient_in_domain
    ENTER   QD_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp                      /* z */
    mov     %rdx, %r12                      /* poly */
    mov     %rcx, %r13                      /* y */
    mov     %r8, %r14                       /* the domain */
    lea     131072(%r14), %r15              /* z (z - d_i), then the inverses at 262144 */
    mov     %r14, %rdi
    call    crypto_kzg_domain
    movq    $0, QD_I(%rsp)
1:  mov     QD_I(%rsp), %rdx
    shl     $5, %rdx
    lea     (%r15,%rdx), %rdi
    add     %r14, %rdx
    mov     %rbp, %rsi
    call    crypto_kzg_fr_sub
    mov     QD_I(%rsp), %rdi
    shl     $5, %rdi
    add     %r15, %rdi
    mov     %rbp, %rsi
    mov     %rdi, %rdx
    call    crypto_kzg_fr_mul
    mov     QD_I(%rsp), %rax
    add     $1, %rax
    mov     %rax, QD_I(%rsp)
    cmp     $4096, %rax
    jb      1b
    lea     262144(%r14), %rdi
    mov     %r15, %rsi
    mov     $4096, %edx
    call    crypto_kzg_batch_inverse
    ZERO    %rbx, 0, 32
    movq    $0, QD_I(%rsp)
2:  mov     QD_I(%rsp), %rsi
    shl     $5, %rsi
    add     %r14, %rsi
    EQUAL   %rsi, 0, %rbp, 0, 32            /* skip d_i = z */
    je      3f
    mov     QD_I(%rsp), %rsi
    shl     $5, %rsi
    add     %r12, %rsi
    lea     QD_T(%rsp), %rdi
    mov     %r13, %rdx
    call    crypto_kzg_fr_sub
    mov     QD_I(%rsp), %rdx
    shl     $5, %rdx
    add     %r14, %rdx
    lea     QD_T(%rsp), %rdi
    mov     %rdi, %rsi
    call    crypto_kzg_fr_mul
    mov     QD_I(%rsp), %rdx
    shl     $5, %rdx
    lea     262144(%r14,%rdx), %rdx
    lea     QD_T(%rsp), %rdi
    mov     %rdi, %rsi
    call    crypto_kzg_fr_mul
    RADD    %rbx, 0, %rbx, 0, %rsp, QD_T
3:  mov     QD_I(%rsp), %rax
    add     $1, %rax
    mov     %rax, QD_I(%rsp)
    cmp     $4096, %rax
    jb      2b
    LEAVE   QD_SIZE
END_FUNCTION crypto_kzg_quotient_in_domain

/*
 * crypto_kzg_proof_impl(settings, poly, z, work, proof, y): computeKzgProofImpl:
 * y = p(z), the quotient q_i = (p_i - y) / (d_i - z), or the quotient in the
 * domain where d_i = z, and the proof, the sum of q_i times Lagrange point i.
 * proof is a G1 point, y an element of Fr. work holds 1310720 bytes. z, the
 * outputs and poly are not in work.
 */
.set PI_DOMAIN, 0
.set PI_SHIFT, 131072
.set PI_DEN, 262144
.set PI_INV, 393216
.set PI_Q, 524288
.set PI_WORK, 655360
.set PI_I, 0
LOCAL_FUNCTION crypto_kzg_proof_impl
    ENTER   8
    mov     %rdi, %rbx                      /* settings */
    mov     %rsi, %rbp                      /* poly */
    mov     %rdx, %r12                      /* z */
    mov     %rcx, %r13                      /* work */
    mov     %r8, %r14                       /* proof */
    mov     %r9, %r15                       /* y */
    mov     %r15, %rdi
    mov     %rbp, %rsi
    mov     %r12, %rdx
    lea     PI_WORK(%r13), %rcx
    call    crypto_kzg_evaluate
    mov     %r13, %rdi
    call    crypto_kzg_domain
    movq    $0, PI_I(%rsp)
1:  mov     PI_I(%rsp), %rax                /* p_i - y, and d_i - z */
    shl     $5, %rax
    lea     PI_SHIFT(%r13,%rax), %rdi
    lea     (%rbp,%rax), %rsi
    mov     %r15, %rdx
    call    crypto_kzg_fr_sub
    mov     PI_I(%rsp), %rax
    shl     $5, %rax
    lea     PI_DEN(%r13,%rax), %rdi
    lea     (%r13,%rax), %rsi
    mov     %r12, %rdx
    call    crypto_kzg_fr_sub
    mov     PI_I(%rsp), %rax
    add     $1, %rax
    mov     %rax, PI_I(%rsp)
    cmp     $4096, %rax
    jb      1b
    lea     PI_INV(%r13), %rdi
    lea     PI_DEN(%r13), %rsi
    mov     $4096, %edx
    call    crypto_kzg_batch_inverse
    movq    $0, PI_I(%rsp)
2:  mov     PI_I(%rsp), %rax
    shl     $5, %rax
    lea     PI_DEN(%r13,%rax), %rsi
    IS_ZERO %rsi, 0, 32
    jnz     3f
    mov     PI_I(%rsp), %rax                /* z is the domain point d_i */
    shl     $5, %rax
    lea     PI_Q(%r13,%rax), %rdi
    lea     (%r13,%rax), %rsi
    mov     %rbp, %rdx
    mov     %r15, %rcx
    lea     PI_WORK(%r13), %r8
    call    crypto_kzg_quotient_in_domain
    jmp     4f
3:  mov     PI_I(%rsp), %rax
    shl     $5, %rax
    lea     PI_Q(%r13,%rax), %rdi
    lea     PI_SHIFT(%r13,%rax), %rsi
    lea     PI_INV(%r13,%rax), %rdx
    call    crypto_kzg_fr_mul
4:  mov     PI_I(%rsp), %rax
    add     $1, %rax
    mov     %rax, PI_I(%rsp)
    cmp     $4096, %rax
    jb      2b
    mov     %r14, %rdi
    lea     CRYPTO_KZG_SETTINGS_G1_LAGRANGE(%rbx), %rsi
    lea     PI_Q(%r13), %rdx
    mov     $4096, %ecx
    lea     PI_WORK(%r13), %r8
    call    crypto_kzg_g1_lincomb
    LEAVE   8
END_FUNCTION crypto_kzg_proof_impl

/*
 * crypto_kzg_verify_impl(s, area, valid): verifyKzgProofWith: the u64 1 when
 * e(C - [y], -[1]) e(proof, [s] - [z]) = 1, else 0. s is a G2 point. area
 * holds C, the proof (G1 points), z and y, then 5872 bytes of work.
 */
.set VI_C, 0
.set VI_P, 144
.set VI_Z, 288
.set VI_Y, 320
.set VI_K, 352
.set VI_PAIRS, 384
.set VI_WORK, 1256
LOCAL_FUNCTION crypto_kzg_verify_impl
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    lea     VI_PAIRS(%rbp), %r13            /* pair 1: (C - [y], -[1]) */
    C2      crypto_kzg_fr_neg, %rbp, VI_K, %rbp, VI_Y
    C2      crypto_kzg_fr_canonical, %rbp, VI_K, %rbp, VI_K
    G1_GEN  %r13, 8
    C3      crypto_bls_g1_mul, %r13, 8, %r13, 8, %rbp, VI_K
    G3      crypto_bls_g1_add, %rbp, VI_C, %r13, 8, %r13, 8
    G2_GEN  %r13, 152
    C2      crypto_bls_g2_neg, %r13, 152, %r13, 152
    COPY    %r13, 440, %rbp, VI_P, BLS_G1   /* pair 2: (proof, [s] - [z]) */
    C2      crypto_kzg_fr_neg, %rbp, VI_K, %rbp, VI_Z
    C2      crypto_kzg_fr_canonical, %rbp, VI_K, %rbp, VI_K
    G2_GEN  %r13, 584
    C3      crypto_bls_g2_mul, %r13, 584, %r13, 584, %rbp, VI_K
    C3      crypto_bls_g2_add, %r13, 584, %rbx, 0, %r13, 584
    movq    $2, (%r13)
    mov     %r13, %rdi
    lea     VI_WORK(%rbp), %rsi
    mov     %r12, %rdx
    call    crypto_bls_pairing_check
    LEAVE   8
END_FUNCTION crypto_kzg_verify_impl

/* ---------------------------------------------------------------- Blob functions (Core.lean) */

/* crypto_kzg_blob_to_kzg_commitment(settings, blob, scratch, commitment) -> status: blobToKzgCommitment. */
.set BC_POINT, 131072
.set BC_WORK, 131216
FUNCTION crypto_kzg_blob_to_kzg_commitment
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    KZG_SCRATCH_CHECK %r12, $0, 8f
    lea     8(%r12), %r14
    mov     %r14, %rdi
    mov     %rbp, %rsi
    mov     $4096, %edx
    call    crypto_kzg_blob_to_poly
    test    %rax, %rax
    jnz     9f
    lea     BC_POINT(%r14), %rdi
    lea     CRYPTO_KZG_SETTINGS_G1_LAGRANGE(%rbx), %rsi
    mov     %r14, %rdx
    mov     $4096, %ecx
    lea     BC_WORK(%r14), %r8
    call    crypto_kzg_g1_lincomb
    G2      crypto_bls_g1_compress, %r14, BC_POINT, %r13, 0
    mov     $CRYPTO_OK, %eax
9:  LEAVE   8
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   8
END_FUNCTION crypto_kzg_blob_to_kzg_commitment

/* crypto_kzg_compute_kzg_proof(settings, blob, z, scratch, proof, y) -> status: computeKzgProof. */
.set KP_Z, 131072
.set KP_Y, 131104
.set KP_POINT, 131136
.set KP_WORK, 131280
FUNCTION crypto_kzg_compute_kzg_proof
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     %r8, %r14
    mov     %r9, %r15
    KZG_SCRATCH_CHECK %r13, $0, 8f
    add     $8, %r13                        /* work */
    mov     %r13, %rdi
    mov     %rbp, %rsi
    mov     $4096, %edx
    call    crypto_kzg_blob_to_poly
    test    %rax, %rax
    jnz     9f
    lea     KP_Z(%r13), %rdi
    mov     %r12, %rsi
    call    crypto_kzg_fr_from_bytes
    test    %rax, %rax
    jnz     9f
    mov     %rbx, %rdi
    mov     %r13, %rsi
    lea     KP_Z(%r13), %rdx
    lea     KP_WORK(%r13), %rcx
    lea     KP_POINT(%r13), %r8
    lea     KP_Y(%r13), %r9
    call    crypto_kzg_proof_impl
    G2      crypto_bls_g1_compress, %r13, KP_POINT, %r14, 0
    C2      crypto_kzg_fr_to_bytes, %r15, 0, %r13, KP_Y
    mov     $CRYPTO_OK, %eax
9:  LEAVE   8
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   8
END_FUNCTION crypto_kzg_compute_kzg_proof

/*
 * crypto_kzg_verify_kzg_proof(settings, commitment, z, y, proof, scratch, valid)
 * -> status: verifyKzgProof. valid, the seventh argument, is on the stack.
 */
FUNCTION crypto_kzg_verify_kzg_proof
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     %r8, %r14
    mov     %r9, %r15
    KZG_SCRATCH_CHECK %r15, $0, 8f
    add     $8, %r15                        /* the area of crypto_kzg_verify_impl */
    C2      crypto_kzg_validate_g1, %rbp, 0, %r15, VI_C
    test    %rax, %rax
    jnz     5f
    C2      crypto_kzg_validate_g1, %r14, 0, %r15, VI_P
    test    %rax, %rax
    jnz     6f
    C2      crypto_kzg_fr_from_bytes, %r15, VI_Z, %r12, 0
    test    %rax, %rax
    jnz     9f
    C2      crypto_kzg_fr_from_bytes, %r15, VI_Y, %r13, 0
    test    %rax, %rax
    jnz     9f
    lea     CRYPTO_KZG_SETTINGS_G2_MONOMIAL+BLS_G2(%rbx), %rdi     /* [s] */
    mov     %r15, %rsi
    mov     64(%rsp), %rdx                  /* valid */
    call    crypto_kzg_verify_impl
    mov     $CRYPTO_OK, %eax
9:  LEAVE   8
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   8
5:  mov     $CRYPTO_KZG_INVALID_COMMITMENT, %eax
    LEAVE   8
6:  mov     $CRYPTO_KZG_INVALID_PROOF, %eax
    LEAVE   8
END_FUNCTION crypto_kzg_verify_kzg_proof

/* crypto_kzg_compute_blob_kzg_proof(settings, blob, commitment, scratch, proof) -> status: computeBlobKzgProof. */
FUNCTION crypto_kzg_compute_blob_kzg_proof
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     %r8, %r14
    KZG_SCRATCH_CHECK %r13, $0, 8f
    add     $8, %r13
    mov     %r12, %rdi                      /* bytesToKzgCommitment */
    lea     KP_POINT(%r13), %rsi
    call    crypto_kzg_validate_g1
    test    %rax, %rax
    jnz     7f
    mov     %r13, %rdi
    mov     %rbp, %rsi
    mov     $4096, %edx
    call    crypto_kzg_blob_to_poly
    test    %rax, %rax
    jnz     9f
    lea     KP_Z(%r13), %rdi                /* z = the challenge */
    mov     %rbp, %rsi
    mov     %r12, %rdx
    lea     KP_WORK(%r13), %rcx
    call    crypto_kzg_challenge
    mov     %rbx, %rdi
    mov     %r13, %rsi
    lea     KP_Z(%r13), %rdx
    lea     KP_WORK(%r13), %rcx
    lea     KP_POINT(%r13), %r8
    lea     KP_Y(%r13), %r9
    call    crypto_kzg_proof_impl
    G2      crypto_bls_g1_compress, %r13, KP_POINT, %r14, 0
    mov     $CRYPTO_OK, %eax
9:  LEAVE   8
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   8
7:  mov     $CRYPTO_KZG_INVALID_COMMITMENT, %eax
    LEAVE   8
END_FUNCTION crypto_kzg_compute_blob_kzg_proof

/* crypto_kzg_verify_blob_kzg_proof(settings, blob, commitment, proof, scratch, valid) -> status: verifyBlobKzgProof. */
.set VB_AREA, 131072
.set VB_WORK, 138240
FUNCTION crypto_kzg_verify_blob_kzg_proof
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     %r8, %r14
    mov     %r9, %r15
    KZG_SCRATCH_CHECK %r14, $0, 8f
    add     $8, %r14
    C2      crypto_kzg_validate_g1, %r12, 0, %r14, VB_AREA+VI_C
    test    %rax, %rax
    jnz     5f
    mov     %r14, %rdi
    mov     %rbp, %rsi
    mov     $4096, %edx
    call    crypto_kzg_blob_to_poly
    test    %rax, %rax
    jnz     9f
    lea     VB_AREA+VI_Z(%r14), %rdi        /* z = the challenge, y = p(z) */
    mov     %rbp, %rsi
    mov     %r12, %rdx
    lea     VB_WORK(%r14), %rcx
    call    crypto_kzg_challenge
    lea     VB_AREA+VI_Y(%r14), %rdi
    mov     %r14, %rsi
    lea     VB_AREA+VI_Z(%r14), %rdx
    lea     VB_WORK(%r14), %rcx
    call    crypto_kzg_evaluate
    C2      crypto_kzg_validate_g1, %r13, 0, %r14, VB_AREA+VI_P
    test    %rax, %rax
    jnz     6f
    lea     CRYPTO_KZG_SETTINGS_G2_MONOMIAL+BLS_G2(%rbx), %rdi
    lea     VB_AREA(%r14), %rsi
    mov     %r15, %rdx
    call    crypto_kzg_verify_impl
    mov     $CRYPTO_OK, %eax
9:  LEAVE   8
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   8
5:  mov     $CRYPTO_KZG_INVALID_COMMITMENT, %eax
    LEAVE   8
6:  mov     $CRYPTO_KZG_INVALID_PROOF, %eax
    LEAVE   8
END_FUNCTION crypto_kzg_verify_blob_kzg_proof

/*
 * crypto_kzg_verify_blob_kzg_proof_batch(settings, blobs, commitments, proofs,
 * scratch, valid) -> status: verifyBlobKzgProofBatch, then verifyKzgProofBatch.
 * work: the polynomial, the work of the evaluation and the challenges, the
 * fixed points, then the arrays of the n entries and the work of the sums.
 */
.set VBB_EVAL, 131072
.set VBB_R, 524288
.set VBB_K, 524320
.set VBB_L1, 524352
.set VBB_L2, 524496
.set VBB_L3, 524640
.set VBB_TMP, 524784
.set VBB_PAIRS, 524928
.set VBB_PW, 525800
.set VBB_ARR, 532480
/* stack: the arrays, the counter and the list addresses */
.set VBS_CG, 0
.set VBS_PG, 8
.set VBS_ZS, 16
.set VBS_YS, 24
.set VBS_RP, 32
.set VBS_ZR, 40
.set VBS_CM, 48
.set VBS_DATA, 56
.set VBS_MSM, 64
.set VBS_PROOFS, 72
.set VBS_I, 80
.set VBS_P, 88
.set VBS_SIZE, 104
FUNCTION crypto_kzg_verify_blob_kzg_proof_batch
    ENTER   VBS_SIZE
    mov     %rdi, %rbx                      /* settings */
    mov     %r8, %r14                       /* scratch, then work */
    mov     %r9, %r15                       /* valid */
    mov     CRYPTO_KZG_LIST_COUNT(%rsi), %r13       /* n */
    KZG_SCRATCH_CHECK %r14, %r13, 8f
    cmp     %r13, CRYPTO_KZG_LIST_COUNT(%rdx)
    jne     4f
    cmp     %r13, CRYPTO_KZG_LIST_COUNT(%rcx)
    jne     4f
    mov     CRYPTO_KZG_LIST_OFFSET(%rsi), %rbp      /* the blobs, commitments and proofs */
    add     %rsi, %rbp
    mov     CRYPTO_KZG_LIST_OFFSET(%rdx), %r12
    add     %rdx, %r12
    mov     CRYPTO_KZG_LIST_OFFSET(%rcx), %rax
    add     %rcx, %rax
    mov     %rax, VBS_PROOFS(%rsp)
    add     $8, %r14
    lea     VBB_ARR(%r14), %rax             /* the arrays */
    imul    $BLS_G1, %r13, %rcx             /* 144 n */
    mov     %r13, %rdx
    shl     $5, %rdx                        /* 32 n */
    mov     %rax, VBS_CG(%rsp)
    add     %rcx, %rax
    mov     %rax, VBS_PG(%rsp)
    add     %rcx, %rax
    mov     %rax, VBS_ZS(%rsp)
    add     %rdx, %rax
    mov     %rax, VBS_YS(%rsp)
    add     %rdx, %rax
    mov     %rax, VBS_RP(%rsp)
    add     %rdx, %rax
    mov     %rax, VBS_ZR(%rsp)
    add     %rdx, %rax
    mov     %rax, VBS_CM(%rsp)
    add     %rcx, %rax
    mov     %rax, VBS_DATA(%rsp)
    imul    $160, %r13, %rcx                /* the data: 24 + 32 + 160 n, then the digest */
    lea     24+32+32(%rax,%rcx), %rax
    mov     %rax, VBS_MSM(%rsp)
    movq    $0, VBS_I(%rsp)
1:  mov     VBS_I(%rsp), %rax            /* each triple: commitment, blob, proof */
    cmp     %r13, %rax
    jae     2f
    imul    $48, %rax, %rdi
    add     %r12, %rdi
    imul    $BLS_G1, %rax, %rsi
    add     VBS_CG(%rsp), %rsi
    call    crypto_kzg_validate_g1
    test    %rax, %rax
    jnz     5f
    mov     %r14, %rdi
    mov     VBS_I(%rsp), %rsi
    shl     $17, %rsi
    add     %rbp, %rsi
    mov     $4096, %edx
    call    crypto_kzg_blob_to_poly
    test    %rax, %rax
    jnz     9f
    mov     VBS_I(%rsp), %rax            /* z_i = the challenge */
    mov     %rax, %rdi
    shl     $5, %rdi
    add     VBS_ZS(%rsp), %rdi
    mov     %rax, %rsi
    shl     $17, %rsi
    add     %rbp, %rsi
    imul    $48, %rax, %rdx
    add     %r12, %rdx
    lea     VBB_EVAL(%r14), %rcx
    call    crypto_kzg_challenge
    mov     VBS_I(%rsp), %rax            /* y_i = p_i(z_i) */
    shl     $5, %rax
    mov     %rax, %rdi
    add     VBS_YS(%rsp), %rdi
    mov     %r14, %rsi
    mov     %rax, %rdx
    add     VBS_ZS(%rsp), %rdx
    lea     VBB_EVAL(%r14), %rcx
    call    crypto_kzg_evaluate
    mov     VBS_I(%rsp), %rax
    imul    $48, %rax, %rdi
    add     VBS_PROOFS(%rsp), %rdi
    imul    $BLS_G1, %rax, %rsi
    add     VBS_PG(%rsp), %rsi
    call    crypto_kzg_validate_g1
    test    %rax, %rax
    jnz     6f
    addq    $1, VBS_I(%rsp)
    jmp     1b
2:  mov     VBS_DATA(%rsp), %rdi         /* r: computeVerifyKzgProofBatchChallenge */
    imul    $160, %r13, %rax
    lea     32(%rax), %rcx                  /* count */
    lea     24+32+32(%rax), %rax            /* size */
    mov     %rax, (%rdi)
    movq    $24, 8(%rdi)
    mov     %rcx, 16(%rdi)
    mov     946f(%rip), %rax
    mov     %rax, 24(%rdi)
    mov     946f+8(%rip), %rax
    mov     %rax, 32(%rdi)
    movabs  $0x0010000000000000, %rax       /* I2OSP(4096, 8) */
    mov     %rax, 40(%rdi)
    mov     %r13, %rax                      /* I2OSP(n, 8) */
    bswap   %rax
    mov     %rax, 48(%rdi)
    lea     56(%rdi), %rax
    mov     %rax, VBS_P(%rsp)            /* the next byte of the data */
    movq    $0, VBS_I(%rsp)                      /* i */
3:  mov     VBS_I(%rsp), %rax
    cmp     %r13, %rax
    jae     30f
    imul    $48, %rax, %rsi                 /* commitment, z, y, proof */
    add     %r12, %rsi
    mov     VBS_P(%rsp), %rdi
    mov     $48, %ecx
    rep movsb
    mov     VBS_I(%rsp), %rsi
    shl     $5, %rsi
    add     VBS_ZS(%rsp), %rsi
    mov     VBS_P(%rsp), %rdi
    add     $48, %rdi
    call    crypto_kzg_fr_to_bytes
    mov     VBS_I(%rsp), %rsi
    shl     $5, %rsi
    add     VBS_YS(%rsp), %rsi
    mov     VBS_P(%rsp), %rdi
    add     $80, %rdi
    call    crypto_kzg_fr_to_bytes
    mov     VBS_I(%rsp), %rax
    imul    $48, %rax, %rsi
    add     VBS_PROOFS(%rsp), %rsi
    mov     VBS_P(%rsp), %rdi
    add     $112, %rdi
    mov     $48, %ecx
    rep movsb
    addq    $160, VBS_P(%rsp)
    addq    $1, VBS_I(%rsp)
    jmp     3b
30: mov     VBS_DATA(%rsp), %rdi
    mov     VBS_P(%rsp), %rsi            /* the digest, after the data */
    CALL_GLOBAL crypto_sha256
    lea     VBB_R(%r14), %rdi
    mov     VBS_P(%rsp), %rsi
    call    crypto_kzg_fr_from_digest
    test    %r13, %r13                      /* r^i: computePowers */
    jz      32f
    mov     VBS_RP(%rsp), %rsi
    SET_FR_ONE %rsi, 0
    movq    $1, VBS_I(%rsp)
31: mov     VBS_I(%rsp), %rax
    cmp     %r13, %rax
    jae     32f
    shl     $5, %rax
    mov     VBS_RP(%rsp), %rdi
    add     %rax, %rdi
    lea     -32(%rdi), %rsi
    lea     VBB_R(%r14), %rdx
    call    crypto_kzg_fr_mul
    addq    $1, VBS_I(%rsp)
    jmp     31b
32: lea     VBB_L1(%r14), %rdi              /* the sum of r^i proof_i */
    mov     VBS_PG(%rsp), %rsi
    mov     VBS_RP(%rsp), %rdx
    mov     %r13, %rcx
    mov     VBS_MSM(%rsp), %r8
    call    crypto_kzg_g1_lincomb
    movq    $0, VBS_I(%rsp)                      /* z_i r^i */
33: mov     VBS_I(%rsp), %rax
    cmp     %r13, %rax
    jae     34f
    shl     $5, %rax
    mov     VBS_ZR(%rsp), %rdi
    add     %rax, %rdi
    mov     VBS_ZS(%rsp), %rsi
    add     %rax, %rsi
    mov     VBS_RP(%rsp), %rdx
    add     %rax, %rdx
    call    crypto_kzg_fr_mul
    addq    $1, VBS_I(%rsp)
    jmp     33b
34: lea     VBB_L2(%r14), %rdi              /* the sum of z_i r^i proof_i */
    mov     VBS_PG(%rsp), %rsi
    mov     VBS_ZR(%rsp), %rdx
    mov     %r13, %rcx
    mov     VBS_MSM(%rsp), %r8
    call    crypto_kzg_g1_lincomb
    movq    $0, VBS_I(%rsp)                      /* C_i - [y_i] */
35: mov     VBS_I(%rsp), %rax
    cmp     %r13, %rax
    jae     36f
    shl     $5, %rax
    mov     VBS_YS(%rsp), %rsi
    add     %rax, %rsi
    lea     VBB_K(%r14), %rdi
    call    crypto_kzg_fr_neg
    C2      crypto_kzg_fr_canonical, %r14, VBB_K, %r14, VBB_K
    G1_GEN  %r14, VBB_TMP
    C3      crypto_bls_g1_mul, %r14, VBB_TMP, %r14, VBB_TMP, %r14, VBB_K
    mov     VBS_I(%rsp), %rax
    imul    $BLS_G1, %rax, %rax
    mov     VBS_CG(%rsp), %rdi
    add     %rax, %rdi
    lea     VBB_TMP(%r14), %rsi
    mov     VBS_CM(%rsp), %rdx
    add     %rax, %rdx
    CALL_GLOBAL crypto_bls_g1_add
    addq    $1, VBS_I(%rsp)
    jmp     35b
36: lea     VBB_L3(%r14), %rdi              /* the sum of r^i (C_i - [y_i]) */
    mov     VBS_CM(%rsp), %rsi
    mov     VBS_RP(%rsp), %rdx
    mov     %r13, %rcx
    mov     VBS_MSM(%rsp), %r8
    call    crypto_kzg_g1_lincomb
    lea     VBB_PAIRS(%r14), %r12           /* the pairs */
    movq    $2, (%r12)
    COPY    %r12, 8, %r14, VBB_L1, BLS_G1
    lea     152(%r12), %rdi                 /* -[s] */
    lea     CRYPTO_KZG_SETTINGS_G2_MONOMIAL+BLS_G2(%rbx), %rsi
    call    crypto_bls_g2_neg
    lea     VBB_L3(%r14), %rdi
    lea     VBB_L2(%r14), %rsi
    lea     440(%r12), %rdx
    CALL_GLOBAL crypto_bls_g1_add
    G2_GEN  %r12, 584
    mov     %r12, %rdi
    lea     VBB_PW(%r14), %rsi
    mov     %r15, %rdx
    call    crypto_bls_pairing_check
    mov     $CRYPTO_OK, %eax
9:  LEAVE   VBS_SIZE
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   VBS_SIZE
4:  mov     $CRYPTO_KZG_LENGTH_MISMATCH, %eax
    LEAVE   VBS_SIZE
5:  mov     $CRYPTO_KZG_INVALID_COMMITMENT, %eax
    LEAVE   VBS_SIZE
6:  mov     $CRYPTO_KZG_INVALID_PROOF, %eax
    LEAVE   VBS_SIZE
END_FUNCTION crypto_kzg_verify_blob_kzg_proof_batch

/* ---------------------------------------------------------------- Cells (Cells.lean, Fft.lean) */

/*
 * crypto_kzg_g1_fft(vals, n, roots, work): the FFT in G1 of the n points at
 * vals, in place (fftG1): the butterflies of fftG1Vector, in the order of
 * fftFieldIter: the bit-reversal permutation, then for each pair the
 * product t of the second point by its root, and the pair (l + t, l - t).
 * n (a power of two) in rsi; roots holds the n-th roots of unity. work holds
 * 320 bytes.
 */
.set GF_T, 0
.set GF_N, 144
.set GF_K, 288
.set GT_J, 0
.set GT_I1, 8
.set GT_I2, 16
.set GT_SIZE, 24
LOCAL_FUNCTION crypto_kzg_g1_fft
    ENTER   GT_SIZE
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     $BLS_G1, %edx
    call    crypto_kzg_bit_reversal
    xor     %r14d, %r14d                    /* log2 h */
    mov     %rbp, %r15                      /* m */
    shr     $1, %r15
1:  test    %r15, %r15
    jz      9f
    movq    $0, GT_J(%rsp)                  /* pair j < n / 2 */
2:  mov     GT_J(%rsp), %rax
    mov     %r14, %rcx
    mov     %rax, %r9
    shr     %cl, %r9
    mov     $1, %r8d
    shl     %cl, %r8                        /* h */
    lea     -1(%r8), %r10
    and     %rax, %r10                      /* r = j mod h */
    add     $1, %ecx
    shl     %cl, %r9
    add     %r10, %r9                       /* i1 */
    lea     (%r9,%r8), %r11                 /* i2 = i1 + h */
    imul    $BLS_G1, %r9, %r9
    add     %rbx, %r9
    mov     %r9, GT_I1(%rsp)
    imul    $BLS_G1, %r11, %r11
    add     %rbx, %r11
    mov     %r11, GT_I2(%rsp)
    mov     %r15, %rsi                      /* root m r */
    imul    %r10, %rsi
    shl     $5, %rsi
    add     %r12, %rsi
    lea     GF_K(%r13), %rdi
    call    crypto_kzg_fr_canonical
    lea     GF_T(%r13), %rdi
    mov     GT_I2(%rsp), %rsi
    lea     GF_K(%r13), %rdx
    call    crypto_bls_g1_mul
    G2      crypto_bls_g1_neg, %r13, GF_T, %r13, GF_N
    mov     GT_I1(%rsp), %rdi               /* l - t */
    lea     GF_N(%r13), %rsi
    mov     GT_I2(%rsp), %rdx
    CALL_GLOBAL crypto_bls_g1_add
    mov     GT_I1(%rsp), %rdi               /* l + t */
    lea     GF_T(%r13), %rsi
    mov     %rdi, %rdx
    CALL_GLOBAL crypto_bls_g1_add
    mov     GT_J(%rsp), %rax
    add     $1, %rax
    mov     %rax, GT_J(%rsp)
    mov     %rbp, %rcx
    shr     $1, %rcx
    cmp     %rcx, %rax
    jb      2b
    add     $1, %r14
    shr     $1, %r15
    jmp     1b
9:  LEAVE   GT_SIZE
END_FUNCTION crypto_kzg_g1_fft

/*
 * crypto_kzg_fk20(settings, coeff, work, cells, proofs): the cells and the
 * proofs of the 4096 coefficients at coeff
 * (computeCellsAndKzgProofsPolynomialcoeff): H_d = the sum of
 * coeff[i + 64 d] [s^i] for d = 1 to 63, then the FFT in G1 of the H_d,
 * padded to 128 with the point at infinity, in bit-reversed order. work
 * holds 720896 bytes; coeff is not in work.
 */
.set FK_EXT, 0
.set FK_H, 524288
.set FK_R, 542720
.set FK_FW, 546816
.set FK_MSM, 548864
LOCAL_FUNCTION crypto_kzg_fk20
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     %r8, %r14
    mov     %r13, %rdi                      /* the cells */
    mov     %rbp, %rsi
    lea     FK_EXT(%r12), %rdx
    call    crypto_kzg_extended_cells
    mov     $1, %r15d                       /* d */
1:  lea     -1(%r15), %rdi                  /* H_d, in entry d - 1 */
    imul    $BLS_G1, %rdi, %rdi
    lea     FK_H(%r12,%rdi), %rdi
    lea     CRYPTO_KZG_SETTINGS_G1_MONOMIAL(%rbx), %rsi
    mov     %r15, %rdx                      /* coeff[64 d] */
    shl     $11, %rdx
    add     %rbp, %rdx
    mov     %r15, %rcx                      /* 4096 - 64 d points */
    shl     $6, %rcx
    neg     %rcx
    add     $4096, %rcx
    lea     FK_MSM(%r12), %r8
    call    crypto_kzg_g1_lincomb
    add     $1, %r15
    cmp     $64, %r15
    jb      1b
    mov     $63, %r15d                      /* padding */
2:  imul    $BLS_G1, %r15, %rsi
    lea     FK_H(%r12,%rsi), %rsi
    G1_ZERO %rsi, 0
    add     $1, %r15
    cmp     $128, %r15
    jb      2b
    lea     FK_R(%r12), %rdi
    mov     $128, %esi
    call    crypto_kzg_roots_of_unity
    lea     FK_H(%r12), %rdi
    mov     $128, %esi
    lea     FK_R(%r12), %rdx
    lea     FK_FW(%r12), %rcx
    call    crypto_kzg_g1_fft
    lea     FK_H(%r12), %rdi
    mov     $128, %esi
    mov     $BLS_G1, %edx
    call    crypto_kzg_bit_reversal
    xor     %r15d, %r15d
3:  imul    $BLS_G1, %r15, %rdi
    lea     FK_H(%r12,%rdi), %rdi
    imul    $48, %r15, %rsi
    add     %r14, %rsi
    CALL_GLOBAL crypto_bls_g1_compress
    add     $1, %r15
    cmp     $128, %r15
    jb      3b
    LEAVE   8
END_FUNCTION crypto_kzg_fk20

/* crypto_kzg_compute_cells_and_kzg_proofs(settings, blob, scratch, cells, proofs) -> status: computeCellsAndKzgProofs. */
FUNCTION crypto_kzg_compute_cells_and_kzg_proofs
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     %r8, %r14
    KZG_SCRATCH_CHECK %r12, $0, 8f
    lea     8(%r12), %r15                   /* the polynomial, then the roots, then the work of crypto_kzg_fk20 */
    mov     %r15, %rdi
    mov     %rbp, %rsi
    mov     $4096, %edx
    call    crypto_kzg_blob_to_poly
    test    %rax, %rax
    jnz     9f
    mov     %r15, %rdi
    lea     131072(%r15), %rsi
    call    crypto_kzg_eval_to_coeff
    mov     %rbx, %rdi
    mov     %r15, %rsi
    lea     262144(%r15), %rdx
    mov     %r13, %rcx
    mov     %r14, %r8
    call    crypto_kzg_fk20
    mov     $CRYPTO_OK, %eax
9:  LEAVE   8
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   8
END_FUNCTION crypto_kzg_compute_cells_and_kzg_proofs

/*
 * crypto_kzg_cell_challenge(result, request, work): computeVerifyCellKzgProofBatchChallenge:
 * SHA-256 of "RCKZGCBATCH__V1_" || I2OSP(4096, 8) || I2OSP(64, 8) ||
 * I2OSP(m, 8) || I2OSP(n, 8) || the m commitments || for each cell k:
 * I2OSP(commitment index, 8) || I2OSP(cell index, 8) || its 64 values ||
 * proof k, as a number mod r. request holds m, the address of an array of
 * m commitment addresses, n, then the addresses of the n commitment
 * indices, cell indices (u64 each), cells and proofs. The cells hold
 * canonical values, so their bytes are those of blsFieldToBytes. work holds
 * 104 + 48 m + 2112 n bytes.
 */
.set CQ_M, 0
.set CQ_COMMITMENTS, 8
.set CQ_N, 16
.set CQ_CIDX, 24
.set CQ_IDX, 32
.set CQ_CELLS, 40
.set CQ_PROOFS, 48
LOCAL_FUNCTION crypto_kzg_cell_challenge
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     CQ_M(%rbp), %r13
    mov     CQ_N(%rbp), %r14
    imul    $48, %r13, %rax                 /* count = 48 + 48 m + 2112 n */
    imul    $2112, %r14, %rcx
    lea     48(%rax,%rcx), %rax
    mov     %rax, 16(%r12)
    add     $24+32, %rax                    /* size, with room for the digest */
    mov     %rax, (%r12)
    movq    $24, 8(%r12)
    mov     947f(%rip), %rax
    mov     %rax, 24(%r12)
    mov     947f+8(%rip), %rax
    mov     %rax, 32(%r12)
    movabs  $0x0010000000000000, %rax       /* I2OSP(4096, 8) */
    mov     %rax, 40(%r12)
    movabs  $0x4000000000000000, %rax       /* I2OSP(64, 8) */
    mov     %rax, 48(%r12)
    mov     %r13, %rax
    bswap   %rax
    mov     %rax, 56(%r12)
    mov     %r14, %rax
    bswap   %rax
    mov     %rax, 64(%r12)
    lea     72(%r12), %rdi
    xor     %r15d, %r15d                    /* the commitments */
1:  cmp     %r13, %r15
    jae     2f
    mov     CQ_COMMITMENTS(%rbp), %rsi
    mov     (%rsi,%r15,8), %rsi
    mov     $48, %ecx
    rep movsb
    add     $1, %r15
    jmp     1b
2:  xor     %r15d, %r15d                    /* the cells */
3:  cmp     %r14, %r15
    jae     5f
    mov     CQ_CIDX(%rbp), %rsi
    mov     (%rsi,%r15,8), %rax
    bswap   %rax
    mov     %rax, (%rdi)
    mov     CQ_IDX(%rbp), %rsi
    mov     (%rsi,%r15,8), %rax
    bswap   %rax
    mov     %rax, 8(%rdi)
    add     $16, %rdi
    mov     %r15, %rsi
    shl     $11, %rsi
    add     CQ_CELLS(%rbp), %rsi
    mov     $2048, %ecx
    rep movsb
    imul    $48, %r15, %rsi
    add     CQ_PROOFS(%rbp), %rsi
    mov     $48, %ecx
    rep movsb
    add     $1, %r15
    jmp     3b
5:  mov     %rdi, %r13                      /* the digest, after the data */
    mov     %r12, %rdi
    mov     %r13, %rsi
    CALL_GLOBAL crypto_sha256
    mov     %rbx, %rdi
    mov     %r13, %rsi
    call    crypto_kzg_fr_from_digest
    LEAVE   8
END_FUNCTION crypto_kzg_cell_challenge

/*
 * crypto_kzg_check_cell_indices(indices, n) -> status: CRYPTO_KZG_CELL_INDEX
 * when one of the n u64 values is 128 or more. A leaf.
 */
LOCAL_FUNCTION crypto_kzg_check_cell_indices
    UNWIND_END_PROLOGUE
    test    %rsi, %rsi
    jz      2f
1:  cmpq    $CRYPTO_KZG_CELLS_PER_EXT_BLOB, (%rdi)
    jae     8f
    add     $8, %rdi
    sub     $1, %rsi
    jnz     1b
2:  mov     $CRYPTO_OK, %eax
    ret
8:  mov     $CRYPTO_KZG_CELL_INDEX, %eax
    ret
END_FUNCTION crypto_kzg_check_cell_indices

/*
 * crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge(commitments,
 * commitment_indices, cell_indices, cells, proofs, scratch, challenge) ->
 * status: computeVerifyCellKzgProofBatchChallengeExport. challenge, the
 * seventh argument, is on the stack.
 */
.set VQ_REQ, 0
.set VQ_FR, 64
.set VQ_POINT, 96
.set VQ_EVALS, 240
.set VQ_PTRS, 2288
.set VQS_M, 0
.set VQS_N, 8
.set VQS_I, 16
.set VQS_SIZE, 24
FUNCTION crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge
    ENTER   VQS_SIZE
    mov     %rdi, %rbx                      /* commitments */
    mov     %rsi, %rbp                      /* commitment indices */
    mov     %rdx, %r12                      /* cell indices */
    mov     %rcx, %r13                      /* cells */
    mov     %r8, %r14                       /* proofs */
    mov     %r9, %r15                       /* scratch, then work */
    mov     CRYPTO_KZG_LIST_COUNT(%rbx), %rax       /* m */
    mov     %rax, VQS_M(%rsp)
    mov     CRYPTO_KZG_LIST_COUNT(%rbp), %rcx       /* n */
    mov     %rcx, VQS_N(%rsp)
    add     %rcx, %rax
    KZG_SCRATCH_CHECK %r15, %rax, 8f
    add     $8, %r15
    mov     VQS_N(%rsp), %rax
    cmp     %rax, CRYPTO_KZG_LIST_COUNT(%r12)
    jne     4f
    cmp     %rax, CRYPTO_KZG_LIST_COUNT(%r13)
    jne     4f
    cmp     %rax, CRYPTO_KZG_LIST_COUNT(%r14)
    jne     4f
    .irp r, %rbx, %rbp, %r12, %r13, %r14
    mov     CRYPTO_KZG_LIST_OFFSET(\r), %rax
    add     %rax, \r
    .endr
    mov     VQS_M(%rsp), %rax               /* the request */
    mov     %rax, VQ_REQ+CQ_M(%r15)
    lea     VQ_PTRS(%r15), %rax
    mov     %rax, VQ_REQ+CQ_COMMITMENTS(%r15)
    mov     VQS_N(%rsp), %rax
    mov     %rax, VQ_REQ+CQ_N(%r15)
    mov     %rbp, VQ_REQ+CQ_CIDX(%r15)
    mov     %r12, VQ_REQ+CQ_IDX(%r15)
    mov     %r13, VQ_REQ+CQ_CELLS(%r15)
    mov     %r14, VQ_REQ+CQ_PROOFS(%r15)
    movq    $0, VQS_I(%rsp)                 /* each commitment */
1:  mov     VQS_I(%rsp), %rax
    cmp     VQS_M(%rsp), %rax
    jae     2f
    imul    $48, %rax, %rdi
    add     %rbx, %rdi
    mov     %rdi, VQ_PTRS(%r15,%rax,8)
    lea     VQ_POINT(%r15), %rsi
    call    crypto_kzg_validate_g1
    test    %rax, %rax
    jnz     5f
    addq    $1, VQS_I(%rsp)
    jmp     1b
2:  xor     %eax, %eax                      /* each commitment index */
21: cmp     VQS_N(%rsp), %rax
    jae     22f
    mov     (%rbp,%rax,8), %rcx
    cmp     VQS_M(%rsp), %rcx
    jae     6f
    add     $1, %rax
    jmp     21b
22: mov     %r12, %rdi                      /* the cell indices */
    mov     VQS_N(%rsp), %rsi
    call    crypto_kzg_check_cell_indices
    test    %rax, %rax
    jnz     9f
    movq    $0, VQS_I(%rsp)                 /* each proof */
3:  mov     VQS_I(%rsp), %rax
    cmp     VQS_N(%rsp), %rax
    jae     31f
    imul    $48, %rax, %rdi
    add     %r14, %rdi
    lea     VQ_POINT(%r15), %rsi
    call    crypto_kzg_validate_g1
    test    %rax, %rax
    jnz     7f
    addq    $1, VQS_I(%rsp)
    jmp     3b
31: movq    $0, VQS_I(%rsp)                 /* each cell */
32: mov     VQS_I(%rsp), %rax
    cmp     VQS_N(%rsp), %rax
    jae     33f
    lea     VQ_EVALS(%r15), %rdi
    mov     %rax, %rsi
    shl     $11, %rsi
    add     %r13, %rsi
    mov     $64, %edx
    call    crypto_kzg_blob_to_poly
    test    %rax, %rax
    jnz     9f
    addq    $1, VQS_I(%rsp)
    jmp     32b
33: lea     VQ_FR(%r15), %rdi
    lea     VQ_REQ(%r15), %rsi
    mov     VQS_M(%rsp), %rdx               /* the data, after the m addresses */
    lea     VQ_PTRS(%r15,%rdx,8), %rdx
    call    crypto_kzg_cell_challenge
    mov     VQS_SIZE+56(%rsp), %rdi         /* challenge */
    lea     VQ_FR(%r15), %rsi
    call    crypto_kzg_fr_to_bytes
    mov     $CRYPTO_OK, %eax
9:  LEAVE   VQS_SIZE
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   VQS_SIZE
4:  mov     $CRYPTO_KZG_LENGTH_MISMATCH, %eax
    LEAVE   VQS_SIZE
5:  mov     $CRYPTO_KZG_INVALID_COMMITMENT, %eax
    LEAVE   VQS_SIZE
6:  mov     $CRYPTO_KZG_COMMITMENT_INDEX, %eax
    LEAVE   VQS_SIZE
7:  mov     $CRYPTO_KZG_INVALID_PROOF, %eax
    LEAVE   VQS_SIZE
END_FUNCTION crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge

/*
 * crypto_kzg_interpolate(interp, shift, evals, work): the 64 coefficients of
 * the polynomial with the 64 values evals on the coset of shift
 * (interpolateCosetEvals): the inverse FFT of the bit-reversed values over
 * the 64-th roots of unity, then shiftVals by 1 / shift. work holds 2080
 * bytes; interp is not evals.
 */
.set IP_R, 0
.set IP_H, 2048
LOCAL_FUNCTION crypto_kzg_interpolate
    ENTER   8
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    mov     %rbx, %rdi
    mov     %r12, %rsi
    mov     $2048, %ecx
    rep movsb
    mov     %rbx, %rdi
    mov     $64, %esi
    mov     $32, %edx
    call    crypto_kzg_bit_reversal
    mov     %r13, %rdi
    mov     $64, %esi
    call    crypto_kzg_roots_of_unity
    mov     %rbx, %rdi
    mov     $64, %esi
    mov     %r13, %rdx
    mov     $1, %ecx
    call    crypto_kzg_fft
    C2      crypto_kzg_fr_inverse, %r13, IP_H, %rbp, 0
    mov     %rbx, %rdi
    mov     $64, %esi
    lea     IP_H(%r13), %rdx
    call    crypto_kzg_shift_vals
    LEAVE   8
END_FUNCTION crypto_kzg_interpolate

/*
 * crypto_kzg_verify_cell_kzg_proof_batch(settings, commitments, cell_indices,
 * cells, proofs, scratch, valid) -> status: verifyCellKzgProofBatch, then
 * verifyCellKzgProofBatchImpl. valid, the seventh argument, is on the stack.
 */
.set VC_DOMAIN, 0
.set VC_R, 262144
.set VC_K, 262176
.set VC_E, 262208
.set VC_SUM, 262240
.set VC_INTERP, 264288
.set VC_IW, 266336
.set VC_LL, 268416
.set VC_RLC, 268560
.set VC_RLI, 268704
.set VC_RLP, 268848
.set VC_PAIRS, 268992
.set VC_PW, 269864
.set VC_REQ, 274472
.set VC_ARR, 278528
/* stack: the arrays of the n entries, counters */
.set VCS_CPTR, 0
.set VCS_CIDX, 8
.set VCS_CG, 16
.set VCS_PG, 24
.set VCS_EV, 32
.set VCS_RP, 40
.set VCS_WT, 48
.set VCS_SH, 56
.set VCS_WR, 64
.set VCS_DATA, 72
.set VCS_MSM, 80
.set VCS_M, 88
.set VCS_J, 96
.set VCS_K, 104
.set VCS_N, 112
.set VCS_SIZE, 120
FUNCTION crypto_kzg_verify_cell_kzg_proof_batch
    ENTER   VCS_SIZE
    mov     %rdi, %rbx                      /* settings */
    mov     %rsi, %rbp                      /* commitments */
    mov     %rdx, %r12                      /* cell indices */
    mov     %rcx, %r13                      /* cells */
    mov     %r8, %r14                       /* proofs */
    mov     %r9, %r15                       /* scratch, then work */
    mov     CRYPTO_KZG_LIST_COUNT(%rbp), %rax       /* n */
    mov     %rax, VCS_N(%rsp)
    KZG_SCRATCH_CHECK %r15, %rax, 8f
    add     $8, %r15
    mov     VCS_N(%rsp), %rax
    cmp     %rax, CRYPTO_KZG_LIST_COUNT(%r13)
    jne     4f
    cmp     %rax, CRYPTO_KZG_LIST_COUNT(%r14)
    jne     4f
    cmp     %rax, CRYPTO_KZG_LIST_COUNT(%r12)
    jne     4f
    .irp r, %rbp, %r12, %r13, %r14
    mov     CRYPTO_KZG_LIST_OFFSET(\r), %rax
    add     %rax, \r
    .endr
    mov     %r12, %rdi
    mov     VCS_N(%rsp), %rsi
    call    crypto_kzg_check_cell_indices
    test    %rax, %rax
    jnz     9f
    lea     VC_ARR(%r15), %rax              /* the arrays */
    mov     VCS_N(%rsp), %rcx
    mov     %rax, VCS_CPTR(%rsp)
    lea     (%rax,%rcx,8), %rax
    mov     %rax, VCS_CIDX(%rsp)
    lea     (%rax,%rcx,8), %rax
    mov     %rax, VCS_CG(%rsp)
    imul    $BLS_G1, %rcx, %rdx             /* 144 n */
    add     %rdx, %rax
    mov     %rax, VCS_PG(%rsp)
    add     %rdx, %rax
    mov     %rax, VCS_EV(%rsp)
    mov     %rcx, %rdx
    shl     $11, %rdx
    add     %rdx, %rax
    mov     %rax, VCS_RP(%rsp)
    mov     %rcx, %rdx
    shl     $5, %rdx                        /* 32 n */
    add     %rdx, %rax
    mov     %rax, VCS_WT(%rsp)
    add     %rdx, %rax
    mov     %rax, VCS_SH(%rsp)
    add     %rdx, %rax
    mov     %rax, VCS_WR(%rsp)
    add     %rdx, %rax
    mov     %rax, VCS_DATA(%rsp)
    imul    $2160, %rcx, %rdx               /* the data: 104 + 48 m + 2112 n bytes, m <= n */
    lea     104(%rax,%rdx), %rax
    mov     %rax, VCS_MSM(%rsp)
    movq    $0, VCS_K(%rsp)                 /* each commitment: check, and keep the first of equal ones */
    movq    $0, VCS_M(%rsp)
1:  mov     VCS_K(%rsp), %rax
    cmp     VCS_N(%rsp), %rax
    jae     20f
    imul    $48, %rax, %rdi                 /* commitment k */
    add     %rbp, %rdi
    imul    $BLS_G1, VCS_M(%rsp), %rsi
    add     VCS_CG(%rsp), %rsi
    call    crypto_kzg_validate_g1
    test    %rax, %rax
    jnz     5f
    imul    $48, VCS_K(%rsp), %rdi
    add     %rbp, %rdi
    movq    $0, VCS_J(%rsp)                 /* j: the kept commitment with these bytes */
10: mov     VCS_J(%rsp), %rax
    cmp     VCS_M(%rsp), %rax
    jae     12f
    mov     VCS_CPTR(%rsp), %rsi
    mov     (%rsi,%rax,8), %rsi
    EQUAL   %rsi, 0, %rdi, 0, 48
    je      13f
    addq    $1, VCS_J(%rsp)
    jmp     10b
12: mov     VCS_CPTR(%rsp), %rsi            /* a new one: j = m, m + 1 */
    mov     %rdi, (%rsi,%rax,8)
    add     $1, %rax
    mov     %rax, VCS_M(%rsp)
13: mov     VCS_J(%rsp), %rax
    mov     VCS_K(%rsp), %rcx
    mov     VCS_CIDX(%rsp), %rsi
    mov     %rax, (%rsi,%rcx,8)
    addq    $1, VCS_K(%rsp)
    jmp     1b
20: movq    $0, VCS_K(%rsp)                 /* each cell: cellToCosetEvals */
2:  mov     VCS_K(%rsp), %rax
    cmp     VCS_N(%rsp), %rax
    jae     3f
    shl     $11, %rax
    mov     VCS_EV(%rsp), %rdi
    add     %rax, %rdi
    lea     (%r13,%rax), %rsi
    mov     $64, %edx
    call    crypto_kzg_blob_to_poly
    test    %rax, %rax
    jnz     9f
    addq    $1, VCS_K(%rsp)
    jmp     2b
3:  movq    $0, VCS_K(%rsp)                 /* each proof */
30: mov     VCS_K(%rsp), %rax
    cmp     VCS_N(%rsp), %rax
    jae     31f
    imul    $48, %rax, %rdi
    add     %r14, %rdi
    imul    $BLS_G1, %rax, %rsi
    add     VCS_PG(%rsp), %rsi
    call    crypto_kzg_validate_g1
    test    %rax, %rax
    jnz     6f
    addq    $1, VCS_K(%rsp)
    jmp     30b
31: mov     VCS_M(%rsp), %rax               /* r */
    mov     %rax, VC_REQ+CQ_M(%r15)
    mov     VCS_CPTR(%rsp), %rax
    mov     %rax, VC_REQ+CQ_COMMITMENTS(%r15)
    mov     VCS_N(%rsp), %rax
    mov     %rax, VC_REQ+CQ_N(%r15)
    mov     VCS_CIDX(%rsp), %rax
    mov     %rax, VC_REQ+CQ_CIDX(%r15)
    mov     %r12, VC_REQ+CQ_IDX(%r15)
    mov     %r13, VC_REQ+CQ_CELLS(%r15)
    mov     %r14, VC_REQ+CQ_PROOFS(%r15)
    lea     VC_R(%r15), %rdi
    lea     VC_REQ(%r15), %rsi
    mov     VCS_DATA(%rsp), %rdx
    call    crypto_kzg_cell_challenge
    cmpq    $0, VCS_N(%rsp)                 /* r^k */
    je      41f
    mov     VCS_RP(%rsp), %rsi
    SET_FR_ONE %rsi, 0
    movq    $1, VCS_K(%rsp)
40: mov     VCS_K(%rsp), %rax
    cmp     VCS_N(%rsp), %rax
    jae     41f
    shl     $5, %rax
    mov     VCS_RP(%rsp), %rdi
    add     %rax, %rdi
    lea     -32(%rdi), %rsi
    lea     VC_R(%r15), %rdx
    call    crypto_kzg_fr_mul
    addq    $1, VCS_K(%rsp)
    jmp     40b
41: lea     VC_LL(%r15), %rdi               /* LL = the sum of r^k proof_k */
    mov     VCS_PG(%rsp), %rsi
    mov     VCS_RP(%rsp), %rdx
    mov     VCS_N(%rsp), %rcx
    mov     VCS_MSM(%rsp), %r8
    call    crypto_kzg_g1_lincomb
    mov     VCS_WT(%rsp), %rdi              /* weights[i] = the sum of r^k over the cells of commitment i */
    mov     VCS_M(%rsp), %rcx
    shl     $5, %rcx
    xor     %eax, %eax
    rep stosb
    movq    $0, VCS_K(%rsp)
44: mov     VCS_K(%rsp), %rax
    cmp     VCS_N(%rsp), %rax
    jae     45f
    mov     VCS_CIDX(%rsp), %rsi
    mov     (%rsi,%rax,8), %rdi
    shl     $5, %rdi
    add     VCS_WT(%rsp), %rdi
    mov     %rdi, %rsi
    mov     %rax, %rdx
    shl     $5, %rdx
    add     VCS_RP(%rsp), %rdx
    call    crypto_kzg_fr_add
    addq    $1, VCS_K(%rsp)
    jmp     44b
45: lea     VC_RLC(%r15), %rdi              /* RLC = the sum of weights[i] C_i */
    mov     VCS_CG(%rsp), %rsi
    mov     VCS_WT(%rsp), %rdx
    mov     VCS_M(%rsp), %rcx
    mov     VCS_MSM(%rsp), %r8
    call    crypto_kzg_g1_lincomb
    mov     %r15, %rdi                      /* the domain: rootsOfUnityBrp 8192 */
    mov     $8192, %esi
    call    crypto_kzg_roots_of_unity
    mov     %r15, %rdi
    mov     $8192, %esi
    mov     $32, %edx
    call    crypto_kzg_bit_reversal
    xor     %ecx, %ecx                      /* shift_k = domain[64 cell index] */
46: cmp     VCS_N(%rsp), %rcx
    jae     47f
    mov     (%r12,%rcx,8), %rsi
    shl     $11, %rsi
    add     %r15, %rsi
    mov     %rcx, %rdi
    shl     $5, %rdi
    add     VCS_SH(%rsp), %rdi
    .irp i, 0, 8, 16, 24
    mov     \i(%rsi), %rax
    mov     %rax, \i(%rdi)
    .endr
    add     $1, %rcx
    jmp     46b
47: lea     VC_SUM(%r15), %rdi              /* the sum of r^k I_k */
    mov     $2048, %ecx
    xor     %eax, %eax
    rep stosb
    movq    $0, VCS_K(%rsp)
48: mov     VCS_K(%rsp), %rax
    cmp     VCS_N(%rsp), %rax
    jae     49f
    lea     VC_INTERP(%r15), %rdi
    mov     %rax, %rsi
    shl     $5, %rsi
    add     VCS_SH(%rsp), %rsi
    mov     %rax, %rdx
    shl     $11, %rdx
    add     VCS_EV(%rsp), %rdx
    lea     VC_IW(%r15), %rcx
    call    crypto_kzg_interpolate
    movq    $0, VCS_J(%rsp)                 /* sum += r^k interp */
480: mov    VCS_J(%rsp), %rax
    shl     $5, %rax
    lea     VC_INTERP(%r15,%rax), %rdi
    mov     %rdi, %rsi
    mov     VCS_K(%rsp), %rdx
    shl     $5, %rdx
    add     VCS_RP(%rsp), %rdx
    call    crypto_kzg_fr_mul
    mov     VCS_J(%rsp), %rax
    shl     $5, %rax
    lea     VC_SUM(%r15,%rax), %rdi
    mov     %rdi, %rsi
    lea     VC_INTERP(%r15,%rax), %rdx
    call    crypto_kzg_fr_add
    mov     VCS_J(%rsp), %rax
    add     $1, %rax
    mov     %rax, VCS_J(%rsp)
    cmp     $64, %rax
    jb      480b
    addq    $1, VCS_K(%rsp)
    jmp     48b
49: lea     VC_RLI(%r15), %rdi              /* RLI = [the sum at s] */
    lea     CRYPTO_KZG_SETTINGS_G1_MONOMIAL(%rbx), %rsi
    lea     VC_SUM(%r15), %rdx
    mov     $64, %ecx
    mov     VCS_MSM(%rsp), %r8
    call    crypto_kzg_g1_lincomb
    movq    $64, VC_E(%r15)                 /* r^k shift_k^64 */
    movq    $0, VC_E+8(%r15)
    movq    $0, VC_E+16(%r15)
    movq    $0, VC_E+24(%r15)
    movq    $0, VCS_K(%rsp)
50: mov     VCS_K(%rsp), %rax
    cmp     VCS_N(%rsp), %rax
    jae     51f
    lea     VC_K(%r15), %rdi
    mov     %rax, %rsi
    shl     $5, %rsi
    add     VCS_SH(%rsp), %rsi
    lea     VC_E(%r15), %rdx
    call    crypto_kzg_fr_pow
    mov     VCS_K(%rsp), %rax
    shl     $5, %rax
    mov     VCS_WR(%rsp), %rdi
    add     %rax, %rdi
    mov     VCS_RP(%rsp), %rsi
    add     %rax, %rsi
    lea     VC_K(%r15), %rdx
    call    crypto_kzg_fr_mul
    addq    $1, VCS_K(%rsp)
    jmp     50b
51: lea     VC_RLP(%r15), %rdi              /* RLP = the sum of r^k shift_k^64 proof_k */
    mov     VCS_PG(%rsp), %rsi
    mov     VCS_WR(%rsp), %rdx
    mov     VCS_N(%rsp), %rcx
    mov     VCS_MSM(%rsp), %r8
    call    crypto_kzg_g1_lincomb
    lea     VC_PAIRS(%r15), %r12            /* the pairs: (LL, [s^64]), (RLC - RLI + RLP, -[1]) */
    movq    $2, (%r12)
    COPY    %r12, 8, %r15, VC_LL, BLS_G1
    COPY    %r12, 152, %rbx, CRYPTO_KZG_SETTINGS_G2_MONOMIAL + 64 * BLS_G2, BLS_G2
    lea     VC_RLI(%r15), %rdi
    mov     %rdi, %rsi
    CALL_GLOBAL crypto_bls_g1_neg
    lea     VC_RLC(%r15), %rdi
    lea     VC_RLI(%r15), %rsi
    lea     440(%r12), %rdx
    CALL_GLOBAL crypto_bls_g1_add
    lea     440(%r12), %rdi
    lea     VC_RLP(%r15), %rsi
    mov     %rdi, %rdx
    CALL_GLOBAL crypto_bls_g1_add
    lea     584(%r12), %rdi
    lea     CRYPTO_KZG_SETTINGS_G2_MONOMIAL(%rbx), %rsi
    call    crypto_bls_g2_neg
    mov     %r12, %rdi
    lea     VC_PW(%r15), %rsi
    mov     VCS_SIZE+56(%rsp), %rdx         /* valid */
    call    crypto_bls_pairing_check
    mov     $CRYPTO_OK, %eax
9:  LEAVE   VCS_SIZE
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   VCS_SIZE
4:  mov     $CRYPTO_KZG_LENGTH_MISMATCH, %eax
    LEAVE   VCS_SIZE
5:  mov     $CRYPTO_KZG_INVALID_COMMITMENT, %eax
    LEAVE   VCS_SIZE
6:  mov     $CRYPTO_KZG_INVALID_PROOF, %eax
    LEAVE   VCS_SIZE
END_FUNCTION crypto_kzg_verify_cell_kzg_proof_batch

/*
 * crypto_kzg_recover_cells_and_kzg_proofs(settings, cell_indices, cells,
 * scratch, recovered_cells, recovered_proofs) -> status:
 * recoverCellsAndKzgProofs: the checks, recoverPolynomialcoeff, then the
 * cells and proofs of crypto_kzg_fk20.
 */
.set RC_EVALS, 0
.set RC_EXT, 262144
.set RC_ROU, 524288
.set RC_ZC, 786432
.set RC_ZE, 1048576
.set RC_ZI, 1310720
.set RC_R128, 1572864
.set RC_SHORT, 1576960
.set RC_MISS, 1581056
.set RC_X, 1582080
.set RC_T, 1582112
.set RCS_N, 0
.set RCS_I, 8
.set RCS_K, 16
.set RCS_NM, 24
.set RCS_SIZE, 40
FUNCTION crypto_kzg_recover_cells_and_kzg_proofs
    ENTER   RCS_SIZE
    mov     %rdi, %rbx                      /* settings */
    mov     %rsi, %rbp                      /* cell indices */
    mov     %rdx, %r12                      /* cells */
    mov     %rcx, %r13                      /* scratch, then work */
    mov     %r8, %r14
    mov     %r9, %r15
    KZG_SCRATCH_CHECK %r13, $0, 8f
    add     $8, %r13
    mov     CRYPTO_KZG_LIST_COUNT(%rbp), %rax       /* n */
    mov     %rax, RCS_N(%rsp)
    cmp     %rax, CRYPTO_KZG_LIST_COUNT(%r12)
    jne     4f
    cmp     $CRYPTO_KZG_CELLS_PER_EXT_BLOB / 2, %rax
    jb      5f
    cmp     $CRYPTO_KZG_CELLS_PER_EXT_BLOB, %rax
    ja      6f
    mov     CRYPTO_KZG_LIST_OFFSET(%rbp), %rax
    add     %rax, %rbp
    mov     CRYPTO_KZG_LIST_OFFSET(%r12), %rax
    add     %rax, %r12
    mov     %rbp, %rdi
    mov     RCS_N(%rsp), %rsi
    call    crypto_kzg_check_cell_indices
    test    %rax, %rax
    jnz     9f
    mov     $1, %ecx                        /* strictly ascending */
1:  cmp     RCS_N(%rsp), %rcx
    jae     2f
    mov     (%rbp,%rcx,8), %rax
    cmp     -8(%rbp,%rcx,8), %rax
    jbe     7f
    add     $1, %rcx
    jmp     1b
2:  movq    $0, RCS_I(%rsp)                 /* cellToCosetEvals */
3:  mov     RCS_I(%rsp), %rax
    cmp     RCS_N(%rsp), %rax
    jae     10f
    shl     $11, %rax
    lea     RC_EVALS(%r13,%rax), %rdi
    lea     (%r12,%rax), %rsi
    mov     $64, %edx
    call    crypto_kzg_blob_to_poly
    test    %rax, %rax
    jnz     9f
    addq    $1, RCS_I(%rsp)
    jmp     3b
10: lea     RC_ROU(%r13), %rdi              /* the 8192-th roots of unity */
    mov     $8192, %esi
    call    crypto_kzg_roots_of_unity
    lea     RC_EXT(%r13), %rdi              /* E: the values in their places, zeros elsewhere */
    mov     $262144, %ecx
    xor     %eax, %eax
    rep stosb
    xor     %edx, %edx
12: cmp     RCS_N(%rsp), %rdx
    jae     14f
    mov     (%rbp,%rdx,8), %rdi
    shl     $11, %rdi
    lea     RC_EXT(%r13,%rdi), %rdi
    mov     %rdx, %rsi
    shl     $11, %rsi
    lea     RC_EVALS(%r13,%rsi), %rsi
    mov     $2048, %ecx
    rep movsb
    add     $1, %rdx
    jmp     12b
14: lea     RC_EXT(%r13), %rdi
    mov     $8192, %esi
    mov     $32, %edx
    call    crypto_kzg_bit_reversal
    lea     RC_R128(%r13), %rdi             /* the missing cells, and their roots */
    mov     $128, %esi
    call    crypto_kzg_roots_of_unity
    xor     %edx, %edx                      /* cell index ci */
    xor     %r8d, %r8d                      /* missing count */
15: xor     %ecx, %ecx
16: cmp     RCS_N(%rsp), %rcx
    jae     17f
    cmp     %rdx, (%rbp,%rcx,8)
    je      18f
    add     $1, %rcx
    jmp     16b
17: mov     %rdx, RC_MISS(%r13,%r8,8)
    add     $1, %r8
18: add     $1, %rdx
    cmp     $128, %rdx
    jb      15b
    mov     %r8, RCS_NM(%rsp)
    lea     RC_SHORT(%r13), %rsi            /* the short polynomial: 1, then times (X - x) for each */
    SET_FR_ONE %rsi, 0
    movq    $0, RCS_I(%rsp)                 /* missing cells done; also the length - 1 */
20: mov     RCS_I(%rsp), %rax
    cmp     RCS_NM(%rsp), %rax
    jae     25f
    mov     RC_MISS(%r13,%rax,8), %rax      /* x = root rev(mci) of 128 */
    xor     %esi, %esi
    mov     $7, %ecx
21: shl     $1, %rsi
    mov     %rax, %rdx
    and     $1, %edx
    or      %rdx, %rsi
    shr     $1, %rax
    sub     $1, %ecx
    jnz     21b
    shl     $5, %rsi
    lea     RC_R128(%r13,%rsi), %rsi
    .irp i, 0, 8, 16, 24
    mov     \i(%rsi), %rax
    mov     %rax, RC_X+\i(%r13)
    .endr
    mov     RCS_I(%rsp), %rax               /* p[L] = p[L - 1], L = count + 1 */
    shl     $5, %rax
    lea     RC_SHORT(%r13,%rax), %rsi
    .irp i, 0, 8, 16, 24
    mov     \i(%rsi), %rdx
    mov     %rdx, 32+\i(%rsi)
    .endr
    mov     RCS_I(%rsp), %rax               /* k from L - 1 down to 1: p[k] = p[k - 1] - x p[k] */
    mov     %rax, RCS_K(%rsp)
22: cmpq    $0, RCS_K(%rsp)
    je      23f
    lea     RC_T(%r13), %rdi
    mov     RCS_K(%rsp), %rsi
    shl     $5, %rsi
    lea     RC_SHORT(%r13,%rsi), %rsi
    lea     RC_X(%r13), %rdx
    call    crypto_kzg_fr_mul
    mov     RCS_K(%rsp), %rdi
    shl     $5, %rdi
    lea     RC_SHORT(%r13,%rdi), %rdi
    lea     -32(%rdi), %rsi
    lea     RC_T(%r13), %rdx
    call    crypto_kzg_fr_sub
    subq    $1, RCS_K(%rsp)
    jmp     22b
23: lea     RC_SHORT(%r13), %rdi            /* p[0] = -(x p[0]) */
    mov     %rdi, %rsi
    lea     RC_X(%r13), %rdx
    call    crypto_kzg_fr_mul
    lea     RC_SHORT(%r13), %rdi
    mov     %rdi, %rsi
    call    crypto_kzg_fr_neg
    addq    $1, RCS_I(%rsp)
    jmp     20b
25: lea     RC_ZC(%r13), %rdi               /* Z: coefficient i of the short one at 64 i */
    mov     $262144, %ecx
    xor     %eax, %eax
    rep stosb
    xor     %ecx, %ecx
27: cmp     RCS_I(%rsp), %rcx
    ja      28f
    mov     %rcx, %rsi
    shl     $5, %rsi
    lea     RC_SHORT(%r13,%rsi), %rsi
    mov     %rcx, %rdi
    shl     $11, %rdi
    lea     RC_ZC(%r13,%rdi), %rdi
    .irp i, 0, 8, 16, 24
    mov     \i(%rsi), %rax
    mov     %rax, \i(%rdi)
    .endr
    add     $1, %rcx
    jmp     27b
28: lea     RC_ZE(%r13), %rdi               /* the FFT of Z */
    lea     RC_ZC(%r13), %rsi
    mov     $262144, %ecx
    rep movsb
    lea     RC_ZE(%r13), %rdi
    mov     $8192, %esi
    lea     RC_ROU(%r13), %rdx
    xor     %ecx, %ecx
    call    crypto_kzg_fft
    movq    $0, RCS_I(%rsp)                 /* E Z, then P Z = its inverse FFT */
29: mov     RCS_I(%rsp), %rax
    shl     $5, %rax
    lea     RC_EXT(%r13,%rax), %rdi
    lea     RC_ZE(%r13,%rax), %rsi
    mov     %rdi, %rdx
    call    crypto_kzg_fr_mul
    addq    $1, RCS_I(%rsp)
    cmpq    $8192, RCS_I(%rsp)
    jb      29b
    lea     RC_EXT(%r13), %rdi
    mov     $8192, %esi
    lea     RC_ROU(%r13), %rdx
    mov     $1, %ecx
    call    crypto_kzg_fft
    lea     RC_EXT(%r13), %rdi              /* P Z and Z over the coset */
    mov     $8192, %esi
    lea     RC_ROU(%r13), %rdx
    xor     %ecx, %ecx
    call    crypto_kzg_coset_fft
    lea     RC_ZE(%r13), %rdi
    lea     RC_ZC(%r13), %rsi
    mov     $262144, %ecx
    rep movsb
    lea     RC_ZE(%r13), %rdi
    mov     $8192, %esi
    lea     RC_ROU(%r13), %rdx
    xor     %ecx, %ecx
    call    crypto_kzg_coset_fft
    lea     RC_ZI(%r13), %rdi               /* P = P Z / Z over the coset */
    lea     RC_ZE(%r13), %rsi
    mov     $8192, %edx
    call    crypto_kzg_batch_inverse
    movq    $0, RCS_I(%rsp)
30: mov     RCS_I(%rsp), %rax
    shl     $5, %rax
    lea     RC_EXT(%r13,%rax), %rdi
    mov     %rdi, %rsi
    lea     RC_ZI(%r13,%rax), %rdx
    call    crypto_kzg_fr_mul
    addq    $1, RCS_I(%rsp)
    cmpq    $8192, RCS_I(%rsp)
    jb      30b
    lea     RC_EXT(%r13), %rdi
    mov     $8192, %esi
    lea     RC_ROU(%r13), %rdx
    mov     $1, %ecx
    call    crypto_kzg_coset_fft
    mov     %rbx, %rdi                      /* the cells and proofs of the first 4096 coefficients */
    lea     RC_EXT(%r13), %rsi
    lea     RC_ROU(%r13), %rdx
    mov     %r14, %rcx
    mov     %r15, %r8
    call    crypto_kzg_fk20
    mov     $CRYPTO_OK, %eax
9:  LEAVE   RCS_SIZE
8:  mov     $CRYPTO_BUFFER_TOO_SMALL, %eax
    LEAVE   RCS_SIZE
4:  mov     $CRYPTO_KZG_LENGTH_MISMATCH, %eax
    LEAVE   RCS_SIZE
5:  mov     $CRYPTO_KZG_NOT_ENOUGH_CELLS, %eax
    LEAVE   RCS_SIZE
6:  mov     $CRYPTO_KZG_TOO_MANY_CELLS, %eax
    LEAVE   RCS_SIZE
7:  mov     $CRYPTO_KZG_INDICES_NOT_ASCENDING, %eax
    LEAVE   RCS_SIZE
END_FUNCTION crypto_kzg_recover_cells_and_kzg_proofs

/* ---------------------------------------------------------------- Constants */

    .p2align 3
/* p, -p^-1 mod 2^64, 2^384 mod p, 2^768 mod p (Fp.lean) */
900:
    .quad   0xB9FEFFFFFFFFAAAB, 0x1EABFFFEB153FFFF, 0x6730D2A0F6B0F624, 0x64774B84F38512BF, 0x4B1BA7B6434BACD7, 0x1A0111EA397FE69A
    .quad   0x89F3FFFCFFFCFFFD
    .quad   0x760900000002FFFD, 0xEBF4000BC40C0002, 0x5F48985753C758BA, 0x77CE585370525745, 0x5C071A97A256EC6D, 0x15F65EC3FA80E493
    .quad   0xF4DF1F341C341746, 0x0A76E6A609D104F1, 0x8DE5476C4C95B6D5, 0x67EB88A9939D83C0, 0x9A793E85B519952D, 0x11988FE592CAE3AA
/* b' = 4 (1 + u) of E2, Montgomery form */
901:
    .quad   0xAA270000000CFFF3, 0x53CC0032FC34000A, 0x478FE97A6B0A807F, 0xB1D37EBEE6BA24D7, 0x8EC9733BBF78AB2F, 0x09D645513D83DE7E
    .quad   0xAA270000000CFFF3, 0x53CC0032FC34000A, 0x478FE97A6B0A807F, 0xB1D37EBEE6BA24D7, 0x8EC9733BBF78AB2F, 0x09D645513D83DE7E
/* 1 / 2, Montgomery form (Fp2.sqrt: BaseField.inverse 2) */
903:
    .quad   0x1804000000015554, 0x855000053AB00001, 0x633CB57C253C276F, 0x6E22D1EC31EBB502, 0xD3916126F2D14CA2, 0x17FBB8571A006596
/* the generator of G2, x.c0, x.c1, y.c0, y.c1, Montgomery form (G2.lean) */
905:
    .quad   0xF5F28FA202940A10, 0xB3F5FB2687B4961A, 0xA1A893B53E2AE580, 0x9894999D1A3CAEE9, 0x6F67B7631863366B, 0x058191924350BCD7
    .quad   0xA5A9C0759E23F606, 0xAAA0C59DBCCD60C3, 0x3BB17E18E2867806, 0x1B1AB6CC8541B367, 0xC2B6ED0EF2158547, 0x11922A097360EDF3
    .quad   0x4C730AF860494C4A, 0x597CFA1F5E369C5A, 0xE7E6856CAA0A635A, 0xBBEFB5E96E0D495F, 0x07D3A975F0EF25A2, 0x0083FD8E7E80DAE5
    .quad   0xADC0FC92DF64B05D, 0x18AA270A2B1461DC, 0x86ADAC6A3BE4EBA0, 0x79495C4EC93DA33A, 0xE7175850A43CCAED, 0x0B2BC2A163DE1BF2
/* the generator of G1, x then y, Montgomery form (G1.lean) */
904:
    .quad   0x5CB38790FD530C16, 0x7817FC679976FFF5, 0x154F95C7143BA1C1, 0xF0AE6ACDF3D0E747, 0xEDCE6ECC21DBF440, 0x120177419E0BFB75
    .quad   0xBAAC93D50CE72271, 0x8C22631A7918FD8E, 0xDD595F13570725CE, 0x51AC582950405194, 0x0E1C8C3FAD0059C0, 0x0BBC3EFC5008A26A
/* p - 2, the exponent of Fp.inverse */
917:
    .quad   0xB9FEFFFFFFFFAAA9, 0x1EABFFFEB153FFFF, 0x6730D2A0F6B0F624, 0x64774B84F38512BF, 0x4B1BA7B6434BACD7, 0x1A0111EA397FE69A
/* (p + 1) / 4, the exponent of Fp.sqrt */
918:
    .quad   0xEE7FBFFFFFFFEAAB, 0x07AAFFFFAC54FFFF, 0xD9CC34A83DAC3D89, 0xD91DD2E13CE144AF, 0x92C6E9ED90D2EB35, 0x0680447A8E5FF9A6
/* b = 4 of E1, Montgomery form */
923:
    .quad   0xAA270000000CFFF3, 0x53CC0032FC34000A, 0x478FE97A6B0A807F, 0xB1D37EBEE6BA24D7, 0x8EC9733BBF78AB2F, 0x09D645513D83DE7E
/* r, the order of G1 and G2 (Fr.lean), 4 limbs */
924:
    .quad   0xFFFFFFFF00000001, 0x53BDA402FFFE5BFE, 0x3339D80809A1D805, 0x73EDA753299D7D48
/* the psi constants of HashToCurve.lean: c1Psi = 1 / (1 + u)^((p - 1) / 3), then c2Psi = 1 / (1 + u)^((p - 1) / 2), Montgomery form */
907:
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x890DC9E4867545C3, 0x2AF322533285A5D5, 0x50880866309B7E2C, 0xA20D1B8C7E881024, 0x14E4F04FE2DB9068, 0x14E56D3F1564853A
    .quad   0x3E2F585DA55C9AD1, 0x4294213D86C18183, 0x382844C88B623732, 0x92AD2AFD19103E18, 0x1D794E4FAC7CF0B9, 0x0BD592FC7D825EC8
    .quad   0x7BCFA7A25AA30FDA, 0xDC17DEC12A927E7C, 0x2F088DD86B4EBEF1, 0xD1CA2087DA74D4A7, 0x2DA2596696CEBC1D, 0x0E2B7EEDBBFD87D2
/* c1Psi2 = 1 / 2^((p - 1) / 3), in Fp, Montgomery form */
908:
    .quad   0xCD03C9E48671F071, 0x5DAB22461FCDA5D2, 0x587042AFD3851B95, 0x8EB60EBE01BACB9E, 0x03F97D6E83D050D2, 0x18F0206554638741
/* the SSWU constants of HashToCurve.lean: A' = 240 u, B' = 1012 (1 + u), Z = -(2 + u), Montgomery form */
910:
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0xE53A000003135242, 0x01080C0FDEF80285, 0xE7889EDBE340F6BD, 0x0B51375126310601, 0x02D6985717C744AB, 0x1220B4E979EA5467
    .quad   0x22EA00000CF89DB2, 0x6EC832DF71380AA4, 0x6E1B94403DB5A66E, 0x75BF3C53A79473BA, 0x3DD3A569412C0A34, 0x125CDB5E74DC4FD1
    .quad   0x22EA00000CF89DB2, 0x6EC832DF71380AA4, 0x6E1B94403DB5A66E, 0x75BF3C53A79473BA, 0x3DD3A569412C0A34, 0x125CDB5E74DC4FD1
    .quad   0x87EBFFFFFFF9555C, 0x656FFFE5DA8FFFFA, 0x0FD0749345D33AD2, 0xD951E663066576F4, 0xDE291A3D41E980D3, 0x0815664C7DFE040D
    .quad   0x43F5FFFFFFFCAAAE, 0x32B7FFF2ED47FFFD, 0x07E83A49A2E99D69, 0xECA8F3318332BB7A, 0xEF148D1EA0F4C069, 0x040AB3263EFF0206
/* the 3-isogeny of HashToCurve.lean: k10..k13, k20, k21, k30..k33, k40..k42, each c0 then c1, Montgomery form */
913:
/* k10 */
    .quad   0x47F671C71CE05E62, 0x06DD57071206393E, 0x7C80CD2AF3FD71A2, 0x048103EA9E6CD062, 0xC54516ACC8D037F6, 0x13808F550920EA41
    .quad   0x47F671C71CE05E62, 0x06DD57071206393E, 0x7C80CD2AF3FD71A2, 0x048103EA9E6CD062, 0xC54516ACC8D037F6, 0x13808F550920EA41
/* k11 */
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x5FE55555554C71D0, 0x873FFFDD236AAAA3, 0x6A6B4619B26EF918, 0x21C2888408874945, 0x2836CDA7028CABC5, 0x0AC73310A7FD5ABD
/* k12 */
    .quad   0x0A0C5555555971C3, 0xDB0C00101F9EAAAE, 0xB1FB2F941D797997, 0xD3960742EF416E1C, 0xB70040E2C20556F4, 0x149D7861E581393B
    .quad   0xAFF2AAAAAAA638E8, 0x439FFFEE91B55551, 0xB535A30CD9377C8C, 0x90E144420443A4A2, 0x941B66D3814655E2, 0x0563998853FEAD5E
/* k13 */
    .quad   0x40AAC71C71C725ED, 0x190955557A84E38E, 0xD817050A8F41ABC3, 0xD86485D4C87F6FB1, 0x696EB479F885D059, 0x198E1A74328002D2
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
/* k20 */
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x1F3AFFFFFF13AB97, 0xF25BFC611DA3FF3E, 0xCA3757CB3819B208, 0x3E6427366F8CEC18, 0x03977BC86095B089, 0x04F69DB13F39A952
/* k21 */
    .quad   0x447600000027552E, 0xDCB8009A43480020, 0x6F7EE9CE4A6E8B59, 0xB10330B7C0A95BC6, 0x6140B1FCFB1E54B7, 0x0381BE097F0BB4E1
    .quad   0x7588FFFFFFD8557D, 0x41F3FF646E0BFFDF, 0xF7B1E8D2AC426ACA, 0xB3741ACD32DBB6F8, 0xE9DAF5B9482D581F, 0x167F53E0BA7431B8
/* k30 */
    .quad   0x96D8F684BDFC77BE, 0xB530E4F43B66D0E2, 0x184A88FF379652FD, 0x57CB23ECFAE804E1, 0x0FD2E39EADA3EBA9, 0x08C8055E31C5D5C3
    .quad   0x96D8F684BDFC77BE, 0xB530E4F43B66D0E2, 0x184A88FF379652FD, 0x57CB23ECFAE804E1, 0x0FD2E39EADA3EBA9, 0x08C8055E31C5D5C3
/* k31 */
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0xBF0A71C71C91B406, 0x4D6D55D28B7638FD, 0x9D82F98E5F205AEE, 0xA27AA27B1D1A18D5, 0x02C3B2B2D2938E86, 0x0C7D13420B09807F
/* k32 */
    .quad   0xD7F9555555531C74, 0x21CFFFF748DAAAA8, 0x5A9AD1866C9BBE46, 0x4870A2210221D251, 0x4A0DB369C0A32AF1, 0x02B1CCC429FF56AF
    .quad   0xE205AAAAAAAC8E37, 0xFCDC000768795556, 0x0C96011A8A1537DD, 0x1C06A963F163406E, 0x010DF44C82A881E6, 0x174F45260F808FEB
/* k33 */
    .quad   0xA470BDA12F67F35C, 0xC0FE38E23327B425, 0xC9D3D0F2C6F0678D, 0x1C55C9935B5A982E, 0x27F6C0E2F0746764, 0x117C5E6E28AA9054
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
/* k40 */
    .quad   0x0162FFFFFA765ADF, 0x8F7BEA480083FB75, 0x561B3C2259E93611, 0x11E19FC1A9C875D5, 0xCA713EFC00367660, 0x03C6A03D41DA1151
    .quad   0x0162FFFFFA765ADF, 0x8F7BEA480083FB75, 0x561B3C2259E93611, 0x11E19FC1A9C875D5, 0xCA713EFC00367660, 0x03C6A03D41DA1151
/* k41 */
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x5DB0FFFFFD3B02C5, 0xD713F52358EBFDBA, 0x5EA60761A84D161A, 0xBB2C75A34EA6C44A, 0x0AC6735921C1119B, 0x0EE3D913BDACFBF6
/* k42 */
    .quad   0x66B10000003AFFC5, 0xCB1400E764EC0030, 0xA73E5EB56FA5D106, 0x8984C913A0FE09A9, 0x11E10AFB78AD7F13, 0x05429D0E3E918F52
    .quad   0x534DFFFFFFC4AAE6, 0x5397FF174C67FFCF, 0xBFF273EB870B251D, 0xDAF2827152870915, 0x393A9CBACA9E2DC3, 0x14BE74DBFAEE5748
/* R^3 mod p, R = 2^384, plain limbs (fpFromBytesL) */
925:
    .quad   0xED48AC6BD94CA1E0, 0x315F831E03A7ADF8, 0x9A53352A615E29DD, 0x34C04E5E921E1761, 0x2512D43565724728, 0x0AA6346091755D4D
/* |x| = 0xd201000000010000, the BLS parameter x = -|x|, 4 limbs (blsAbsX) */
926:
    .quad   0xD201000000010000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
/* "H2C-OVERSIZE-DST-" (RFC 9380 section 5.3.3) */
930:
    .ascii  "H2C-OVERSIZE-DST-"
    .p2align 3
/* the DST of the signatures (Signatures.lean DST), as a ByteList: size, offset, count, bytes */
    .p2align 3
931:
    .quad   72, 24, 43
    .ascii  "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_"
    .p2align 3
/* Fp12.frobeniusCoeff g = (1 + u)^((p - 1) / 6): g^0 to g^5, Montgomery form */
    .p2align 3
909:
    .quad   0x760900000002FFFD, 0xEBF4000BC40C0002, 0x5F48985753C758BA, 0x77CE585370525745, 0x5C071A97A256EC6D, 0x15F65EC3FA80E493
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x07089552B319D465, 0xC6695F92B50A8313, 0x97E83CCCD117228F, 0xA35BAECAB2DC29EE, 0x1CE393EA5DAACE4D, 0x08F2220FB0FB66EB
    .quad   0xB2F66AAD4CE5D646, 0x5842A06BFC497CEC, 0xCF4895D42599D394, 0xC11B9CBA40A8E8D0, 0x2E3813CBE5A0DE89, 0x110EEFDA88847FAF
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0xCD03C9E48671F071, 0x5DAB22461FCDA5D2, 0x587042AFD3851B95, 0x8EB60EBE01BACB9E, 0x03F97D6E83D050D2, 0x18F0206554638741
    .quad   0x7BCFA7A25AA30FDA, 0xDC17DEC12A927E7C, 0x2F088DD86B4EBEF1, 0xD1CA2087DA74D4A7, 0x2DA2596696CEBC1D, 0x0E2B7EEDBBFD87D2
    .quad   0x7BCFA7A25AA30FDA, 0xDC17DEC12A927E7C, 0x2F088DD86B4EBEF1, 0xD1CA2087DA74D4A7, 0x2DA2596696CEBC1D, 0x0E2B7EEDBBFD87D2
    .quad   0x890DC9E4867545C3, 0x2AF322533285A5D5, 0x50880866309B7E2C, 0xA20D1B8C7E881024, 0x14E4F04FE2DB9068, 0x14E56D3F1564853A
    .quad   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x82D83CF50DBCE43F, 0xA2813E53DF9D018F, 0xC6F0CAA53C65E181, 0x7525CF528D50FE95, 0x4A85ED50F4798A6B, 0x171DA0FD6CF8EEBD
    .quad   0x3726C30AF242C66C, 0x7C2AC1AAD1B6FE70, 0xA04007FBBA4B14A2, 0xEF517C3266341429, 0x0095BA654ED2226B, 0x02E370ECCC86F7DD
/* the exponents of finalExponentiation: |x|, |x| + 1, (|x| + 1) / 3 */
927:
    .quad   0xD201000000010000, 0xD201000000010001, 0x460055555555AAAB
/* r, -r^-1 mod 2^64, 2^256 mod r, 2^512 mod r (Bls/Fr.lean Fr.params) */
    .p2align 3
940:
    .quad   0xFFFFFFFF00000001, 0x53BDA402FFFE5BFE, 0x3339D80809A1D805, 0x73EDA753299D7D48
    .quad   0xFFFFFFFEFFFFFFFF
    .quad   0x00000001FFFFFFFE, 0x5884B7FA00034802, 0x998C4FEFECBC4FF5, 0x1824B159ACC5056F
    .quad   0xC999E990F3F29C6D, 0x2B6CEDCB87925C23, 0x05D314967254398F, 0x0748D9D99F59FF11
/* r - 2, the exponent of Fr.inverse */
941:
    .quad   0xFFFFFFFEFFFFFFFF, 0x53BDA402FFFE5BFE, 0x3339D80809A1D805, 0x73EDA753299D7D48
/* r - 1, divided by the order for computeRootsOfUnity */
942:
    .quad   0xFFFFFFFF00000000, 0x53BDA402FFFE5BFE, 0x3339D80809A1D805, 0x73EDA753299D7D48
/* the domain separators of Kzg/Constants.lean, 16 bytes each */
945:
    .ascii  "FSBLOBVERIFY_V1_"
946:
    .ascii  "RCKZGBATCH___V1_"
947:
    .ascii  "RCKZGCBATCH__V1_"
/* Fp12.frobenius: the offset of each coefficient a_k in an element, then k */
    .p2align 2
932:
    .short  0, 0, 96, 2, 192, 4, 288, 1, 384, 3, 480, 5
    .p2align 3
