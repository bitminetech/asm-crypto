/*
 * Ed25519 (RFC 8032 section 5.1) for x86-64 (System V AMD64 psABI).
 * AT&T syntax. Baseline x86-64 instructions only.
 * Requirements: docs/reference/ed25519.md. Layouts: include/ed25519.inc.
 *
 * The functions and their steps follow the ARM64 file one for one. Field
 * elements are 4 limbs of 64 bits below 2^256, mod p = 2^255 - 19, as in
 * x25519.s. A scalar multiplication doubles and adds for every bit and
 * keeps the sum with a mask, so no branch or address depends on a secret
 * scalar. Numbers mod L use Montgomery multiplication (CIOS).
 *
 * Every macro has a named parameter. In a macro without one, the Mach-O
 * assembler reads $0 to $9 as positional arguments.
 */
.set ISA_X86_64, 1
.include "crypto.inc"
.include "sha512.inc"
.include "ed25519.inc"
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
    OP      crypto_ed25519_fe_mul, \d, \a, \b
.endm

.macro FADD d, a, b
    OP      crypto_ed25519_fe_add, \d, \a, \b
.endm

.macro FSUB d, a, b
    OP      crypto_ed25519_fe_sub, \d, \a, \b
.endm

/* Copy 32 bytes from soff(src) to doff(dst). Uses rax. */
.macro COPY32 dst, doff, src, soff
    .irp w, 0, 8, 16, 24
    mov     (\soff + \w)(\src), %rax
    mov     %rax, (\doff + \w)(\dst)
    .endr
.endm

/* Copy a 128-byte point. Uses rax. */
.macro COPY128 dst, doff, src, soff
    COPY32  \dst, \doff, \src, \soff
    COPY32  \dst, (\doff + 32), \src, (\soff + 32)
    COPY32  \dst, (\doff + 64), \src, (\soff + 64)
    COPY32  \dst, (\doff + 96), \src, (\soff + 96)
.endm

/* Store the small number v as a field element at off(base). */
.macro SETSMALL base, off, v
    movq    $\v, \off(\base)
    movq    $0, (\off + 8)(\base)
    movq    $0, (\off + 16)(\base)
    movq    $0, (\off + 24)(\base)
.endm

/* ---------------------------------------------------------------- Public key */

.set PK_H, 0                        /* SHA-512 of the private key, clamped */
.set PK_P, 64                       /* A */
.set PK_FRAME, 200

/* crypto_ed25519_public_key(private_key, public_key) -> status. rbx public_key. */
FUNCTION crypto_ed25519_public_key
    ENTER   PK_FRAME
    mov     %rsi, %rbx
    mov     %rdi, %rsi
    lea     PK_H(%rsp), %rdi
    call    crypto_ed25519_expand
    lea     PK_P(%rsp), %rdi
    lea     PK_H(%rsp), %rsi
    lea     330f(%rip), %rdx
    call    crypto_ed25519_point_mul
    mov     %rbx, %rdi
    lea     PK_P(%rsp), %rsi
    call    crypto_ed25519_point_encode
    mov     $CRYPTO_OK, %eax
    LEAVE   PK_FRAME
END_FUNCTION crypto_ed25519_public_key

/* ---------------------------------------------------------------- Sign */

.set SG_H, 0                        /* a (clamped), then the prefix */
.set SG_RA, 64                      /* R, then A: encodings */
.set SG_RH, 128                     /* SHA-512(prefix || M) */
.set SG_KH, 192                     /* SHA-512(R || A || M) */
.set SG_R, 256                      /* r mod L */
.set SG_K, 288                      /* k mod L */
.set SG_T, 320                      /* k * a mod L */
.set SG_P, 352                      /* a point */
.set SG_FRAME, 488

/*
 * crypto_ed25519_sign(private_key, message, signature) -> status.
 * rbx message, rbp signature, r12 the modulus record of L.
 */
FUNCTION crypto_ed25519_sign
    ENTER   SG_FRAME
    mov     %rsi, %rbx
    mov     %rdx, %rbp
    lea     320f(%rip), %r12
    mov     %rdi, %rsi                      /* h = SHA-512(private key), a clamped */
    lea     SG_H(%rsp), %rdi
    call    crypto_ed25519_expand
    lea     SG_P(%rsp), %rdi                /* A = [a]B */
    lea     SG_H(%rsp), %rsi
    lea     330f(%rip), %rdx
    call    crypto_ed25519_point_mul
    lea     (SG_RA + 32)(%rsp), %rdi
    lea     SG_P(%rsp), %rsi
    call    crypto_ed25519_point_encode
    lea     SG_RH(%rsp), %rdi               /* r = SHA-512(prefix || M) mod L */
    lea     (SG_H + 32)(%rsp), %rsi
    mov     $32, %edx
    mov     %rbx, %rcx
    call    crypto_ed25519_hash
    lea     SG_R(%rsp), %rdi
    lea     SG_RH(%rsp), %rsi
    call    crypto_ed25519_scalar_reduce
    lea     SG_P(%rsp), %rdi                /* R = [r]B */
    lea     SG_R(%rsp), %rsi
    lea     330f(%rip), %rdx
    call    crypto_ed25519_point_mul
    lea     SG_RA(%rsp), %rdi
    lea     SG_P(%rsp), %rsi
    call    crypto_ed25519_point_encode
    lea     SG_KH(%rsp), %rdi               /* k = SHA-512(R || A || M) mod L */
    lea     SG_RA(%rsp), %rsi
    mov     $64, %edx
    mov     %rbx, %rcx
    call    crypto_ed25519_hash
    lea     SG_K(%rsp), %rdi
    lea     SG_KH(%rsp), %rsi
    call    crypto_ed25519_scalar_reduce
    lea     SG_T(%rsp), %rdi                /* k * a / 2^256, then * 2^512 / 2^256 */
    lea     SG_H(%rsp), %rsi
    lea     SG_K(%rsp), %rdx
    mov     %r12, %rcx
    call    crypto_ed25519_scalar_mul
    lea     SG_T(%rsp), %rdi
    lea     SG_T(%rsp), %rsi
    lea     CRYPTO_ED25519_MOD_R2(%r12), %rdx
    mov     %r12, %rcx
    call    crypto_ed25519_scalar_mul
    lea     32(%rbp), %rdi                  /* S = r + k * a mod L */
    lea     SG_R(%rsp), %rsi
    lea     SG_T(%rsp), %rdx
    mov     %r12, %rcx
    call    crypto_ed25519_scalar_add
    COPY32  %rbp, 0, %rsp, SG_RA
    mov     $CRYPTO_OK, %eax
    LEAVE   SG_FRAME
END_FUNCTION crypto_ed25519_sign

/* ---------------------------------------------------------------- Verify */

.set VF_A, 0                        /* the point A */
.set VF_P1, 128                     /* [S]B */
.set VF_P2, 256                     /* [k]A */
.set VF_KH, 384                     /* SHA-512(R || A || M) */
.set VF_K, 448                      /* k mod L */
.set VF_RA, 480                     /* R, then A: encodings */
.set VF_E, 544                      /* the encoding of [S]B - [k]A */
.set VF_ZERO, 576
.set VF_FRAME, 616

/*
 * crypto_ed25519_verify(public_key, message, signature, valid) -> status.
 * rbx public_key, rbp message, r12 signature, r13 valid.
 */
FUNCTION crypto_ed25519_verify
    ENTER   VF_FRAME
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rdx, %r12
    mov     %rcx, %r13
    lea     VF_A(%rsp), %rdi
    mov     %rbx, %rsi
    call    crypto_ed25519_point_decode
    test    %rax, %rax
    jz      1f
    mov     $CRYPTO_INVALID_PUBLIC_KEY, %eax
    jmp     9f
1:  lea     320f(%rip), %rcx                /* S < L */
    mov     32(%r12), %rax
    sub     (%rcx), %rax
    mov     40(%r12), %rax
    sbb     8(%rcx), %rax
    mov     48(%r12), %rax
    sbb     16(%rcx), %rax
    mov     56(%r12), %rax
    sbb     24(%rcx), %rax
    jae     8f                              /* S >= L: not valid */
    COPY32  %rsp, VF_RA, %r12, 0
    COPY32  %rsp, (VF_RA + 32), %rbx, 0
    lea     VF_KH(%rsp), %rdi
    lea     VF_RA(%rsp), %rsi
    mov     $64, %edx
    mov     %rbp, %rcx
    call    crypto_ed25519_hash
    lea     VF_K(%rsp), %rdi
    lea     VF_KH(%rsp), %rsi
    call    crypto_ed25519_scalar_reduce
    lea     VF_P1(%rsp), %rdi               /* [S]B */
    lea     32(%r12), %rsi
    lea     330f(%rip), %rdx
    call    crypto_ed25519_point_mul
    lea     VF_P2(%rsp), %rdi               /* [k]A */
    lea     VF_K(%rsp), %rsi
    lea     VF_A(%rsp), %rdx
    call    crypto_ed25519_point_mul
    SETSMALL %rsp, VF_ZERO, 0
    FSUB    (VF_P2 + CRYPTO_ED25519_POINT_X), VF_ZERO, (VF_P2 + CRYPTO_ED25519_POINT_X)  /* -[k]A */
    FSUB    (VF_P2 + CRYPTO_ED25519_POINT_T), VF_ZERO, (VF_P2 + CRYPTO_ED25519_POINT_T)
    lea     VF_P1(%rsp), %rdi
    lea     VF_P1(%rsp), %rsi
    lea     VF_P2(%rsp), %rdx
    call    crypto_ed25519_point_add
    lea     VF_E(%rsp), %rdi
    lea     VF_P1(%rsp), %rsi
    call    crypto_ed25519_point_encode
    mov     VF_E(%rsp), %rax                /* valid when the encoding equals R */
    xor     (%r12), %rax
    mov     (VF_E + 8)(%rsp), %rcx
    xor     8(%r12), %rcx
    or      %rcx, %rax
    mov     (VF_E + 16)(%rsp), %rcx
    xor     16(%r12), %rcx
    or      %rcx, %rax
    mov     (VF_E + 24)(%rsp), %rcx
    xor     24(%r12), %rcx
    or      %rcx, %rax
    sete    %al
    movzbl  %al, %eax
    mov     %rax, (%r13)
    mov     $CRYPTO_OK, %eax
    jmp     9f
8:  movq    $0, (%r13)
    mov     $CRYPTO_OK, %eax
9:  LEAVE   VF_FRAME
END_FUNCTION crypto_ed25519_verify

/* ---------------------------------------------------------------- Hashing */

/*
 * crypto_ed25519_expand(h, private_key): h = SHA-512(private_key), then
 * the first half clamped as section 5.1.5 step 2 says. The 32-byte message
 * as a ByteList at rsp. rbx h.
 */
LOCAL_FUNCTION crypto_ed25519_expand
    ENTER   72
    mov     %rdi, %rbx
    movq    $56, (%rsp)                     /* size, offset, count */
    movq    $24, 8(%rsp)
    movq    $32, 16(%rsp)
    COPY32  %rsp, 24, %rsi, 0
    mov     %rsp, %rdi
    mov     %rbx, %rsi
    CALL_GLOBAL crypto_sha512
    andb    $248, (%rbx)
    andb    $127, 31(%rbx)
    orb     $64, 31(%rbx)
    LEAVE   72
END_FUNCTION crypto_ed25519_expand

/*
 * crypto_ed25519_hash(digest, prefix, prefix_length, message): SHA-512 of
 * the prefix (32 or 64 bytes) followed by the message bytes. The state at
 * rsp, the prefix as a ByteList at rsp + 208. rbx digest, rbp message.
 */
LOCAL_FUNCTION crypto_ed25519_hash
    ENTER   312
    mov     %rdi, %rbx
    mov     %rcx, %rbp
    movq    $88, 208(%rsp)                  /* size, offset, count */
    movq    $24, 216(%rsp)
    mov     %rdx, 224(%rsp)
    xor     %ecx, %ecx
1:  mov     (%rsi,%rcx), %rax
    mov     %rax, 232(%rsp,%rcx)
    add     $8, %rcx
    cmp     %rdx, %rcx
    jb      1b
    mov     %rsp, %rdi
    CALL_GLOBAL crypto_sha512_init
    mov     %rsp, %rdi
    lea     208(%rsp), %rsi
    CALL_GLOBAL crypto_sha512_update
    mov     %rsp, %rdi
    mov     %rbp, %rsi
    CALL_GLOBAL crypto_sha512_update
    mov     %rsp, %rdi
    mov     %rbx, %rsi
    CALL_GLOBAL crypto_sha512_final
    LEAVE   312
END_FUNCTION crypto_ed25519_hash

/* ---------------------------------------------------------------- Numbers mod L */

/*
 * crypto_ed25519_scalar_reduce(result, h): the 64-byte little-endian h
 * mod L. With lo and hi the halves: lo * 2^256 + hi * 2^512 mod L, from
 * two Montgomery products, then one more by 1 removes the 2^256.
 * rbx result, rbp the modulus record. lo at rsp, hi at rsp + 32, the sum
 * at rsp + 64, 1 at rsp + 96.
 */
LOCAL_FUNCTION crypto_ed25519_scalar_reduce
    ENTER   136
    mov     %rdi, %rbx
    lea     320f(%rip), %rbp
    COPY32  %rsp, 0, %rsi, 0
    COPY32  %rsp, 32, %rsi, 32
    mov     %rsp, %rdi
    mov     %rsp, %rsi
    lea     CRYPTO_ED25519_MOD_R2(%rbp), %rdx
    mov     %rbp, %rcx
    call    crypto_ed25519_scalar_mul
    lea     32(%rsp), %rdi
    lea     32(%rsp), %rsi
    lea     CRYPTO_ED25519_MOD_R3(%rbp), %rdx
    mov     %rbp, %rcx
    call    crypto_ed25519_scalar_mul
    lea     64(%rsp), %rdi
    mov     %rsp, %rsi
    lea     32(%rsp), %rdx
    mov     %rbp, %rcx
    call    crypto_ed25519_scalar_add
    SETSMALL %rsp, 96, 1
    mov     %rbx, %rdi
    lea     64(%rsp), %rsi
    lea     96(%rsp), %rdx
    mov     %rbp, %rcx
    call    crypto_ed25519_scalar_mul
    LEAVE   136
END_FUNCTION crypto_ed25519_scalar_reduce

/*
 * crypto_ed25519_scalar_mul(result, a, b, modulus): a * b / 2^256 mod m,
 * for a below 2^256 and b below m (CIOS). result may be a or b.
 * b at rbx, T r8 to r13, b_i r14, q r15, the carry rbp.
 */
LOCAL_FUNCTION crypto_ed25519_scalar_mul
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
    UNWIND_END_PROLOGUE
    mov     %rdx, %rbx
    xor     %r8d, %r8d
    xor     %r9d, %r9d
    xor     %r10d, %r10d
    xor     %r11d, %r11d
    xor     %r12d, %r12d
    .irp off, 0, 8, 16, 24
    xor     %r13d, %r13d
    mov     \off(%rbx), %r14                /* T += a * b_i */
    mov     (%rsi), %rax
    mul     %r14
    add     %rax, %r8
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     8(%rsi), %rax
    mul     %r14
    add     %rbp, %rax
    adc     $0, %rdx
    add     %rax, %r9
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     16(%rsi), %rax
    mul     %r14
    add     %rbp, %rax
    adc     $0, %rdx
    add     %rax, %r10
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     24(%rsi), %rax
    mul     %r14
    add     %rbp, %rax
    adc     $0, %rdx
    add     %rax, %r11
    adc     $0, %rdx
    add     %rdx, %r12
    adc     $0, %r13
    mov     %r8, %r15                       /* q = T0 * -m^-1 mod 2^64 */
    imul    CRYPTO_ED25519_MOD_INVERSE(%rcx), %r15
    mov     (%rcx), %rax                    /* T = (T + q * m) / 2^64 */
    mul     %r15
    add     %rax, %r8
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     8(%rcx), %rax
    mul     %r15
    add     %rbp, %rax
    adc     $0, %rdx
    add     %rax, %r9
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     16(%rcx), %rax
    mul     %r15
    add     %rbp, %rax
    adc     $0, %rdx
    add     %rax, %r10
    adc     $0, %rdx
    mov     %rdx, %rbp
    mov     24(%rcx), %rax
    mul     %r15
    add     %rbp, %rax
    adc     $0, %rdx
    add     %rax, %r11
    adc     $0, %rdx
    add     %rdx, %r12
    adc     $0, %r13
    mov     %r9, %r8
    mov     %r10, %r9
    mov     %r11, %r10
    mov     %r12, %r11
    mov     %r13, %r12
    .endr
    mov     %r8, %rax                       /* T - m when T >= m */
    sub     (%rcx), %rax
    mov     %r9, %rdx
    sbb     8(%rcx), %rdx
    mov     %r10, %r14
    sbb     16(%rcx), %r14
    mov     %r11, %r15
    sbb     24(%rcx), %r15
    sbb     $0, %r12
    cmovnc  %rax, %r8
    cmovnc  %rdx, %r9
    cmovnc  %r14, %r10
    cmovnc  %r15, %r11
    mov     %r8, (%rdi)
    mov     %r9, 8(%rdi)
    mov     %r10, 16(%rdi)
    mov     %r11, 24(%rdi)
    UNWIND_BEGIN_EPILOGUE
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
END_FUNCTION crypto_ed25519_scalar_mul

/* crypto_ed25519_scalar_add(result, a, b, modulus): a + b mod m, for a, b < m. */
LOCAL_FUNCTION crypto_ed25519_scalar_add
    UNWIND_END_PROLOGUE
    mov     (%rsi), %r8
    mov     8(%rsi), %r9
    mov     16(%rsi), %r10
    mov     24(%rsi), %r11
    add     (%rdx), %r8
    adc     8(%rdx), %r9
    adc     16(%rdx), %r10
    adc     24(%rdx), %r11
    mov     $0, %eax
    adc     $0, %rax
    mov     %r8, (%rdi)                     /* the sum, then the sum - m when that does not borrow */
    mov     %r9, 8(%rdi)
    mov     %r10, 16(%rdi)
    mov     %r11, 24(%rdi)
    sub     (%rcx), %r8
    sbb     8(%rcx), %r9
    sbb     16(%rcx), %r10
    sbb     24(%rcx), %r11
    sbb     $0, %rax
    cmovc   (%rdi), %r8
    cmovc   8(%rdi), %r9
    cmovc   16(%rdi), %r10
    cmovc   24(%rdi), %r11
    mov     %r8, (%rdi)
    mov     %r9, 8(%rdi)
    mov     %r10, 16(%rdi)
    mov     %r11, 24(%rdi)
    ret
END_FUNCTION crypto_ed25519_scalar_add

/* ---------------------------------------------------------------- Points */

/*
 * crypto_ed25519_point_mul(result, scalar, point): [scalar]point for a
 * 32-byte little-endian scalar. From bit 255 down: double, add the point,
 * and keep the sum when the bit is 1, through a mask.
 * rbx result, rbp scalar, r12 bit index. The sum at rsp, the next sum at
 * rsp + 128, the point at rsp + 256.
 */
LOCAL_FUNCTION crypto_ed25519_point_mul
    ENTER   392
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    COPY128 %rsp, 256, %rdx, 0
    SETSMALL %rsp, 0, 0                     /* the neutral point (0, 1, 1, 0) */
    SETSMALL %rsp, 32, 1
    SETSMALL %rsp, 64, 1
    SETSMALL %rsp, 96, 0
    mov     $255, %r12d
1:  mov     %rsp, %rdi
    mov     %rsp, %rsi
    call    crypto_ed25519_point_double
    lea     128(%rsp), %rdi
    mov     %rsp, %rsi
    lea     256(%rsp), %rdx
    call    crypto_ed25519_point_add
    mov     %r12, %rax                      /* mask = -bit */
    shr     $3, %rax
    movzbl  (%rbp,%rax), %edx
    mov     %r12d, %ecx
    and     $7, %ecx
    shr     %cl, %edx
    and     $1, %edx
    neg     %rdx
    xor     %ecx, %ecx
2:  mov     (%rsp,%rcx), %rax               /* sum ^= (sum ^ next) & mask */
    mov     128(%rsp,%rcx), %rsi
    xor     %rax, %rsi
    and     %rdx, %rsi
    xor     %rsi, %rax
    mov     %rax, (%rsp,%rcx)
    add     $8, %rcx
    cmp     $128, %rcx
    jb      2b
    sub     $1, %r12
    jge     1b
    COPY128 %rbx, 0, %rsp, 0
    LEAVE   392
END_FUNCTION crypto_ed25519_point_mul

.set PA_P, 0
.set PA_Q, 128
.set PA_A, 256
.set PA_B, 288
.set PA_C, 320
.set PA_D, 352
.set PA_E, 384
.set PA_F, 416
.set PA_G, 448
.set PA_H, 480
.set PA_T1, 512
.set PA_T2, 544
.set PA_FRAME, 584

/*
 * crypto_ed25519_point_add(result, p, q): p + q, with the formulas of
 * section 5.1.4. result may be p or q. rbx result.
 */
LOCAL_FUNCTION crypto_ed25519_point_add
    ENTER   PA_FRAME
    mov     %rdi, %rbx
    COPY128 %rsp, PA_P, %rsi, 0
    COPY128 %rsp, PA_Q, %rdx, 0
    FSUB    PA_T1, (PA_P + 32), PA_P        /* A = (Y1 - X1) * (Y2 - X2) */
    FSUB    PA_T2, (PA_Q + 32), PA_Q
    FMUL    PA_A, PA_T1, PA_T2
    FADD    PA_T1, (PA_P + 32), PA_P        /* B = (Y1 + X1) * (Y2 + X2) */
    FADD    PA_T2, (PA_Q + 32), PA_Q
    FMUL    PA_B, PA_T1, PA_T2
    FMUL    PA_C, (PA_P + 96), (PA_Q + 96)  /* C = T1 * 2d * T2 */
    lea     PA_C(%rsp), %rdi
    lea     PA_C(%rsp), %rsi
    lea     310f(%rip), %rdx
    call    crypto_ed25519_fe_mul
    FMUL    PA_D, (PA_P + 64), (PA_Q + 64)  /* D = Z1 * 2 * Z2 */
    FADD    PA_D, PA_D, PA_D
    FSUB    PA_E, PA_B, PA_A
    FSUB    PA_F, PA_D, PA_C
    FADD    PA_G, PA_D, PA_C
    FADD    PA_H, PA_B, PA_A
    mov     %rbx, %rdi                      /* X3 = E * F */
    lea     PA_E(%rsp), %rsi
    lea     PA_F(%rsp), %rdx
    call    crypto_ed25519_fe_mul
    lea     32(%rbx), %rdi                  /* Y3 = G * H */
    lea     PA_G(%rsp), %rsi
    lea     PA_H(%rsp), %rdx
    call    crypto_ed25519_fe_mul
    lea     96(%rbx), %rdi                  /* T3 = E * H */
    lea     PA_E(%rsp), %rsi
    lea     PA_H(%rsp), %rdx
    call    crypto_ed25519_fe_mul
    lea     64(%rbx), %rdi                  /* Z3 = F * G */
    lea     PA_F(%rsp), %rsi
    lea     PA_G(%rsp), %rdx
    call    crypto_ed25519_fe_mul
    LEAVE   PA_FRAME
END_FUNCTION crypto_ed25519_point_add

.set PD_P, 0
.set PD_A, 128
.set PD_B, 160
.set PD_C, 192
.set PD_H, 224
.set PD_E, 256
.set PD_G, 288
.set PD_F, 320
.set PD_T, 352
.set PD_FRAME, 392

/*
 * crypto_ed25519_point_double(result, p): 2p, with the doubling formulas
 * of section 5.1.4. result may be p. rbx result.
 */
LOCAL_FUNCTION crypto_ed25519_point_double
    ENTER   PD_FRAME
    mov     %rdi, %rbx
    COPY128 %rsp, PD_P, %rsi, 0
    FMUL    PD_A, PD_P, PD_P                /* A = X1^2 */
    FMUL    PD_B, (PD_P + 32), (PD_P + 32)  /* B = Y1^2 */
    FMUL    PD_C, (PD_P + 64), (PD_P + 64)  /* C = 2 * Z1^2 */
    FADD    PD_C, PD_C, PD_C
    FADD    PD_H, PD_A, PD_B                /* H = A + B */
    FADD    PD_T, PD_P, (PD_P + 32)         /* E = H - (X1 + Y1)^2 */
    FMUL    PD_T, PD_T, PD_T
    FSUB    PD_E, PD_H, PD_T
    FSUB    PD_G, PD_A, PD_B                /* G = A - B */
    FADD    PD_F, PD_C, PD_G                /* F = C + G */
    mov     %rbx, %rdi                      /* X3 = E * F */
    lea     PD_E(%rsp), %rsi
    lea     PD_F(%rsp), %rdx
    call    crypto_ed25519_fe_mul
    lea     32(%rbx), %rdi                  /* Y3 = G * H */
    lea     PD_G(%rsp), %rsi
    lea     PD_H(%rsp), %rdx
    call    crypto_ed25519_fe_mul
    lea     96(%rbx), %rdi                  /* T3 = E * H */
    lea     PD_E(%rsp), %rsi
    lea     PD_H(%rsp), %rdx
    call    crypto_ed25519_fe_mul
    lea     64(%rbx), %rdi                  /* Z3 = F * G */
    lea     PD_F(%rsp), %rsi
    lea     PD_G(%rsp), %rdx
    call    crypto_ed25519_fe_mul
    LEAVE   PD_FRAME
END_FUNCTION crypto_ed25519_point_double

/*
 * crypto_ed25519_point_encode(encoding, p): y = Y / Z with the low bit of
 * x = X / Z in bit 255 (section 5.1.2). rbx encoding, rbp p.
 * 1 / Z at rsp, x at rsp + 32, y at rsp + 64.
 */
LOCAL_FUNCTION crypto_ed25519_point_encode
    ENTER   104
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    mov     %rsp, %rdi
    lea     64(%rbp), %rsi
    lea     300f(%rip), %rdx
    call    crypto_ed25519_fe_pow
    lea     32(%rsp), %rdi
    mov     %rbp, %rsi
    mov     %rsp, %rdx
    call    crypto_ed25519_fe_mul
    lea     64(%rsp), %rdi
    lea     32(%rbp), %rsi
    mov     %rsp, %rdx
    call    crypto_ed25519_fe_mul
    lea     32(%rsp), %rdi
    lea     32(%rsp), %rsi
    call    crypto_ed25519_fe_freeze
    lea     64(%rsp), %rdi
    lea     64(%rsp), %rsi
    call    crypto_ed25519_fe_freeze
    mov     32(%rsp), %rcx
    shl     $63, %rcx
    mov     88(%rsp), %rax
    or      %rcx, %rax
    mov     %rax, 24(%rbx)
    mov     64(%rsp), %rax
    mov     %rax, (%rbx)
    mov     72(%rsp), %rax
    mov     %rax, 8(%rbx)
    mov     80(%rsp), %rax
    mov     %rax, 16(%rbx)
    LEAVE   104
END_FUNCTION crypto_ed25519_point_encode

.set DC_Y, 0
.set DC_U, 32
.set DC_V, 64
.set DC_V3, 96
.set DC_V7, 128
.set DC_X, 160
.set DC_T, 192
.set DC_W, 224
.set DC_N, 256
.set DC_ZERO, 288
.set DC_ONE, 320
.set DC_FRAME, 360

/* Compare the 32 bytes at rsp + a and rsp + b: ZF set when equal. Uses rax, rcx. */
.macro FEQ a, b
    mov     \a(%rsp), %rax
    xor     \b(%rsp), %rax
    mov     (\a + 8)(%rsp), %rcx
    xor     (\b + 8)(%rsp), %rcx
    or      %rcx, %rax
    mov     (\a + 16)(%rsp), %rcx
    xor     (\b + 16)(%rsp), %rcx
    or      %rcx, %rax
    mov     (\a + 24)(%rsp), %rcx
    xor     (\b + 24)(%rsp), %rcx
    or      %rcx, %rax
.endm

/*
 * crypto_ed25519_point_decode(result, encoding) -> 0, or 1 when the
 * encoding is not a point: section 5.1.3, with y below p and no x = 0
 * with the sign bit set. Public data: it branches on it.
 * rbx result, rbp the sign bit.
 */
LOCAL_FUNCTION crypto_ed25519_point_decode
    ENTER   DC_FRAME
    mov     %rdi, %rbx
    mov     (%rsi), %r8
    mov     8(%rsi), %r9
    mov     16(%rsi), %r10
    mov     24(%rsi), %r11
    mov     %r11, %rbp
    shr     $63, %rbp
    btr     $63, %r11
    mov     %r8, DC_Y(%rsp)
    mov     %r9, (DC_Y + 8)(%rsp)
    mov     %r10, (DC_Y + 16)(%rsp)
    mov     %r11, (DC_Y + 24)(%rsp)
    mov     %r9, %rax                       /* y >= p: the top limbs all ones and y0 >= 2^64 - 19 */
    and     %r10, %rax
    cmp     $-1, %rax
    jne     1f
    mov     $0x7FFFFFFFFFFFFFFF, %rax
    cmp     %rax, %r11
    jne     1f
    cmp     $-19, %r8
    jae     8f
1:  SETSMALL %rsp, DC_ZERO, 0
    SETSMALL %rsp, DC_ONE, 1
    FMUL    DC_U, DC_Y, DC_Y                /* u = y^2 - 1, v = d y^2 + 1 */
    lea     DC_V(%rsp), %rdi
    lea     DC_U(%rsp), %rsi
    lea     311f(%rip), %rdx
    call    crypto_ed25519_fe_mul
    FADD    DC_V, DC_V, DC_ONE
    FSUB    DC_U, DC_U, DC_ONE
    FMUL    DC_V3, DC_V, DC_V               /* v^3, v^7 */
    FMUL    DC_V3, DC_V3, DC_V
    FMUL    DC_V7, DC_V3, DC_V3
    FMUL    DC_V7, DC_V7, DC_V
    FMUL    DC_T, DC_U, DC_V7               /* x = u v^3 (u v^7)^((p - 5) / 8) */
    lea     DC_T(%rsp), %rdi
    lea     DC_T(%rsp), %rsi
    lea     301f(%rip), %rdx
    call    crypto_ed25519_fe_pow
    FMUL    DC_X, DC_U, DC_V3
    FMUL    DC_X, DC_X, DC_T
    FMUL    DC_W, DC_X, DC_X                /* v x^2 against u and -u */
    FMUL    DC_W, DC_W, DC_V
    lea     DC_W(%rsp), %rdi
    lea     DC_W(%rsp), %rsi
    call    crypto_ed25519_fe_freeze
    lea     DC_U(%rsp), %rdi
    lea     DC_U(%rsp), %rsi
    call    crypto_ed25519_fe_freeze
    FSUB    DC_N, DC_ZERO, DC_U
    lea     DC_N(%rsp), %rdi
    lea     DC_N(%rsp), %rsi
    call    crypto_ed25519_fe_freeze
    FEQ     DC_W, DC_U
    jz      2f
    FEQ     DC_W, DC_N
    jnz     8f
    lea     DC_X(%rsp), %rdi                /* x = x * 2^((p - 1) / 4) */
    lea     DC_X(%rsp), %rsi
    lea     312f(%rip), %rdx
    call    crypto_ed25519_fe_mul
2:  lea     DC_X(%rsp), %rdi
    lea     DC_X(%rsp), %rsi
    call    crypto_ed25519_fe_freeze
    FEQ     DC_X, DC_ZERO
    jnz     3f
    test    %rbp, %rbp
    jnz     8f                              /* x = 0 with the sign bit set */
3:  mov     DC_X(%rsp), %rax
    and     $1, %eax
    cmp     %rbp, %rax
    je      4f
    FSUB    DC_X, DC_ZERO, DC_X             /* x = p - x */
    lea     DC_X(%rsp), %rdi
    lea     DC_X(%rsp), %rsi
    call    crypto_ed25519_fe_freeze
4:  COPY32  %rbx, 0, %rsp, DC_X
    COPY32  %rbx, 32, %rsp, DC_Y
    SETSMALL %rbx, 64, 1
    lea     96(%rbx), %rdi
    lea     DC_X(%rsp), %rsi
    lea     DC_Y(%rsp), %rdx
    call    crypto_ed25519_fe_mul
    xor     %eax, %eax
    jmp     9f
8:  mov     $1, %eax
9:  LEAVE   DC_FRAME
END_FUNCTION crypto_ed25519_point_decode

/* ---------------------------------------------------------------- Field arithmetic */

/*
 * crypto_ed25519_fe_pow(result, a, exponent): a^exponent for a public
 * exponent below 2^255, by squaring and multiplying from bit 254 down.
 * rbx result, r12 bit, r13 exponent. a at rsp, the running value at rsp + 32.
 */
LOCAL_FUNCTION crypto_ed25519_fe_pow
    ENTER   72
    mov     %rdi, %rbx
    mov     %rdx, %r13
    COPY32  %rsp, 0, %rsi, 0
    SETSMALL %rsp, 32, 1
    mov     $254, %r12d
1:  lea     32(%rsp), %rdi
    lea     32(%rsp), %rsi
    lea     32(%rsp), %rdx
    call    crypto_ed25519_fe_mul
    mov     %r12, %rax                      /* bit t of the exponent */
    shr     $6, %rax
    mov     (%r13,%rax,8), %rax
    mov     %r12d, %ecx
    shr     %cl, %rax
    test    $1, %al
    jz      2f
    lea     32(%rsp), %rdi
    lea     32(%rsp), %rsi
    mov     %rsp, %rdx
    call    crypto_ed25519_fe_mul
2:  sub     $1, %r12
    jge     1b
    COPY32  %rbx, 0, %rsp, 32
    LEAVE   72
END_FUNCTION crypto_ed25519_fe_pow

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
 * crypto_ed25519_fe_freeze(result, a): a mod p, below p. A leaf: folds
 * bit 255 twice, then subtracts p when the value is p or more, by a mask.
 */
LOCAL_FUNCTION crypto_ed25519_fe_freeze
    UNWIND_END_PROLOGUE
    mov     (%rsi), %r8
    mov     8(%rsi), %r9
    mov     16(%rsi), %r10
    mov     24(%rsi), %r11
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
    mov     %r8, (%rdi)
    mov     %r9, 8(%rdi)
    mov     %r10, 16(%rdi)
    mov     %r11, 24(%rdi)
    ret
END_FUNCTION crypto_ed25519_fe_freeze

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
 * crypto_ed25519_fe_mul(result, a, b): a * b mod p, below 2^256, for a, b
 * below 2^256. result may be a or b. A leaf: b at rcx, the column r8 to
 * r10. The 8-limb product at rsp.
 */
LOCAL_FUNCTION crypto_ed25519_fe_mul
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
END_FUNCTION crypto_ed25519_fe_mul

/*
 * crypto_ed25519_fe_add(result, a, b): a + b mod p, below 2^256. A leaf:
 * the sum r8 to r11.
 */
LOCAL_FUNCTION crypto_ed25519_fe_add
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
END_FUNCTION crypto_ed25519_fe_add

/*
 * crypto_ed25519_fe_sub(result, a, b): a - b mod p, below 2^256. A leaf:
 * the difference r8 to r11.
 */
LOCAL_FUNCTION crypto_ed25519_fe_sub
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
END_FUNCTION crypto_ed25519_fe_sub

/* ---------------------------------------------------------------- Constants (RFC 8032 section 5.1) */

    .p2align 3
/* p - 2: the exponent of 1 / a. */
300:
    .quad   0xFFFFFFFFFFFFFFEB, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF
/* (p - 5) / 8: the exponent of the square root candidate. */
301:
    .quad   0xFFFFFFFFFFFFFFFD, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x0FFFFFFFFFFFFFFF
/* 2d. */
310:
    .quad   0xEBD69B9426B2F159, 0x00E0149A8283B156, 0x198E80F2EEF3D130, 0x2406D9DC56DFFCE7
/* d = -121665 / 121666. */
311:
    .quad   0x75EB4DCA135978A3, 0x00700A4D4141D8AB, 0x8CC740797779E898, 0x52036CEE2B6FFE73
/* 2^((p - 1) / 4), a square root of -1. */
312:
    .quad   0xC4EE1B274A0EA0B0, 0x2F431806AD2FE478, 0x2B4D00993DFBD7A7, 0x2B8324804FC1DF0B
/* L, -L^-1 mod 2^64, 2^256 mod L, 2^512 mod L, 2^768 mod L. */
320:
    .quad   0x5812631A5CF5D3ED, 0x14DEF9DEA2F79CD6, 0x0000000000000000, 0x1000000000000000
    .quad   0xD2B51DA312547E1B
    .quad   0xD6EC31748D98951D, 0xC6EF5BF4737DCF70, 0xFFFFFFFFFFFFFFFE, 0x0FFFFFFFFFFFFFFF
    .quad   0xA40611E3449C0F01, 0xD00E1BA768859347, 0xCEEC73D217F5BE65, 0x0399411B7C309A3D
    .quad   0x2A9E49687B83A2DB, 0x278324E6AEF7F3EC, 0x8065DC6C04EC5B65, 0x0E530B773599CEC7
/* B: X, Y, Z = 1, T = X * Y. */
330:
    .quad   0xC9562D608F25D51A, 0x692CC7609525A7B2, 0xC0A4E231FDD6DC5C, 0x216936D3CD6E53FE
    .quad   0x6666666666666658, 0x6666666666666666, 0x6666666666666666, 0x6666666666666666
    .quad   0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000
    .quad   0x6DDE8AB3A5B7DDA3, 0x20F09F80775152F5, 0x66EA4E8E64ABE37D, 0x67875F0FD78B7665
