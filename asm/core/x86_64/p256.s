/*
 * P-256 (secp256r1) for x86-64 (System V AMD64 psABI): public keys, and
 * ECDSA signing (RFC 6979 nonces) and verification, for the TLS
 * certificates of libp2p. AT&T syntax. Baseline x86-64 instructions only.
 * Requirements: docs/reference/p256.md. Layouts: include/p256.inc.
 *
 * The functions and their steps follow the ARM64 file one for one, with the
 * design of secp256k1.s: Montgomery multiplication (CIOS) for p and n, and
 * the complete formulas of Renes, Costello and Batina (algorithms 4 and 6,
 * a = -3). The scalar multiplication doubles and adds for all 256 bits and
 * picks the sum with a mask. No branch or address depends on a private key
 * or a nonce.
 *
 * Every macro has a named parameter. In a macro without one, the Mach-O
 * assembler reads $0 to $9 as positional arguments.
 */
.set ISA_X86_64, 1
.include "crypto.inc"
.include "p256.inc"
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

/* fn(rsp + d, rsp + a, rsp + b, modulus record m). */
.macro OP fn, d, a, b, m
    lea     \d(%rsp), %rdi
    lea     \a(%rsp), %rsi
    lea     \b(%rsp), %rdx
    mov     \m, %rcx
    call    \fn
.endm

.macro FMUL d, a, b, m=%r15
    OP      crypto_p256_mod_mul, \d, \a, \b, \m
.endm

.macro FADD d, a, b, m=%r15
    OP      crypto_p256_mod_add, \d, \a, \b, \m
.endm

.macro FSUB d, a, b, m=%r15
    OP      crypto_p256_mod_sub, \d, \a, \b, \m
.endm

/* rsp + d = b * (rsp + a) mod p, with b in Montgomery form at r14. */
.macro FMULB d, a
    lea     \d(%rsp), %rdi
    mov     %r14, %rsi
    lea     \a(%rsp), %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_mul
.endm

/* Copy 32 bytes from soff(src) to doff(dst). Uses rax. */
.macro COPY dst, doff, src, soff
    .irp i, 0, 8, 16, 24
    mov     \soff+\i(\src), %rax
    mov     %rax, \doff+\i(\dst)
    .endr
.endm

/* r8 to r11 = the 32 big-endian bytes at off(src), as limbs. */
.macro LOAD_BE src, off=0
    mov     \off(\src), %r11
    bswap   %r11
    mov     \off+8(\src), %r10
    bswap   %r10
    mov     \off+16(\src), %r9
    bswap   %r9
    mov     \off+24(\src), %r8
    bswap   %r8
.endm

/* The limbs r8 to r11 as 32 big-endian bytes at off(dst). Uses rax. */
.macro STORE_BE dst, off=0
    mov     %r11, %rax
    bswap   %rax
    mov     %rax, \off(\dst)
    mov     %r10, %rax
    bswap   %rax
    mov     %rax, \off+8(\dst)
    mov     %r9, %rax
    bswap   %rax
    mov     %rax, \off+16(\dst)
    mov     %r8, %rax
    bswap   %rax
    mov     %rax, \off+24(\dst)
.endm

.macro LOAD_LIMBS src, off=0
    mov     \off(\src), %r8
    mov     \off+8(\src), %r9
    mov     \off+16(\src), %r10
    mov     \off+24(\src), %r11
.endm

.macro STORE_LIMBS dst, off=0
    mov     %r8, \off(\dst)
    mov     %r9, \off+8(\dst)
    mov     %r10, \off+16(\dst)
    mov     %r11, \off+24(\dst)
.endm

/* Carry set when the limbs r8 to r11 are below the 4 limbs at m. Uses rax. */
.macro BELOW m
    mov     %r8, %rax
    sub     (\m), %rax
    mov     %r9, %rax
    sbb     8(\m), %rax
    mov     %r10, %rax
    sbb     16(\m), %rax
    mov     %r11, %rax
    sbb     24(\m), %rax
.endm

/* Jump to label when the limbs r8 to r11 are all zero. Uses rcx. */
.macro IF_ZERO label
    mov     %r8, %rcx
    or      %r9, %rcx
    or      %r10, %rcx
    or      %r11, %rcx
    jz      \label
.endm

/* The limbs r8 to r11 minus n when they are n or more (they are below 2n). Uses rax, rcx, rdx, rsi. */
.macro REDUCE_N m
    mov     %r8, %rax
    sub     (\m), %rax
    mov     %r9, %rdx
    sbb     8(\m), %rdx
    mov     %r10, %rcx
    sbb     16(\m), %rcx
    mov     %r11, %rsi
    sbb     24(\m), %rsi
    cmovnc  %rax, %r8
    cmovnc  %rdx, %r9
    cmovnc  %rcx, %r10
    cmovnc  %rsi, %r11
.endm

/* The point G at rsp + off: x, y and Z = 1, in Montgomery form. Uses rax, rdx. */
.macro LOAD_G off
    lea     322f(%rip), %rdx
    COPY    %rsp, \off, %rdx, 0
    COPY    %rsp, \off+32, %rdx, 32
    lea     320f(%rip), %rdx
    COPY    %rsp, \off+64, %rdx, CRYPTO_P256_MOD_ONE
.endm

/* The 32 bytes at rsp + off = the number 1, or 0. */
.macro SET_ONE off
    movq    $1, \off(%rsp)
    movq    $0, \off+8(%rsp)
    movq    $0, \off+16(%rsp)
    movq    $0, \off+24(%rsp)
.endm

.macro SET_ZERO off
    movq    $0, \off(%rsp)
    movq    $0, \off+8(%rsp)
    movq    $0, \off+16(%rsp)
    movq    $0, \off+24(%rsp)
.endm

/* ---------------------------------------------------------------- Public keys */

.set K_D, 0
.set K_G, 32
.set K_Q, 128
.set K_XY, 224
.set K_FRAME, 296

/*
 * crypto_p256_public_key(private_key, public_key) -> status
 * rbx private_key, rbp public_key.
 */
FUNCTION crypto_p256_public_key
    ENTER   K_FRAME
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    LOAD_BE %rbx
    mov     $CRYPTO_INVALID_PRIVATE_KEY, %eax
    IF_ZERO 9f
    lea     321f(%rip), %rdx
    BELOW   %rdx
    mov     $CRYPTO_INVALID_PRIVATE_KEY, %eax
    jae     9f
    STORE_LIMBS %rsp, K_D
    LOAD_G  K_G
    lea     K_Q(%rsp), %rdi
    lea     K_D(%rsp), %rsi
    lea     K_G(%rsp), %rdx
    call    crypto_p256_point_mul
    lea     K_XY(%rsp), %rdi
    lea     K_Q(%rsp), %rsi
    call    crypto_p256_point_affine
    movb    $4, (%rbp)                      /* 0x04, x, y */
    LOAD_LIMBS %rsp, K_XY
    STORE_BE %rbp, 1
    LOAD_LIMBS %rsp, K_XY+32
    STORE_BE %rbp, 33
    mov     $CRYPTO_OK, %eax
9:  LEAVE   K_FRAME
END_FUNCTION crypto_p256_public_key

/* ---------------------------------------------------------------- ECDSA */

.set S_KL, 0            /* K as a ByteList: 24 bytes of header, then K */
.set S_ML, 64           /* the HMAC message as a ByteList: V, a byte, x, h */
.set S_SCR, 192         /* HMAC scratch, 200 bytes */
.set S_OUT, 392         /* HMAC output */
.set S_D, 424           /* the private key d */
.set S_Z, 456           /* the hash, mod n */
.set S_K, 488           /* the nonce k */
.set S_G, 520
.set S_R, 616           /* k * G */
.set S_XY, 712
.set S_RR, 776          /* r */
.set S_S, 808           /* s */
.set S_T1, 840
.set S_T2, 872
.set S_T3, 904
.set S_ONE, 936
.set S_R2, 968          /* 2^512 mod n */
.set S_FRAME, 1016
.set S_V, S_ML + 24
.set S_SEP, S_ML + 56

/* K or V (dst) = HMAC-SHA-256 with key K of the first count bytes of the message. */
.macro HMAC_STEP count, dst
    movq    $\count, S_ML+CRYPTO_BYTES_COUNT(%rsp)
    movq    $200, S_SCR(%rsp)
    lea     S_KL(%rsp), %rdi
    lea     S_ML(%rsp), %rsi
    lea     S_SCR(%rsp), %rdx
    lea     S_OUT(%rsp), %rcx
    CALL_GLOBAL crypto_hmac_sha256
    COPY    %rsp, \dst, %rsp, S_OUT
.endm

/*
 * crypto_p256_sign(private_key, hash, signature) -> status
 * r12 private_key, r13 hash, r14 signature, r15 n record.
 * The nonce follows RFC 6979 section 3.2 with HMAC-SHA-256, qlen = hlen = 256.
 * s is written as computed: P-256 has no low s rule.
 */
FUNCTION crypto_p256_sign
    ENTER   S_FRAME
    mov     %rdi, %r12
    mov     %rsi, %r13
    mov     %rdx, %r14
    lea     321f(%rip), %r15
    LOAD_BE %r12
    mov     $CRYPTO_INVALID_PRIVATE_KEY, %eax
    IF_ZERO 9f
    BELOW   %r15
    mov     $CRYPTO_INVALID_PRIVATE_KEY, %eax
    jae     9f
    STORE_LIMBS %rsp, S_D
    LOAD_BE %r13
    REDUCE_N %r15
    STORE_LIMBS %rsp, S_Z
    STORE_BE %rsp, S_ML+24+33+32            /* bits2octets(h) */
    COPY    %rsp, S_ML+24+33, %r12, 0       /* int2octets(x): the key bytes */
    SET_ONE S_ONE
    COPY    %rsp, S_R2, %r15, CRYPTO_P256_MOD_R2
    LOAD_G  S_G
    movq    $(CRYPTO_BYTES_FIXED + 32), S_KL+CRYPTO_BYTES_SIZE(%rsp)    /* K = 0x00 * 32 */
    movq    $CRYPTO_BYTES_FIXED, S_KL+CRYPTO_BYTES_OFFSET(%rsp)
    movq    $32, S_KL+CRYPTO_BYTES_COUNT(%rsp)
    SET_ZERO S_KL+24
    movq    $128, S_ML+CRYPTO_BYTES_SIZE(%rsp)                         /* V = 0x01 * 32 */
    movq    $CRYPTO_BYTES_FIXED, S_ML+CRYPTO_BYTES_OFFSET(%rsp)
    movabs  $0x0101010101010101, %rax
    mov     %rax, S_V(%rsp)
    mov     %rax, S_V+8(%rsp)
    mov     %rax, S_V+16(%rsp)
    mov     %rax, S_V+24(%rsp)
    movb    $0, S_SEP(%rsp)                 /* K = HMAC_K(V || 0x00 || x || h) */
    HMAC_STEP 97, S_KL+24
    HMAC_STEP 32, S_V                       /* V = HMAC_K(V) */
    movb    $1, S_SEP(%rsp)                 /* K = HMAC_K(V || 0x01 || x || h) */
    HMAC_STEP 97, S_KL+24
    HMAC_STEP 32, S_V

    /* T = V = HMAC_K(V); k = bits2int(T), used when 1 <= k < n. */
1:  HMAC_STEP 32, S_V
    LOAD_BE %rsp, S_V
    IF_ZERO 8f
    BELOW   %r15
    jae     8f
    STORE_LIMBS %rsp, S_K
    lea     S_R(%rsp), %rdi
    lea     S_K(%rsp), %rsi
    lea     S_G(%rsp), %rdx
    call    crypto_p256_point_mul
    lea     S_XY(%rsp), %rdi
    lea     S_R(%rsp), %rsi
    call    crypto_p256_point_affine
    LOAD_LIMBS %rsp, S_XY                   /* r = x mod n */
    REDUCE_N %r15
    IF_ZERO 8f
    STORE_LIMBS %rsp, S_RR
    FMUL    S_T1, S_RR, S_R2                /* s = k^-1 (z + r d) mod n, Montgomery form */
    FMUL    S_T2, S_D, S_R2
    FMUL    S_T1, S_T1, S_T2
    FMUL    S_T2, S_Z, S_R2
    FADD    S_T1, S_T1, S_T2
    FMUL    S_T2, S_K, S_R2
    lea     S_T3(%rsp), %rdi
    lea     S_T2(%rsp), %rsi
    lea     327f(%rip), %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_pow
    FMUL    S_T1, S_T3, S_T1
    FMUL    S_S, S_T1, S_ONE
    LOAD_LIMBS %rsp, S_S
    IF_ZERO 8f
    STORE_BE %r14, 32
    LOAD_LIMBS %rsp, S_RR
    STORE_BE %r14, 0
    mov     $CRYPTO_OK, %eax
    jmp     9f

    /* Next candidate: K = HMAC_K(V || 0x00), V = HMAC_K(V). */
8:  movb    $0, S_SEP(%rsp)
    HMAC_STEP 33, S_KL+24
    HMAC_STEP 32, S_V
    jmp     1b
9:  LEAVE   S_FRAME
END_FUNCTION crypto_p256_sign

.set V_P, 0
.set V_G, 96
.set V_A, 192
.set V_B, 288
.set V_C, 384
.set V_XY, 480
.set V_RR, 544
.set V_S, 576
.set V_Z, 608
.set V_W, 640
.set V_U1, 672
.set V_U2, 704
.set V_T, 736
.set V_ONE, 768
.set V_R2, 800
.set V_FRAME, 840

/*
 * crypto_p256_verify(public_key, hash, signature, valid) -> status
 * r12 public_key, r13 hash, r14 signature, rbx valid, rbp the result,
 * r15 n record. Valid when 1 <= r, s < n and x(u1 G + u2 Q) mod n = r,
 * with u1 = z / s and u2 = r / s.
 */
FUNCTION crypto_p256_verify
    ENTER   V_FRAME
    mov     %rdi, %r12
    mov     %rsi, %r13
    mov     %rdx, %r14
    mov     %rcx, %rbx
    lea     321f(%rip), %r15
    lea     V_P(%rsp), %rdi
    mov     %r12, %rsi
    call    crypto_p256_point_load
    test    %rax, %rax
    jnz     9f
    xor     %ebp, %ebp
    LOAD_BE %r14, 0
    IF_ZERO 7f
    BELOW   %r15
    jae     7f
    STORE_LIMBS %rsp, V_RR
    LOAD_BE %r14, 32
    IF_ZERO 7f
    BELOW   %r15
    jae     7f
    STORE_LIMBS %rsp, V_S
    LOAD_BE %r13
    REDUCE_N %r15
    STORE_LIMBS %rsp, V_Z
    SET_ONE V_ONE
    COPY    %rsp, V_R2, %r15, CRYPTO_P256_MOD_R2
    LOAD_G  V_G
    FMUL    V_T, V_S, V_R2
    lea     V_W(%rsp), %rdi
    lea     V_T(%rsp), %rsi
    lea     327f(%rip), %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_pow
    FMUL    V_T, V_Z, V_R2
    FMUL    V_U1, V_T, V_W
    FMUL    V_U1, V_U1, V_ONE
    FMUL    V_T, V_RR, V_R2
    FMUL    V_U2, V_T, V_W
    FMUL    V_U2, V_U2, V_ONE
    lea     V_A(%rsp), %rdi
    lea     V_U1(%rsp), %rsi
    lea     V_G(%rsp), %rdx
    call    crypto_p256_point_mul
    lea     V_B(%rsp), %rdi
    lea     V_U2(%rsp), %rsi
    lea     V_P(%rsp), %rdx
    call    crypto_p256_point_mul
    lea     V_C(%rsp), %rdi
    lea     V_A(%rsp), %rsi
    lea     V_B(%rsp), %rdx
    call    crypto_p256_point_add
    lea     V_XY(%rsp), %rdi
    lea     V_C(%rsp), %rsi
    call    crypto_p256_point_affine
    LOAD_LIMBS %rsp, V_XY
    REDUCE_N %r15
    xor     V_RR(%rsp), %r8
    xor     V_RR+8(%rsp), %r9
    xor     V_RR+16(%rsp), %r10
    xor     V_RR+24(%rsp), %r11
    or      %r9, %r8
    or      %r11, %r10
    or      %r10, %r8
    sete    %bpl
7:  mov     %rbp, (%rbx)
    mov     $CRYPTO_OK, %eax
9:  LEAVE   V_FRAME
END_FUNCTION crypto_p256_verify

/* ---------------------------------------------------------------- Points */

.set L_X, 0
.set L_Y, 32
.set L_RHS, 64
.set L_T, 96
.set L_FRAME, 136

/*
 * crypto_p256_point_load(point, public_key) -> status: the point of an
 * uncompressed public key (SEC 1 section 2.3.4), with Z = 1, after checking
 * that x, y < p and y^2 = x^3 - 3x + b. rbx point, rbp public_key,
 * r15 p record.
 */
LOCAL_FUNCTION crypto_p256_point_load
    ENTER   L_FRAME
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    lea     320f(%rip), %r15
    mov     $CRYPTO_INVALID_PUBLIC_KEY, %eax
    cmpb    $4, (%rbp)
    jne     9f
    LOAD_BE %rbp, 1
    BELOW   %r15
    mov     $CRYPTO_INVALID_PUBLIC_KEY, %eax
    jae     9f
    STORE_LIMBS %rsp, L_X
    LOAD_BE %rbp, 33
    BELOW   %r15
    mov     $CRYPTO_INVALID_PUBLIC_KEY, %eax
    jae     9f
    STORE_LIMBS %rsp, L_Y
    mov     %rbx, %rdi                      /* X, Y in Montgomery form */
    lea     L_X(%rsp), %rsi
    lea     CRYPTO_P256_MOD_R2(%r15), %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_mul
    lea     32(%rbx), %rdi
    lea     L_Y(%rsp), %rsi
    lea     CRYPTO_P256_MOD_R2(%r15), %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_mul
    COPY    %rbx, 64, %r15, CRYPTO_P256_MOD_ONE
    lea     L_RHS(%rsp), %rdi               /* x^3 - 3x + b */
    mov     %rbx, %rsi
    mov     %rbx, %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_mul
    lea     L_RHS(%rsp), %rdi
    lea     L_RHS(%rsp), %rsi
    mov     %rbx, %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_mul
    lea     L_T(%rsp), %rdi
    mov     %rbx, %rsi
    mov     %rbx, %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_add
    lea     L_T(%rsp), %rdi
    lea     L_T(%rsp), %rsi
    mov     %rbx, %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_add
    FSUB    L_RHS, L_RHS, L_T
    lea     L_RHS(%rsp), %rdi
    lea     L_RHS(%rsp), %rsi
    lea     323f(%rip), %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_add
    lea     L_T(%rsp), %rdi                 /* y^2 */
    lea     32(%rbx), %rsi
    lea     32(%rbx), %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_mul
    LOAD_LIMBS %rsp, L_T
    xor     L_RHS(%rsp), %r8
    xor     L_RHS+8(%rsp), %r9
    xor     L_RHS+16(%rsp), %r10
    xor     L_RHS+24(%rsp), %r11
    or      %r9, %r8
    or      %r11, %r10
    or      %r10, %r8
    mov     $CRYPTO_INVALID_PUBLIC_KEY, %eax
    jnz     9f                              /* not on the curve */
    mov     $CRYPTO_OK, %eax
9:  LEAVE   L_FRAME
END_FUNCTION crypto_p256_point_load

.set M_R, 0
.set M_T, 96
.set M_P, 192
.set M_FRAME, 296

/*
 * crypto_p256_point_mul(point, scalar, base): point = scalar * base.
 * scalar: 4 limbs. For each bit from 255 down: R = 2R, T = R + base, and R
 * takes T where the bit is 1, through a mask. rbx point, rbp scalar, r12 bit.
 */
LOCAL_FUNCTION crypto_p256_point_mul
    ENTER   M_FRAME
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    lea     320f(%rip), %r15
    COPY    %rsp, M_P, %rdx, 0
    COPY    %rsp, M_P+32, %rdx, 32
    COPY    %rsp, M_P+64, %rdx, 64
    SET_ZERO M_R                            /* R = (0 : 1 : 0), the point at infinity */
    COPY    %rsp, M_R+32, %r15, CRYPTO_P256_MOD_ONE
    SET_ZERO M_R+64
    mov     $255, %r12d
1:  mov     %rsp, %rdi
    mov     %rsp, %rsi
    call    crypto_p256_point_double
    lea     M_T(%rsp), %rdi
    mov     %rsp, %rsi
    lea     M_P(%rsp), %rdx
    call    crypto_p256_point_add
    mov     %r12, %rax
    shr     $6, %rax
    mov     (%rbp,%rax,8), %rax
    mov     %r12d, %ecx
    shr     %cl, %rax
    and     $1, %eax
    neg     %rax
    xor     %ecx, %ecx
2:  mov     (%rsp,%rcx,8), %rdx
    mov     M_T(%rsp,%rcx,8), %rsi
    xor     %rdx, %rsi
    and     %rax, %rsi
    xor     %rsi, %rdx
    mov     %rdx, (%rsp,%rcx,8)
    inc     %ecx
    cmp     $12, %ecx
    jb      2b
    dec     %r12
    jns     1b
    COPY    %rbx, 0, %rsp, M_R
    COPY    %rbx, 32, %rsp, M_R+32
    COPY    %rbx, 64, %rsp, M_R+64
    LEAVE   M_FRAME
END_FUNCTION crypto_p256_point_mul

.set A_X1, 0
.set A_Y1, 32
.set A_Z1, 64
.set A_X2, 96
.set A_Y2, 128
.set A_Z2, 160
.set A_T0, 192
.set A_T1, 224
.set A_T2, 256
.set A_T3, 288
.set A_T4, 320
.set A_X3, 352
.set A_Y3, 384
.set A_Z3, 416
.set A_FRAME, 456

/*
 * crypto_p256_point_add(point, first, second): point = first + second,
 * Renes-Costello-Batina algorithm 4 (a = -3). Any of the three may be the
 * same. rbx point, r14 b, r15 p record.
 */
LOCAL_FUNCTION crypto_p256_point_add
    ENTER   A_FRAME
    mov     %rdi, %rbx
    lea     320f(%rip), %r15
    lea     323f(%rip), %r14
    COPY    %rsp, A_X1, %rsi, 0
    COPY    %rsp, A_Y1, %rsi, 32
    COPY    %rsp, A_Z1, %rsi, 64
    COPY    %rsp, A_X2, %rdx, 0
    COPY    %rsp, A_Y2, %rdx, 32
    COPY    %rsp, A_Z2, %rdx, 64
    FMUL    A_T0, A_X1, A_X2                /* 1 */
    FMUL    A_T1, A_Y1, A_Y2                /* 2 */
    FMUL    A_T2, A_Z1, A_Z2                /* 3 */
    FADD    A_T3, A_X1, A_Y1                /* 4 */
    FADD    A_T4, A_X2, A_Y2                /* 5 */
    FMUL    A_T3, A_T3, A_T4                /* 6 */
    FADD    A_T4, A_T0, A_T1                /* 7 */
    FSUB    A_T3, A_T3, A_T4                /* 8 */
    FADD    A_T4, A_Y1, A_Z1                /* 9 */
    FADD    A_X3, A_Y2, A_Z2                /* 10 */
    FMUL    A_T4, A_T4, A_X3                /* 11 */
    FADD    A_X3, A_T1, A_T2                /* 12 */
    FSUB    A_T4, A_T4, A_X3                /* 13 */
    FADD    A_X3, A_X1, A_Z1                /* 14 */
    FADD    A_Y3, A_X2, A_Z2                /* 15 */
    FMUL    A_X3, A_X3, A_Y3                /* 16 */
    FADD    A_Y3, A_T0, A_T2                /* 17 */
    FSUB    A_Y3, A_X3, A_Y3                /* 18 */
    FMULB   A_Z3, A_T2                      /* 19 */
    FSUB    A_X3, A_Y3, A_Z3                /* 20 */
    FADD    A_Z3, A_X3, A_X3                /* 21 */
    FADD    A_X3, A_X3, A_Z3                /* 22 */
    FSUB    A_Z3, A_T1, A_X3                /* 23 */
    FADD    A_X3, A_T1, A_X3                /* 24 */
    FMULB   A_Y3, A_Y3                      /* 25 */
    FADD    A_T1, A_T2, A_T2                /* 26 */
    FADD    A_T2, A_T1, A_T2                /* 27 */
    FSUB    A_Y3, A_Y3, A_T2                /* 28 */
    FSUB    A_Y3, A_Y3, A_T0                /* 29 */
    FADD    A_T1, A_Y3, A_Y3                /* 30 */
    FADD    A_Y3, A_T1, A_Y3                /* 31 */
    FADD    A_T1, A_T0, A_T0                /* 32 */
    FADD    A_T0, A_T1, A_T0                /* 33 */
    FSUB    A_T0, A_T0, A_T2                /* 34 */
    FMUL    A_T1, A_T4, A_Y3                /* 35 */
    FMUL    A_T2, A_T0, A_Y3                /* 36 */
    FMUL    A_Y3, A_X3, A_Z3                /* 37 */
    FADD    A_Y3, A_Y3, A_T2                /* 38 */
    FMUL    A_X3, A_T3, A_X3                /* 39 */
    FSUB    A_X3, A_X3, A_T1                /* 40 */
    FMUL    A_Z3, A_T4, A_Z3                /* 41 */
    FMUL    A_T1, A_T3, A_T0                /* 42 */
    FADD    A_Z3, A_Z3, A_T1                /* 43 */
    COPY    %rbx, 0, %rsp, A_X3
    COPY    %rbx, 32, %rsp, A_Y3
    COPY    %rbx, 64, %rsp, A_Z3
    LEAVE   A_FRAME
END_FUNCTION crypto_p256_point_add

.set D_X, 0
.set D_Y, 32
.set D_Z, 64
.set D_T0, 96
.set D_T1, 128
.set D_T2, 160
.set D_T3, 192
.set D_X3, 224
.set D_Y3, 256
.set D_Z3, 288
.set D_FRAME, 328

/*
 * crypto_p256_point_double(point, base): point = 2 * base,
 * Renes-Costello-Batina algorithm 6 (a = -3). point may be base.
 * rbx point, r14 b, r15 p record.
 */
LOCAL_FUNCTION crypto_p256_point_double
    ENTER   D_FRAME
    mov     %rdi, %rbx
    lea     320f(%rip), %r15
    lea     323f(%rip), %r14
    COPY    %rsp, D_X, %rsi, 0
    COPY    %rsp, D_Y, %rsi, 32
    COPY    %rsp, D_Z, %rsi, 64
    FMUL    D_T0, D_X, D_X                  /* 1 */
    FMUL    D_T1, D_Y, D_Y                  /* 2 */
    FMUL    D_T2, D_Z, D_Z                  /* 3 */
    FMUL    D_T3, D_X, D_Y                  /* 4 */
    FADD    D_T3, D_T3, D_T3                /* 5 */
    FMUL    D_Z3, D_X, D_Z                  /* 6 */
    FADD    D_Z3, D_Z3, D_Z3                /* 7 */
    FMULB   D_Y3, D_T2                      /* 8 */
    FSUB    D_Y3, D_Y3, D_Z3                /* 9 */
    FADD    D_X3, D_Y3, D_Y3                /* 10 */
    FADD    D_Y3, D_X3, D_Y3                /* 11 */
    FSUB    D_X3, D_T1, D_Y3                /* 12 */
    FADD    D_Y3, D_T1, D_Y3                /* 13 */
    FMUL    D_Y3, D_X3, D_Y3                /* 14 */
    FMUL    D_X3, D_X3, D_T3                /* 15 */
    FADD    D_T3, D_T2, D_T2                /* 16 */
    FADD    D_T2, D_T2, D_T3                /* 17 */
    FMULB   D_Z3, D_Z3                      /* 18 */
    FSUB    D_Z3, D_Z3, D_T2                /* 19 */
    FSUB    D_Z3, D_Z3, D_T0                /* 20 */
    FADD    D_T3, D_Z3, D_Z3                /* 21 */
    FADD    D_Z3, D_Z3, D_T3                /* 22 */
    FADD    D_T3, D_T0, D_T0                /* 23 */
    FADD    D_T0, D_T3, D_T0                /* 24 */
    FSUB    D_T0, D_T0, D_T2                /* 25 */
    FMUL    D_T0, D_T0, D_Z3                /* 26 */
    FADD    D_Y3, D_Y3, D_T0                /* 27 */
    FMUL    D_T0, D_Y, D_Z                  /* 28 */
    FADD    D_T0, D_T0, D_T0                /* 29 */
    FMUL    D_Z3, D_T0, D_Z3                /* 30 */
    FSUB    D_X3, D_X3, D_Z3                /* 31 */
    FMUL    D_Z3, D_T0, D_T1                /* 32 */
    FADD    D_Z3, D_Z3, D_Z3                /* 33 */
    FADD    D_Z3, D_Z3, D_Z3                /* 34 */
    COPY    %rbx, 0, %rsp, D_X3
    COPY    %rbx, 32, %rsp, D_Y3
    COPY    %rbx, 64, %rsp, D_Z3
    LEAVE   D_FRAME
END_FUNCTION crypto_p256_point_double

/*
 * crypto_p256_point_affine(xy, point): x = X / Z and y = Y / Z as plain
 * limbs at xy and xy + 32. The point at infinity gives 0, 0.
 * rbx xy, rbp point, r15 p record. 1 / Z at rsp, the number 1 at rsp + 32.
 */
LOCAL_FUNCTION crypto_p256_point_affine
    ENTER   72
    mov     %rdi, %rbx
    mov     %rsi, %rbp
    lea     320f(%rip), %r15
    SET_ONE 32
    mov     %rsp, %rdi
    lea     64(%rbp), %rsi
    lea     325f(%rip), %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_pow
    mov     %rbx, %rdi
    mov     %rbp, %rsi
    mov     %rsp, %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_mul
    mov     %rbx, %rdi
    mov     %rbx, %rsi
    lea     32(%rsp), %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_mul
    lea     32(%rbx), %rdi
    lea     32(%rbp), %rsi
    mov     %rsp, %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_mul
    lea     32(%rbx), %rdi
    lea     32(%rbx), %rsi
    lea     32(%rsp), %rdx
    mov     %r15, %rcx
    call    crypto_p256_mod_mul
    LEAVE   72
END_FUNCTION crypto_p256_point_affine

/* ---------------------------------------------------------------- Modular arithmetic */

/*
 * crypto_p256_mod_pow(result, base, exponent, modulus): base^exponent
 * in Montgomery form, by squaring and multiplying from bit 255 down. The
 * exponent is public. rbx result, rbp exponent, r12 modulus, r13 bit.
 * base at rsp, the running value at rsp + 32.
 */
LOCAL_FUNCTION crypto_p256_mod_pow
    ENTER   72
    mov     %rdi, %rbx
    mov     %rdx, %rbp
    mov     %rcx, %r12
    COPY    %rsp, 0, %rsi, 0
    COPY    %rsp, 32, %r12, CRYPTO_P256_MOD_ONE
    mov     $255, %r13d
1:  lea     32(%rsp), %rdi
    lea     32(%rsp), %rsi
    lea     32(%rsp), %rdx
    mov     %r12, %rcx
    call    crypto_p256_mod_mul
    mov     %r13, %rax
    shr     $6, %rax
    mov     (%rbp,%rax,8), %rax
    mov     %r13d, %ecx
    shr     %cl, %rax
    test    $1, %al
    jz      2f
    lea     32(%rsp), %rdi
    lea     32(%rsp), %rsi
    mov     %rsp, %rdx
    mov     %r12, %rcx
    call    crypto_p256_mod_mul
2:  dec     %r13
    jns     1b
    COPY    %rbx, 0, %rsp, 32
    LEAVE   72
END_FUNCTION crypto_p256_mod_pow

/*
 * crypto_p256_mod_mul(result, a, b, modulus): a * b / 2^256 mod m, for
 * a, b < m (CIOS). result may be a or b.
 * rbx b, T r8 to r13, b_i r14, q r15, rbp the carry limb.
 */
LOCAL_FUNCTION crypto_p256_mod_mul
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
    imul    CRYPTO_P256_MOD_INVERSE(%rcx), %r15
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
END_FUNCTION crypto_p256_mod_mul

/* crypto_p256_mod_add(result, a, b, modulus): a + b mod m, for a, b < m. */
LOCAL_FUNCTION crypto_p256_mod_add
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
END_FUNCTION crypto_p256_mod_add

/* crypto_p256_mod_sub(result, a, b, modulus): a - b mod m, for a, b < m. */
LOCAL_FUNCTION crypto_p256_mod_sub
    UNWIND_END_PROLOGUE
    mov     (%rsi), %r8
    mov     8(%rsi), %r9
    mov     16(%rsi), %r10
    mov     24(%rsi), %r11
    sub     (%rdx), %r8
    sbb     8(%rdx), %r9
    sbb     16(%rdx), %r10
    sbb     24(%rdx), %r11
    sbb     %rax, %rax                      /* all ones on a borrow */
    mov     %r8, (%rdi)                     /* the difference, then the difference + m on a borrow */
    mov     %r9, 8(%rdi)
    mov     %r10, 16(%rdi)
    mov     %r11, 24(%rdi)
    add     (%rcx), %r8
    adc     8(%rcx), %r9
    adc     16(%rcx), %r10
    adc     24(%rcx), %r11
    test    %rax, %rax
    cmovz   (%rdi), %r8
    cmovz   8(%rdi), %r9
    cmovz   16(%rdi), %r10
    cmovz   24(%rdi), %r11
    mov     %r8, (%rdi)
    mov     %r9, 8(%rdi)
    mov     %r10, 16(%rdi)
    mov     %r11, 24(%rdi)
    ret
END_FUNCTION crypto_p256_mod_sub

/* ---------------------------------------------------------------- Constants (SP 800-186 section 3.2.1.3) */

    .p2align 3
/* p = 2^256 - 2^224 + 2^192 + 2^96 - 1: p, -p^-1 mod 2^64, 2^256 mod p, 2^512 mod p. */
320:
    .quad   0xFFFFFFFFFFFFFFFF, 0x00000000FFFFFFFF, 0x0000000000000000, 0xFFFFFFFF00000001
    .quad   0x0000000000000001
    .quad   0x0000000000000001, 0xFFFFFFFF00000000, 0xFFFFFFFFFFFFFFFF, 0x00000000FFFFFFFE
    .quad   0x0000000000000003, 0xFFFFFFFBFFFFFFFF, 0xFFFFFFFFFFFFFFFE, 0x00000004FFFFFFFD
/* n, the group order: n, -n^-1 mod 2^64, 2^256 mod n, 2^512 mod n. */
321:
    .quad   0xF3B9CAC2FC632551, 0xBCE6FAADA7179E84, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF00000000
    .quad   0xCCD1C8AAEE00BC4F
    .quad   0x0C46353D039CDAAF, 0x4319055258E8617B, 0x0000000000000000, 0x00000000FFFFFFFF
    .quad   0x83244C95BE79EEA2, 0x4699799C49BD6FA6, 0x2845B2392B6BEC59, 0x66E12D94F3D95620
/* G: x, then y, in Montgomery form. */
322:
    .quad   0x79E730D418A9143C, 0x75BA95FC5FEDB601, 0x79FB732B77622510, 0x18905F76A53755C6
    .quad   0xDDF25357CE95560A, 0x8B4AB8E4BA19E45C, 0xD2E88688DD21F325, 0x8571FF1825885D85
/* b, in Montgomery form. */
323:
    .quad   0xD89CDF6229C4BDDF, 0xACF005CD78843090, 0xE5A220ABF7212ED6, 0xDC30061D04874834
/* p - 2: the exponent of 1 / a mod p. */
325:
    .quad   0xFFFFFFFFFFFFFFFD, 0x00000000FFFFFFFF, 0x0000000000000000, 0xFFFFFFFF00000001
/* n - 2: the exponent of 1 / a mod n. */
327:
    .quad   0xF3B9CAC2FC63254F, 0xBCE6FAADA7179E84, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF00000000
