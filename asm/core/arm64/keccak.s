/*
 * Keccak-256 for ARM64 (AAPCS64).
 * Requirements: docs/reference/keccak-256.md. Layouts: include/crypto.inc.
 *
 * The state is 25 lanes of 8 bytes on the stack, lane x + 5y at 8 * (x + 5y).
 * The 200 bytes after it hold B, the lanes after rho and pi, and before that
 * the last block with its padding. x18 is never used. The function is a leaf.
 */
.set ISA_ARM64, 1
.include "crypto.inc"
.include "keccak.inc"
.include "platform.inc"

.set STATE, 0
.set B, 200
.set FRAME, 400

/* theta: C[x] for column x into register number c. Uses x7. */
.macro COLUMN c, x
    ldr     x\c, [sp, #STATE + 8 * \x]
    ldr     x7, [sp, #STATE + 8 * (\x + 5)]
    eor     x\c, x\c, x7
    ldr     x7, [sp, #STATE + 8 * (\x + 10)]
    eor     x\c, x\c, x7
    ldr     x7, [sp, #STATE + 8 * (\x + 15)]
    eor     x\c, x\c, x7
    ldr     x7, [sp, #STATE + 8 * (\x + 20)]
    eor     x\c, x\c, x7
.endm

/* theta: lane i ^= register number d. Uses x7. */
.macro MIX i, d
    ldr     x7, [sp, #STATE + 8 * \i]
    eor     x7, x7, x\d
    str     x7, [sp, #STATE + 8 * \i]
.endm

/* rho and pi: B[dst] = A[src] rotated left by rot. Uses x7. */
.macro RHO_PI src, dst, rot
    ldr     x7, [sp, #STATE + 8 * \src]
    ror     x7, x7, #((64 - \rot) % 64)
    str     x7, [sp, #B + 8 * \dst]
.endm

/* chi for row y: A[x + 5y] = B[x + 5y] ^ (~B[x + 1 + 5y] & B[x + 2 + 5y]). Uses x7 to x12. */
.macro CHI y
    ldp     x8, x9, [sp, #B + 40 * \y]
    ldp     x10, x11, [sp, #B + 40 * \y + 16]
    ldr     x12, [sp, #B + 40 * \y + 32]
    bic     x7, x10, x9
    eor     x7, x7, x8
    str     x7, [sp, #STATE + 40 * \y]
    bic     x7, x11, x10
    eor     x7, x7, x9
    str     x7, [sp, #STATE + 40 * \y + 8]
    bic     x7, x12, x11
    eor     x7, x7, x10
    str     x7, [sp, #STATE + 40 * \y + 16]
    bic     x7, x8, x12
    eor     x7, x7, x11
    str     x7, [sp, #STATE + 40 * \y + 24]
    bic     x7, x9, x8
    eor     x7, x7, x12
    str     x7, [sp, #STATE + 40 * \y + 32]
.endm

/*
 * crypto_keccak256(message, digest) -> status
 * x0 message (ByteList), x1 digest (32 bytes).
 * x2 next input bytes, x3 bytes left, x4 1 on the last block, x5 rounds left,
 * x6 round constant, x7 to x17 temporary.
 */
FUNCTION crypto_keccak256
    sub     sp, sp, #FRAME
    UNWIND_ALLOC FRAME
    UNWIND_END_PROLOGUE
    ldr     x2, [x0, #CRYPTO_BYTES_OFFSET]
    ldr     x3, [x0, #CRYPTO_BYTES_COUNT]
    add     x2, x0, x2
    mov     x4, #0
    .irp i, 0, 16, 32, 48, 64, 80, 96, 112, 128, 144, 160, 176
    stp     xzr, xzr, [sp, #STATE + \i]
    .endr
    str     xzr, [sp, #STATE + 192]

    /* Take a full block, or build the last one: the bytes left, 0x01, zeros, 0x80. */
1:  cmp     x3, #CRYPTO_KECCAK256_RATE
    b.hs    3f
    .irp i, 0, 16, 32, 48, 64, 80, 96, 112
    stp     xzr, xzr, [sp, #B + \i]
    .endr
    str     xzr, [sp, #B + 128]
    add     x8, sp, #B
    mov     x9, #0
2:  cmp     x9, x3
    b.hs    21f
    ldrb    w10, [x2, x9]
    strb    w10, [x8, x9]
    add     x9, x9, #1
    b       2b
21: ldrb    w10, [x8, x3]
    eor     w10, w10, #0x01
    strb    w10, [x8, x3]
    ldrb    w10, [x8, #CRYPTO_KECCAK256_RATE - 1]
    eor     w10, w10, #0x80
    strb    w10, [x8, #CRYPTO_KECCAK256_RATE - 1]
    mov     x2, x8
    mov     x3, #CRYPTO_KECCAK256_RATE
    mov     x4, #1

    /* Absorb: XOR the 17 lanes of the block into the state. */
3:  mov     x9, #0
4:  ldr     x10, [x2, x9]
    ldr     x11, [sp, x9]
    eor     x11, x11, x10
    str     x11, [sp, x9]
    add     x9, x9, #8
    cmp     x9, #CRYPTO_KECCAK256_RATE
    b.lo    4b
    add     x2, x2, #CRYPTO_KECCAK256_RATE
    sub     x3, x3, #CRYPTO_KECCAK256_RATE

    /* Keccak-f[1600]: 24 rounds of theta, rho, pi, chi and iota. */
    adr     x6, 300f
    mov     x5, #24
5:  COLUMN  8, 0
    COLUMN  9, 1
    COLUMN  10, 2
    COLUMN  11, 3
    COLUMN  12, 4
    ror     x13, x9, #63                    /* D[0] = C[4] ^ rotl(C[1], 1) */
    eor     x13, x13, x12
    ror     x14, x10, #63                   /* D[1] = C[0] ^ rotl(C[2], 1) */
    eor     x14, x14, x8
    ror     x15, x11, #63                   /* D[2] = C[1] ^ rotl(C[3], 1) */
    eor     x15, x15, x9
    ror     x16, x12, #63                   /* D[3] = C[2] ^ rotl(C[4], 1) */
    eor     x16, x16, x10
    ror     x17, x8, #63                    /* D[4] = C[3] ^ rotl(C[0], 1) */
    eor     x17, x17, x11
    .irp y, 0, 5, 10, 15, 20
    MIX     (\y + 0), 13
    MIX     (\y + 1), 14
    MIX     (\y + 2), 15
    MIX     (\y + 3), 16
    MIX     (\y + 4), 17
    .endr
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
    ldr     x7, [x6], #8                    /* iota */
    ldr     x8, [sp, #STATE]
    eor     x8, x8, x7
    str     x8, [sp, #STATE]
    subs    x5, x5, #1
    b.ne    5b
    cbz     x4, 1b

    /* The digest is the first 32 bytes of the state. */
    ldp     x8, x9, [sp, #STATE]
    ldp     x10, x11, [sp, #STATE + 16]
    stp     x8, x9, [x1]
    stp     x10, x11, [x1, #16]
    mov     x0, #CRYPTO_OK
    UNWIND_BEGIN_EPILOGUE
    add     sp, sp, #FRAME
    UNWIND_FREE FRAME
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
