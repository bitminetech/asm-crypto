/*
 * Keccak-256 for RISC-V (RISC-V ELF psABI, LP64D).
 * Requirements: docs/reference/keccak-256.md. Layouts: include/crypto.inc.
 *
 * The state is 25 lanes of 8 bytes on the stack, lane x + 5y at 8 * (x + 5y).
 * The 200 bytes after it hold B, the lanes after rho and pi, and before that
 * the last block with its padding. Baseline RV64GC instructions only, so
 * rotations are built from shifts. The function is a leaf.
 */
.set ISA_RISCV64, 1
.include "crypto.inc"
.include "keccak.inc"
.include "platform.inc"

.set STATE, 0
.set B, 200
.set DATA, 400          /* next input bytes */
.set LEFT, 408          /* bytes left */
.set LAST, 416          /* 1 on the last block */
.set DIGEST, 424        /* the digest pointer */
.set FRAME, 432

/* d = s rotated left by r. Uses tmp. d may be s. */
.macro ROL d, s, r, tmp
    .if \r
    slli    \tmp, \s, \r
    srli    \d, \s, 64 - \r
    or      \d, \d, \tmp
    .else
    mv      \d, \s
    .endif
.endm

/* theta: register c = C[x], the XOR of column x. Uses a5. */
.macro COLUMN c, x
    ld      \c, 8*\x(sp)
    ld      a5, 8*\x+40(sp)
    xor     \c, \c, a5
    ld      a5, 8*\x+80(sp)
    xor     \c, \c, a5
    ld      a5, 8*\x+120(sp)
    xor     \c, \c, a5
    ld      a5, 8*\x+160(sp)
    xor     \c, \c, a5
.endm

/* theta: lane at byte off ^= register d. Uses a5. */
.macro MIX off, d
    ld      a5, \off(sp)
    xor     a5, a5, \d
    sd      a5, \off(sp)
.endm

/* rho and pi: B[dst] = A[src] rotated left by rot. Uses a5, a6. */
.macro RHO_PI src, dst, rot
    ld      a5, 8*\src(sp)
    ROL     a5, a5, \rot, a6
    sd      a5, B+8*\dst(sp)
.endm

/* chi: lane at byte out = b0 ^ (~b1 & b2). Uses a5. */
.macro CHI_LANE out, b0, b1, b2
    not     a5, \b1
    and     a5, a5, \b2
    xor     a5, a5, \b0
    sd      a5, \out(sp)
.endm

.macro CHI y
    ld      t0, B+40*\y(sp)
    ld      t1, B+40*\y+8(sp)
    ld      t2, B+40*\y+16(sp)
    ld      t3, B+40*\y+24(sp)
    ld      t4, B+40*\y+32(sp)
    CHI_LANE 40*\y, t0, t1, t2
    CHI_LANE 40*\y+8, t1, t2, t3
    CHI_LANE 40*\y+16, t2, t3, t4
    CHI_LANE 40*\y+24, t3, t4, t0
    CHI_LANE 40*\y+32, t4, t0, t1
.endm

/*
 * crypto_keccak256(message, digest) -> status
 * a1 rounds left, a7 the round constant. t0 to t4 C, t5, t6, a2, a3, a4 D
 * in theta. a5, a6 temporary.
 */
FUNCTION crypto_keccak256
    addi    sp, sp, -FRAME
    UNWIND_ALLOC FRAME
    UNWIND_END_PROLOGUE
    sd      a1, DIGEST(sp)
    ld      t0, CRYPTO_BYTES_OFFSET(a0)
    ld      t1, CRYPTO_BYTES_COUNT(a0)
    add     t0, a0, t0
    sd      t0, DATA(sp)
    sd      t1, LEFT(sp)
    sd      zero, LAST(sp)
    li      t0, 0
1:  add     t1, sp, t0
    sd      zero, 0(t1)
    addi    t0, t0, 8
    li      t1, 200
    bltu    t0, t1, 1b

    /* Take a full block, or build the last one: the bytes left, 0x01, zeros, 0x80. */
2:  ld      t1, LEFT(sp)
    ld      t2, DATA(sp)
    li      t3, CRYPTO_KECCAK256_RATE
    bgeu    t1, t3, 4f
    addi    t4, sp, B
    li      t0, 0
3:  add     t5, t4, t0
    sd      zero, 0(t5)
    addi    t0, t0, 8
    bltu    t0, t3, 3b
    li      t0, 0
31: bgeu    t0, t1, 32f
    add     t5, t2, t0
    lbu     t6, 0(t5)
    add     t5, t4, t0
    sb      t6, 0(t5)
    addi    t0, t0, 1
    j       31b
32: add     t5, t4, t1
    lbu     t6, 0(t5)
    xori    t6, t6, 0x01
    sb      t6, 0(t5)
    lbu     t6, CRYPTO_KECCAK256_RATE-1(t4)
    xori    t6, t6, 0x80
    sb      t6, CRYPTO_KECCAK256_RATE-1(t4)
    mv      t2, t4
    li      t1, CRYPTO_KECCAK256_RATE
    sd      t1, LEFT(sp)
    li      t5, 1
    sd      t5, LAST(sp)

    /* Absorb: XOR the 17 lanes of the block into the state. */
4:  li      t0, 0
5:  add     t5, t2, t0
    ld      t6, 0(t5)
    add     t5, sp, t0
    ld      a5, 0(t5)
    xor     a5, a5, t6
    sd      a5, 0(t5)
    addi    t0, t0, 8
    bltu    t0, t3, 5b
    add     t2, t2, t3
    sd      t2, DATA(sp)
    ld      t1, LEFT(sp)
    sub     t1, t1, t3
    sd      t1, LEFT(sp)

    /* Keccak-f[1600]: 24 rounds of theta, rho, pi, chi and iota. */
    lla     a7, 300f
    li      a1, 24
6:  COLUMN  t0, 0
    COLUMN  t1, 1
    COLUMN  t2, 2
    COLUMN  t3, 3
    COLUMN  t4, 4
    ROL     t5, t1, 1, a5                   # D[0] = C[4] ^ rotl(C[1], 1)
    xor     t5, t5, t4
    ROL     t6, t2, 1, a5                   # D[1] = C[0] ^ rotl(C[2], 1)
    xor     t6, t6, t0
    ROL     a2, t3, 1, a5                   # D[2] = C[1] ^ rotl(C[3], 1)
    xor     a2, a2, t1
    ROL     a3, t4, 1, a5                   # D[3] = C[2] ^ rotl(C[4], 1)
    xor     a3, a3, t2
    ROL     a4, t0, 1, a5                   # D[4] = C[3] ^ rotl(C[0], 1)
    xor     a4, a4, t3
    .irp row, 0, 40, 80, 120, 160
    MIX     \row, t5
    MIX     \row+8, t6
    MIX     \row+16, a2
    MIX     \row+24, a3
    MIX     \row+32, a4
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
    ld      a5, 0(a7)                       # iota
    ld      a6, 0(sp)
    xor     a6, a6, a5
    sd      a6, 0(sp)
    addi    a7, a7, 8
    addi    a1, a1, -1
    bnez    a1, 6b
    ld      t0, LAST(sp)
    li      t3, CRYPTO_KECCAK256_RATE
    beqz    t0, 2b

    /* The digest is the first 32 bytes of the state. */
    ld      a1, DIGEST(sp)
    ld      t0, 0(sp)
    ld      t1, 8(sp)
    ld      t2, 16(sp)
    ld      t3, 24(sp)
    sd      t0, 0(a1)
    sd      t1, 8(a1)
    sd      t2, 16(a1)
    sd      t3, 24(a1)
    li      a0, CRYPTO_OK
    UNWIND_BEGIN_EPILOGUE
    addi    sp, sp, FRAME
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
