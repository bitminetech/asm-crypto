/*
 * crypto_sha256 for RISC-V (RISC-V ELF psABI, LP64D), FIPS 180-4 section 6.2.
 * Requirements: docs/reference/sha-256.md
 *
 * v1: follows the specification steps directly, one block at a time.
 * Baseline RV64GC instructions only, so rotations are built from shifts.
 * Saves s0-s7, then uses a 480-byte frame.
 *
 * Every 32-bit value is kept sign-extended to 64 bits, which the W-form
 * instructions (addw, slliw, srliw) and lw preserve.
 *
 * Registers:
 *   a0      message, then the address of K
 *   a1      digest
 *   a2      address of the current block
 *   a3      blocks left in the current phase
 *   a4      phase: 0 for message blocks, 1 for padding blocks
 *   a5      round or word index t
 *   a6      number of padding blocks (1 or 2)
 *   s0-s7   working variables a, b, c, d, e, f, g, h
 *   t0-t6   temporaries
 *
 * Frame:
 *   sp + 0    W[0..63], 256 bytes
 *   sp + 256  H[0..7], 32 bytes
 *   sp + 288  padding blocks, 128 bytes
 *   sp + 416  saved s0-s7, 64 bytes
 *
 * Labels: 1 copy, 2 copied, 3 one padding block, 4 blocks, 5 load, 6 expand,
 * 7 round, 8 phase end, 9 done, 20 K, 21 initial H.
 */
.set ISA_RISCV64, 1
.include "crypto.inc"
.include "platform.inc"

FUNCTION crypto_sha256
    addi    sp, sp, -480
    UNWIND_ALLOC 480
    sd      s0, 416(sp)
    UNWIND_SAVE s0, 416
    sd      s1, 424(sp)
    UNWIND_SAVE s1, 424
    sd      s2, 432(sp)
    UNWIND_SAVE s2, 432
    sd      s3, 440(sp)
    UNWIND_SAVE s3, 440
    sd      s4, 448(sp)
    UNWIND_SAVE s4, 448
    sd      s5, 456(sp)
    UNWIND_SAVE s5, 456
    sd      s6, 464(sp)
    UNWIND_SAVE s6, 464
    sd      s7, 472(sp)
    UNWIND_SAVE s7, 472
    UNWIND_END_PROLOGUE

    ld      t0, CRYPTO_BYTES_OFFSET(a0)
    ld      t1, CRYPTO_BYTES_COUNT(a0)          # count
    add     a2, a0, t0                          # message bytes

    /* Zero the 128-byte padding area. */
    sd      zero, 288(sp)
    sd      zero, 296(sp)
    sd      zero, 304(sp)
    sd      zero, 312(sp)
    sd      zero, 320(sp)
    sd      zero, 328(sp)
    sd      zero, 336(sp)
    sd      zero, 344(sp)
    sd      zero, 352(sp)
    sd      zero, 360(sp)
    sd      zero, 368(sp)
    sd      zero, 376(sp)
    sd      zero, 384(sp)
    sd      zero, 392(sp)
    sd      zero, 400(sp)
    sd      zero, 408(sp)

    /* Copy the bytes after the last full block into the padding area. */
    andi    t2, t1, 63                          # rem = count mod 64
    srli    a3, t1, 6                           # full blocks
    slli    t3, a3, 6
    add     t3, a2, t3                          # first byte after them
    addi    t4, sp, 288                         # padding area
    li      t5, 0
1:
    bgeu    t5, t2, 2f
    add     t6, t3, t5
    lbu     t0, 0(t6)
    add     t6, t4, t5
    sb      t0, 0(t6)
    addi    t5, t5, 1
    j       1b
2:
    add     t6, t4, t2
    li      t0, 0x80
    sb      t0, 0(t6)

    /* One padding block when rem < 56, else two. */
    li      a6, 1
    li      t0, 56
    bltu    t2, t0, 3f
    li      a6, 2
3:
    /* Message length in bits, big-endian, in the last 8 bytes of the padding. */
    slli    t0, t1, 3
    slli    t5, a6, 6
    add     t5, t4, t5                          # end of the padding
    srli    t6, t0, 56
    sb      t6, -8(t5)
    srli    t6, t0, 48
    sb      t6, -7(t5)
    srli    t6, t0, 40
    sb      t6, -6(t5)
    srli    t6, t0, 32
    sb      t6, -5(t5)
    srli    t6, t0, 24
    sb      t6, -4(t5)
    srli    t6, t0, 16
    sb      t6, -3(t5)
    srli    t6, t0, 8
    sb      t6, -2(t5)
    sb      t0, -1(t5)

    /* H = initial hash value. */
    lla     t0, 21f
    ld      t1, 0(t0)
    sd      t1, 256(sp)
    ld      t1, 8(t0)
    sd      t1, 264(sp)
    ld      t1, 16(t0)
    sd      t1, 272(sp)
    ld      t1, 24(t0)
    sd      t1, 280(sp)

    lla     a0, 20f
    li      a4, 0

4:
    beqz    a3, 8f

    /* W[0..15]: the block as big-endian words. */
    li      a5, 0
5:
    slli    t1, a5, 2
    add     t2, a2, t1
    lbu     t3, 0(t2)
    lbu     t4, 1(t2)
    lbu     t5, 2(t2)
    lbu     t6, 3(t2)
    slliw   t3, t3, 24
    slli    t4, t4, 16
    slli    t5, t5, 8
    or      t3, t3, t4
    or      t3, t3, t5
    or      t3, t3, t6
    add     t2, sp, t1
    sw      t3, 0(t2)
    addi    a5, a5, 1
    li      t0, 16
    bltu    a5, t0, 5b

    /* W[16..63] = s1(W[t-2]) + W[t-7] + s0(W[t-15]) + W[t-16]. */
6:
    slli    t1, a5, 2
    add     t2, sp, t1                          # address of W[t]
    lw      t0, -60(t2)                         # W[t-15]
    srliw   t3, t0, 7
    slliw   t4, t0, 25
    or      t3, t3, t4
    srliw   t4, t0, 18
    slliw   t5, t0, 14
    or      t4, t4, t5
    xor     t3, t3, t4
    srliw   t4, t0, 3
    xor     t3, t3, t4                          # s0
    lw      t0, -8(t2)                          # W[t-2]
    srliw   t4, t0, 17
    slliw   t5, t0, 15
    or      t4, t4, t5
    srliw   t5, t0, 19
    slliw   t6, t0, 13
    or      t5, t5, t6
    xor     t4, t4, t5
    srliw   t5, t0, 10
    xor     t4, t4, t5                          # s1
    lw      t0, -64(t2)                         # W[t-16]
    addw    t3, t3, t0
    lw      t0, -28(t2)                         # W[t-7]
    addw    t3, t3, t0
    addw    t3, t3, t4
    sw      t3, 0(t2)
    addi    a5, a5, 1
    li      t0, 64
    bltu    a5, t0, 6b

    /* a..h = H. */
    lw      s0, 256(sp)
    lw      s1, 260(sp)
    lw      s2, 264(sp)
    lw      s3, 268(sp)
    lw      s4, 272(sp)
    lw      s5, 276(sp)
    lw      s6, 280(sp)
    lw      s7, 284(sp)

    li      a5, 0
7:
    srliw   t0, s4, 6
    slliw   t1, s4, 26
    or      t0, t0, t1
    srliw   t1, s4, 11
    slliw   t2, s4, 21
    or      t1, t1, t2
    xor     t0, t0, t1
    srliw   t1, s4, 25
    slliw   t2, s4, 7
    or      t1, t1, t2
    xor     t0, t0, t1                          # S1(e)
    addw    s7, s7, t0
    xor     t0, s5, s6
    and     t0, t0, s4
    xor     t0, t0, s6                          # Ch(e, f, g)
    addw    s7, s7, t0
    slli    t1, a5, 2
    add     t2, a0, t1
    lw      t0, 0(t2)                           # K[t]
    addw    s7, s7, t0
    add     t2, sp, t1
    lw      t0, 0(t2)                           # W[t]
    addw    s7, s7, t0                          # T1
    addw    s3, s3, s7                          # d + T1
    srliw   t0, s0, 2
    slliw   t1, s0, 30
    or      t0, t0, t1
    srliw   t1, s0, 13
    slliw   t2, s0, 19
    or      t1, t1, t2
    xor     t0, t0, t1
    srliw   t1, s0, 22
    slliw   t2, s0, 10
    or      t1, t1, t2
    xor     t0, t0, t1                          # S0(a)
    addw    s7, s7, t0
    or      t0, s0, s1
    and     t0, t0, s2
    and     t1, s0, s1
    or      t0, t0, t1                          # Maj(a, b, c)
    addw    t3, s7, t0                          # T1 + T2
    mv      s7, s6                              # h = g
    mv      s6, s5                              # g = f
    mv      s5, s4                              # f = e
    mv      s4, s3                              # e = d + T1
    mv      s3, s2                              # d = c
    mv      s2, s1                              # c = b
    mv      s1, s0                              # b = a
    mv      s0, t3                              # a = T1 + T2
    addi    a5, a5, 1
    li      t0, 64
    bltu    a5, t0, 7b

    /* H = H + a..h. */
    lw      t0, 256(sp)
    addw    t0, t0, s0
    sw      t0, 256(sp)
    lw      t0, 260(sp)
    addw    t0, t0, s1
    sw      t0, 260(sp)
    lw      t0, 264(sp)
    addw    t0, t0, s2
    sw      t0, 264(sp)
    lw      t0, 268(sp)
    addw    t0, t0, s3
    sw      t0, 268(sp)
    lw      t0, 272(sp)
    addw    t0, t0, s4
    sw      t0, 272(sp)
    lw      t0, 276(sp)
    addw    t0, t0, s5
    sw      t0, 276(sp)
    lw      t0, 280(sp)
    addw    t0, t0, s6
    sw      t0, 280(sp)
    lw      t0, 284(sp)
    addw    t0, t0, s7
    sw      t0, 284(sp)

    addi    a2, a2, 64
    addi    a3, a3, -1
    j       4b

8:
    /* After the message blocks, hash the padding blocks once. */
    bnez    a4, 9f
    li      a4, 1
    addi    a2, sp, 288
    mv      a3, a6
    j       4b

9:
    /* digest = H as big-endian words. */
    lw      t0, 256(sp)
    srli    t1, t0, 24
    sb      t1, 0(a1)
    srli    t1, t0, 16
    sb      t1, 1(a1)
    srli    t1, t0, 8
    sb      t1, 2(a1)
    sb      t0, 3(a1)
    lw      t0, 260(sp)
    srli    t1, t0, 24
    sb      t1, 4(a1)
    srli    t1, t0, 16
    sb      t1, 5(a1)
    srli    t1, t0, 8
    sb      t1, 6(a1)
    sb      t0, 7(a1)
    lw      t0, 264(sp)
    srli    t1, t0, 24
    sb      t1, 8(a1)
    srli    t1, t0, 16
    sb      t1, 9(a1)
    srli    t1, t0, 8
    sb      t1, 10(a1)
    sb      t0, 11(a1)
    lw      t0, 268(sp)
    srli    t1, t0, 24
    sb      t1, 12(a1)
    srli    t1, t0, 16
    sb      t1, 13(a1)
    srli    t1, t0, 8
    sb      t1, 14(a1)
    sb      t0, 15(a1)
    lw      t0, 272(sp)
    srli    t1, t0, 24
    sb      t1, 16(a1)
    srli    t1, t0, 16
    sb      t1, 17(a1)
    srli    t1, t0, 8
    sb      t1, 18(a1)
    sb      t0, 19(a1)
    lw      t0, 276(sp)
    srli    t1, t0, 24
    sb      t1, 20(a1)
    srli    t1, t0, 16
    sb      t1, 21(a1)
    srli    t1, t0, 8
    sb      t1, 22(a1)
    sb      t0, 23(a1)
    lw      t0, 280(sp)
    srli    t1, t0, 24
    sb      t1, 24(a1)
    srli    t1, t0, 16
    sb      t1, 25(a1)
    srli    t1, t0, 8
    sb      t1, 26(a1)
    sb      t0, 27(a1)
    lw      t0, 284(sp)
    srli    t1, t0, 24
    sb      t1, 28(a1)
    srli    t1, t0, 16
    sb      t1, 29(a1)
    srli    t1, t0, 8
    sb      t1, 30(a1)
    sb      t0, 31(a1)

    li      a0, CRYPTO_OK
    UNWIND_BEGIN_EPILOGUE
    ld      s0, 416(sp)
    UNWIND_RESTORE s0
    ld      s1, 424(sp)
    UNWIND_RESTORE s1
    ld      s2, 432(sp)
    UNWIND_RESTORE s2
    ld      s3, 440(sp)
    UNWIND_RESTORE s3
    ld      s4, 448(sp)
    UNWIND_RESTORE s4
    ld      s5, 456(sp)
    UNWIND_RESTORE s5
    ld      s6, 464(sp)
    UNWIND_RESTORE s6
    ld      s7, 472(sp)
    UNWIND_RESTORE s7
    addi    sp, sp, 480
    UNWIND_FREE 480
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_sha256

/* Constants: FIPS 180-4 sections 4.2.2 and 5.3.3. */
    .p2align 4
20:
    .long 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
    .long 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
    .long 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
    .long 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
    .long 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
    .long 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
    .long 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
    .long 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
21:
    .long 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
