/*
 * SHA-512 (FIPS 180-4 sections 5.1.2, 5.2.2, 5.3.5 and 6.4) for RISC-V
 * (RISC-V ELF psABI, LP64D). Baseline RV64GC instructions only: a rotation
 * is two shifts and an or, and message words are read a byte at a time.
 * Requirements: docs/reference/sha-512.md. Layouts: include/sha512.inc.
 *
 * The functions and their steps follow the ARM64 file one for one.
 */
.set ISA_RISCV64, 1
.include "crypto.inc"
.include "sha512.inc"
.include "platform.inc"

/* Frame of a non-leaf function: locals at sp, then ra and s0-s11. */
.macro ENTER locals
    addi    sp, sp, -(\locals + 112)
    UNWIND_ALLOC (\locals + 112)
    sd      ra, \locals(sp)
    UNWIND_SAVE ra, \locals
    sd      s0, \locals+8(sp)
    UNWIND_SAVE s0, \locals+8
    sd      s1, \locals+16(sp)
    UNWIND_SAVE s1, \locals+16
    sd      s2, \locals+24(sp)
    UNWIND_SAVE s2, \locals+24
    sd      s3, \locals+32(sp)
    UNWIND_SAVE s3, \locals+32
    sd      s4, \locals+40(sp)
    UNWIND_SAVE s4, \locals+40
    sd      s5, \locals+48(sp)
    UNWIND_SAVE s5, \locals+48
    sd      s6, \locals+56(sp)
    UNWIND_SAVE s6, \locals+56
    sd      s7, \locals+64(sp)
    UNWIND_SAVE s7, \locals+64
    sd      s8, \locals+72(sp)
    UNWIND_SAVE s8, \locals+72
    sd      s9, \locals+80(sp)
    UNWIND_SAVE s9, \locals+80
    sd      s10, \locals+88(sp)
    UNWIND_SAVE s10, \locals+88
    sd      s11, \locals+96(sp)
    UNWIND_SAVE s11, \locals+96
    UNWIND_END_PROLOGUE
.endm

.macro LEAVE locals
    UNWIND_BEGIN_EPILOGUE
    ld      ra, \locals(sp)
    UNWIND_RESTORE ra
    ld      s0, \locals+8(sp)
    UNWIND_RESTORE s0
    ld      s1, \locals+16(sp)
    UNWIND_RESTORE s1
    ld      s2, \locals+24(sp)
    UNWIND_RESTORE s2
    ld      s3, \locals+32(sp)
    UNWIND_RESTORE s3
    ld      s4, \locals+40(sp)
    UNWIND_RESTORE s4
    ld      s5, \locals+48(sp)
    UNWIND_RESTORE s5
    ld      s6, \locals+56(sp)
    UNWIND_RESTORE s6
    ld      s7, \locals+64(sp)
    UNWIND_RESTORE s7
    ld      s8, \locals+72(sp)
    UNWIND_RESTORE s8
    ld      s9, \locals+80(sp)
    UNWIND_RESTORE s9
    ld      s10, \locals+88(sp)
    UNWIND_RESTORE s10
    ld      s11, \locals+96(sp)
    UNWIND_RESTORE s11
    addi    sp, sp, (\locals + 112)
    UNWIND_FREE (\locals + 112)
    UNWIND_END_EPILOGUE
    ret
.endm

/* d = s rotated right by n bits. Uses tmp. */
.macro ROR d, s, n, tmp
    srli    \d, \s, \n
    slli    \tmp, \s, (64 - \n)
    or      \d, \d, \tmp
.endm

/* ---------------------------------------------------------------- crypto_sha512 */

/* crypto_sha512(message, digest) -> status. s0 message, s1 digest, the state at sp. */
FUNCTION crypto_sha512
    ENTER   208
    mv      s0, a0
    mv      s1, a1
    mv      a0, sp
    CALL_GLOBAL crypto_sha512_init
    mv      a0, sp
    mv      a1, s0
    CALL_GLOBAL crypto_sha512_update
    mv      a0, sp
    mv      a1, s1
    CALL_GLOBAL crypto_sha512_final
    li      a0, CRYPTO_OK
    LEAVE   208
END_FUNCTION crypto_sha512

/* crypto_sha512_init(state) -> status: H = H(0) of section 5.3.5, count 0. A leaf. */
FUNCTION crypto_sha512_init
    UNWIND_END_PROLOGUE
    lla     t0, 21f
    .irp off, 0, 8, 16, 24, 32, 40, 48, 56
    ld      t1, \off(t0)
    sd      t1, (CRYPTO_SHA512_STATE_H + \off)(a0)
    .endr
    sd      zero, CRYPTO_SHA512_STATE_COUNT(a0)
    li      a0, CRYPTO_OK
    ret
END_FUNCTION crypto_sha512_init

/*
 * crypto_sha512_update(state, message) -> status.
 * s0 state, s1 the next message byte, s2 bytes left, s3 fill.
 */
FUNCTION crypto_sha512_update
    ENTER   0
    mv      s0, a0
    ld      t0, CRYPTO_BYTES_OFFSET(a1)
    ld      s2, CRYPTO_BYTES_COUNT(a1)
    add     s1, a1, t0
    ld      t0, CRYPTO_SHA512_STATE_COUNT(s0)
    andi    s3, t0, 127
    add     t0, t0, s2
    sd      t0, CRYPTO_SHA512_STATE_COUNT(s0)
    beqz    s3, 3f
    li      t1, 128                         # fill the buffer up to 128 bytes
    sub     t1, t1, s3
    bgeu    s2, t1, 1f
    mv      t1, s2
1:  addi    t2, s0, CRYPTO_SHA512_STATE_BUFFER
    add     t2, t2, s3
    add     s3, s3, t1
    sub     s2, s2, t1
2:  beqz    t1, 6f
    lbu     t3, 0(s1)
    sb      t3, 0(t2)
    addi    s1, s1, 1
    addi    t2, t2, 1
    addi    t1, t1, -1
    j       2b
6:  li      t0, 128
    bltu    s3, t0, 9f                      # the message ended in the buffer
    mv      a0, s0
    addi    a1, s0, CRYPTO_SHA512_STATE_BUFFER
    li      a2, 1
    call    crypto_sha512_blocks
3:  srli    a2, s2, 7                       # full blocks straight from the message
    beqz    a2, 4f
    mv      a0, s0
    mv      a1, s1
    slli    t0, a2, 7
    add     s1, s1, t0
    call    crypto_sha512_blocks
4:  andi    t1, s2, 127                     # keep the rest
    addi    t2, s0, CRYPTO_SHA512_STATE_BUFFER
5:  beqz    t1, 9f
    lbu     t3, 0(s1)
    sb      t3, 0(t2)
    addi    s1, s1, 1
    addi    t2, t2, 1
    addi    t1, t1, -1
    j       5b
9:  li      a0, CRYPTO_OK
    LEAVE   0
END_FUNCTION crypto_sha512_update

/*
 * crypto_sha512_final(state, digest) -> status: pads as section 5.1.2 says
 * and writes H big endian. s0 state, s1 digest, s2 the buffer.
 */
FUNCTION crypto_sha512_final
    ENTER   0
    mv      s0, a0
    mv      s1, a1
    addi    s2, s0, CRYPTO_SHA512_STATE_BUFFER
    ld      t0, CRYPTO_SHA512_STATE_COUNT(s0)
    andi    t0, t0, 127
    add     t1, s2, t0
    li      t2, 0x80
    sb      t2, 0(t1)
    addi    t0, t0, 1
    li      t3, 128
1:  bgeu    t0, t3, 2f                      # zeros after the 0x80 byte
    add     t1, s2, t0
    sb      zero, 0(t1)
    addi    t0, t0, 1
    j       1b
2:  ld      t0, CRYPTO_SHA512_STATE_COUNT(s0)
    andi    t0, t0, 127
    li      t1, 112
    bltu    t0, t1, 4f
    mv      a0, s0                          # no room for the length: one more block
    mv      a1, s2
    li      a2, 1
    call    crypto_sha512_blocks
    li      t0, 0
    li      t1, 112
3:  add     t2, s2, t0
    sd      zero, 0(t2)
    addi    t0, t0, 8
    bltu    t0, t1, 3b
4:  ld      t0, CRYPTO_SHA512_STATE_COUNT(s0)
    srli    t1, t0, 61                      # the length in bits, 128 bits big endian
    slli    t0, t0, 3
    li      t2, 7
    addi    t3, s2, 112
5:  sb      t1, 0(t3)                       # bytes 112 to 119 from the top down
    srli    t1, t1, 8
    sb      t0, 8(t3)                       # bytes 120 to 127
    srli    t0, t0, 8
    addi    t3, t3, 1
    addi    t2, t2, -1
    bgez    t2, 5b
    li      t2, 0                           # reverse each of the two words in place
    addi    t3, s2, 112
6:  add     t4, t3, t2
    li      t5, 7
    sub     t5, t5, t2
    add     t5, t3, t5
    lbu     t0, 0(t4)
    lbu     t1, 0(t5)
    sb      t1, 0(t4)
    sb      t0, 0(t5)
    lbu     t0, 8(t4)
    lbu     t1, 8(t5)
    sb      t1, 8(t4)
    sb      t0, 8(t5)
    addi    t2, t2, 1
    li      t0, 4
    bltu    t2, t0, 6b
    mv      a0, s0
    mv      a1, s2
    li      a2, 1
    call    crypto_sha512_blocks
    li      t0, 0                           # digest = H as big-endian words
7:  add     t1, s0, t0
    ld      t2, 0(t1)
    add     t3, s1, t0
    addi    t3, t3, 7
    li      t4, 8
8:  sb      t2, 0(t3)
    srli    t2, t2, 8
    addi    t3, t3, -1
    addi    t4, t4, -1
    bnez    t4, 8b
    addi    t0, t0, 8
    li      t1, 64
    bltu    t0, t1, 7b
    li      a0, CRYPTO_OK
    LEAVE   0
END_FUNCTION crypto_sha512_final

/* ---------------------------------------------------------------- Compression */

/*
 * One round of section 6.4.2, step 3, for the working variables a to h.
 * h becomes T1 + T2 (the next a) and d becomes d + T1 (the next e).
 * s8 walks K and s9 walks W. Uses t0 to t2.
 */
.macro ROUND a, b, c, d, e, f, g, h
    ld      t0, 0(s8)
    ld      t1, 0(s9)
    addi    s8, s8, 8
    addi    s9, s9, 8
    add     \h, \h, t0
    add     \h, \h, t1
    ROR     t0, \e, 14, t2                  # Sigma1(e)
    ROR     t1, \e, 18, t2
    xor     t0, t0, t1
    ROR     t1, \e, 41, t2
    xor     t0, t0, t1
    add     \h, \h, t0
    xor     t0, \f, \g                      # Ch(e, f, g) = ((f ^ g) & e) ^ g
    and     t0, t0, \e
    xor     t0, t0, \g
    add     \h, \h, t0                      # T1
    add     \d, \d, \h
    ROR     t0, \a, 28, t2                  # Sigma0(a)
    ROR     t1, \a, 34, t2
    xor     t0, t0, t1
    ROR     t1, \a, 39, t2
    xor     t0, t0, t1
    add     \h, \h, t0
    xor     t0, \a, \b                      # Maj(a, b, c) = ((a ^ b) & c) ^ (a & b)
    and     t0, t0, \c
    and     t1, \a, \b
    xor     t0, t0, t1
    add     \h, \h, t0                      # T1 + T2
.endm

/*
 * crypto_sha512_blocks(h, data, count): runs section 6.4.2 on count blocks
 * of 128 bytes at data, updating the 8 words at h. a0 h, a1 data, a2 blocks
 * left, s0 to s7 a to h, s8 K, s9 W, s10 the round groups left, t0 to t6
 * temporaries. W[0..79] at sp.
 */
LOCAL_FUNCTION crypto_sha512_blocks
    ENTER   640
    beqz    a2, 9f
1:  mv      s9, sp                          # W[0..15]: the block as big-endian words
    li      t3, 16
2:  li      t0, 0
    li      t4, 8
3:  lbu     t1, 0(a1)
    slli    t0, t0, 8
    or      t0, t0, t1
    addi    a1, a1, 1
    addi    t4, t4, -1
    bnez    t4, 3b
    sd      t0, 0(s9)
    addi    s9, s9, 8
    addi    t3, t3, -1
    bnez    t3, 2b
    li      t3, 64                          # W[16..79]
4:  ld      t0, -16(s9)                     # sigma1(W[t-2])
    ROR     t1, t0, 19, t2
    ROR     t4, t0, 61, t2
    xor     t1, t1, t4
    srli    t4, t0, 6
    xor     t1, t1, t4
    ld      t0, -120(s9)                    # sigma0(W[t-15])
    ROR     t5, t0, 1, t2
    ROR     t4, t0, 8, t2
    xor     t5, t5, t4
    srli    t4, t0, 7
    xor     t5, t5, t4
    add     t1, t1, t5
    ld      t0, -56(s9)                     # W[t-7]
    add     t1, t1, t0
    ld      t0, -128(s9)                    # W[t-16]
    add     t1, t1, t0
    sd      t1, 0(s9)
    addi    s9, s9, 8
    addi    t3, t3, -1
    bnez    t3, 4b
    ld      s0, 0(a0)
    ld      s1, 8(a0)
    ld      s2, 16(a0)
    ld      s3, 24(a0)
    ld      s4, 32(a0)
    ld      s5, 40(a0)
    ld      s6, 48(a0)
    ld      s7, 56(a0)
    lla     s8, 20f
    mv      s9, sp
    li      s10, 10
5:  ROUND   s0, s1, s2, s3, s4, s5, s6, s7
    ROUND   s7, s0, s1, s2, s3, s4, s5, s6
    ROUND   s6, s7, s0, s1, s2, s3, s4, s5
    ROUND   s5, s6, s7, s0, s1, s2, s3, s4
    ROUND   s4, s5, s6, s7, s0, s1, s2, s3
    ROUND   s3, s4, s5, s6, s7, s0, s1, s2
    ROUND   s2, s3, s4, s5, s6, s7, s0, s1
    ROUND   s1, s2, s3, s4, s5, s6, s7, s0
    addi    s10, s10, -1
    bnez    s10, 5b
    .irp r, 0, 1, 2, 3, 4, 5, 6, 7          # H += a to h
    ld      t0, (8 * \r)(a0)
    add     t0, t0, s\r
    sd      t0, (8 * \r)(a0)
    .endr
    addi    a2, a2, -1
    bnez    a2, 1b
9:  LEAVE   640
END_FUNCTION crypto_sha512_blocks

/* ---------------------------------------------------------------- Constants */

/* K of section 4.2.3, then H(0) of section 5.3.5. */
    .p2align 3
20:
    .quad   0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc
    .quad   0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118
    .quad   0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2
    .quad   0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694
    .quad   0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65
    .quad   0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5
    .quad   0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4
    .quad   0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70
    .quad   0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df
    .quad   0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b
    .quad   0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30
    .quad   0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8
    .quad   0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8
    .quad   0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3
    .quad   0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec
    .quad   0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b
    .quad   0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178
    .quad   0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b
    .quad   0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c
    .quad   0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
21:
    .quad   0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1
    .quad   0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
