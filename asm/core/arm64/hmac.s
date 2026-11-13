/*
 * HMAC-SHA-256 and HKDF-SHA-256 for ARM64 (AAPCS64).
 * Requirements: docs/reference/hmac.md. Layouts: include/crypto.inc, include/hmac.inc.
 *
 * Every hash goes through crypto_sha256. The inner hash input sits in the
 * caller's scratch buffer, as a ByteList at scratch + 8. The outer hash input,
 * 96 bytes, sits on the stack. x18 is never used. Every function that calls
 * keeps an x29 frame record.
 */
.set ISA_ARM64, 1
.include "crypto.inc"
.include "hmac.inc"
.include "platform.inc"

/* Frame of a non-leaf function: x29, x30, x19-x28, then locals at sp + 96. */
.macro ENTER locals
    stp     x29, x30, [sp, #-(96 + \locals)]!
    UNWIND_SAVE_FPLR_X (96 + \locals)
    mov     x29, sp
    UNWIND_SET_FP
    stp     x19, x20, [sp, #16]
    UNWIND_SAVE_REGP x19, x20, 16, (96 + \locals)
    stp     x21, x22, [sp, #32]
    UNWIND_SAVE_REGP x21, x22, 32, (96 + \locals)
    stp     x23, x24, [sp, #48]
    UNWIND_SAVE_REGP x23, x24, 48, (96 + \locals)
    stp     x25, x26, [sp, #64]
    UNWIND_SAVE_REGP x25, x26, 64, (96 + \locals)
    stp     x27, x28, [sp, #80]
    UNWIND_SAVE_REGP x27, x28, 80, (96 + \locals)
    UNWIND_END_PROLOGUE
.endm

.macro LEAVE locals
    UNWIND_BEGIN_EPILOGUE
    ldp     x27, x28, [sp, #80]
    UNWIND_RESTORE_REGP x27, x28, 80
    ldp     x25, x26, [sp, #64]
    UNWIND_RESTORE_REGP x25, x26, 64
    ldp     x23, x24, [sp, #48]
    UNWIND_RESTORE_REGP x23, x24, 48
    ldp     x21, x22, [sp, #32]
    UNWIND_RESTORE_REGP x21, x22, 32
    ldp     x19, x20, [sp, #16]
    UNWIND_RESTORE_REGP x19, x20, 16
    ldp     x29, x30, [sp], #(96 + \locals)
    UNWIND_RESTORE_FPLR_X (96 + \locals)
    UNWIND_END_EPILOGUE
    ret
.endm

/* Register xp = 8 copies of the byte b. */
.macro PATTERN xp, b
    mov     \xp, #\b
    mov     x9, #0x0101010101010101
    mul     \xp, \xp, x9
.endm

/* Write the 64 bytes at k0 XOR the pattern register xp to dst. Uses x9, x10. */
.macro PAD dst, k0, xp
    .irp i, 0, 16, 32, 48
    ldp     x9, x10, [\k0, #\i]
    eor     x9, x9, \xp
    eor     x10, x10, \xp
    stp     x9, x10, [\dst, #\i]
    .endr
.endm

/* Copy n bytes from src to dst, both 8-byte aligned. Moves src and dst; n ends at 0. Uses x9. */
.macro COPY dst, src, n
97: cmp     \n, #8
    b.lo    98f
    ldr     x9, [\src], #8
    str     x9, [\dst], #8
    sub     \n, \n, #8
    b       97b
98: cbz     \n, 99f
    ldrb    w9, [\src], #1
    strb    w9, [\dst], #1
    sub     \n, \n, #1
    b       98b
99:
.endm

/*
 * crypto_hmac_sha256(key, message, scratch, mac) -> status
 * x19 key, x20 message, x21 scratch, x22 mac. K0 at sp + 96.
 */
FUNCTION crypto_hmac_sha256
    ENTER   64
    mov     x19, x0
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    ldr     x4, [x21]
    ldr     x5, [x20, #CRYPTO_BYTES_COUNT]
    subs    x4, x4, #CRYPTO_HMAC_SCRATCH
    b.lo    9f
    cmp     x4, x5
    b.lo    9f

    mov     x0, x19
    add     x1, sp, #96
    bl      crypto_hmac_key

    /* The inner list: K0 ^ ipad, then the message. */
    ldr     x4, [x21]
    sub     x4, x4, #8
    str     x4, [x21, #8 + CRYPTO_BYTES_SIZE]
    mov     x4, #CRYPTO_BYTES_FIXED
    str     x4, [x21, #8 + CRYPTO_BYTES_OFFSET]
    ldr     x5, [x20, #CRYPTO_BYTES_COUNT]
    add     x4, x5, #CRYPTO_HMAC_BLOCK
    str     x4, [x21, #8 + CRYPTO_BYTES_COUNT]
    PATTERN x11, 0x36
    add     x8, x21, #32
    add     x12, sp, #96
    PAD     x8, x12, x11
    add     x8, x21, #96
    ldr     x6, [x20, #CRYPTO_BYTES_OFFSET]
    add     x6, x20, x6
    COPY    x8, x6, x5

    add     x0, x21, #8
    add     x1, sp, #96
    mov     x2, x22
    bl      crypto_hmac_finish
    mov     x0, #CRYPTO_OK
9:  LEAVE   64
END_FUNCTION crypto_hmac_sha256

/* crypto_hkdf_extract(salt, ikm, scratch, prk) -> status: HMAC-SHA-256 with key salt. */
FUNCTION crypto_hkdf_extract
    stp     x29, x30, [sp, #-16]!
    UNWIND_SAVE_FPLR_X 16
    mov     x29, sp
    UNWIND_SET_FP
    UNWIND_END_PROLOGUE
    CALL_GLOBAL crypto_hmac_sha256
    UNWIND_BEGIN_EPILOGUE
    ldp     x29, x30, [sp], #16
    UNWIND_RESTORE_FPLR_X 16
    UNWIND_END_EPILOGUE
    ret
END_FUNCTION crypto_hkdf_extract

/*
 * crypto_hkdf_expand(prk, info, length, scratch, okm) -> status
 * x19 prk, x20 info, x21 scratch, x22 okm, x23 length, x24 block number i,
 * x25 info bytes, x26 bytes done, x27 okm bytes, x28 ipad pattern.
 * K0 at sp + 96, T(i) at sp + 160.
 *
 * Scratch: the inner list header at 8, its bytes from 32. Block 1 puts
 * K0 ^ ipad at 64 (list offset 56); block i > 1 puts it at 32 and T(i - 1) at
 * 96 (list offset 24). The info bytes at 128 and the byte i after them stay put.
 */
FUNCTION crypto_hkdf_expand
    ENTER   96
    mov     x19, x0
    mov     x20, x1
    mov     x21, x3
    mov     x22, x4
    ldr     x23, [x2]
    mov     x0, #CRYPTO_HKDF_LENGTH
    mov     x9, #CRYPTO_HKDF_MAX_LENGTH
    cmp     x23, x9
    b.hi    9f
    mov     x0, #CRYPTO_BUFFER_TOO_SMALL
    ldr     x25, [x20, #CRYPTO_BYTES_COUNT]
    ldr     x9, [x21]
    subs    x9, x9, #CRYPTO_HKDF_EXPAND_SCRATCH
    b.lo    9f
    cmp     x9, x25
    b.lo    9f
    ldr     x9, [x22, #CRYPTO_BYTES_SIZE]
    subs    x9, x9, #CRYPTO_BYTES_FIXED
    b.lo    9f
    cmp     x9, x23
    b.lo    9f

    mov     x0, x19
    add     x1, sp, #96
    bl      crypto_hmac_key
    add     x8, x21, #128
    ldr     x6, [x20, #CRYPTO_BYTES_OFFSET]
    add     x6, x20, x6
    mov     x7, x25
    COPY    x8, x6, x7
    mov     x9, #CRYPTO_BYTES_FIXED
    str     x9, [x22, #CRYPTO_BYTES_OFFSET]
    str     x23, [x22, #CRYPTO_BYTES_COUNT]
    ldr     x9, [x21]
    sub     x9, x9, #8
    str     x9, [x21, #8 + CRYPTO_BYTES_SIZE]
    mov     x24, #1
    mov     x26, #0
    add     x27, x22, #CRYPTO_BYTES_FIXED
    PATTERN x28, 0x36

1:  cmp     x26, x23
    b.hs    8f
    add     x9, x21, #128
    strb    w24, [x9, x25]
    cmp     x24, #1
    b.ne    2f
    mov     x9, #56
    str     x9, [x21, #8 + CRYPTO_BYTES_OFFSET]
    add     x9, x25, #(CRYPTO_HMAC_BLOCK + 1)
    str     x9, [x21, #8 + CRYPTO_BYTES_COUNT]
    add     x8, x21, #64
    b       3f
2:  mov     x9, #CRYPTO_BYTES_FIXED
    str     x9, [x21, #8 + CRYPTO_BYTES_OFFSET]
    add     x9, x25, #(CRYPTO_HMAC_BLOCK + 32 + 1)
    str     x9, [x21, #8 + CRYPTO_BYTES_COUNT]
    ldp     x9, x10, [sp, #160]
    stp     x9, x10, [x21, #96]
    ldp     x9, x10, [sp, #176]
    stp     x9, x10, [x21, #112]
    add     x8, x21, #32
3:  add     x12, sp, #96
    PAD     x8, x12, x28
    add     x0, x21, #8
    add     x1, sp, #96
    add     x2, sp, #160
    bl      crypto_hmac_finish

    /* okm gets min(32, length - done) bytes of T(i). */
    sub     x7, x23, x26
    mov     x10, #32
    cmp     x7, x10
    csel    x7, x7, x10, lo
    add     x8, x27, x26
    add     x6, sp, #160
    COPY    x8, x6, x7
    add     x26, x26, #32
    add     x24, x24, #1
    b       1b
8:  mov     x0, #CRYPTO_OK
9:  LEAVE   96
END_FUNCTION crypto_hkdf_expand

/*
 * crypto_hmac_key(key, k0): K0 of RFC 2104 into the 64 bytes at k0. A key of
 * at most 64 bytes is copied, a longer key is hashed; zeros fill the rest.
 */
LOCAL_FUNCTION crypto_hmac_key
    ENTER   0
    stp     xzr, xzr, [x1]
    stp     xzr, xzr, [x1, #16]
    stp     xzr, xzr, [x1, #32]
    stp     xzr, xzr, [x1, #48]
    ldr     x2, [x0, #CRYPTO_BYTES_COUNT]
    cmp     x2, #CRYPTO_HMAC_BLOCK
    b.hi    1f
    ldr     x3, [x0, #CRYPTO_BYTES_OFFSET]
    add     x3, x0, x3
    COPY    x1, x3, x2
    b       2f
1:  CALL_GLOBAL crypto_sha256
2:  LEAVE   0
END_FUNCTION crypto_hmac_key

/*
 * crypto_hmac_finish(inner, k0, mac): the inner hash of the list inner, which
 * holds K0 ^ ipad and the message, then the outer hash into mac.
 * x19 k0, x20 mac. The outer list at sp + 96: 24 bytes of header, 96 bytes.
 */
LOCAL_FUNCTION crypto_hmac_finish
    ENTER   128
    mov     x19, x1
    mov     x20, x2
    add     x1, sp, #(96 + CRYPTO_BYTES_FIXED + CRYPTO_HMAC_BLOCK)
    CALL_GLOBAL crypto_sha256
    mov     x9, #(CRYPTO_BYTES_FIXED + 96)
    str     x9, [sp, #96 + CRYPTO_BYTES_SIZE]
    mov     x9, #CRYPTO_BYTES_FIXED
    str     x9, [sp, #96 + CRYPTO_BYTES_OFFSET]
    mov     x9, #96
    str     x9, [sp, #96 + CRYPTO_BYTES_COUNT]
    PATTERN x11, 0x5C
    add     x8, sp, #(96 + CRYPTO_BYTES_FIXED)
    PAD     x8, x19, x11
    add     x0, sp, #96
    mov     x1, x20
    CALL_GLOBAL crypto_sha256
    LEAVE   128
END_FUNCTION crypto_hmac_finish
