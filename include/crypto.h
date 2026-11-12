/*
 * asm-crypto shared definitions.
 *
 * Assembly files read this file through the C preprocessor (.S files).
 * C code, such as tests/runner/, reads it directly.
 * The requirement entry for each function is in docs/reference/.
 */
#ifndef ASM_CRYPTO_H
#define ASM_CRYPTO_H

/* Status codes (ARCHITECTURE.md section 6). */
#define CRYPTO_OK               0
#define CRYPTO_BUFFER_TOO_SMALL 1

/*
 * Byte list value (ARCHITECTURE.md section 6, a standalone list with one field).
 * All fields are unsigned 8-byte little-endian numbers.
 */
#define CRYPTO_BYTES_SIZE   0  /* total buffer size in bytes */
#define CRYPTO_BYTES_OFFSET 8  /* offset of the byte part from the buffer start */
#define CRYPTO_BYTES_COUNT  16 /* number of bytes in use in the byte part */
#define CRYPTO_BYTES_FIXED  24 /* end of the fixed fields */
#define CRYPTO_BYTES_ALIGN  8  /* alignment of the buffer and of the byte part */

/* Digest value: 32 bytes, fixed size, no size header. */
#define CRYPTO_SHA256_DIGEST_SIZE 32

/*
 * Functions, roles and allowed calls (ARCHITECTURE.md sections 4 and 5).
 *
 * | Function      | Role | Requirements                 | Allowed calls |
 * |---------------|------|------------------------------|---------------|
 * | crypto_sha256 | L2   | docs/reference/sha-256.md    | none          |
 */
#ifndef __ASSEMBLER__
#include <stdint.h>

/* The core ABI on x86-64 is System V on every OS, including Windows. */
#if defined(_WIN32) && defined(__x86_64__)
#define CRYPTO_ABI __attribute__((sysv_abi))
#else
#define CRYPTO_ABI
#endif

CRYPTO_ABI uint64_t crypto_sha256(const void *message, void *digest);

#endif /* __ASSEMBLER__ */

#endif /* ASM_CRYPTO_H */
