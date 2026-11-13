/*
 * asm-crypto shared definitions, in assembler syntax.
 * Every core and shell file includes this file with .include.
 * The requirement entry for each function is in docs/reference/.
 */

/* Status codes (ARCHITECTURE.md section 6). */
.set CRYPTO_OK, 0
.set CRYPTO_BUFFER_TOO_SMALL, 1
.set CRYPTO_INVALID_PRIVATE_KEY, 4      /* secp256k1 and P-256: the private key is 0, or n or more */
.set CRYPTO_INVALID_PUBLIC_KEY, 5       /* secp256k1 and P-256: the public key is not a point of the curve in the form the function takes */

/*
 * Byte list value (ARCHITECTURE.md section 6, a standalone list with one field).
 * All fields are unsigned 8-byte little-endian numbers.
 */
.set CRYPTO_BYTES_SIZE, 0       /* total buffer size in bytes */
.set CRYPTO_BYTES_OFFSET, 8     /* offset of the byte part from the buffer start */
.set CRYPTO_BYTES_COUNT, 16     /* number of bytes in use in the byte part */
.set CRYPTO_BYTES_FIXED, 24     /* end of the fixed fields */
.set CRYPTO_BYTES_ALIGN, 8      /* alignment of the buffer and of the byte part */

/* Digest value: 32 bytes, fixed size, no size header. */
.set CRYPTO_SHA256_DIGEST_SIZE, 32

/*
 * Functions, roles and allowed calls (ARCHITECTURE.md sections 4 and 5).
 *
 * | Function      | Role | Arguments          | Requirements              | Allowed calls |
 * |---------------|------|--------------------|---------------------------|---------------|
 * | crypto_sha256 | L2   | message, digest    | docs/reference/sha-256.md | none          |
 */
