/*
 * asm-crypto SHA-512 definitions, in assembler syntax.
 * The requirement entries are in docs/reference/sha-512.md.
 */

.set CRYPTO_SHA512_DIGEST_SIZE, 64
.set CRYPTO_SHA512_BLOCK, 128

/*
 * Sha512State: the hash value H, the number of bytes taken so far, and the
 * bytes after the last full block. 200 bytes, at a multiple of 8.
 */
.set CRYPTO_SHA512_STATE_H, 0           /* H[0..7]: 8 u64 words, native little endian */
.set CRYPTO_SHA512_STATE_COUNT, 64      /* u64: bytes taken so far */
.set CRYPTO_SHA512_STATE_BUFFER, 72     /* 128 bytes: the last count mod 128 bytes taken */
.set CRYPTO_SHA512_STATE_SIZE, 200

/*
 * Functions, roles and allowed calls (ARCHITECTURE.md sections 4 and 5).
 *
 * | Function              | Role | Arguments          | Requirements              | Allowed calls |
 * |-----------------------|------|--------------------|---------------------------|---------------|
 * | crypto_sha512         | L2   | message, digest    | docs/reference/sha-512.md | crypto_sha512_init, crypto_sha512_update, crypto_sha512_final |
 * | crypto_sha512_init    | L2   | state              | docs/reference/sha-512.md | none          |
 * | crypto_sha512_update  | L2   | state, message     | docs/reference/sha-512.md | crypto_sha512_blocks |
 * | crypto_sha512_final   | L2   | state, digest      | docs/reference/sha-512.md | crypto_sha512_blocks |
 * | crypto_sha512_blocks  | L0   | h, data, count     | docs/reference/sha-512.md | none          |
 */
