/*
 * asm-crypto HMAC-SHA-256 and HKDF-SHA-256 definitions, in assembler syntax.
 * The requirement entries are in docs/reference/hmac.md and docs/reference/hkdf.md.
 */

/* Status codes (ARCHITECTURE.md section 6). */
.set CRYPTO_HKDF_LENGTH, 2              /* crypto_hkdf_expand: length is above 255 * 32 */

.set CRYPTO_HMAC_BLOCK, 64              /* SHA-256 block size B of RFC 2104 */
.set CRYPTO_HKDF_MAX_LENGTH, 8160       /* 255 * 32, RFC 5869 section 2.3 */

/* Scratch sizes: a scratch buffer holds at least this many bytes, plus the message or info bytes. */
.set CRYPTO_HMAC_SCRATCH, 96            /* crypto_hmac_sha256 and crypto_hkdf_extract */
.set CRYPTO_HKDF_EXPAND_SCRATCH, 129    /* crypto_hkdf_expand */

/*
 * Functions, roles and allowed calls (ARCHITECTURE.md sections 4 and 5).
 *
 * | Function            | Role | Arguments                          | Requirements            | Allowed calls |
 * |---------------------|------|------------------------------------|-------------------------|---------------|
 * | crypto_hmac_sha256  | L2   | key, message, scratch, mac         | docs/reference/hmac.md  | crypto_hmac_key, crypto_hmac_finish |
 * | crypto_hkdf_extract | L2   | salt, ikm, scratch, prk            | docs/reference/hkdf.md  | crypto_hmac_sha256 |
 * | crypto_hkdf_expand  | L2   | prk, info, length, scratch, okm    | docs/reference/hkdf.md  | crypto_hmac_key, crypto_hmac_finish |
 * | crypto_hmac_key     | L0   | key, k0                            | docs/reference/hmac.md  | crypto_sha256 |
 * | crypto_hmac_finish  | L0   | inner, k0, mac                     | docs/reference/hmac.md  | crypto_sha256 |
 */
