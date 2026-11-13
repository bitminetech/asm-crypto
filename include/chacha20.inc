/*
 * asm-crypto ChaCha20, Poly1305 and ChaCha20-Poly1305 definitions, in assembler syntax.
 * The requirement entries are in docs/reference/chacha20.md, docs/reference/poly1305.md
 * and docs/reference/chacha20-poly1305.md.
 */

/* Status codes (ARCHITECTURE.md section 6). */
.set CRYPTO_CHACHA20_POLY1305_FAIL, 6   /* crypto_chacha20_aead_decrypt: the tag does not match */

.set CRYPTO_CHACHA20_KEY_SIZE, 32
.set CRYPTO_CHACHA20_NONCE_SIZE, 12
.set CRYPTO_CHACHA20_BLOCK_SIZE, 64
.set CRYPTO_POLY1305_KEY_SIZE, 32
.set CRYPTO_POLY1305_TAG_SIZE, 16

/*
 * The Poly1305 state: the accumulator h as three 64-bit limbs (h2 below
 * 2^3 between blocks), the clamped r as two limbs, s1 = r1 + r1 / 4, and the
 * 16-byte s. Numbers are little endian.
 */
.set CRYPTO_POLY1305_H0, 0
.set CRYPTO_POLY1305_H1, 8
.set CRYPTO_POLY1305_H2, 16
.set CRYPTO_POLY1305_R0, 24
.set CRYPTO_POLY1305_R1, 32
.set CRYPTO_POLY1305_S1, 40
.set CRYPTO_POLY1305_S, 48
.set CRYPTO_POLY1305_STATE_SIZE, 64

/*
 * Functions, roles and allowed calls (ARCHITECTURE.md sections 4 and 5).
 *
 * | Function                     | Role | Arguments                                | Requirements                        | Allowed calls |
 * |------------------------------|------|------------------------------------------|-------------------------------------|---------------|
 * | crypto_chacha20_aead_encrypt | L2   | key, nonce, plaintext, aad, sealed       | docs/reference/chacha20-poly1305.md | crypto_chacha20_block, crypto_chacha20_xor, crypto_poly1305_init, crypto_poly1305_blocks, crypto_poly1305_emit |
 * | crypto_chacha20_aead_decrypt | L2   | key, nonce, sealed, aad, plaintext       | docs/reference/chacha20-poly1305.md | crypto_chacha20_block, crypto_chacha20_xor, crypto_poly1305_init, crypto_poly1305_blocks, crypto_poly1305_emit |
 * | crypto_poly1305_mac          | L2   | key, message, tag                        | docs/reference/poly1305.md          | crypto_poly1305_init, crypto_poly1305_blocks, crypto_poly1305_emit |
 * | crypto_chacha20_block        | L0   | key, counter, nonce, block               | docs/reference/chacha20.md          | none          |
 * | crypto_chacha20_xor          | L0   | key, nonce, counter, source, target, count | docs/reference/chacha20.md        | crypto_chacha20_block |
 * | crypto_poly1305_init         | L0   | state, key                               | docs/reference/poly1305.md          | none          |
 * | crypto_poly1305_blocks       | L0   | state, data, count, pad                  | docs/reference/poly1305.md          | none          |
 * | crypto_poly1305_emit         | L0   | state, tag                               | docs/reference/poly1305.md          | none          |
 */
