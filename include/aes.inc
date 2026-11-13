/*
 * asm-crypto AES-128, CTR and GCM definitions, in assembler syntax.
 * The requirement entries are in docs/reference/aes.md, docs/reference/ctr.md and docs/reference/gcm.md.
 */

/* Status codes (ARCHITECTURE.md section 6). */
.set CRYPTO_GCM_FAIL, 3                 /* crypto_aes128_gcm_ad: the tag does not match */

.set CRYPTO_AES128_KEY_SIZE, 16
.set CRYPTO_AES_BLOCK_SIZE, 16
.set CRYPTO_GCM_IV_SIZE, 12
.set CRYPTO_GCM_TAG_SIZE, 16

/*
 * The internal key schedule: the 11 round keys of FIPS 197 section 5.2, each
 * repeated 4 times and held as 8 bit planes of 8 bytes. Plane i holds bit i
 * of the 64 bytes, byte g at bit g.
 */
.set CRYPTO_AES128_SCHEDULE_SIZE, 704

/*
 * Functions, roles and allowed calls (ARCHITECTURE.md sections 4 and 5).
 *
 * | Function                 | Role | Arguments                                 | Requirements          | Allowed calls |
 * |--------------------------|------|-------------------------------------------|-----------------------|---------------|
 * | crypto_aes128_ctr        | L2   | key, counter, input, output               | docs/reference/ctr.md | crypto_aes128_expand, crypto_aes128_ctr_xor |
 * | crypto_aes128_gcm_ae     | L2   | key, iv, plaintext, aad, sealed           | docs/reference/gcm.md | crypto_aes128_expand, crypto_aes128_encrypt4, crypto_aes128_ctr_xor, crypto_aes128_ghash |
 * | crypto_aes128_gcm_ad     | L2   | key, iv, sealed, aad, plaintext           | docs/reference/gcm.md | crypto_aes128_expand, crypto_aes128_encrypt4, crypto_aes128_ctr_xor, crypto_aes128_ghash |
 * | crypto_aes128_expand     | L0   | key, schedule                             | docs/reference/aes.md | crypto_aes128_bitslice, crypto_aes128_sbox |
 * | crypto_aes128_ctr_xor    | L0   | schedule, counter, source, target, count, mode | docs/reference/ctr.md | crypto_aes128_encrypt4 |
 * | crypto_aes128_encrypt4   | L0   | schedule, blocks                          | docs/reference/aes.md | crypto_aes128_bitslice, crypto_aes128_sbox, crypto_aes128_mix |
 * | crypto_aes128_bitslice   | L0   | blocks, inverse                           | docs/reference/aes.md | none          |
 * | crypto_aes128_sbox       | L0   | planes                                    | docs/reference/aes.md | none          |
 * | crypto_aes128_mix        | L0   | planes, round_key, columns                | docs/reference/aes.md | none          |
 * | crypto_aes128_ghash      | L0   | y, h, data, count                         | docs/reference/gcm.md | none          |
 */
