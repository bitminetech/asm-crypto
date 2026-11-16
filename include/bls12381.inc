/*
 * asm-crypto BLS12-381 definitions, in assembler syntax.
 * The requirement entries are in docs/reference/bls-signatures.md,
 * docs/reference/bls12-381.md and docs/reference/hash-to-curve.md.
 * Shared status codes: CRYPTO_INVALID_PRIVATE_KEY, CRYPTO_INVALID_PUBLIC_KEY,
 * CRYPTO_INVALID_SIGNATURE, CRYPTO_EMPTY_LIST and CRYPTO_INVALID_ENCODING,
 * in crypto.inc.
 */

/* Status codes (ARCHITECTURE.md section 6). */
.set CRYPTO_BLS_XMD_LENGTH, 11          /* crypto_bls_expand_message_xmd: length is above 8160 (RFC 9380 section 5.3.1) */
.set CRYPTO_BLS_POINT_AT_INFINITY, 12   /* crypto_bls_hash_to_g2: the point has no affine form */

/* Encodings. */
.set CRYPTO_BLS_SECRET_KEY_SIZE, 32     /* big-endian, 1 to r - 1 */
.set CRYPTO_BLS_PUBLIC_KEY_SIZE, 48     /* compressed G1 point */
.set CRYPTO_BLS_SIGNATURE_SIZE, 96      /* compressed G2 point */
.set CRYPTO_BLS_G2_AFFINE_SIZE, 192     /* x.c0, x.c1, y.c0, y.c1, 48 big-endian bytes each */
.set CRYPTO_BLS_XMD_MAX_LENGTH, 8160    /* 255 * 32, RFC 9380 section 5.3.1 */

/*
 * Lists of keys and of signatures: a standalone list (ARCHITECTURE.md
 * section 6): size at 0, offset at 8, count at 16, where count is the number
 * of entries; the entries follow each other from offset, 48 or 96 bytes each.
 */
.set CRYPTO_BLS_LIST_SIZE, 0
.set CRYPTO_BLS_LIST_OFFSET, 8
.set CRYPTO_BLS_LIST_COUNT, 16
.set CRYPTO_BLS_LIST_FIXED, 24

/*
 * Scratch sizes: the size field of a scratch buffer is at least this many
 * bytes plus the count of the message (and of the DST where named).
 */
.set CRYPTO_BLS_SCRATCH, 8192           /* sign, verify, fast_aggregate_verify, eth_fast_aggregate_verify: + message */
.set CRYPTO_BLS_H2C_SCRATCH, 4096       /* expand_message_xmd, hash_to_g2: + message + DST */

/*
 * Internal layouts. An element of Fp is 6 little-endian 64-bit limbs, least
 * significant first, in Montgomery form a * 2^384 mod p (48 bytes). Fp2 is
 * c0, c1 (96 bytes); Fp6 is c0, c1, c2 over Fp2 (288 bytes); Fp12 is c0, c1
 * over Fp6 (576 bytes). A G1 point is x, y, z of Jacobian coordinates over
 * Fp (144 bytes); a G2 point is x, y, z over Fp2 (288 bytes). z = 0 is the
 * point at infinity.
 */
.set BLS_FP, 48
.set BLS_FP2, 96
.set BLS_FP6, 288
.set BLS_FP12, 576
.set BLS_G1, 144
.set BLS_G2, 288

/* The p record: p at 0, -p^-1 mod 2^64 at 48, 2^384 mod p at 56, 2^768 mod p at 104. */
.set BLS_FP_RECORD_INVERSE, 48
.set BLS_FP_RECORD_ONE, 56
.set BLS_FP_RECORD_R2, 104

/*
 * Functions, roles and allowed calls (ARCHITECTURE.md sections 4 and 5).
 * L0 helpers are listed in their documents as they are added.
 *
 * | Function                             | Role | Arguments                                              | Requirements                       |
 * |--------------------------------------|------|--------------------------------------------------------|------------------------------------|
 * | crypto_bls_sk_to_pk                  | L2   | secret_key, public_key                                 | docs/reference/bls-signatures.md   |
 * | crypto_bls_sign                      | L2   | secret_key, message, scratch, signature                | docs/reference/bls-signatures.md   |
 * | crypto_bls_verify                    | L2   | public_key, message, signature, scratch, valid         | docs/reference/bls-signatures.md   |
 * | crypto_bls_aggregate                 | L2   | signatures, signature                                  | docs/reference/bls-signatures.md   |
 * | crypto_bls_fast_aggregate_verify     | L2   | public_keys, message, signature, scratch, valid        | docs/reference/bls-signatures.md   |
 * | crypto_bls_key_validate              | L2   | public_key, valid                                      | docs/reference/bls-signatures.md   |
 * | crypto_bls_eth_aggregate_pubkeys     | L2   | public_keys, public_key                                | docs/reference/bls-signatures.md   |
 * | crypto_bls_eth_fast_aggregate_verify | L2   | public_keys, message, signature, scratch, valid        | docs/reference/bls-signatures.md   |
 * | crypto_bls_g1_decode                 | L2   | bytes, point                                           | docs/reference/bls12-381.md        |
 * | crypto_bls_g1_compress               | L2   | point, bytes                                           | docs/reference/bls12-381.md        |
 * | crypto_bls_g1_add                    | L2   | first, second, point                                   | docs/reference/bls12-381.md        |
 * | crypto_bls_g1_neg                    | L2   | point, negated                                         | docs/reference/bls12-381.md        |
 * | crypto_bls_g2_decode                 | L2   | bytes, point                                           | docs/reference/bls12-381.md        |
 * | crypto_bls_g2_compress               | L2   | point, bytes                                           | docs/reference/bls12-381.md        |
 * | crypto_bls_expand_message_xmd        | L2   | message, dst, length, scratch, uniform                 | docs/reference/hash-to-curve.md    |
 * | crypto_bls_hash_to_g2                | L2   | message, dst, scratch, point                           | docs/reference/hash-to-curve.md    |
 */
