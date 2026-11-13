/*
 * asm-crypto P-256 (secp256r1) definitions, in assembler syntax.
 * The requirement entry for each function is in docs/reference/p256.md.
 * Status codes: CRYPTO_INVALID_PRIVATE_KEY and CRYPTO_INVALID_PUBLIC_KEY, in crypto.inc.
 */

.set CRYPTO_P256_PRIVATE_KEY_SIZE, 32
.set CRYPTO_P256_PUBLIC_KEY_SIZE, 65    /* 0x04, then x, then y */
.set CRYPTO_P256_SIGNATURE_SIZE, 64     /* r, then s */

/*
 * Internal layouts, as in secp256k1.inc. A number below a modulus m is 4
 * little-endian 64-bit limbs, least significant first; field elements are
 * in Montgomery form a * 2^256 mod p. A point is X, Y, Z of projective
 * coordinates (96 bytes); Z = 0 is the point at infinity.
 * A modulus record: m at 0, -m^-1 mod 2^64 at 32, 2^256 mod m at 40,
 * 2^512 mod m at 72.
 */
.set CRYPTO_P256_MOD_INVERSE, 32
.set CRYPTO_P256_MOD_ONE, 40
.set CRYPTO_P256_MOD_R2, 72

/*
 * Functions, roles and allowed calls (ARCHITECTURE.md sections 4 and 5).
 *
 * | Function                  | Role | Arguments                          | Requirements           | Allowed calls |
 * |---------------------------|------|------------------------------------|------------------------|---------------|
 * | crypto_p256_public_key    | L2   | private_key, public_key            | docs/reference/p256.md | crypto_p256_point_mul, crypto_p256_point_affine |
 * | crypto_p256_sign          | L2   | private_key, hash, signature       | docs/reference/p256.md | crypto_hmac_sha256, crypto_p256_point_mul, crypto_p256_point_affine, crypto_p256_mod_mul, crypto_p256_mod_add, crypto_p256_mod_pow |
 * | crypto_p256_verify        | L2   | public_key, hash, signature, valid | docs/reference/p256.md | crypto_p256_point_load, crypto_p256_point_mul, crypto_p256_point_add, crypto_p256_point_affine, crypto_p256_mod_mul, crypto_p256_mod_pow |
 * | crypto_p256_point_load    | L0   | point, public_key                  | docs/reference/p256.md | crypto_p256_mod_mul, crypto_p256_mod_add, crypto_p256_mod_sub |
 * | crypto_p256_point_mul     | L0   | point, scalar, base                | docs/reference/p256.md | crypto_p256_point_double, crypto_p256_point_add |
 * | crypto_p256_point_add     | L0   | point, first, second               | docs/reference/p256.md | crypto_p256_mod_mul, crypto_p256_mod_add, crypto_p256_mod_sub |
 * | crypto_p256_point_double  | L0   | point, base                        | docs/reference/p256.md | crypto_p256_mod_mul, crypto_p256_mod_add, crypto_p256_mod_sub |
 * | crypto_p256_point_affine  | L0   | xy, point                          | docs/reference/p256.md | crypto_p256_mod_mul, crypto_p256_mod_pow |
 * | crypto_p256_mod_pow       | L0   | result, base, exponent, modulus    | docs/reference/p256.md | crypto_p256_mod_mul |
 * | crypto_p256_mod_mul       | L0   | result, a, b, modulus              | docs/reference/p256.md | none          |
 * | crypto_p256_mod_add       | L0   | result, a, b, modulus              | docs/reference/p256.md | none          |
 * | crypto_p256_mod_sub       | L0   | result, a, b, modulus              | docs/reference/p256.md | none          |
 */
