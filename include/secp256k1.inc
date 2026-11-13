/*
 * asm-crypto secp256k1 definitions, in assembler syntax.
 * The requirement entry for each function is in docs/reference/secp256k1.md.
 */

/* Status codes (ARCHITECTURE.md section 6). */
.set CRYPTO_INVALID_PRIVATE_KEY, 4      /* the private key is 0, or n or more */
.set CRYPTO_INVALID_PUBLIC_KEY, 5       /* the public key is not a compressed point on the curve */

.set CRYPTO_SECP256K1_PRIVATE_KEY_SIZE, 32
.set CRYPTO_SECP256K1_PUBLIC_KEY_SIZE, 33   /* 0x02 or 0x03 for even or odd y, then x */
.set CRYPTO_SECP256K1_POINT_SIZE, 64        /* x, then y */
.set CRYPTO_SECP256K1_SIGNATURE_SIZE, 64    /* r, then s */

/*
 * Internal layouts. A number below a modulus m is 4 little-endian 64-bit
 * limbs, least significant first; field elements are in Montgomery form
 * a * 2^256 mod p. A point is X, Y, Z of projective coordinates (96 bytes);
 * Z = 0 is the point at infinity.
 * A modulus record: m at 0, -m^-1 mod 2^64 at 32, 2^256 mod m at 40,
 * 2^512 mod m at 72.
 */
.set CRYPTO_SECP256K1_MOD_INVERSE, 32
.set CRYPTO_SECP256K1_MOD_ONE, 40
.set CRYPTO_SECP256K1_MOD_R2, 72

/*
 * Functions, roles and allowed calls (ARCHITECTURE.md sections 4 and 5).
 *
 * | Function                        | Role | Arguments                       | Requirements                | Allowed calls |
 * |---------------------------------|------|---------------------------------|-----------------------------|---------------|
 * | crypto_secp256k1_public_key     | L2   | private_key, public_key         | docs/reference/secp256k1.md | crypto_secp256k1_point_mul, crypto_secp256k1_point_affine |
 * | crypto_secp256k1_decompress     | L2   | public_key, point               | docs/reference/secp256k1.md | crypto_secp256k1_lift_x, crypto_secp256k1_point_affine |
 * | crypto_secp256k1_ecdh           | L2   | public_key, private_key, shared | docs/reference/secp256k1.md | crypto_secp256k1_lift_x, crypto_secp256k1_point_mul, crypto_secp256k1_point_affine |
 * | crypto_secp256k1_sign           | L2   | private_key, hash, signature    | docs/reference/secp256k1.md | crypto_hmac_sha256, crypto_secp256k1_point_mul, crypto_secp256k1_point_affine, crypto_secp256k1_mod_mul, crypto_secp256k1_mod_add, crypto_secp256k1_mod_pow |
 * | crypto_secp256k1_verify         | L2   | public_key, hash, signature, valid | docs/reference/secp256k1.md | crypto_secp256k1_lift_x, crypto_secp256k1_point_mul, crypto_secp256k1_point_add, crypto_secp256k1_point_affine, crypto_secp256k1_mod_mul, crypto_secp256k1_mod_pow |
 * | crypto_secp256k1_lift_x         | L0   | point, public_key               | docs/reference/secp256k1.md | crypto_secp256k1_mod_mul, crypto_secp256k1_mod_add, crypto_secp256k1_mod_sub, crypto_secp256k1_mod_pow |
 * | crypto_secp256k1_point_mul      | L0   | point, scalar, base             | docs/reference/secp256k1.md | crypto_secp256k1_point_double, crypto_secp256k1_point_add |
 * | crypto_secp256k1_point_add      | L0   | point, first, second            | docs/reference/secp256k1.md | crypto_secp256k1_mod_mul, crypto_secp256k1_mod_add, crypto_secp256k1_mod_sub |
 * | crypto_secp256k1_point_double   | L0   | point, base                     | docs/reference/secp256k1.md | crypto_secp256k1_mod_mul, crypto_secp256k1_mod_add, crypto_secp256k1_mod_sub |
 * | crypto_secp256k1_point_affine   | L0   | xy, point                       | docs/reference/secp256k1.md | crypto_secp256k1_mod_mul, crypto_secp256k1_mod_pow |
 * | crypto_secp256k1_mod_pow        | L0   | result, base, exponent, modulus | docs/reference/secp256k1.md | crypto_secp256k1_mod_mul |
 * | crypto_secp256k1_mod_mul        | L0   | result, a, b, modulus           | docs/reference/secp256k1.md | none          |
 * | crypto_secp256k1_mod_add        | L0   | result, a, b, modulus           | docs/reference/secp256k1.md | none          |
 * | crypto_secp256k1_mod_sub        | L0   | result, a, b, modulus           | docs/reference/secp256k1.md | none          |
 */
