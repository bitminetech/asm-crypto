/*
 * asm-crypto Ed25519 definitions, in assembler syntax.
 * The requirement entries are in docs/reference/ed25519.md.
 * Status codes: CRYPTO_INVALID_PUBLIC_KEY, in crypto.inc.
 */

.set CRYPTO_ED25519_PRIVATE_KEY_SIZE, 32
.set CRYPTO_ED25519_PUBLIC_KEY_SIZE, 32
.set CRYPTO_ED25519_SIGNATURE_SIZE, 64  /* R, then S */

/*
 * Internal layouts. A field element is 4 little-endian 64-bit limbs, least
 * significant first, any number below 2^256 that stands for its value mod
 * p = 2^255 - 19. A point is X, Y, Z, T of extended coordinates (RFC 8032
 * section 5.1.4), 128 bytes. A number mod L is 4 limbs below L.
 * The modulus record of L: L at 0, -L^-1 mod 2^64 at 32, 2^256 mod L at 40,
 * 2^512 mod L at 72, 2^768 mod L at 104.
 */
.set CRYPTO_ED25519_POINT_SIZE, 128
.set CRYPTO_ED25519_POINT_X, 0
.set CRYPTO_ED25519_POINT_Y, 32
.set CRYPTO_ED25519_POINT_Z, 64
.set CRYPTO_ED25519_POINT_T, 96
.set CRYPTO_ED25519_MOD_INVERSE, 32
.set CRYPTO_ED25519_MOD_ONE, 40
.set CRYPTO_ED25519_MOD_R2, 72
.set CRYPTO_ED25519_MOD_R3, 104

/*
 * Functions, roles and allowed calls (ARCHITECTURE.md sections 4 and 5).
 *
 * | Function                       | Role | Arguments                               | Requirements              | Allowed calls |
 * |--------------------------------|------|-----------------------------------------|---------------------------|---------------|
 * | crypto_ed25519_public_key      | L2   | private_key, public_key                 | docs/reference/ed25519.md | crypto_ed25519_expand, crypto_ed25519_point_mul, crypto_ed25519_point_encode |
 * | crypto_ed25519_sign            | L2   | private_key, message, signature         | docs/reference/ed25519.md | crypto_ed25519_expand, crypto_ed25519_point_mul, crypto_ed25519_point_encode, crypto_ed25519_hash, crypto_ed25519_scalar_reduce, crypto_ed25519_scalar_mul, crypto_ed25519_scalar_add |
 * | crypto_ed25519_verify          | L2   | public_key, message, signature, valid   | docs/reference/ed25519.md | crypto_ed25519_point_decode, crypto_ed25519_hash, crypto_ed25519_scalar_reduce, crypto_ed25519_point_mul, crypto_ed25519_point_add, crypto_ed25519_point_encode, crypto_ed25519_fe_sub |
 * | crypto_ed25519_expand          | L0   | h, private_key                          | docs/reference/ed25519.md | crypto_sha512 |
 * | crypto_ed25519_hash            | L0   | digest, prefix, prefix_length, message  | docs/reference/ed25519.md | crypto_sha512_init, crypto_sha512_update, crypto_sha512_final |
 * | crypto_ed25519_scalar_reduce   | L0   | result, h                               | docs/reference/ed25519.md | crypto_ed25519_scalar_mul, crypto_ed25519_scalar_add |
 * | crypto_ed25519_scalar_mul      | L0   | result, a, b, modulus                   | docs/reference/ed25519.md | none          |
 * | crypto_ed25519_scalar_add      | L0   | result, a, b, modulus                   | docs/reference/ed25519.md | none          |
 * | crypto_ed25519_point_mul       | L0   | result, scalar, point                   | docs/reference/ed25519.md | crypto_ed25519_point_double, crypto_ed25519_point_add |
 * | crypto_ed25519_point_add       | L0   | result, p, q                            | docs/reference/ed25519.md | crypto_ed25519_fe_mul, crypto_ed25519_fe_add, crypto_ed25519_fe_sub |
 * | crypto_ed25519_point_double    | L0   | result, p                               | docs/reference/ed25519.md | crypto_ed25519_fe_mul, crypto_ed25519_fe_add, crypto_ed25519_fe_sub |
 * | crypto_ed25519_point_encode    | L0   | encoding, p                             | docs/reference/ed25519.md | crypto_ed25519_fe_pow, crypto_ed25519_fe_mul, crypto_ed25519_fe_freeze |
 * | crypto_ed25519_point_decode    | L0   | result, encoding                        | docs/reference/ed25519.md | crypto_ed25519_fe_mul, crypto_ed25519_fe_add, crypto_ed25519_fe_sub, crypto_ed25519_fe_pow, crypto_ed25519_fe_freeze |
 * | crypto_ed25519_fe_pow          | L0   | result, a, exponent                     | docs/reference/ed25519.md | crypto_ed25519_fe_mul |
 * | crypto_ed25519_fe_mul          | L0   | result, a, b                            | docs/reference/ed25519.md | none          |
 * | crypto_ed25519_fe_add          | L0   | result, a, b                            | docs/reference/ed25519.md | none          |
 * | crypto_ed25519_fe_sub          | L0   | result, a, b                            | docs/reference/ed25519.md | none          |
 * | crypto_ed25519_fe_freeze       | L0   | result, a                               | docs/reference/ed25519.md | none          |
 */
