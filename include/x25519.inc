/*
 * asm-crypto X25519 definitions, in assembler syntax.
 * The requirement entries are in docs/reference/x25519.md.
 */

/* Status codes (ARCHITECTURE.md section 6). */
.set CRYPTO_X25519_ZERO, 7              /* crypto_x25519: the result is all zero bytes */

.set CRYPTO_X25519_SIZE, 32             /* a scalar, a u-coordinate, a result */

/*
 * A field element: 4 little-endian 64-bit limbs, least significant first,
 * any number below 2^256 that stands for its value mod p = 2^255 - 19.
 */
.set CRYPTO_X25519_FE_SIZE, 32

/*
 * Functions, roles and allowed calls (ARCHITECTURE.md sections 4 and 5).
 *
 * | Function                | Role | Arguments          | Requirements             | Allowed calls |
 * |-------------------------|------|--------------------|--------------------------|---------------|
 * | crypto_x25519           | L2   | scalar, u, result  | docs/reference/x25519.md | crypto_x25519_mul, crypto_x25519_add, crypto_x25519_sub, crypto_x25519_mul_a24, crypto_x25519_cswap, crypto_x25519_invert |
 * | crypto_x25519_invert    | L0   | result, a          | docs/reference/x25519.md | crypto_x25519_mul |
 * | crypto_x25519_mul       | L0   | result, a, b       | docs/reference/x25519.md | none          |
 * | crypto_x25519_add       | L0   | result, a, b       | docs/reference/x25519.md | none          |
 * | crypto_x25519_sub       | L0   | result, a, b       | docs/reference/x25519.md | none          |
 * | crypto_x25519_mul_a24   | L0   | result, a          | docs/reference/x25519.md | none          |
 * | crypto_x25519_cswap     | L0   | a, b, mask         | docs/reference/x25519.md | none          |
 */
