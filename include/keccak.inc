/*
 * asm-crypto Keccak-256 definitions, in assembler syntax.
 * The requirement entry for each function is in docs/reference/keccak-256.md.
 */

/* Keccak-256: Keccak[c = 512] with the original padding 10*1 and domain byte 0x01. */
.set CRYPTO_KECCAK256_RATE, 136         /* bytes absorbed per permutation */
.set CRYPTO_KECCAK256_DIGEST_SIZE, 32   /* digest bytes, the first 4 lanes of the state */

/*
 * Functions, roles and allowed calls (ARCHITECTURE.md sections 4 and 5).
 *
 * | Function         | Role | Arguments       | Requirements                  | Allowed calls |
 * |------------------|------|-----------------|-------------------------------|---------------|
 * | crypto_keccak256 | L2   | message, digest | docs/reference/keccak-256.md  | none          |
 */
