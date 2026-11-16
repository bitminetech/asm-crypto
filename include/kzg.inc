/*
 * asm-crypto KZG definitions, in assembler syntax.
 * The requirement entries are in docs/reference/kzg.md and
 * docs/reference/kzg-cells.md. The KZG functions are in the object of
 * bls12381.s, so that they can call its local helpers.
 * Shared status codes: CRYPTO_INVALID_ENCODING, in crypto.inc.
 */

/* Status codes (ARCHITECTURE.md section 6). */
.set CRYPTO_KZG_INVALID_COMMITMENT, 13      /* a commitment is not a point of G1 in the form KZG takes */
.set CRYPTO_KZG_INVALID_PROOF, 14           /* a proof is not a point of G1 in the form KZG takes */
.set CRYPTO_KZG_LENGTH_MISMATCH, 15         /* input lists that must have one length do not */
.set CRYPTO_KZG_CELL_INDEX, 16              /* a cell index is 128 or more */
.set CRYPTO_KZG_COMMITMENT_INDEX, 17        /* a commitment index names no commitment */
.set CRYPTO_KZG_INDICES_NOT_ASCENDING, 18   /* cell indices are not strictly ascending */
.set CRYPTO_KZG_NOT_ENOUGH_CELLS, 19        /* fewer than 64 cells */
.set CRYPTO_KZG_TOO_MANY_CELLS, 20          /* more than 128 cells */
.set CRYPTO_KZG_INVALID_TRUSTED_SETUP, 21   /* a list of the setup has the wrong length, or a point does not decompress */

/* Sizes (Kzg/Constants.lean). */
.set CRYPTO_KZG_FIELD_ELEMENT_SIZE, 32      /* big-endian, below r */
.set CRYPTO_KZG_COMMITMENT_SIZE, 48         /* compressed G1 point */
.set CRYPTO_KZG_PROOF_SIZE, 48              /* compressed G1 point */
.set CRYPTO_KZG_FIELD_ELEMENTS_PER_BLOB, 4096
.set CRYPTO_KZG_BLOB_SIZE, 131072           /* 4096 field elements */
.set CRYPTO_KZG_FIELD_ELEMENTS_PER_CELL, 64
.set CRYPTO_KZG_CELL_SIZE, 2048             /* 64 field elements */
.set CRYPTO_KZG_CELLS_PER_EXT_BLOB, 128
.set CRYPTO_KZG_CELLS_SIZE, 262144          /* the 128 cells of an extended blob */
.set CRYPTO_KZG_PROOFS_SIZE, 6144           /* the 128 proofs of an extended blob */
.set CRYPTO_KZG_SETUP_G1_SIZE, 196608       /* 4096 compressed G1 points */
.set CRYPTO_KZG_SETUP_G2_SIZE, 6240         /* 65 compressed G2 points */

/*
 * KzgSettings: the decoded trusted setup, 1198368 bytes. The Lagrange
 * points in bit-reversed order, then the monomial points, as G1 points of
 * bls12381.inc (144 bytes each), then the 65 monomial G2 points (288 bytes
 * each).
 */
.set CRYPTO_KZG_SETTINGS_G1_LAGRANGE, 0
.set CRYPTO_KZG_SETTINGS_G1_MONOMIAL, 589824
.set CRYPTO_KZG_SETTINGS_G2_MONOMIAL, 1179648
.set CRYPTO_KZG_SETTINGS_SIZE, 1198368

/*
 * Lists of blobs, commitments, proofs, cells and indices: a standalone list
 * (ARCHITECTURE.md section 6): size at 0, offset at 8, count at 16, where
 * count is the number of entries; the entries follow each other from offset.
 */
.set CRYPTO_KZG_LIST_SIZE, 0
.set CRYPTO_KZG_LIST_OFFSET, 8
.set CRYPTO_KZG_LIST_COUNT, 16
.set CRYPTO_KZG_LIST_FIXED, 24

/*
 * Scratch: the size field of a scratch buffer is at least
 * CRYPTO_KZG_SCRATCH + CRYPTO_KZG_SCRATCH_PER_ENTRY * entries, with entries
 * as each function states.
 */
.set CRYPTO_KZG_SCRATCH, 2097152
.set CRYPTO_KZG_SCRATCH_PER_ENTRY, 8192

/*
 * Internal layouts. An element of Fr is 4 little-endian 64-bit limbs, least
 * significant first, in Montgomery form a * 2^256 mod r (32 bytes). The r
 * record: r at 0, -r^-1 mod 2^64 at 32, 2^256 mod r at 40, 2^512 mod r at 72.
 */
.set KZG_FR, 32
.set KZG_FR_RECORD_INVERSE, 32
.set KZG_FR_RECORD_ONE, 40
.set KZG_FR_RECORD_R2, 72

/*
 * Functions, roles and allowed calls (ARCHITECTURE.md sections 4 and 5).
 * L0 helpers are listed in their documents as they are added.
 *
 * | Function                                                  | Role | Arguments                                                                | Requirements                  |
 * |-----------------------------------------------------------|------|--------------------------------------------------------------------------|-------------------------------|
 * | crypto_kzg_trusted_setup_of_bytes                         | L2   | g1_lagrange, g1_monomial, g2_monomial, settings                          | docs/reference/kzg.md         |
 * | crypto_kzg_blob_to_kzg_commitment                         | L2   | settings, blob, scratch, commitment                                      | docs/reference/kzg.md         |
 * | crypto_kzg_compute_kzg_proof                              | L2   | settings, blob, z, scratch, proof, y                                     | docs/reference/kzg.md         |
 * | crypto_kzg_verify_kzg_proof                               | L2   | settings, commitment, z, y, proof, scratch, valid                        | docs/reference/kzg.md         |
 * | crypto_kzg_compute_blob_kzg_proof                         | L2   | settings, blob, commitment, scratch, proof                               | docs/reference/kzg.md         |
 * | crypto_kzg_verify_blob_kzg_proof                          | L2   | settings, blob, commitment, proof, scratch, valid                        | docs/reference/kzg.md         |
 * | crypto_kzg_verify_blob_kzg_proof_batch                    | L2   | settings, blobs, commitments, proofs, scratch, valid                     | docs/reference/kzg.md         |
 * | crypto_kzg_compute_challenge                              | L2   | blob, commitment, scratch, challenge                                     | docs/reference/kzg.md         |
 * | crypto_kzg_compute_cells                                  | L2   | blob, scratch, cells                                                     | docs/reference/kzg-cells.md   |
 * | crypto_kzg_compute_cells_and_kzg_proofs                   | L2   | settings, blob, scratch, cells, proofs                                   | docs/reference/kzg-cells.md   |
 * | crypto_kzg_verify_cell_kzg_proof_batch                    | L2   | settings, commitments, cell_indices, cells, proofs, scratch, valid       | docs/reference/kzg-cells.md   |
 * | crypto_kzg_recover_cells_and_kzg_proofs                   | L2   | settings, cell_indices, cells, scratch, recovered_cells, recovered_proofs | docs/reference/kzg-cells.md  |
 * | crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge  | L2   | commitments, commitment_indices, cell_indices, cells, proofs, scratch, challenge | docs/reference/kzg-cells.md |
 *
 * A 7th argument is on the stack on x86-64 (System V AMD64 psABI), at 8 bytes
 * above the return address; ARM64 and RISC-V pass it in x6 and a6.
 */
