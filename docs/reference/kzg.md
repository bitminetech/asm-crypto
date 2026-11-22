# KZG

## Contents

### Functions

- [`crypto_kzg_trusted_setup_of_bytes`](#function-crypto_kzg_trusted_setup_of_bytes): decodes the trusted setup.
- [`crypto_kzg_blob_to_kzg_commitment`](#function-crypto_kzg_blob_to_kzg_commitment): commits to a blob.
- [`crypto_kzg_compute_kzg_proof`](#function-crypto_kzg_compute_kzg_proof): proves the value of a blob's polynomial at a point.
- [`crypto_kzg_verify_kzg_proof`](#function-crypto_kzg_verify_kzg_proof): checks such a proof.
- [`crypto_kzg_compute_blob_kzg_proof`](#function-crypto_kzg_compute_blob_kzg_proof): proves a blob against its commitment.
- [`crypto_kzg_verify_blob_kzg_proof`](#function-crypto_kzg_verify_blob_kzg_proof): checks such a proof.
- [`crypto_kzg_verify_blob_kzg_proof_batch`](#function-crypto_kzg_verify_blob_kzg_proof_batch): checks several such proofs at once.
- [`crypto_kzg_compute_challenge`](#function-crypto_kzg_compute_challenge): computes the challenge of a blob and its commitment.
- [`crypto_kzg_fr_mul`](#function-crypto_kzg_fr_mul): multiplies two elements of Fr.
- [`crypto_kzg_fr_add`](#function-crypto_kzg_fr_add): adds two elements of Fr.
- [`crypto_kzg_fr_sub`](#function-crypto_kzg_fr_sub): subtracts two elements of Fr.
- [`crypto_kzg_fr_neg`](#function-crypto_kzg_fr_neg): negates an element of Fr.
- [`crypto_kzg_fr_pow`](#function-crypto_kzg_fr_pow): raises an element of Fr to a public power.
- [`crypto_kzg_fr_inverse`](#function-crypto_kzg_fr_inverse): computes 1 / a in Fr.
- [`crypto_kzg_fr_from_bytes`](#function-crypto_kzg_fr_from_bytes): reads 32 big-endian bytes as an element of Fr.
- [`crypto_kzg_fr_from_digest`](#function-crypto_kzg_fr_from_digest): reads a digest as an element of Fr.
- [`crypto_kzg_fr_from_u64`](#function-crypto_kzg_fr_from_u64): converts a u64 to an element of Fr.
- [`crypto_kzg_fr_canonical`](#function-crypto_kzg_fr_canonical): writes the value of an element of Fr.
- [`crypto_kzg_fr_to_bytes`](#function-crypto_kzg_fr_to_bytes): writes an element of Fr as 32 big-endian bytes.
- [`crypto_kzg_roots_of_unity`](#function-crypto_kzg_roots_of_unity): computes the roots of unity of a power-of-two order.
- [`crypto_kzg_bit_reversal`](#function-crypto_kzg_bit_reversal): puts entries in bit-reversed order.
- [`crypto_kzg_batch_inverse`](#function-crypto_kzg_batch_inverse): inverts many elements of Fr with one inversion.
- [`crypto_kzg_blob_to_poly`](#function-crypto_kzg_blob_to_poly): reads field elements from bytes.
- [`crypto_kzg_validate_g1`](#function-crypto_kzg_validate_g1): checks a commitment or a proof.
- [`crypto_kzg_challenge`](#function-crypto_kzg_challenge): computes the challenge of a blob and its commitment.
- [`crypto_kzg_g1_lincomb`](#function-crypto_kzg_g1_lincomb): computes a linear combination of points of G1.
- [`crypto_kzg_domain`](#function-crypto_kzg_domain): computes the bit-reversed 4096-th roots of unity.
- [`crypto_kzg_evaluate`](#function-crypto_kzg_evaluate): evaluates a polynomial in evaluation form.
- [`crypto_kzg_quotient_in_domain`](#function-crypto_kzg_quotient_in_domain): computes the quotient at a domain point.
- [`crypto_kzg_proof_impl`](#function-crypto_kzg_proof_impl): computes a proof and the value it proves.
- [`crypto_kzg_verify_impl`](#function-crypto_kzg_verify_impl): checks a proof against a commitment.

### Types

- [`KzgSettings`](#type-kzgsettings): the decoded trusted setup.
- [`Blob`](#type-blob): 4096 field elements.
- [`KzgFieldElement`](#type-kzgfieldelement): an element of Fr as 32 bytes.
- [`KzgCommitment`](#type-kzgcommitment): a commitment.
- [`KzgProof`](#type-kzgproof): a proof.
- [`BlobList`](#type-bloblist): a list of blobs.
- [`KzgCommitmentList`](#type-kzgcommitmentlist): a list of commitments.
- [`KzgProofList`](#type-kzgprooflist): a list of proofs.
- [`KzgScratch`](#type-kzgscratch): the workspace of a KZG function.
- [`FrElement`](#type-frelement): an element of Fr, in Montgomery form.

### Constants

- [`CRYPTO_KZG_SCRATCH`](#constant-crypto_kzg_scratch): the fixed part of a `KzgScratch`.
- [`CRYPTO_KZG_SCRATCH_PER_ENTRY`](#constant-crypto_kzg_scratch_per_entry): the part of a `KzgScratch` for each entry.
- [`CRYPTO_KZG_INVALID_COMMITMENT`](#constant-crypto_kzg_invalid_commitment): a commitment is not valid.
- [`CRYPTO_KZG_INVALID_PROOF`](#constant-crypto_kzg_invalid_proof): a proof is not valid.
- [`CRYPTO_KZG_LENGTH_MISMATCH`](#constant-crypto_kzg_length_mismatch): input lists have different lengths.
- [`CRYPTO_KZG_INVALID_TRUSTED_SETUP`](#constant-crypto_kzg_invalid_trusted_setup): the trusted setup does not decode.

## Spec

- Document: [cryptography-specs v0.3.0](https://github.com/ethereum/cryptography-specs/tree/bb6dfe55198243682bc2eaf94611af2dbce1be6f/EthLib/Cryptography/Kzg), commit `bb6dfe55198243682bc2eaf94611af2dbce1be6f`.
- Files: `Constants.lean`, `Errors.lean`, `BitReversal.lean`, `Fft.lean`, `Polynomials.lean`, `TrustedSetup.lean` and `Core.lean`, and `Exports/Kzg.lean` (`computeChallengeExport`).
- EIP-4844 adds these functions at the Dencun fork. The cell functions of EIP-7594 are in [kzg-cells.md](kzg-cells.md).
- Fr is the field of integers mod r, the order of G1 and G2 ([bls12-381.md](bls12-381.md)). A blob holds the values of a polynomial p of degree below 4096 at the 4096-th roots of unity, in bit-reversed order: value i is p(omega_i), with omega_i entry i of the bit-reversed powers of 7^((r - 1) / 4096).
- A commitment to p is [p(s)] in G1, for the secret s of the trusted setup: the sum of p(omega_i) times the Lagrange points of the setup.
- The trusted setup is the output of the KZG ceremony, `trusted_setup_4096.json` of consensus-specs, which `TrustedSetupData.lean` holds as hex strings. It is trusted, not proved.
- The spec does not run in constant time. No function here takes secret data.

## Function `crypto_kzg_trusted_setup_of_bytes`

Decodes the trusted setup from its compressed points (`TrustedSetup.ofBytes`).

### Signature

```
crypto_kzg_trusted_setup_of_bytes(g1_lagrange, g1_monomial, g2_monomial, settings) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `g1_lagrange` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `g1_monomial` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `g2_monomial` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `settings` | output | `KzgSettings` |

### Returns

- `CRYPTO_OK`: `settings` holds the setup.
- `CRYPTO_KZG_INVALID_TRUSTED_SETUP`: the `count` of `g1_lagrange` or `g1_monomial` is not 196608, the `count` of `g2_monomial` is not 6240, or a point does not decompress. `settings` then holds no valid value.

### Caller must

- Pass valid `ByteList` values. They are not checked.
- Keep `settings` apart from the inputs.

### Function does

- Checks the three counts first.
- Decompresses the 4096 Lagrange points, the 4096 monomial points of G1 and the 65 points of G2 with `G1.uncompress` and `G2.uncompress`. As in the spec, it checks that each point is on its curve, not that it is in its subgroup.
- Writes Lagrange point i at position rev(i), with rev the reversal of 12 bits (`bitReversalPermutation`), and the other points in order.

### Function never

- Reads more than the `ByteList` headers and their `count` bytes.
- Writes more than `settings` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 1168 bytes on x86-64 (return address included), 1296 bytes on ARM64, 1424 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_kzg_trusted_setup_of_bytes` (`_crypto_kzg_trusted_setup_of_bytes` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `g1_lagrange`, `g1_monomial`, `g2_monomial`, `settings`.

## Function `crypto_kzg_blob_to_kzg_commitment`

Computes the commitment to the polynomial of a blob (`blobToKzgCommitment`).

### Signature

```
crypto_kzg_blob_to_kzg_commitment(settings, blob, scratch, commitment) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `settings` | input | `KzgSettings` |
| `blob` | input | `Blob` |
| `scratch` | scratch | `KzgScratch` |
| `commitment` | output | `KzgCommitment` |

### Returns

- `CRYPTO_OK`: `commitment` holds the commitment.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_KZG_SCRATCH` bytes. Nothing is written.
- `CRYPTO_INVALID_ENCODING`: a field element of the blob is r or more (`blobToPolynomial`). Nothing is written.

### Caller must

- Pass a `settings` that `crypto_kzg_trusted_setup_of_bytes` wrote.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch` and `commitment` apart from each other and from the inputs.

### Function does

- Checks `scratch` first, then the blob.
- Computes the sum of p_i times Lagrange point i of `settings` (`g1LincombPoints`), by the steps of `G1.msm`: Pippenger's method with windows of 8 bits.
- Writes the compressed sum (`G1.compress`).

### Function never

- Reads more than `settings`, `blob` and the `size` field of `scratch`.
- Writes more than `scratch`, `commitment` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 1552 bytes on x86-64 (return address included), 1616 bytes on ARM64, 1728 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_kzg_blob_to_kzg_commitment` (`_crypto_kzg_blob_to_kzg_commitment` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `settings`, `blob`, `scratch`, `commitment`.

## Function `crypto_kzg_compute_kzg_proof`

Computes the proof that p(z) = y for the polynomial p of a blob, and y (`computeKzgProof`).

### Signature

```
crypto_kzg_compute_kzg_proof(settings, blob, z, scratch, proof, y) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `settings` | input | `KzgSettings` |
| `blob` | input | `Blob` |
| `z` | input | `KzgFieldElement` |
| `scratch` | scratch | `KzgScratch` |
| `proof` | output | `KzgProof` |
| `y` | output | `KzgFieldElement` |

### Returns

- `CRYPTO_OK`: `proof` and `y` hold the proof and p(z).
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_KZG_SCRATCH` bytes. Nothing is written.
- `CRYPTO_INVALID_ENCODING`: a field element of the blob, or z, is r or more. Nothing is written.

### Caller must

- Pass a `settings` that `crypto_kzg_trusted_setup_of_bytes` wrote.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch`, `proof` and `y` apart from each other and from the inputs.

### Function does

- Checks `scratch` first, then the blob, then z.
- Computes y = p(z) (`evaluatePolynomialInEvaluationForm`): p_i when z = omega_i, else (z^4096 - 1) / 4096 times the sum of p_i omega_i / (z - omega_i), with one batch inversion.
- Computes the quotient q_i = (p_i - y) / (omega_i - z) for each i, and for the i with omega_i = z, the sum over j != i of (p_j - y) omega_j / (z (z - omega_j)) (`computeQuotientEvalWithinDomain`).
- Writes the compressed sum of q_i times Lagrange point i, and y as 32 big-endian bytes (`computeKzgProofImpl`).

### Function never

- Reads more than `settings`, `blob`, `z` and the `size` field of `scratch`.
- Writes more than `scratch`, `proof`, `y` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 1616 bytes on x86-64 (return address included), 1712 bytes on ARM64, 1840 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_kzg_compute_kzg_proof` (`_crypto_kzg_compute_kzg_proof` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `settings`, `blob`, `z`, `scratch`, `proof`, `y`.

## Function `crypto_kzg_verify_kzg_proof`

Checks a proof that p(z) = y for the polynomial p of a commitment (`verifyKzgProof`).

### Signature

```
crypto_kzg_verify_kzg_proof(settings, commitment, z, y, proof, scratch, valid) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `settings` | input | `KzgSettings` |
| `commitment` | input | `KzgCommitment` |
| `z` | input | `KzgFieldElement` |
| `y` | input | `KzgFieldElement` |
| `proof` | input | `KzgProof` |
| `scratch` | scratch | `KzgScratch` |
| `valid` | output | [`Valid`](secp256k1.md#type-valid) |

### Returns

- `CRYPTO_OK`: `valid` holds 1 or 0.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_KZG_SCRATCH` bytes. Nothing is written.
- `CRYPTO_KZG_INVALID_COMMITMENT`: the commitment breaks the rule of `KzgCommitment`. Nothing is written.
- `CRYPTO_KZG_INVALID_PROOF`: the proof breaks the rule of `KzgProof`. Nothing is written.
- `CRYPTO_INVALID_ENCODING`: z or y is r or more. Nothing is written.

### Caller must

- Pass a `settings` that `crypto_kzg_trusted_setup_of_bytes` wrote.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch` and `valid` apart from each other and from the inputs.

### Function does

- Checks `scratch` first, then the commitment, the proof, z and y (`validateKzgG1Point`, `bytesToBlsField`).
- Writes 1 when e(C - [y], -[1]) e(proof, [s] - [z]) = 1, else 0 (`verifyKzgProofWith`): [y] is y times the generator of G1, [1] the generator of G2, and [s] G2 point 1 of `settings`.

### Function never

- Reads more than `settings`, `commitment`, `z`, `y`, `proof` and the `size` field of `scratch`.
- Writes more than `scratch`, `valid` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 2688 bytes on x86-64 (return address included), 2912 bytes on ARM64, 3088 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_kzg_verify_kzg_proof` (`_crypto_kzg_verify_kzg_proof` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). On x86-64, `valid`, the seventh argument, is on the stack.
- Argument order: `settings`, `commitment`, `z`, `y`, `proof`, `scratch`, `valid`.

## Function `crypto_kzg_compute_blob_kzg_proof`

Computes the proof of a blob at the challenge of the blob and its commitment (`computeBlobKzgProof`).

### Signature

```
crypto_kzg_compute_blob_kzg_proof(settings, blob, commitment, scratch, proof) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `settings` | input | `KzgSettings` |
| `blob` | input | `Blob` |
| `commitment` | input | `KzgCommitment` |
| `scratch` | scratch | `KzgScratch` |
| `proof` | output | `KzgProof` |

### Returns

- `CRYPTO_OK`: `proof` holds the proof.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_KZG_SCRATCH` bytes. Nothing is written.
- `CRYPTO_KZG_INVALID_COMMITMENT`: the commitment breaks the rule of `KzgCommitment`. Nothing is written.
- `CRYPTO_INVALID_ENCODING`: a field element of the blob is r or more. Nothing is written.

### Caller must

- Pass a `settings` that `crypto_kzg_trusted_setup_of_bytes` wrote.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch` and `proof` apart from each other and from the inputs.

### Function does

- Checks `scratch` first, then the commitment, then the blob.
- Computes z, the challenge of `crypto_kzg_compute_challenge`, and writes the proof of `crypto_kzg_compute_kzg_proof` at z.
- Does not check that the commitment is the one of the blob, as in the spec.

### Function never

- Reads more than `settings`, `blob`, `commitment` and the `size` field of `scratch`.
- Writes more than `scratch`, `proof` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 1952 bytes on x86-64 (return address included), 2112 bytes on ARM64, 2256 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_kzg_compute_blob_kzg_proof` (`_crypto_kzg_compute_blob_kzg_proof` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `settings`, `blob`, `commitment`, `scratch`, `proof`.

## Function `crypto_kzg_verify_blob_kzg_proof`

Checks the proof of a blob against its commitment (`verifyBlobKzgProof`).

### Signature

```
crypto_kzg_verify_blob_kzg_proof(settings, blob, commitment, proof, scratch, valid) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `settings` | input | `KzgSettings` |
| `blob` | input | `Blob` |
| `commitment` | input | `KzgCommitment` |
| `proof` | input | `KzgProof` |
| `scratch` | scratch | `KzgScratch` |
| `valid` | output | [`Valid`](secp256k1.md#type-valid) |

### Returns

- `CRYPTO_OK`: `valid` holds 1 or 0.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_KZG_SCRATCH` bytes. Nothing is written.
- `CRYPTO_KZG_INVALID_COMMITMENT`: the commitment breaks the rule of `KzgCommitment`. Nothing is written.
- `CRYPTO_INVALID_ENCODING`: a field element of the blob is r or more. Nothing is written.
- `CRYPTO_KZG_INVALID_PROOF`: the proof breaks the rule of `KzgProof`. Nothing is written.

### Caller must

- Pass a `settings` that `crypto_kzg_trusted_setup_of_bytes` wrote.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch` and `valid` apart from each other and from the inputs.

### Function does

- Checks `scratch` first, then the commitment, the blob and the proof.
- Computes z, the challenge of `crypto_kzg_compute_challenge`, and y = p(z) as `crypto_kzg_compute_kzg_proof` does.
- Writes the result of the check of `crypto_kzg_verify_kzg_proof` on the commitment, z, y and the proof.

### Function never

- Reads more than `settings`, `blob`, `commitment`, `proof` and the `size` field of `scratch`.
- Writes more than `scratch`, `valid` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 2688 bytes on x86-64 (return address included), 2912 bytes on ARM64, 3088 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_kzg_verify_blob_kzg_proof` (`_crypto_kzg_verify_blob_kzg_proof` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `settings`, `blob`, `commitment`, `proof`, `scratch`, `valid`.

## Function `crypto_kzg_verify_blob_kzg_proof_batch`

Checks the proofs of several blobs against their commitments at once (`verifyBlobKzgProofBatch`).

### Signature

```
crypto_kzg_verify_blob_kzg_proof_batch(settings, blobs, commitments, proofs, scratch, valid) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `settings` | input | `KzgSettings` |
| `blobs` | input | `BlobList` |
| `commitments` | input | `KzgCommitmentList` |
| `proofs` | input | `KzgProofList` |
| `scratch` | scratch | `KzgScratch` |
| `valid` | output | [`Valid`](secp256k1.md#type-valid) |

### Returns

- `CRYPTO_OK`: `valid` holds 1 or 0.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_KZG_SCRATCH` + `CRYPTO_KZG_SCRATCH_PER_ENTRY` * n bytes, with n the `count` of `blobs`. Nothing is written.
- `CRYPTO_KZG_LENGTH_MISMATCH`: the `count` of `commitments` or of `proofs` differs from n. Nothing is written.
- `CRYPTO_KZG_INVALID_COMMITMENT`, `CRYPTO_INVALID_ENCODING` or `CRYPTO_KZG_INVALID_PROOF`: the first failed check of the triples, in order. Nothing is written.

### Caller must

- Pass a `settings` that `crypto_kzg_trusted_setup_of_bytes` wrote.
- Pass valid lists. They are not checked.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch` and `valid` apart from each other and from the inputs.

### Function does

- Checks `scratch` first, then the counts, then each triple in order: its commitment, its blob, then its proof.
- Computes z_i, the challenge of blob i and commitment i, and y_i = p_i(z_i).
- Computes r, SHA-256 of "RCKZGBATCH___V1_" || I2OSP(4096, 8) || I2OSP(n, 8) || C_i || z_i || y_i || proof_i for each i, as a number mod r (`computeVerifyKzgProofBatchChallenge`).
- Writes 1 when e(sum r^i proof_i, -[s]) e(sum r^i (C_i - [y_i]) + sum r^i z_i proof_i, [1]) = 1, else 0. An empty batch gives 1.

### Function never

- Reads more than `settings`, the list headers and their entries, and the `size` field of `scratch`.
- Writes more than `scratch`, `valid` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 2720 bytes on x86-64 (return address included), 2896 bytes on ARM64, 3024 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_kzg_verify_blob_kzg_proof_batch` (`_crypto_kzg_verify_blob_kzg_proof_batch` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `settings`, `blobs`, `commitments`, `proofs`, `scratch`, `valid`.

## Function `crypto_kzg_compute_challenge`

Computes the Fiat-Shamir challenge of a blob and its commitment (`computeChallenge`, `computeChallengeExport`).

### Signature

```
crypto_kzg_compute_challenge(blob, commitment, scratch, challenge) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `blob` | input | `Blob` |
| `commitment` | input | `KzgCommitment` |
| `scratch` | scratch | `KzgScratch` |
| `challenge` | output | `KzgFieldElement` |

### Returns

- `CRYPTO_OK`: `challenge` holds the challenge.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_KZG_SCRATCH` bytes. Nothing is written.
- `CRYPTO_INVALID_ENCODING`: a field element of the blob is r or more. Nothing is written.
- `CRYPTO_KZG_INVALID_COMMITMENT`: the commitment breaks the rule of `KzgCommitment`. Nothing is written.

### Caller must

- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch` and `challenge` apart from each other and from the inputs.

### Function does

- Checks `scratch` first, then the blob, then the commitment, as `computeChallengeExport` does.
- Computes SHA-256 of "FSBLOBVERIFY_V1_" || I2OSP(4096, 16) || blob || commitment, takes it as a big-endian number mod r (`hashToBlsField`), and writes it as 32 big-endian bytes.

### Function never

- Reads more than `blob`, `commitment` and the `size` field of `scratch`.
- Writes more than `scratch`, `challenge` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 1952 bytes on x86-64 (return address included), 2112 bytes on ARM64, 2256 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_kzg_compute_challenge` (`_crypto_kzg_compute_challenge` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `blob`, `commitment`, `scratch`, `challenge`.

## Function `crypto_kzg_fr_mul`

Computes a * b / 2^256 mod r, the Montgomery product (`Fr.mul`).

### Signature

```
crypto_kzg_fr_mul(result, a, b) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `FrElement` |
| `a` | input | `FrElement`, or a number below 2^256 |
| `b` | input | `FrElement` |

### Function does

- Runs CIOS on 4 limbs: for each limb b_i of b, adds a * b_i to T, then q * r with q = T_0 * (-r^-1 mod 2^64), and drops the low limb of T.
- Subtracts r once when T is r or more, which gives a number below r when b is below r.
- Writes `result` last, so it may be `a` or `b`.

### Function never

- Writes more than `result` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 48 bytes on x86-64 (return address included), none on ARM64, 80 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_fr_mul`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `a`, `b`.

## Function `crypto_kzg_fr_add`

Computes a + b mod r (`Fr.add`).

### Signature

```
crypto_kzg_fr_add(result, a, b) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `FrElement` |
| `a` | input | `FrElement` |
| `b` | input | `FrElement` |

### Function does

- Adds, then subtracts r when the sum is r or more.
- Writes `result` last, so it may be `a` or `b`.

### Function never

- Writes more than `result`.
- Makes an OS call.

### Limits

- Stack of its own: 8 bytes on x86-64, its return address, and none on ARM64 and RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_fr_add`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `a`, `b`.

## Function `crypto_kzg_fr_sub`

Computes a - b mod r (`Fr.sub`).

### Signature

```
crypto_kzg_fr_sub(result, a, b) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `FrElement` |
| `a` | input | `FrElement` |
| `b` | input | `FrElement` |

### Function does

- Subtracts, then adds r when the difference borrows.
- Writes `result` last, so it may be `a` or `b`.

### Function never

- Writes more than `result`.
- Makes an OS call.

### Limits

- Stack of its own: 8 bytes on x86-64, its return address, and none on ARM64 and RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_fr_sub`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `a`, `b`.

## Function `crypto_kzg_fr_neg`

Computes -a mod r; 0 stays 0 (`Fr.neg`).

### Signature

```
crypto_kzg_fr_neg(result, a) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `FrElement` |
| `a` | input | `FrElement` |

### Function does

- Computes r - a, or 0 when a is 0.
- Reads `a` first, so `result` may be `a`.

### Function never

- Writes more than `result`.
- Makes an OS call.

### Limits

- Stack of its own: 8 bytes on x86-64, its return address, and none on ARM64 and RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_fr_neg`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `a`.

## Function `crypto_kzg_fr_pow`

Computes base^e (`Fr.powNat`), for a public e.

### Signature

```
crypto_kzg_fr_pow(result, base, exponent) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `FrElement` |
| `base` | input | `FrElement` |
| `exponent` | input | [`Scalar`](bls12-381.md#type-scalar): e |

### Function does

- Squares, and multiplies by base where a bit of e is 1, from the top set bit of e down. e = 0 gives 1.
- Copies `base` first, so `result` may be `base`.

### Function never

- Writes more than `result` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 128 bytes on x86-64 (return address included), 160 bytes on ARM64, 176 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_fr_pow`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `base`, `exponent`.

## Function `crypto_kzg_fr_inverse`

Computes a^(r - 2), which is 1 / a for a not 0, and 0 for a = 0 (`Fr.inverse`).

### Signature

```
crypto_kzg_fr_inverse(result, a) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `FrElement` |
| `a` | input | `FrElement` |

### Function does

- Calls `crypto_kzg_fr_pow` with the exponent r - 2.
- `result` may be `a`.

### Function never

- Writes more than `result` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_fr_inverse`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `a`.

## Function `crypto_kzg_fr_from_bytes`

Reads 32 big-endian bytes as an element of Fr (`Fr.fromBytesBE`, `bytesToBlsField`).

### Signature

```
crypto_kzg_fr_from_bytes(result, bytes) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `FrElement` |
| `bytes` | input | `KzgFieldElement` |

### Returns

- `CRYPTO_OK`: `result` holds the element.
- `CRYPTO_INVALID_ENCODING`: the number is r or more. Nothing is written.

### Caller must

- Keep `result` apart from `bytes`.

### Function does

- Checks that the number is below r.
- Converts it with a Montgomery product by 2^512 mod r.

### Function never

- Writes more than `result` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 96 bytes on x86-64 (return address included), 128 bytes on ARM64, 144 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_fr_from_bytes`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `result`, `bytes`.

## Function `crypto_kzg_fr_from_digest`

Reads 32 big-endian bytes as a number n below 2^256, and writes n mod r (`Fr.ofNat` in `hashToBlsField`).

### Signature

```
crypto_kzg_fr_from_digest(result, bytes) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `FrElement` |
| `bytes` | input | 32 bytes: a big-endian number |

### Caller must

- Keep `result` apart from `bytes`.

### Function does

- Computes n * 2^512 / 2^256 mod r with a Montgomery product.

### Function never

- Writes more than `result` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 96 bytes on x86-64 (return address included), 128 bytes on ARM64, 144 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_fr_from_digest`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `bytes`.

## Function `crypto_kzg_fr_from_u64`

Writes the value as an element of Fr (`Fr.ofNat`).

### Signature

```
crypto_kzg_fr_from_u64(result, value) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `FrElement` |
| `value` | input | u64 in a register |

### Function does

- Computes value * 2^512 / 2^256 mod r with a Montgomery product.

### Function never

- Writes more than `result` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 96 bytes on x86-64 (return address included), 128 bytes on ARM64, 144 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_fr_from_u64`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `value`.

## Function `crypto_kzg_fr_canonical`

Writes the value of a as 4 limbs, out of Montgomery form (`Fr.val`).

### Signature

```
crypto_kzg_fr_canonical(result, a) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | [`Scalar`](bls12-381.md#type-scalar) |
| `a` | input | `FrElement` |

### Function does

- Computes the Montgomery product of a and 1.
- `result` may be `a`.

### Function never

- Writes more than `result` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 96 bytes on x86-64 (return address included), 128 bytes on ARM64, 144 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_fr_canonical`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `a`.

## Function `crypto_kzg_fr_to_bytes`

Writes a as 32 big-endian bytes (`blsFieldToBytes`).

### Signature

```
crypto_kzg_fr_to_bytes(bytes, a) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `bytes` | output | `KzgFieldElement` |
| `a` | input | `FrElement` |

### Function does

- Writes the value from `crypto_kzg_fr_canonical`, most significant byte first.

### Function never

- Writes more than `bytes` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 96 bytes on x86-64 (return address included), 128 bytes on ARM64, 144 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_fr_to_bytes`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `bytes`, `a`.

## Function `crypto_kzg_roots_of_unity`

Writes 1, w, ..., w^(order - 1), with w = 7^((r - 1) / order) (`computeRootsOfUnity`).

### Signature

```
crypto_kzg_roots_of_unity(roots, order) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `roots` | output | order `FrElement` values |
| `order` | input | u64 in a register: a power of two from 2 to 2^32 |

### Function does

- Computes (r - 1) / order by a shift, w with `crypto_kzg_fr_pow`, then each power from the one before (`computePowers`).

### Function never

- Writes more than `roots` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 128 bytes on x86-64 (return address included), 160 bytes on ARM64, 176 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_roots_of_unity`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `roots`, `order`.

## Function `crypto_kzg_bit_reversal`

Applies the bit-reversal permutation to n entries, in place (`bitReversalPermutation`).

### Signature

```
crypto_kzg_bit_reversal(array, n, size) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `array` | state | n entries of size bytes |
| `n` | input | u64 in a register: a power of two from 2 up |
| `size` | input | u64 in a register: a multiple of 16 |

### Function does

- Swaps entry i with entry rev(i) for each i < rev(i), with rev the reversal of log2 n bits (`reverseBits`).

### Function never

- Writes more than `array` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), none on ARM64, none on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_bit_reversal`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `array`, `n`, `size`.

## Function `crypto_kzg_batch_inverse`

Writes out[i] = 1 / in[i], and 0 for 0 (`Fr.batchInverse`).

### Signature

```
crypto_kzg_batch_inverse(out, in, n) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `out` | output | n `FrElement` values |
| `in` | input | n `FrElement` values |
| `n` | input | u64 in a register |

### Caller must

- Keep `out` apart from `in`.

### Function does

- Writes in out[i] the product of the nonzero values before i, inverts the product of all of them once, then walks back: out[i] = out[i] s and s = s in[i] for each nonzero in[i].

### Function never

- Writes more than `out` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 128 bytes on x86-64 (return address included), 160 bytes on ARM64, 176 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_batch_inverse`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `out`, `in`, `n`.

## Function `crypto_kzg_blob_to_poly`

Reads count field elements of 32 big-endian bytes (`bytesToBlsFields`, `blobToPolynomial`).

### Signature

```
crypto_kzg_blob_to_poly(poly, bytes, count) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `poly` | output | count `FrElement` values |
| `bytes` | input | count `KzgFieldElement` values |
| `count` | input | u64 in a register |

### Returns

- `CRYPTO_OK`: `poly` holds the values.
- `CRYPTO_INVALID_ENCODING`: a value is r or more. The values before it are written.

### Caller must

- Keep `poly` apart from `bytes`.

### Function does

- Reads each one with `crypto_kzg_fr_from_bytes`, in order, and stops at the first that is r or more.

### Function never

- Writes more than `poly` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_blob_to_poly`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `poly`, `bytes`, `count`.

## Function `crypto_kzg_validate_g1`

Reads a commitment or a proof as a point of G1 (`validateKzgG1Point`).

### Signature

```
crypto_kzg_validate_g1(bytes, point) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `bytes` | input | `KzgCommitment` |
| `point` | output | [`G1Point`](bls12-381.md#type-g1point) |

### Returns

- `CRYPTO_OK`: `point` holds the point.
- `CRYPTO_INVALID_PUBLIC_KEY`: the bytes break the rule of `KzgCommitment`. Nothing is written.

### Caller must

- Keep `point` apart from `bytes`.

### Function does

- Writes the point at infinity for 0xC0 followed by 47 zero bytes.
- Otherwise runs `crypto_bls_key_validate_point`.

### Function never

- Writes more than `point` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_validate_g1`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `bytes`, `point`.

## Function `crypto_kzg_challenge`

Computes the Fiat-Shamir challenge of a blob and its commitment (`computeChallenge`).

### Signature

```
crypto_kzg_challenge(result, blob, commitment, work) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `FrElement` |
| `blob` | input | `Blob` |
| `commitment` | input | `KzgCommitment` |
| `work` | scratch | 131232 bytes |

### Caller must

- Keep `work` apart from the other arguments.

### Function does

- Writes "FSBLOBVERIFY_V1_" || I2OSP(4096, 16) || blob || commitment in `work` as a `ByteList`, hashes it with `crypto_sha256`, and reads the digest with `crypto_kzg_fr_from_digest`.

### Function never

- Writes more than `result` and `work` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_challenge`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `blob`, `commitment`, `work`.

## Function `crypto_kzg_g1_lincomb`

Computes the sum of scalars[j] times points[j] (`g1LincombPoints`), by the steps of `G1.msm`.

### Signature

```
crypto_kzg_g1_lincomb(result, points, scalars, n, work) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | [`G1Point`](bls12-381.md#type-g1point) |
| `points` | input | n [`G1Point`](bls12-381.md#type-g1point) values |
| `scalars` | input | n `FrElement` values |
| `n` | input | u64 in a register |
| `work` | scratch | 32 n + 37296 bytes |

### Caller must

- Keep `work` apart from the other arguments.

### Function does

- Writes the point at infinity for n = 0, or when every scalar is 0.
- Takes the values of the scalars, and nW = the top bit length over 8, rounded up.
- For each window k from nW - 1 down to 0: adds each point to bucket v, its digit k (`msmBuckets`), takes the sum of v B_v by running sums from bucket 255 down (`msmRunning`), and adds it to the sum, after 8 doublings except at the first window (`msmCombine`).

### Function never

- Writes more than `result` and `work` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 96 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_g1_lincomb`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `points`, `scalars`, `n`, `work`.

## Function `crypto_kzg_domain`

Writes the 4096-th roots of unity in bit-reversed order (`rootsOfUnityBrp 4096`).

### Signature

```
crypto_kzg_domain(domain) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `domain` | output | 4096 `FrElement` values |

### Function does

- Calls `crypto_kzg_roots_of_unity`, then `crypto_kzg_bit_reversal`.

### Function never

- Writes more than `domain` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_domain`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `domain`.

## Function `crypto_kzg_evaluate`

Computes p(z) for the 4096 values of p (`evaluatePolynomialInEvaluationForm`).

### Signature

```
crypto_kzg_evaluate(result, poly, z, work) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `FrElement` |
| `poly` | input | 4096 `FrElement` values |
| `z` | input | `FrElement` |
| `work` | scratch | 393216 bytes |

### Caller must

- Keep `work` apart from the other arguments.

### Function does

- Writes value i when z is point i of the domain.
- Otherwise writes (z^4096 - 1) / 4096 times the sum of p_i d_i / (z - d_i), with one batch inversion.

### Function never

- Writes more than `result` and `work` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 160 bytes on x86-64 (return address included), 192 bytes on ARM64, 208 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_evaluate`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `poly`, `z`, `work`.

## Function `crypto_kzg_quotient_in_domain`

Computes the quotient of the proof at the domain point z (`computeQuotientEvalWithinDomain`).

### Signature

```
crypto_kzg_quotient_in_domain(result, z, poly, y, work) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `FrElement` |
| `z` | input | `FrElement` |
| `poly` | input | 4096 `FrElement` values |
| `y` | input | `FrElement`: p(z) |
| `work` | scratch | 393216 bytes |

### Caller must

- Keep `work` apart from the other arguments.

### Function does

- Writes the sum over the domain points d_i != z of (p_i - y) d_i / (z (z - d_i)), with one batch inversion.

### Function never

- Writes more than `result` and `work` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 96 bytes on x86-64 (return address included), 128 bytes on ARM64, 144 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_quotient_in_domain`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `z`, `poly`, `y`, `work`.

## Function `crypto_kzg_proof_impl`

Computes y = p(z) and the proof of it (`computeKzgProofImpl`).

### Signature

```
crypto_kzg_proof_impl(settings, poly, z, work, proof, y) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `settings` | input | `KzgSettings` |
| `poly` | input | 4096 `FrElement` values |
| `z` | input | `FrElement` |
| `work` | scratch | 1310720 bytes |
| `proof` | output | [`G1Point`](bls12-381.md#type-g1point) |
| `y` | output | `FrElement` |

### Caller must

- Keep `work`, `proof` and `y` apart from each other and from the inputs.

### Function does

- Computes y with `crypto_kzg_evaluate`.
- Computes q_i = (p_i - y) / (d_i - z), with one batch inversion, or `crypto_kzg_quotient_in_domain` where d_i = z.
- Writes the sum of q_i times Lagrange point i of `settings`, with `crypto_kzg_g1_lincomb`.

### Function never

- Writes more than `work`, `proof` and `y` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_proof_impl`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `settings`, `poly`, `z`, `work`, `proof`, `y`.

## Function `crypto_kzg_verify_impl`

Writes 1 when e(C - [y], -[1]) e(proof, [s] - [z]) = 1, else 0 (`verifyKzgProofWith`).

### Signature

```
crypto_kzg_verify_impl(s, area, valid) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `s` | input | [`G2Point`](bls12-381.md#type-g2point): [s] |
| `area` | state | 5864 bytes: C and the proof (`G1Point`), z and y (`FrElement`), then the work |
| `valid` | output | [`Valid`](secp256k1.md#type-valid) |

### Caller must

- Keep `area` and `valid` apart from each other and from `s`.

### Function does

- Reads C at 0, the proof at 144, z at 288 and y at 320.
- Builds the pairs (C + (-y) G, -H) and (proof, s + (-z) H), with G and H the generators of G1 and G2, and runs `crypto_bls_pairing_check`.

### Function never

- Writes more than `area` and `valid` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_verify_impl`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `s`, `area`, `valid`.

## Type `KzgSettings`

The decoded trusted setup (`TrustedSetup`).

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `g1_lagrange_brp` | 4096 [`G1Point`](bls12-381.md#type-g1point) | The Lagrange points, in bit-reversed order |
| 589824 | `g1_monomial` | 4096 [`G1Point`](bls12-381.md#type-g1point) | The monomial points [s^i] |
| 1179648 | `g2_monomial` | 65 [`G2Point`](bls12-381.md#type-g2point) | The monomial points [s^i] of G2 |

### Rules

- 1198368 bytes, at a multiple of 8.
- Only `crypto_kzg_trusted_setup_of_bytes` writes it. It holds no pointer, so it can be copied as one block.

## Type `Blob`

The values of a polynomial at the 4096-th roots of unity, in bit-reversed order.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 32i | `value[i]` | `KzgFieldElement` | p(omega_i) |

### Rules

- 131072 bytes, at a multiple of 8.
- Valid when each value is below r.

## Type `KzgFieldElement`

An element of Fr as 32 bytes (`Bytes32`, `bytesToBlsField`, `blsFieldToBytes`).

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `value` | 32 bytes | A big-endian number |

### Rules

- Valid when the number is below r.
- A buffer of its own starts at a multiple of 8.

## Type `KzgCommitment`

A commitment, a compressed point of G1 (`KZGCommitment`).

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `point` | 48 bytes | A [`G1Compressed`](bls12-381.md#type-g1compressed) |

### Rules

- Valid when it is 0xC0 followed by 47 zero bytes, the point at infinity, or passes [`crypto_bls_key_validate`](bls-signatures.md#function-crypto_bls_key_validate) (`validateKzgG1Point`).
- A buffer of its own starts at a multiple of 8.

## Type `KzgProof`

A proof, a compressed point of G1 (`KZGProof`).

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `point` | 48 bytes | A [`G1Compressed`](bls12-381.md#type-g1compressed) |

### Rules

- Valid under the rule of `KzgCommitment`.
- A buffer of its own starts at a multiple of 8.

## Type `BlobList`

A list of blobs.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `offset` | u64 | Offset of the first blob from the buffer start |
| 16 | `count` | u64 | Number of blobs |

### Rules

- The buffer starts at a multiple of 8.
- `offset` is at least 24 and a multiple of 8.
- The blobs follow each other from `offset`, 131072 bytes each.
- `offset` + 131072 * `count` is at most `size`.

## Type `KzgCommitmentList`

A list of commitments.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `offset` | u64 | Offset of the first commitment from the buffer start |
| 16 | `count` | u64 | Number of commitments |

### Rules

- The buffer starts at a multiple of 8.
- `offset` is at least 24 and a multiple of 8.
- The commitments follow each other from `offset`, 48 bytes each.
- `offset` + 48 * `count` is at most `size`.

## Type `KzgProofList`

A list of proofs.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `offset` | u64 | Offset of the first proof from the buffer start |
| 16 | `count` | u64 | Number of proofs |

### Rules

- The rules of `KzgCommitmentList`, with proofs.

## Type `KzgScratch`

The workspace of a KZG function.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `work` | bytes | Written and read by the function |

### Rules

- The buffer starts at a multiple of 8.
- `size` is at least `CRYPTO_KZG_SCRATCH`, plus `CRYPTO_KZG_SCRATCH_PER_ENTRY` times the entries each function names.

## Type `FrElement`

An element of Fr, in Montgomery form.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 8i | `limb[i]` | u64 | Bits 64i to 64i + 63 of a * 2^256 mod r, for the element a |

### Rules

- 32 bytes, at a multiple of 8.
- The number is below r.

## Constant `CRYPTO_KZG_SCRATCH`

- Value: 2097152.
- The fixed part of the `size` of a `KzgScratch`.

## Constant `CRYPTO_KZG_SCRATCH_PER_ENTRY`

- Value: 8192.
- The part of the `size` of a `KzgScratch` for each entry.

## Constant `CRYPTO_KZG_INVALID_COMMITMENT`

- Value: 13.
- A commitment breaks the rule of `KzgCommitment`.

## Constant `CRYPTO_KZG_INVALID_PROOF`

- Value: 14.
- A proof breaks the rule of `KzgProof`.

## Constant `CRYPTO_KZG_LENGTH_MISMATCH`

- Value: 15.
- Input lists that must have one length do not.

## Constant `CRYPTO_KZG_INVALID_TRUSTED_SETUP`

- Value: 21.
- A list of the trusted setup has the wrong length, or one of its points does not decompress.

## Test vectors

- cryptography-specs v0.3.0, `tests/cryptography/kzg`: the handlers `blob_to_kzg_commitment`, `compute_kzg_proof`, `verify_kzg_proof`, `compute_blob_kzg_proof`, `verify_blob_kzg_proof`, `verify_blob_kzg_proof_batch` and `compute_challenge`
  - File: `tests/cryptography/kzg/SHA256SUMS` at commit `bb6dfe55198243682bc2eaf94611af2dbce1be6f`, SHA-256 `11341d6864faaeec2302c12b1ac5bb215c7757b5fbd6e6e2eb69ff496b19bc71`, which pins each case file.
  - A case whose inputs have the wrong number of bytes is left out: the types here have fixed sizes.
- The trusted setup of every case: `EthLib/Cryptography/Kzg/TrustedSetupData.lean` at the same commit, SHA-256 `ea834a0ed4af25acb32e47a9852a445fd0522b5943bdcbdb8bde8f3fea67b7a5`.
- Generated cases
  - `crypto_kzg_trusted_setup_of_bytes` with each list one point short or long, and with a point that does not decompress in each list.
  - Expected results: `TrustedSetup.ofBytes`, written out in [tests/generator/kzg.py](../../tests/generator/kzg.py).

## Results

<!-- CI generates the tick table for each function here. -->

### `crypto_kzg_trusted_setup_of_bytes`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_blob_to_kzg_commitment`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_compute_kzg_proof`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_verify_kzg_proof`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_compute_blob_kzg_proof`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_verify_blob_kzg_proof`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_verify_blob_kzg_proof_batch`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_compute_challenge`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_fr_mul`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_fr_add`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_fr_sub`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_fr_neg`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_fr_pow`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_fr_inverse`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_fr_from_bytes`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_fr_from_digest`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_fr_from_u64`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_fr_canonical`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_fr_to_bytes`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_roots_of_unity`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_bit_reversal`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_batch_inverse`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_blob_to_poly`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_validate_g1`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_challenge`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_g1_lincomb`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_domain`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_evaluate`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_quotient_in_domain`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_proof_impl`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_verify_impl`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |
