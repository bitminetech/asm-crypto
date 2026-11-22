# KZG cells

## Contents

### Functions

- [`crypto_kzg_compute_cells`](#function-crypto_kzg_compute_cells): extends a blob and cuts it into cells.
- [`crypto_kzg_compute_cells_and_kzg_proofs`](#function-crypto_kzg_compute_cells_and_kzg_proofs): extends a blob, and proves each cell.
- [`crypto_kzg_verify_cell_kzg_proof_batch`](#function-crypto_kzg_verify_cell_kzg_proof_batch): checks cells against their commitments.
- [`crypto_kzg_recover_cells_and_kzg_proofs`](#function-crypto_kzg_recover_cells_and_kzg_proofs): recovers all cells and proofs from half of the cells.
- [`crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge`](#function-crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge): computes the challenge of the cell check.
- [`crypto_kzg_fft`](#function-crypto_kzg_fft): computes an FFT over Fr.
- [`crypto_kzg_shift_vals`](#function-crypto_kzg_shift_vals): multiplies values by the powers of a factor.
- [`crypto_kzg_coset_fft`](#function-crypto_kzg_coset_fft): computes an FFT over a coset.
- [`crypto_kzg_eval_to_coeff`](#function-crypto_kzg_eval_to_coeff): converts a blob polynomial to coefficients.
- [`crypto_kzg_extended_cells`](#function-crypto_kzg_extended_cells): writes the cells of a polynomial.
- [`crypto_kzg_g1_fft`](#function-crypto_kzg_g1_fft): computes an FFT over G1.
- [`crypto_kzg_fk20`](#function-crypto_kzg_fk20): computes the cells and proofs of a polynomial.
- [`crypto_kzg_cell_challenge`](#function-crypto_kzg_cell_challenge): computes the challenge of the cell check.
- [`crypto_kzg_check_cell_indices`](#function-crypto_kzg_check_cell_indices): checks cell indices.
- [`crypto_kzg_interpolate`](#function-crypto_kzg_interpolate): interpolates the values of a cell.

### Types

- [`Cell`](#type-cell): 64 values of an extended blob.
- [`Cells`](#type-cells): the 128 cells of an extended blob.
- [`CellProofs`](#type-cellproofs): the 128 proofs of an extended blob.
- [`CellList`](#type-celllist): a list of cells.
- [`CellIndexList`](#type-cellindexlist): a list of cell indices.
- [`CommitmentIndexList`](#type-commitmentindexlist): a list of commitment indices.
- [`CellChallengeRequest`](#type-cellchallengerequest): the inputs of the cell challenge.

### Constants

- [`CRYPTO_KZG_CELL_INDEX`](#constant-crypto_kzg_cell_index): a cell index is 128 or more.
- [`CRYPTO_KZG_COMMITMENT_INDEX`](#constant-crypto_kzg_commitment_index): a commitment index names no commitment.
- [`CRYPTO_KZG_INDICES_NOT_ASCENDING`](#constant-crypto_kzg_indices_not_ascending): cell indices are not strictly ascending.
- [`CRYPTO_KZG_NOT_ENOUGH_CELLS`](#constant-crypto_kzg_not_enough_cells): fewer than 64 cells.
- [`CRYPTO_KZG_TOO_MANY_CELLS`](#constant-crypto_kzg_too_many_cells): more than 128 cells.

## Spec

- Document: [cryptography-specs v0.3.0](https://github.com/ethereum/cryptography-specs/tree/bb6dfe55198243682bc2eaf94611af2dbce1be6f/EthLib/Cryptography/Kzg), commit `bb6dfe55198243682bc2eaf94611af2dbce1be6f`.
- Files: `Cells.lean` and `Recovery.lean`, with `Fft.lean` and `Polynomials.lean`, and `Exports/Kzg.lean` (`computeVerifyCellKzgProofBatchChallengeExport`).
- EIP-7594 adds these functions at the Fusaka fork. The blob functions, the trusted setup and the types they share are in [kzg.md](kzg.md).
- The extended blob holds the values of the polynomial p of a blob at the 8192-th roots of unity, in bit-reversed order. Cell i holds values 64 i to 64 i + 63: the values on the coset h_i G, with G the subgroup of order 64 and h_i entry 64 i of the bit-reversed domain.
- The proof of cell i is [q_i(s)], with q_i the quotient of p by X^64 - h_i^64.

## Function `crypto_kzg_compute_cells`

Extends a blob and writes its 128 cells (`computeCells`).

### Signature

```
crypto_kzg_compute_cells(blob, scratch, cells) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `blob` | input | [`Blob`](kzg.md#type-blob) |
| `scratch` | scratch | [`KzgScratch`](kzg.md#type-kzgscratch) |
| `cells` | output | `Cells` |

### Returns

- `CRYPTO_OK`: `cells` holds the cells.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_KZG_SCRATCH` bytes. Nothing is written.
- `CRYPTO_INVALID_ENCODING`: a field element of the blob is r or more. Nothing is written.

### Caller must

- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch` and `cells` apart from each other and from `blob`.

### Function does

- Checks `scratch` first, then the blob.
- Takes the coefficients of p by an inverse FFT of the bit-reversed values (`polynomialEvalToCoeff`).
- Pads them with zeros to 8192, takes the FFT over the 8192-th roots of unity, and puts the values in bit-reversed order (`extendedEvaluations`).
- Writes cell i as values 64 i to 64 i + 63, 32 big-endian bytes each (`cellsOfExtendedEvaluations`).

### Function never

- Reads more than `blob` and the `size` field of `scratch`.
- Writes more than `scratch`, `cells` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 480 bytes on x86-64 (return address included), 576 bytes on ARM64, 736 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_kzg_compute_cells` (`_crypto_kzg_compute_cells` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `blob`, `scratch`, `cells`.

## Function `crypto_kzg_compute_cells_and_kzg_proofs`

Extends a blob, and writes its 128 cells and the proof of each cell (`computeCellsAndKzgProofs`).

### Signature

```
crypto_kzg_compute_cells_and_kzg_proofs(settings, blob, scratch, cells, proofs) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `settings` | input | [`KzgSettings`](kzg.md#type-kzgsettings) |
| `blob` | input | [`Blob`](kzg.md#type-blob) |
| `scratch` | scratch | [`KzgScratch`](kzg.md#type-kzgscratch) |
| `cells` | output | `Cells` |
| `proofs` | output | `CellProofs` |

### Returns

- `CRYPTO_OK`: `cells` and `proofs` hold the cells and the proofs.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_KZG_SCRATCH` bytes. Nothing is written.
- `CRYPTO_INVALID_ENCODING`: a field element of the blob is r or more. Nothing is written.

### Caller must

- Pass a `settings` that `crypto_kzg_trusted_setup_of_bytes` wrote.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch`, `cells` and `proofs` apart from each other and from the inputs.

### Function does

- Checks `scratch` first, then the blob.
- Writes the cells of `crypto_kzg_compute_cells`.
- Computes H_d = sum_i f_(i + 64 d) [s^i] for d = 1 to 63, with f the 4096 coefficients of p and [s^i] the monomial points of `settings`, each by the steps of `G1.msm`.
- Takes the FFT in G1 of H_1, ..., H_63, padded with the point at infinity to 128, over the 128-th roots of unity (`fftG1`), and writes the results in bit-reversed order, compressed (`computeCellsAndKzgProofsPolynomialcoeff`, the method of FK20).

### Function never

- Reads more than `settings`, `blob` and the `size` field of `scratch`.
- Writes more than `scratch`, `cells`, `proofs` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 1616 bytes on x86-64 (return address included), 1712 bytes on ARM64, 1840 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_kzg_compute_cells_and_kzg_proofs` (`_crypto_kzg_compute_cells_and_kzg_proofs` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `settings`, `blob`, `scratch`, `cells`, `proofs`.

## Function `crypto_kzg_verify_cell_kzg_proof_batch`

Checks that cells belong to their commitments (`verifyCellKzgProofBatch`).

### Signature

```
crypto_kzg_verify_cell_kzg_proof_batch(settings, commitments, cell_indices, cells, proofs, scratch, valid) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `settings` | input | [`KzgSettings`](kzg.md#type-kzgsettings) |
| `commitments` | input | [`KzgCommitmentList`](kzg.md#type-kzgcommitmentlist) |
| `cell_indices` | input | `CellIndexList` |
| `cells` | input | `CellList` |
| `proofs` | input | [`KzgProofList`](kzg.md#type-kzgprooflist) |
| `scratch` | scratch | [`KzgScratch`](kzg.md#type-kzgscratch) |
| `valid` | output | [`Valid`](secp256k1.md#type-valid) |

### Returns

- `CRYPTO_OK`: `valid` holds 1 or 0.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_KZG_SCRATCH` + `CRYPTO_KZG_SCRATCH_PER_ENTRY` * n bytes, with n the `count` of `commitments`. Nothing is written.
- `CRYPTO_KZG_LENGTH_MISMATCH`: the `count` of `cells`, of `proofs` or of `cell_indices` differs from n. Nothing is written.
- `CRYPTO_KZG_CELL_INDEX`: a cell index is 128 or more. Nothing is written.
- [`CRYPTO_KZG_INVALID_COMMITMENT`](kzg.md#constant-crypto_kzg_invalid_commitment), `CRYPTO_INVALID_ENCODING` or [`CRYPTO_KZG_INVALID_PROOF`](kzg.md#constant-crypto_kzg_invalid_proof): the first commitment, cell or proof that fails its check, in that order. Nothing is written.

### Caller must

- Pass a `settings` that `crypto_kzg_trusted_setup_of_bytes` wrote.
- Pass valid lists. They are not checked.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch` and `valid` apart from each other and from the inputs.

### Function does

- Checks `scratch` first, then the counts, then the cell indices.
- Checks each commitment in order, and keeps the first of equal commitments, with the index of each cell's commitment among the kept ones.
- Checks the field elements of each cell in order, then each proof in order.
- Computes r, the challenge of `crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge` on the kept commitments.
- Writes 1 when e(LL, [s^64]) e(RL, -[1]) = 1, else 0, with LL = sum_k r^k proof_k and RL = sum_i w_i C_i - [sum_k r^k I_k(s)] + sum_k r^k h_k^64 proof_k (`verifyCellKzgProofBatchImpl`): w_i is the sum of r^k over the cells k of commitment i, I_k the polynomial of degree below 64 with the values of cell k on its coset (`interpolateCosetEvals`), and [s^64] and [1] G2 points 64 and 0 of `settings`.
- An empty batch gives 1.

### Function never

- Reads more than `settings`, the list headers and their entries, and the `size` field of `scratch`.
- Writes more than `scratch`, `valid` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 2736 bytes on x86-64 (return address included), 2992 bytes on ARM64, 3088 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_kzg_verify_cell_kzg_proof_batch` (`_crypto_kzg_verify_cell_kzg_proof_batch` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). On x86-64, `valid`, the seventh argument, is on the stack.
- Argument order: `settings`, `commitments`, `cell_indices`, `cells`, `proofs`, `scratch`, `valid`.

## Function `crypto_kzg_recover_cells_and_kzg_proofs`

Recovers all cells and proofs of an extended blob from at least half of its cells (`recoverCellsAndKzgProofs`).

### Signature

```
crypto_kzg_recover_cells_and_kzg_proofs(settings, cell_indices, cells, scratch, recovered_cells, recovered_proofs) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `settings` | input | [`KzgSettings`](kzg.md#type-kzgsettings) |
| `cell_indices` | input | `CellIndexList` |
| `cells` | input | `CellList` |
| `scratch` | scratch | [`KzgScratch`](kzg.md#type-kzgscratch) |
| `recovered_cells` | output | `Cells` |
| `recovered_proofs` | output | `CellProofs` |

### Returns

- `CRYPTO_OK`: `recovered_cells` and `recovered_proofs` hold all the cells and proofs.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_KZG_SCRATCH` bytes. Nothing is written.
- `CRYPTO_KZG_LENGTH_MISMATCH`: the `count` of `cells` differs from the `count` of `cell_indices`. Nothing is written.
- `CRYPTO_KZG_NOT_ENOUGH_CELLS`: fewer than 64 cells. Nothing is written.
- `CRYPTO_KZG_TOO_MANY_CELLS`: more than 128 cells. Nothing is written.
- `CRYPTO_KZG_CELL_INDEX`: a cell index is 128 or more. Nothing is written.
- `CRYPTO_KZG_INDICES_NOT_ASCENDING`: the cell indices are not strictly ascending. Nothing is written.
- `CRYPTO_INVALID_ENCODING`: a field element of a cell is r or more. Nothing is written.

### Caller must

- Pass a `settings` that `crypto_kzg_trusted_setup_of_bytes` wrote.
- Pass valid lists. They are not checked.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch`, `recovered_cells` and `recovered_proofs` apart from each other and from the inputs.

### Function does

- Checks `scratch` first, then the rules in the order of the Returns list.
- Puts the values of the cells in their places of the extended blob, with zeros for the missing cells, and in natural order: E.
- Builds Z, the polynomial that vanishes on the points of the missing cells: the short vanishing polynomial on their bit-reversed 128-th roots of unity, with coefficient i moved to 64 i (`constructVanishingPolynomial`).
- Takes P Z as the inverse FFT of the products of E and the FFT of Z, then P as the quotient of the coset FFTs of P Z and of Z, with shift 7, by one batch inversion and an inverse coset FFT (`recoverPolynomialcoeff`).
- Writes the cells and proofs of the first 4096 coefficients of P, as `crypto_kzg_compute_cells_and_kzg_proofs` does.

### Function never

- Reads more than `settings`, the list headers and their entries, and the `size` field of `scratch`.
- Writes more than `scratch`, `recovered_cells`, `recovered_proofs` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 1648 bytes on x86-64 (return address included), 1712 bytes on ARM64, 1856 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_kzg_recover_cells_and_kzg_proofs` (`_crypto_kzg_recover_cells_and_kzg_proofs` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `settings`, `cell_indices`, `cells`, `scratch`, `recovered_cells`, `recovered_proofs`.

## Function `crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge`

Computes the challenge r of the cell check (`computeVerifyCellKzgProofBatchChallenge`, `computeVerifyCellKzgProofBatchChallengeExport`).

### Signature

```
crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge(commitments, commitment_indices, cell_indices, cells, proofs, scratch, challenge) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `commitments` | input | [`KzgCommitmentList`](kzg.md#type-kzgcommitmentlist) |
| `commitment_indices` | input | `CommitmentIndexList` |
| `cell_indices` | input | `CellIndexList` |
| `cells` | input | `CellList` |
| `proofs` | input | [`KzgProofList`](kzg.md#type-kzgprooflist) |
| `scratch` | scratch | [`KzgScratch`](kzg.md#type-kzgscratch) |
| `challenge` | output | [`KzgFieldElement`](kzg.md#type-kzgfieldelement) |

### Returns

- `CRYPTO_OK`: `challenge` holds r.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_KZG_SCRATCH` + `CRYPTO_KZG_SCRATCH_PER_ENTRY` * (m + n) bytes, with m the `count` of `commitments` and n the `count` of `commitment_indices`. Nothing is written.
- `CRYPTO_KZG_LENGTH_MISMATCH`: the `count` of `cell_indices`, of `cells` or of `proofs` differs from n. Nothing is written.
- [`CRYPTO_KZG_INVALID_COMMITMENT`](kzg.md#constant-crypto_kzg_invalid_commitment): a commitment breaks its rule. Nothing is written.
- `CRYPTO_KZG_COMMITMENT_INDEX`: a commitment index is m or more. Nothing is written.
- `CRYPTO_KZG_CELL_INDEX`: a cell index is 128 or more. Nothing is written.
- [`CRYPTO_KZG_INVALID_PROOF`](kzg.md#constant-crypto_kzg_invalid_proof): a proof breaks its rule. Nothing is written.
- `CRYPTO_INVALID_ENCODING`: a field element of a cell is r or more. Nothing is written.

### Caller must

- Pass valid lists. They are not checked.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch` and `challenge` apart from each other and from the inputs.

### Function does

- Checks `scratch` first, then the rules in the order of the Returns list, as `computeVerifyCellKzgProofBatchChallengeExport` does.
- Computes SHA-256 of "RCKZGCBATCH__V1_" || I2OSP(4096, 8) || I2OSP(64, 8) || I2OSP(m, 8) || I2OSP(n, 8) || the commitments || for each cell k: I2OSP(commitment index, 8) || I2OSP(cell index, 8) || its 64 values || proof_k, takes it as a big-endian number mod r, and writes it as 32 big-endian bytes.

### Function never

- Reads more than the list headers and their entries, and the `size` field of `scratch`.
- Writes more than `scratch`, `challenge` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 1968 bytes on x86-64 (return address included), 2112 bytes on ARM64, 2256 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge` (`_crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). On x86-64, `challenge`, the seventh argument, is on the stack.
- Argument order: `commitments`, `commitment_indices`, `cell_indices`, `cells`, `proofs`, `scratch`, `challenge`.

## Function `crypto_kzg_fft`

Computes the FFT of n values, in place (`fftField`).

### Signature

```
crypto_kzg_fft(vals, n, roots, inverse) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `vals` | state | n [`FrElement`](kzg.md#type-frelement) values |
| `n` | input | u64 in a register: a power of two from 2 up |
| `roots` | input | n [`FrElement`](kzg.md#type-frelement) values: the n-th roots of unity |
| `inverse` | input | u64 in a register: 1 for the inverse FFT, else 0 |

### Caller must

- Keep `vals` apart from `roots`.

### Function does

- Puts the values in bit-reversed order, then runs the stages of `fftStages`: in each block of 2 h values, pair r < h becomes (x + t, x - t) with t the second value times root m r, m = n / (2 h).
- For the inverse FFT, uses root (n - i) mod n for root i, then divides each value by n.

### Function never

- Writes more than `vals` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 112 bytes on x86-64 (return address included), 128 bytes on ARM64, 144 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_fft`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `vals`, `n`, `roots`, `inverse`.

## Function `crypto_kzg_shift_vals`

Multiplies value i by factor^i, in place (`shiftVals`).

### Signature

```
crypto_kzg_shift_vals(vals, n, factor) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `vals` | state | n [`FrElement`](kzg.md#type-frelement) values |
| `n` | input | u64 in a register |
| `factor` | input | [`FrElement`](kzg.md#type-frelement) |

### Caller must

- Keep `factor` out of `vals`.

### Function does

- Starts from 1, and multiplies the power by the factor after each value.

### Function never

- Writes more than `vals` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 96 bytes on x86-64 (return address included), 128 bytes on ARM64, 144 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_shift_vals`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `vals`, `n`, `factor`.

## Function `crypto_kzg_coset_fft`

Computes the FFT over the coset 7 G, in place (`cosetFftField`).

### Signature

```
crypto_kzg_coset_fft(vals, n, roots, inverse) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `vals` | state | n [`FrElement`](kzg.md#type-frelement) values |
| `n` | input | u64 in a register |
| `roots` | input | n [`FrElement`](kzg.md#type-frelement) values: the n-th roots of unity |
| `inverse` | input | u64 in a register: 1 for the inverse, else 0 |

### Caller must

- Keep `vals` apart from `roots`.

### Function does

- Forward: `crypto_kzg_shift_vals` by 7, then `crypto_kzg_fft`.
- Inverse: the inverse `crypto_kzg_fft`, then `crypto_kzg_shift_vals` by 1 / 7.

### Function never

- Writes more than `vals` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 96 bytes on x86-64 (return address included), 128 bytes on ARM64, 144 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_coset_fft`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `vals`, `n`, `roots`, `inverse`.

## Function `crypto_kzg_eval_to_coeff`

Computes the 4096 coefficients of the polynomial of 4096 values, in place (`polynomialEvalToCoeff`).

### Signature

```
crypto_kzg_eval_to_coeff(poly, roots) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `poly` | state | 4096 [`FrElement`](kzg.md#type-frelement) values |
| `roots` | output | 4096 [`FrElement`](kzg.md#type-frelement) values: the 4096-th roots of unity |

### Caller must

- Keep `roots` apart from `poly`.

### Function does

- Writes the roots with `crypto_kzg_roots_of_unity`, puts the values in bit-reversed order, and runs the inverse `crypto_kzg_fft`.

### Function never

- Writes more than `poly` and `roots` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_eval_to_coeff`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `poly`, `roots`.

## Function `crypto_kzg_extended_cells`

Writes the 128 cells of 4096 coefficients (`cellsOfExtendedEvaluations` of `extendedEvaluations`).

### Signature

```
crypto_kzg_extended_cells(cells, coeff, work) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `cells` | output | `Cells` |
| `coeff` | input | 4096 [`FrElement`](kzg.md#type-frelement) values |
| `work` | scratch | 524288 bytes |

### Caller must

- Keep `cells`, `coeff` and `work` apart from each other.

### Function does

- Pads the coefficients with zeros to 8192, runs `crypto_kzg_fft` over the 8192-th roots of unity, puts the values in bit-reversed order, and writes each with `crypto_kzg_fr_to_bytes`.

### Function never

- Writes more than `cells` and `work` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_extended_cells`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `cells`, `coeff`, `work`.

## Function `crypto_kzg_g1_fft`

Computes the FFT in G1 of n points, in place (`fftG1`).

### Signature

```
crypto_kzg_g1_fft(vals, n, roots, work) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `vals` | state | n [`G1Point`](bls12-381.md#type-g1point) values |
| `n` | input | u64 in a register: a power of two from 2 up |
| `roots` | input | n [`FrElement`](kzg.md#type-frelement) values: the n-th roots of unity |
| `work` | scratch | 320 bytes |

### Caller must

- Keep `vals`, `roots` and `work` apart from each other.

### Function does

- Runs the butterflies of `fftG1Vector` in the order of `fftFieldIter`: puts the points in bit-reversed order, then pair (l, x) becomes (l + t, l - t), with t = x times its root, by `crypto_bls_g1_mul`.

### Function never

- Writes more than `vals` and `work` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 80 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_g1_fft`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `vals`, `n`, `roots`, `work`.

## Function `crypto_kzg_fk20`

Computes the cells and the proofs of 4096 coefficients (`computeCellsAndKzgProofsPolynomialcoeff`).

### Signature

```
crypto_kzg_fk20(settings, coeff, work, cells, proofs) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `settings` | input | [`KzgSettings`](kzg.md#type-kzgsettings) |
| `coeff` | input | 4096 [`FrElement`](kzg.md#type-frelement) values |
| `work` | scratch | 720896 bytes |
| `cells` | output | `Cells` |
| `proofs` | output | `CellProofs` |

### Caller must

- Keep `work`, `cells` and `proofs` apart from each other and from the inputs.

### Function does

- Writes the cells with `crypto_kzg_extended_cells`.
- Computes H_d = the sum of coeff[i + 64 d] [s^i] for d = 1 to 63, with `crypto_kzg_g1_lincomb` on the monomial points of `settings`.
- Pads the H_d to 128 with the point at infinity, runs `crypto_kzg_g1_fft` over the 128-th roots of unity, puts the points in bit-reversed order, and writes each with `crypto_bls_g1_compress`.

### Function never

- Writes more than `work`, `cells` and `proofs` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_fk20`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `settings`, `coeff`, `work`, `cells`, `proofs`.

## Function `crypto_kzg_cell_challenge`

Computes r, the Fiat-Shamir challenge of the cell check (`computeVerifyCellKzgProofBatchChallenge`).

### Signature

```
crypto_kzg_cell_challenge(result, request, work) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | [`FrElement`](kzg.md#type-frelement) |
| `request` | input | `CellChallengeRequest` |
| `work` | scratch | 104 + 48 m + 2112 n bytes |

### Caller must

- Pass cells that hold canonical values.
- Keep `work` apart from the other arguments and from the values the request names.

### Function does

- Writes the data of `crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge` in `work` as a `ByteList`, hashes it with `crypto_sha256`, and reads the digest with `crypto_kzg_fr_from_digest`.
- Copies the bytes of the cells: they hold canonical values, so they are those of `blsFieldToBytes`.

### Function never

- Writes more than `result` and `work` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_cell_challenge`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `request`, `work`.

## Function `crypto_kzg_check_cell_indices`

Checks that each of n cell indices is below 128.

### Signature

```
crypto_kzg_check_cell_indices(indices, n) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `indices` | input | n u64 values |
| `n` | input | u64 in a register |

### Returns

- `CRYPTO_OK`: each index is below 128.
- `CRYPTO_KZG_CELL_INDEX`: an index is 128 or more.

### Function does

- Reads the indices in order.

### Function never

- Writes anything.
- Makes an OS call.

### Limits

- Stack of its own: 8 bytes on x86-64, its return address, and none on ARM64 and RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_check_cell_indices`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `indices`, `n`.

## Function `crypto_kzg_interpolate`

Computes the 64 coefficients of the polynomial with the values of a cell on its coset (`interpolateCosetEvals`).

### Signature

```
crypto_kzg_interpolate(interp, shift, evals, work) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `interp` | output | 64 [`FrElement`](kzg.md#type-frelement) values |
| `shift` | input | [`FrElement`](kzg.md#type-frelement): the coset shift |
| `evals` | input | 64 [`FrElement`](kzg.md#type-frelement) values |
| `work` | scratch | 2080 bytes |

### Caller must

- Keep `interp`, `evals` and `work` apart from each other and from `shift`.

### Function does

- Copies the values, puts them in bit-reversed order, runs the inverse `crypto_kzg_fft` over the 64-th roots of unity, then `crypto_kzg_shift_vals` by 1 / shift.

### Function never

- Writes more than `interp` and `work` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_kzg_interpolate`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `interp`, `shift`, `evals`, `work`.

## Type `Cell`

The 64 values of one cell of an extended blob (`Cell`).

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 32j | `value[j]` | [`KzgFieldElement`](kzg.md#type-kzgfieldelement) | Value j of the cell |

### Rules

- 2048 bytes.
- Valid when each value is below r.

## Type `Cells`

The 128 cells of an extended blob.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 2048i | `cell[i]` | `Cell` | Cell i |

### Rules

- 262144 bytes, at a multiple of 8.

## Type `CellProofs`

The proofs of the 128 cells of an extended blob.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 48i | `proof[i]` | [`KzgProof`](kzg.md#type-kzgproof) | The proof of cell i |

### Rules

- 6144 bytes, at a multiple of 8.

## Type `CellList`

A list of cells.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `offset` | u64 | Offset of the first cell from the buffer start |
| 16 | `count` | u64 | Number of cells |

### Rules

- The buffer starts at a multiple of 8.
- `offset` is at least 24 and a multiple of 8.
- The cells follow each other from `offset`, 2048 bytes each.
- `offset` + 2048 * `count` is at most `size`.

## Type `CellIndexList`

A list of cell indices (`CellIndex`).

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `offset` | u64 | Offset of the first index from the buffer start |
| 16 | `count` | u64 | Number of indices |

### Rules

- The buffer starts at a multiple of 8.
- `offset` is at least 24 and a multiple of 8.
- The indices follow each other from `offset`, each a u64.
- `offset` + 8 * `count` is at most `size`.

## Type `CommitmentIndexList`

A list of commitment indices (`CommitmentIndex`).

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `offset` | u64 | Offset of the first index from the buffer start |
| 16 | `count` | u64 | Number of indices |

### Rules

- The rules of `CellIndexList`.

## Type `CellChallengeRequest`

The inputs of `crypto_kzg_cell_challenge`, by address.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `m` | u64 | The number of commitments |
| 8 | `commitments` | u64 | The address of m addresses, each of a `KzgCommitment` |
| 16 | `n` | u64 | The number of cells |
| 24 | `commitment_indices` | u64 | The address of n u64 values |
| 32 | `cell_indices` | u64 | The address of n u64 values |
| 40 | `cells` | u64 | The address of n `Cell` values |
| 48 | `proofs` | u64 | The address of n `KzgProof` values |

### Rules

- 56 bytes, at a multiple of 8, in the scratch of the function that builds it.
- It holds addresses, so it is not a portable value: it lives only during one call inside this library.

## Constant `CRYPTO_KZG_CELL_INDEX`

- Value: 16.
- A cell index is 128 or more.

## Constant `CRYPTO_KZG_COMMITMENT_INDEX`

- Value: 17.
- A commitment index is the number of commitments or more.

## Constant `CRYPTO_KZG_INDICES_NOT_ASCENDING`

- Value: 18.
- The cell indices are not strictly ascending.

## Constant `CRYPTO_KZG_NOT_ENOUGH_CELLS`

- Value: 19.
- Fewer than 64 cells, half of an extended blob.

## Constant `CRYPTO_KZG_TOO_MANY_CELLS`

- Value: 20.
- More than 128 cells.

## Test vectors

- cryptography-specs v0.3.0, `tests/cryptography/kzg`: the handlers `compute_cells`, `compute_cells_and_kzg_proofs`, `verify_cell_kzg_proof_batch`, `recover_cells_and_kzg_proofs` and `compute_verify_cell_kzg_proof_batch_challenge`
  - File: `tests/cryptography/kzg/SHA256SUMS` at commit `bb6dfe55198243682bc2eaf94611af2dbce1be6f`, SHA-256 `11341d6864faaeec2302c12b1ac5bb215c7757b5fbd6e6e2eb69ff496b19bc71`, which pins each case file.
  - A case whose inputs have the wrong number of bytes is left out: the types here have fixed sizes.
  - The trusted setup is the one of [kzg.md](kzg.md#test-vectors).

## Results

<!-- CI generates the tick table for each function here. -->

### `crypto_kzg_compute_cells`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_compute_cells_and_kzg_proofs`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_verify_cell_kzg_proof_batch`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_recover_cells_and_kzg_proofs`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_fft`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_shift_vals`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_coset_fft`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_eval_to_coeff`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_extended_cells`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_g1_fft`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_fk20`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_cell_challenge`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_check_cell_indices`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_kzg_interpolate`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |
