# AES-128

## Contents

### Functions

- [`crypto_aes128_expand`](#function-crypto_aes128_expand): expands a key into the round keys.
- [`crypto_aes128_encrypt4`](#function-crypto_aes128_encrypt4): encrypts 4 blocks.
- [`crypto_aes128_bitslice`](#function-crypto_aes128_bitslice): turns 64 bytes into bit planes, or back.
- [`crypto_aes128_sbox`](#function-crypto_aes128_sbox): SubBytes on bit planes.
- [`crypto_aes128_mix`](#function-crypto_aes128_mix): ShiftRows, MixColumns and AddRoundKey on bit planes.

### Types

- [`Aes128Key`](#type-aes128key): a 16-byte key.
- [`Planes`](#type-planes): 64 bytes as 8 bit planes.
- [`Schedule`](#type-schedule): the 11 round keys as planes.

## Spec

- Document: [FIPS 197](https://doi.org/10.6028/NIST.FIPS.197-upd1), updated May 2023.
- Section: 5.1 (Cipher), 5.2 (KeyExpansion), with Nk = 4 and Nr = 10.

## Function `crypto_aes128_expand`

Expands a key with KeyExpansion and writes the 11 round keys as planes.

### Signature

```
crypto_aes128_expand(key, schedule) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `key` | input | `Aes128Key` |
| `schedule` | output | `Schedule` |

### Caller must

- Keep `schedule` apart from `key`.

### Function does

- Computes w[0] to w[43] of FIPS 197 section 5.2, with SubWord through `crypto_aes128_sbox`.
- Repeats each round key 4 times and turns the 64 bytes into planes with `crypto_aes128_bitslice`.

### Function never

- Writes more than `schedule` and its own stack.
- Branches or picks an address based on key bytes.
- Makes an OS call.

### Limits

- Stack of its own: 304 bytes on x86-64 (return address included), 336 bytes on ARM64, 352 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_aes128_expand`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `key`, `schedule`.

## Function `crypto_aes128_encrypt4`

Encrypts 4 blocks of 16 bytes with the Cipher of FIPS 197 section 5.1, in place.

### Signature

```
crypto_aes128_encrypt4(schedule, blocks) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `schedule` | input | `Schedule` |
| `blocks` | state | 64 bytes |

### Caller must

- Keep `blocks` apart from `schedule`.

### Function does

- Turns the blocks into planes, adds round key 0, then runs 9 rounds of SubBytes, ShiftRows, MixColumns and AddRoundKey, and a last round without MixColumns.
- Turns the planes back into bytes.

### Function never

- Writes more than `blocks` and its own stack.
- Branches or picks an address based on key or block bytes.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_aes128_encrypt4`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `schedule`, `blocks`.

## Function `crypto_aes128_bitslice`

Turns 64 bytes into 8 bit planes in place, or the planes back into bytes.

### Signature

```
crypto_aes128_bitslice(blocks, inverse) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `blocks` | state | 64 bytes, or `Planes` |
| `inverse` | input | u64 by value: 0 for bytes to planes, 1 for planes to bytes |

### Function does

- Forward: transposes the 8 x 8 bit matrix in each 8-byte word, then the 8 x 8 byte matrix across the 8 words.
- Inverse: the same two steps in the other order.

### Function never

- Writes more than `blocks` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 40 bytes on x86-64 (return address included), none on ARM64, 16 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_aes128_bitslice`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `blocks`, `inverse`.

## Function `crypto_aes128_sbox`

Applies SubBytes to the 64 bytes in `Planes`, in place.

### Signature

```
crypto_aes128_sbox(planes) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `planes` | state | `Planes` |

### Function does

- Computes the inverse in GF(2^8) as x^254, with the polynomial x^8 + x^4 + x^3 + x + 1: x^2, x^3, x^6, x^12, x^15, x^30, x^60, x^120, x^240, x^252, x^254.
- Multiplies by shifting and masking the planes, and squares with a fixed linear map.
- Applies the affine map of FIPS 197 section 5.1.1 with c = 0x63. Byte 0 maps to 0x63.

### Function never

- Uses a table lookup.
- Writes more than `planes` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 360 bytes on x86-64 (return address included), 288 bytes on ARM64, 320 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_aes128_sbox`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `planes`.

## Function `crypto_aes128_mix`

Applies ShiftRows, then MixColumns when asked, then AddRoundKey, to the 64 bytes in `Planes`, in place.

### Signature

```
crypto_aes128_mix(planes, round_key, columns) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `planes` | state | `Planes` |
| `round_key` | input | `Planes`, one round key of a `Schedule` |
| `columns` | input | u64 by value: 1 for MixColumns, 0 for the last round |

### Function does

- ShiftRows: moves row r of each block 4r bits down in its 16-bit lane, wrapping inside the lane.
- MixColumns: with u = rot1(a) and t = a ^ u, writes xtime(t) ^ u ^ rot2(t), where rotk takes row r + k of the same column to row r.
- AddRoundKey: XORs `round_key`.

### Function never

- Writes more than `planes` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 80 bytes on x86-64 (return address included), 64 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_aes128_mix`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `planes`, `round_key`, `columns`.

## Type `Aes128Key`

A 16-byte AES-128 key.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `key` | 16 bytes | The key bytes in FIPS 197 order |

### Rules

- The buffer starts at a multiple of 8.

## Type `Planes`

4 blocks of 16 bytes as 8 bit planes.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 8i | `plane[i]` | u64 | Bit i of every byte: byte g = 16 * block + k at bit g |

### Rules

- 64 bytes, at a multiple of 8.
- k = r + 4c is the FIPS 197 state byte of row r and column c.

## Type `Schedule`

The 11 round keys of FIPS 197 section 5.2, each repeated 4 times, as `Planes`.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 64r | `round[r]` | `Planes` | Round key r, for r from 0 to 10 |

### Rules

- 704 bytes, at a multiple of 8. `CRYPTO_AES128_SCHEDULE_SIZE` in [include/aes.inc](../../include/aes.inc).
- It holds key material. It lives on the stack of the calling function.

## Test vectors

- NIST CAVP AES known answers: `ECBGFSbox128.rsp`, `ECBKeySbox128.rsp`, `ECBVarKey128.rsp` and `ECBVarTxt128.rsp`, encrypt cases
  - File: [`KAT_AES.zip`](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/aes/KAT_AES.zip), SHA-256 `a203b16c9246b2ebae31dee5de21a606be80cf78ceabaca37150236fa098eb60`.
  - Run through `crypto_aes128_ctr` with the plaintext as the counter block and 16 zero bytes as input, so the output is the ciphertext.
- The CTR and GCM vectors in [ctr.md](ctr.md) and [gcm.md](gcm.md).

## Results

<!-- CI generates the tick table for each function here. -->

### `crypto_aes128_expand`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_aes128_encrypt4`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_aes128_bitslice`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_aes128_sbox`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_aes128_mix`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |
