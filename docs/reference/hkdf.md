# HKDF-SHA-256

## Contents

### Functions

- [`crypto_hkdf_extract`](#function-crypto_hkdf_extract): makes a pseudorandom key from a salt and input key material.
- [`crypto_hkdf_expand`](#function-crypto_hkdf_expand): expands a pseudorandom key into output key material.

### Types

- [`HkdfScratch`](#type-hkdfscratch): the workspace for the inner hashes.
- [`Length`](#type-length): the number of output bytes.

### Constants

- [`CRYPTO_HKDF_LENGTH`](#constant-crypto_hkdf_length): the status for a length above 8160.
- [`CRYPTO_HKDF_EXPAND_SCRATCH`](#constant-crypto_hkdf_expand_scratch): the fixed part of the expand scratch size.

## Spec

- Document: [RFC 5869](https://www.rfc-editor.org/rfc/rfc5869), May 2010, with Hash = SHA-256 and HashLen = 32.
- Section: 2.2 (HKDF-Extract) and 2.3 (HKDF-Expand).

## Function `crypto_hkdf_extract`

Computes PRK = HMAC-SHA-256(salt, IKM).

### Signature

```
crypto_hkdf_extract(salt, ikm, scratch, prk) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `salt` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `ikm` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `scratch` | scratch | [`HmacScratch`](hmac.md#type-hmacscratch) |
| `prk` | output | [`Mac`](hmac.md#type-mac) |

### Returns

- `CRYPTO_OK`: `prk` holds the result.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than 96 + `count` of `ikm` bytes. Nothing is written.

### Caller must

- Follow the rules of `crypto_hmac_sha256`, with `salt` as the key and `ikm` as the message.

### Function does

- Calls `crypto_hmac_sha256(salt, ikm, scratch, prk)`.
- Treats an empty salt as RFC 5869 says: HMAC pads it to 64 zero bytes, the same K0 as 32 zero bytes.

### Function never

- Writes more than `scratch`, `prk` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 848 bytes on x86-64 (return address included), 816 bytes on ARM64, 912 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_hkdf_extract` (`_crypto_hkdf_extract` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `salt`, `ikm`, `scratch`, `prk`.

## Function `crypto_hkdf_expand`

Computes OKM, the first `length` bytes of T(1) || T(2) || ..., with T(i) = HMAC-SHA-256(PRK, T(i - 1) || info || i) and T(0) empty.

### Signature

```
crypto_hkdf_expand(prk, info, length, scratch, okm) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `prk` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `info` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `length` | input | `Length` |
| `scratch` | scratch | `HkdfScratch` |
| `okm` | output | [`ByteList`](sha-256.md#type-bytelist) |

### Returns

- `CRYPTO_OK`: `okm` holds `length` bytes.
- `CRYPTO_HKDF_LENGTH`: `length` is above 255 * 32 = 8160. Nothing is written.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than 129 + `count` of `info` bytes, or `okm` fewer than 24 + `length` bytes. Nothing is written.

### Caller must

- Pass valid `ByteList` values in `prk` and `info`. They are not checked.
- Set the `size` field of `scratch` and of `okm` to their buffer sizes.
- Keep `scratch` and `okm` apart from each other and from the inputs.

### Function does

- Checks `length`, then `scratch`, then `okm`.
- Uses any length of `prk` as the HMAC key. RFC 5869 asks for at least 32 bytes.
- Copies `info` into `scratch` once, then builds each inner hash input around it.
- Sets `offset` of `okm` to 24 and `count` to `length`.
- Keeps the `size` field of `okm`.

### Function never

- Reads more than the two `ByteList` headers, their `count` bytes, `length` and the `size` fields.
- Writes more than `scratch`, `okm` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.
- Branches or picks an address based on key bytes. Lengths may decide branches.

### Effects

- `scratch` holds key material after the call.

### Limits

- Stack: 864 bytes on x86-64 (return address included), 832 bytes on ARM64, 928 bytes on RISC-V, callees included.
- HMAC blocks: `ceil(length / 32)`, each 2 SHA-256 calls.

### ABI

- Role: L2.
- Symbol: `crypto_hkdf_expand` (`_crypto_hkdf_expand` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `prk`, `info`, `length`, `scratch`, `okm`.

## Type `HkdfScratch`

The workspace for the inner hash inputs of `crypto_hkdf_expand`.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `inner` | `ByteList` | The inner hash input, written by the function |
| 128 | `info` | bytes | The info bytes, then the byte i |

### Rules

- The buffer starts at a multiple of 8.
- `size` is at least 129 + `count` of `info`.

## Type `Length`

The number of output bytes.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `length` | u64 | Output bytes L of RFC 5869 |

### Rules

- 8 bytes, at a multiple of 8.

## Constant `CRYPTO_HKDF_LENGTH`

- Value: 2.
- Status of `crypto_hkdf_expand` when `length` is above 8160.

## Constant `CRYPTO_HKDF_EXPAND_SCRATCH`

- Value: 129.
- The scratch size of `crypto_hkdf_expand` is this plus the info bytes: 8 for `size`, 24 for the inner header, 64 for K0 ^ ipad, 32 for T(i - 1), 1 for i.

## Test vectors

- Wycheproof HKDF-SHA-256
  - File: [`hkdf_sha256_test.json`](https://github.com/C2SP/wycheproof/blob/65ca494727a52944c204441c860b039e6786b99b/testvectors_v1/hkdf_sha256_test.json), SHA-256 `bb2b462a38b251cb52a2aede706d6d4b62b26864f4e80c95497507ddb07c5f1e`.
  - The invalid cases are the lengths above 8160.
- Generated cases
  - Lengths 0, 1, 16, 31, 32, 33, 64, 100, 8160 and 8161, with info of 0, 1, 50 and 200 bytes.
  - Expected results: `cryptography` 50.0.2 (OpenSSL), pinned with hashes in [tests/generator/requirements.txt](../../tests/generator/requirements.txt).
- devp2p discv5 key derivation
  - File: [`discv5-wire-test-vectors.md`](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/discv5/discv5-wire-test-vectors.md), SHA-256 `dbcb81f70bc963cad2d5b28fd7ef99e0c4b4ce4d03497f7c75d63ef752115170`.
  - The initiator and recipient keys from the ECDH secret, the challenge data and the two node IDs.

## Results

<!-- CI generates the tick table for each function here. -->
