# AES-128-GCM

## Contents

### Functions

- [`crypto_aes128_gcm_ae`](#function-crypto_aes128_gcm_ae): encrypts and authenticates.
- [`crypto_aes128_gcm_ad`](#function-crypto_aes128_gcm_ad): checks and decrypts.
- [`crypto_aes128_ghash`](#function-crypto_aes128_ghash): runs GHASH over bytes.

### Types

- [`GcmIv`](#type-gcmiv): a 12-byte IV.
- [`GhashBlock`](#type-ghashblock): a 16-byte GHASH value.

### Constants

- [`CRYPTO_GCM_FAIL`](#constant-crypto_gcm_fail): the status for a tag that does not match.

## Spec

- Document: [NIST SP 800-38D](https://doi.org/10.6028/NIST.SP.800-38D), November 2007, with the cipher of [aes.md](aes.md).
- Section: 7.1 (GCM-AE) and 7.2 (GCM-AD), with a 96-bit IV and a 128-bit tag; 6.4 (GHASH) and 6.3 (multiplication, algorithm 1).
- The ciphertext and the tag travel together as one byte string, C || T, as in discv5.

## Function `crypto_aes128_gcm_ae`

Writes C || T for a plaintext P and additional data A.

### Signature

```
crypto_aes128_gcm_ae(key, iv, plaintext, aad, sealed) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `key` | input | [`Aes128Key`](aes.md#type-aes128key) |
| `iv` | input | `GcmIv` |
| `plaintext` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `aad` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `sealed` | output | [`ByteList`](sha-256.md#type-bytelist) |

### Returns

- `CRYPTO_OK`: `sealed` holds C || T.
- `CRYPTO_BUFFER_TOO_SMALL`: `sealed` holds fewer than 24 + `count` of `plaintext` + 16 bytes. Nothing is written.

### Caller must

- Pass valid `ByteList` values in `plaintext` and `aad`. They are not checked.
- Set the `size` field of `sealed` to its buffer size.
- Keep `sealed` apart from the inputs.
- Use each IV with a key once.

### Function does

- Checks `sealed` first.
- Computes H = E(0^128) and E(J0), with J0 = IV || 0^31 || 1.
- Encrypts with the counter blocks inc32(J0), inc32(inc32(J0)), ...
- Computes S = GHASH(A || 0^v || C || 0^u || [len(A)]64 || [len(C)]64), and T = E(J0) ^ S.
- Sets `offset` of `sealed` to 24 and `count` to `count` of `plaintext` + 16.
- Keeps the `size` field of `sealed`.

### Function never

- Reads more than the two `ByteList` headers and their `count` bytes, `key`, `iv` and the `size` field of `sealed`.
- Writes more than `sealed` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.
- Branches or picks an address based on key or data bytes.

### Limits

- Stack: 1544 bytes on x86-64 (return address included), 1536 bytes on ARM64, 1600 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_aes128_gcm_ae` (`_crypto_aes128_gcm_ae` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `key`, `iv`, `plaintext`, `aad`, `sealed`.

## Function `crypto_aes128_gcm_ad`

Checks the tag of C || T and writes the plaintext P.

### Signature

```
crypto_aes128_gcm_ad(key, iv, sealed, aad, plaintext) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `key` | input | [`Aes128Key`](aes.md#type-aes128key) |
| `iv` | input | `GcmIv` |
| `sealed` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `aad` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `plaintext` | output | [`ByteList`](sha-256.md#type-bytelist) |

### Returns

- `CRYPTO_OK`: the tag matches, and `plaintext` holds P.
- `CRYPTO_GCM_FAIL`: `sealed` has fewer than 16 bytes, or the tag does not match. Nothing is written.
- `CRYPTO_BUFFER_TOO_SMALL`: `plaintext` holds fewer than 24 + `count` of `sealed` - 16 bytes. Nothing is written.

### Caller must

- Pass valid `ByteList` values in `sealed` and `aad`. They are not checked.
- Set the `size` field of `plaintext` to its buffer size.
- Keep `plaintext` apart from the inputs.

### Function does

- Checks the length of `sealed`, then `plaintext`.
- Computes the tag of the ciphertext and compares all 16 bytes before it decrypts.
- Sets `offset` of `plaintext` to 24 and `count` to `count` of `sealed` - 16.
- Keeps the `size` field of `plaintext`.

### Function never

- Writes plaintext when the tag does not match.
- Reads more than the two `ByteList` headers and their `count` bytes, `key`, `iv` and the `size` field of `plaintext`.
- Writes more than `plaintext` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.
- Branches or picks an address based on key or data bytes. Only the result of the whole tag comparison decides a branch.

### Limits

- Stack: 1544 bytes on x86-64 (return address included), 1536 bytes on ARM64, 1600 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_aes128_gcm_ad` (`_crypto_aes128_gcm_ad` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `key`, `iv`, `sealed`, `aad`, `plaintext`.

## Function `crypto_aes128_ghash`

Updates Y = (Y ^ X) * H in GF(2^128) for each 16-byte block X of the bytes.

### Signature

```
crypto_aes128_ghash(y, h, data, count) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `y` | state | `GhashBlock` |
| `h` | input | `GhashBlock` |
| `data` | input | `count` bytes |
| `count` | input | u64 by value |

### Caller must

- Keep `y` apart from `h` and `data`.

### Function does

- Pads the last block with zeros when `count` is not a multiple of 16.
- Multiplies by algorithm 1 of SP 800-38D: 128 steps, each with a mask in place of the branch, and R = 0xe1 || 0^120.

### Function never

- Writes more than `y` and its own stack.
- Branches or picks an address based on H, Y or data bytes.
- Makes an OS call.

### Limits

- Stack of its own: 80 bytes on x86-64 (return address included), 16 bytes on ARM64, 32 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_aes128_ghash`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `y`, `h`, `data`, `count`.

## Type `GcmIv`

A 12-byte IV.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `iv` | 12 bytes | The IV bytes |

### Rules

- The buffer starts at a multiple of 8.

## Type `GhashBlock`

A GHASH value or the hash key H.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `block` | 16 bytes | A 128-bit big-endian number; bit 0 of SP 800-38D is its top bit |

### Rules

- The buffer starts at a multiple of 8.

## Constant `CRYPTO_GCM_FAIL`

- Value: 3.
- Status of `crypto_aes128_gcm_ad` when the tag does not match, or `sealed` is shorter than a tag.

## Test vectors

- NIST CAVP GCM, the 128-bit keys with a 96-bit IV and a 128-bit tag, from `gcmEncryptExtIV128.rsp` and `gcmDecrypt128.rsp`
  - File: [`gcmtestvectors.zip`](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/mac/gcmtestvectors.zip), SHA-256 `f9fc479e134cde2980b3bb7cddbcb567b2cd96fd753835243ed067699f26a023`.
  - The decrypt cases marked FAIL must give `CRYPTO_GCM_FAIL`.
- Wycheproof AES-GCM, the 128-bit keys with a 96-bit IV and a 128-bit tag
  - File: [`aes_gcm_test.json`](https://github.com/C2SP/wycheproof/blob/65ca494727a52944c204441c860b039e6786b99b/testvectors_v1/aes_gcm_test.json), SHA-256 `985e5ecc172e181eaf49e89508b9470dcf478002eb7e8559c707eb42dc97dfe7`.
- Generated cases
  - Plaintexts of 0 to 49 bytes, and 63, 64, 65, 255, 256, 1000 and 1280 bytes, with 0, 1, 16, 17, 32 and 70 bytes of AAD.
  - Each case again with one bit flipped, which must give `CRYPTO_GCM_FAIL`, and a 15-byte `sealed`.
  - Expected results: `cryptography` 50.0.2 (OpenSSL), pinned with hashes in [tests/generator/requirements.txt](../../tests/generator/requirements.txt).
- devp2p discv5 message encryption
  - File: [`discv5-wire-test-vectors.md`](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/discv5/discv5-wire-test-vectors.md), SHA-256 `dbcb81f70bc963cad2d5b28fd7ef99e0c4b4ce4d03497f7c75d63ef752115170`.

## Results

<!-- CI generates the tick table for each function here. -->
