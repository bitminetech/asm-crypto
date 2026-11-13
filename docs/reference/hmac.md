# HMAC-SHA-256

## Contents

### Functions

- [`crypto_hmac_sha256`](#function-crypto_hmac_sha256): computes the HMAC-SHA-256 of a message.
- [`crypto_hmac_key`](#function-crypto_hmac_key): turns a key into the 64-byte K0.
- [`crypto_hmac_finish`](#function-crypto_hmac_finish): computes the inner and outer hashes.

### Types

- [`HmacScratch`](#type-hmacscratch): the workspace for the inner hash.
- [`Mac`](#type-mac): an HMAC-SHA-256 result.

### Constants

- [`CRYPTO_HMAC_SCRATCH`](#constant-crypto_hmac_scratch): the fixed part of the scratch size.

## Spec

- Document: [RFC 2104](https://www.rfc-editor.org/rfc/rfc2104), February 1997, with H = SHA-256 ([FIPS 180-4](https://doi.org/10.6028/NIST.FIPS.180-4)).
- Section: 2.
- The key rules follow [FIPS 198-1](https://doi.org/10.6028/NIST.FIPS.198-1) section 4: K0 is the key, or the hash of a key longer than 64 bytes, then zeros to 64 bytes.

## Function `crypto_hmac_sha256`

Computes H((K0 ^ opad) || H((K0 ^ ipad) || message)) with H = SHA-256.

### Signature

```
crypto_hmac_sha256(key, message, scratch, mac) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `key` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `message` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `scratch` | scratch | `HmacScratch` |
| `mac` | output | `Mac` |

### Returns

- `CRYPTO_OK`: `mac` holds the result.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than 96 + `count` of `message` bytes. Nothing is written.

### Caller must

- Pass valid `ByteList` values in `key` and `message`. They are not checked.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch` and `mac` apart from each other and from the inputs.

### Function does

- Checks `scratch` first.
- Hashes a key longer than 64 bytes with `crypto_sha256`.
- Puts K0 ^ 0x36 and the message bytes in `scratch`, and hashes them with `crypto_sha256`.
- Hashes K0 ^ 0x5c and the inner hash with `crypto_sha256`, on its own stack, into `mac`.

### Function never

- Reads more than the two `ByteList` headers and their `count` bytes, and the `size` field of `scratch`.
- Writes more than `scratch`, `mac` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.
- Branches or picks an address based on key or message bytes. Key and message lengths may decide branches.

### Effects

- `scratch` holds key material after the call.

### Limits

- Stack: 832 bytes on x86-64 (return address included), 800 bytes on ARM64, 896 bytes on RISC-V, `crypto_sha256` included.
- SHA-256 calls: 2, and 1 more for a key longer than 64 bytes.

### ABI

- Role: L2.
- Symbol: `crypto_hmac_sha256` (`_crypto_hmac_sha256` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `key`, `message`, `scratch`, `mac`.

## Function `crypto_hmac_key`

Writes K0 for a key: the key bytes, or the SHA-256 of a key longer than 64 bytes, then zeros to 64 bytes.

### Signature

```
crypto_hmac_key(key, k0) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `key` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `k0` | output | 64 bytes |

### Caller must

- Pass a valid `ByteList` in `key`.
- Pass 64 bytes in `k0`, apart from `key`.

### Function does

- Writes zeros to the 64 bytes of `k0`, then the key bytes or the key hash over them.

### Function never

- Writes more than `k0` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_hmac_key`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `key`, `k0`.

## Function `crypto_hmac_finish`

Hashes the inner list, then K0 ^ opad and the inner hash, into the result.

### Signature

```
crypto_hmac_finish(inner, k0, mac) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `inner` | input | [`ByteList`](sha-256.md#type-bytelist) that holds K0 ^ ipad and the message |
| `k0` | input | 64 bytes |
| `mac` | output | `Mac` |

### Caller must

- Pass a valid `ByteList` in `inner`.
- Keep `mac` apart from `inner` and `k0`.

### Function does

- Hashes `inner` with `crypto_sha256`.
- Builds K0 ^ 0x5c and the inner hash, 96 bytes, as a `ByteList` on its stack, and hashes it into `mac`.

### Function never

- Writes more than `mac` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 192 bytes on x86-64 (return address included), 224 bytes on ARM64, 240 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_hmac_finish`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `inner`, `k0`, `mac`.

## Type `HmacScratch`

The workspace for the inner hash input.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `inner` | `ByteList` | The inner hash input, written by the function |

### Rules

- The buffer starts at a multiple of 8.
- `crypto_hmac_sha256` needs `size` of at least 96 + `count` of `message`.

## Type `Mac`

An HMAC-SHA-256 result.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `mac` | 32 bytes | The outer SHA-256 digest |

### Rules

- 32 bytes.
- The buffer starts at a multiple of 8.

## Constant `CRYPTO_HMAC_SCRATCH`

- Value: 96.
- The scratch size of `crypto_hmac_sha256` is this plus the message bytes: 8 for `size`, 24 for the inner header, 64 for K0 ^ ipad.

## Test vectors

- Wycheproof HMAC-SHA-256, the valid cases
  - File: [`hmac_sha256_test.json`](https://github.com/C2SP/wycheproof/blob/65ca494727a52944c204441c860b039e6786b99b/testvectors_v1/hmac_sha256_test.json), SHA-256 `2d201cfa61d1bf95e6f5d07d96634b4a348b31e8eaa277ad7c8d09677b7a743f`.
  - Expected results: the reference below, which must give a MAC that starts with each Wycheproof tag.
- Generated keys and messages
  - Keys of 0, 1, 31, 32, 33, 63, 64, 65, 100, 131 and 200 bytes, with messages of 0 to 1000 bytes.
  - Expected results: `cryptography` 50.0.2 (OpenSSL), pinned with hashes in [tests/generator/requirements.txt](../../tests/generator/requirements.txt).

## Results

<!-- CI generates the tick table for each function here. -->

### `crypto_hmac_sha256`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_hmac_key`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_hmac_finish`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |
