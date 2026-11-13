# AES-128-CTR

## Contents

### Functions

- [`crypto_aes128_ctr`](#function-crypto_aes128_ctr): encrypts or decrypts bytes with AES-128 in CTR mode.
- [`crypto_aes128_ctr_xor`](#function-crypto_aes128_ctr_xor): XORs the key stream of a counter into bytes.

### Types

- [`CounterBlock`](#type-counterblock): the first counter block.

## Spec

- Document: [NIST SP 800-38A](https://doi.org/10.6028/NIST.SP.800-38A), December 2001, with the cipher of [aes.md](aes.md).
- Section: 6.5 (CTR mode), with the incrementing function of appendix B.1 on all 128 bits.
- discv5 masks packet headers with `aesctr_encrypt(masking-key, masking-iv, header)` ([discv5-wire.md](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/discv5/discv5-wire.md)).

## Function `crypto_aes128_ctr`

Writes input XOR E(T1) || E(T2) || ... to the output, with T1 the counter block and T(j + 1) = T(j) + 1 mod 2^128.

### Signature

```
crypto_aes128_ctr(key, counter, input, output) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `key` | input | [`Aes128Key`](aes.md#type-aes128key) |
| `counter` | input | `CounterBlock` |
| `input` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `output` | output | [`ByteList`](sha-256.md#type-bytelist) |

### Returns

- `CRYPTO_OK`: `output` holds the result.
- `CRYPTO_BUFFER_TOO_SMALL`: `output` holds fewer than 24 + `count` of `input` bytes. Nothing is written.

### Caller must

- Pass a valid `ByteList` in `input`. It is not checked.
- Set the `size` field of `output` to its buffer size.
- Keep `output` apart from the inputs.

### Function does

- Checks `output` first.
- Expands the key with `crypto_aes128_expand`, on its own stack.
- Uses the last block in part when `count` is not a multiple of 16.
- Sets `offset` of `output` to 24 and `count` to the input `count`.
- Keeps the `size` field of `output`.
- Decrypts too: the same call on the ciphertext gives the plaintext.

### Function never

- Reads more than the `input` header and its `count` bytes, `key`, `counter` and the `size` field of `output`.
- Writes more than `output` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.
- Branches or picks an address based on key or data bytes.

### Limits

- Stack: 1432 bytes on x86-64 (return address included), 1424 bytes on ARM64, 1488 bytes on RISC-V, callees included.
- Cipher calls: `ceil(count / 64)` runs of 4 blocks, and the key expansion.

### ABI

- Role: L2.
- Symbol: `crypto_aes128_ctr` (`_crypto_aes128_ctr` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `key`, `counter`, `input`, `output`.

## Function `crypto_aes128_ctr_xor`

XORs `count` bytes of key stream into `target` from `source`, 4 counter blocks at a time.

### Signature

```
crypto_aes128_ctr_xor(schedule, counter, source, target, count, mode) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `schedule` | input | [`Schedule`](aes.md#type-schedule) |
| `counter` | input | `CounterBlock` |
| `source` | input | `count` bytes at a multiple of 8 |
| `target` | output | `count` bytes at a multiple of 8 |
| `count` | input | u64 by value |
| `mode` | input | u64 by value: 0 adds 1 to all 128 bits, 1 adds 1 to the last 32 bits only (inc32 of SP 800-38D) |

### Caller must

- Keep `target` apart from the inputs.

### Function does

- Encrypts the counter blocks with `crypto_aes128_encrypt4` and XORs them into `target`.

### Function never

- Writes more than `target` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 128 bytes on x86-64 (return address included), 160 bytes on ARM64, 176 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_aes128_ctr_xor`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `schedule`, `counter`, `source`, `target`, `count`, `mode`.

## Type `CounterBlock`

The first counter block T1.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `counter` | 16 bytes | A 128-bit big-endian number |

### Rules

- The buffer starts at a multiple of 8.

## Test vectors

- The AES known answers in [aes.md](aes.md).
- Generated cases
  - Inputs of 0 to 69 bytes, and 127, 128, 129, 255, 256, 1000 and 4096 bytes.
  - Counters that carry out of the low 32 bits, the low 64 bits and all 128 bits.
  - Expected results: `cryptography` 50.0.2 (OpenSSL), pinned with hashes in [tests/generator/requirements.txt](../../tests/generator/requirements.txt).

## Results

<!-- CI generates the tick table for each function here. -->

### `crypto_aes128_ctr`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_aes128_ctr_xor`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |
