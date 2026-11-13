# Keccak-256

## Contents

### Functions

- [`crypto_keccak256`](#function-crypto_keccak256): hashes a byte string with Keccak-256.

### Types

- [`KeccakDigest`](#type-keccakdigest): a Keccak-256 result.

## Spec

- Document: [FIPS 202](https://doi.org/10.6028/NIST.FIPS.202), August 2015.
- Section: 5.2, `KECCAK[c]` with c = 512 and d = 256, on the message itself.
- Keccak-256 is the hash that Ethereum calls `keccak256`. It is not SHA3-256, which hashes the message with 2 more bits.

## Function `crypto_keccak256`

Hashes the bytes in a `ByteList` with Keccak-256 and writes the result to a `KeccakDigest`.

### Signature

```
crypto_keccak256(message, digest) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `message` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `digest` | output | `KeccakDigest` |

### Returns

- `CRYPTO_OK`, always.

### Caller must

- Pass a valid `ByteList` in `message`. It is not checked.
- Keep `message` and `digest` apart. They must not overlap.

### Function does

- Absorbs the `count` bytes that start at `offset` in blocks of 136 bytes, with Keccak-f[1600] after each block.
- Pads the last block with pad10*1: the byte 0x01 after the message, zeros, and 0x80 in the last byte of the block.
- Writes the first 32 bytes of the state to `digest`.

### Function never

- Reads more than the `ByteList` header and its `count` bytes.
- Writes more than `digest` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.
- Branches or picks an address based on message bytes.

### Limits

- Stack: 496 bytes on x86-64 (return address included), 400 bytes on ARM64, 432 bytes on RISC-V.
- Permutations: `floor(count / 136) + 1`.

### ABI

- Role: L2.
- Symbol: `crypto_keccak256` (`_crypto_keccak256` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `message`, `digest`.

## Type `KeccakDigest`

A Keccak-256 result.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `z` | 32 bytes | The first 32 bytes of the state, lanes 0 to 3, each lane little endian |

### Rules

- 32 bytes.
- The buffer starts at a multiple of 8.

## Test vectors

- Generated messages
  - Every length from 0 to 599 bytes, and 1087, 1088, 1089, 4096, 65536 and 100000 bytes; all zeros and all 0xff at 0, 135, 136 and 137 bytes.
  - Expected results: `Keccak(1088, 512, message, 0x01, 32)` of the Keccak team's `CompactFIPS202.py` at [XKCP@d20c8fc](https://github.com/XKCP/XKCP/blob/d20c8fcaecc543f816a0721d0dfc13b4cf27c14d/Standalone/CompactFIPS202/Python/CompactFIPS202.py), SHA-256 `0b731097a4dfcf33fdaf395ac0bee81c6a6ebff2975590c35ad8cd8d6f3c204f`.
- devp2p ENR example
  - File: [`enr.md`](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/enr.md), SHA-256 `29260bceb96e289140dc08c1336e1f26e070613664a7ec6db72fffbfb85cc58d`.
  - The node ID, the hash of the 64-byte public key, and the hash of the record content that the signature covers.

## Results

<!-- CI generates the tick table for each function here. -->

### `crypto_keccak256`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |
