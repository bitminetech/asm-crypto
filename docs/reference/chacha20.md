# ChaCha20

## Contents

### Functions

- [`crypto_chacha20_block`](#function-crypto_chacha20_block): computes one 64-byte key stream block.
- [`crypto_chacha20_xor`](#function-crypto_chacha20_xor): XORs the key stream into bytes.

### Types

- [`ChaCha20Key`](#type-chacha20key): a 32-byte key.
- [`ChaCha20Nonce`](#type-chacha20nonce): a 12-byte nonce.
- [`ChaCha20Block`](#type-chacha20block): one 64-byte key stream block.

## Spec

- Document: [RFC 8439](https://www.rfc-editor.org/rfc/rfc8439), June 2018.
- Section: 2.1 (the quarter round), 2.3 (the block function), 2.4 (the encryption algorithm), with a 32-bit block counter and a 96-bit nonce.

## Function `crypto_chacha20_block`

Computes the ChaCha20 block function for a key, a block counter and a nonce.

### Signature

```
crypto_chacha20_block(key, counter, nonce, block) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `key` | input | `ChaCha20Key` |
| `counter` | input | u32 in a register |
| `nonce` | input | `ChaCha20Nonce` |
| `block` | output | `ChaCha20Block` |

### Caller must

- Keep `block` apart from `key` and `nonce`.

### Function does

- Builds the state: the 4 constant words of "expand 32-byte k", the 8 key words, the counter and the 3 nonce words, each word little endian.
- Runs 10 double rounds: 4 column quarter rounds, then 4 diagonal quarter rounds.
- Adds the input state to the result and writes the 16 words little endian.

### Function never

- Branches or picks an address based on key, counter or nonce.
- Writes more than `block` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 8 bytes on x86-64, its return address, 32 bytes on ARM64, 96 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_chacha20_block`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `key`, `counter`, `nonce`, `block`.

## Function `crypto_chacha20_xor`

XORs the key stream from a block counter on into count bytes, as the RFC 8439 encryption algorithm does.

### Signature

```
crypto_chacha20_xor(key, nonce, counter, source, target, count) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `key` | input | `ChaCha20Key` |
| `nonce` | input | `ChaCha20Nonce` |
| `counter` | input | u32 in a register, the first block counter |
| `source` | input | `count` bytes |
| `target` | output | `count` bytes |
| `count` | input | u64 in a register |

### Caller must

- Keep `target` apart from the inputs.
- Start `source` and `target` at multiples of 8.
- Keep the block counters below 2^32: at most (2^32 - `counter`) * 64 bytes.

### Function does

- Uses block counter `counter` for bytes 0 to 63, `counter` + 1 for bytes 64 to 127, and so on.
- Writes `source` XOR the key stream to `target`.
- Uses only the first `count` mod 64 bytes of the last block.

### Function never

- Branches or picks an address based on key, nonce or data bytes.
- Writes more than `target` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 128 bytes on x86-64 (return address included), 160 bytes on ARM64, 176 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_chacha20_xor`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `key`, `nonce`, `counter`, `source`, `target`, `count`.

## Type `ChaCha20Key`

A 32-byte ChaCha20 key.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `key` | 32 bytes | The key bytes in RFC 8439 order |

### Rules

- The buffer starts at a multiple of 8.

## Type `ChaCha20Nonce`

A 12-byte nonce.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `nonce` | 12 bytes | The nonce bytes in RFC 8439 order |

### Rules

- The buffer starts at a multiple of 8.
- Noise uses 4 zero bytes, then the 8-byte little-endian message counter.

## Type `ChaCha20Block`

One block of key stream.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 4i | `word[i]` | u32 | State word i after the rounds and the final addition |

### Rules

- 64 bytes, at a multiple of 8.

## Test vectors

- The ChaCha20-Poly1305 vectors in [chacha20-poly1305.md](chacha20-poly1305.md): each one checks the key stream through the ciphertext and the Poly1305 key.

## Results

<!-- CI generates the tick table for each function here. -->
