# ChaCha20-Poly1305

## Contents

### Functions

- [`crypto_chacha20_aead_encrypt`](#function-crypto_chacha20_aead_encrypt): encrypts and authenticates.
- [`crypto_chacha20_aead_decrypt`](#function-crypto_chacha20_aead_decrypt): checks and decrypts.

### Constants

- [`CRYPTO_CHACHA20_POLY1305_FAIL`](#constant-crypto_chacha20_poly1305_fail): the status for a tag that does not match.

## Spec

- Document: [RFC 8439](https://www.rfc-editor.org/rfc/rfc8439), June 2018, with the block function of [chacha20.md](chacha20.md) and the MAC of [poly1305.md](poly1305.md).
- Section: 2.6 (the Poly1305 key from block 0), 2.8 (AEAD_CHACHA20_POLY1305), with a 96-bit nonce and a 128-bit tag.
- The ciphertext and the tag travel together as one byte string, C || T, as libp2p's Noise (`Noise_XX_25519_ChaChaPoly_SHA256`) carries them.

## Function `crypto_chacha20_aead_encrypt`

Writes C || T for a plaintext P and additional data A.

### Signature

```
crypto_chacha20_aead_encrypt(key, nonce, plaintext, aad, sealed) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `key` | input | [`ChaCha20Key`](chacha20.md#type-chacha20key) |
| `nonce` | input | [`ChaCha20Nonce`](chacha20.md#type-chacha20nonce) |
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
- Pass at most 274877906880 bytes of plaintext: (2^32 - 1) blocks of 64 bytes.
- Use each nonce with a key once.

### Function does

- Checks `sealed` first.
- Takes the Poly1305 key from the first 32 bytes of block 0 of the key stream.
- Encrypts with the key stream from block 1 on.
- Computes T = Poly1305 of A || pad16(A) || C || pad16(C) || le64(len(A)) || le64(len(C)).
- Sets `offset` of `sealed` to 24 and `count` to `count` of `plaintext` + 16.
- Keeps the `size` field of `sealed`.

### Function never

- Reads more than the two `ByteList` headers and their `count` bytes, `key`, `nonce` and the `size` field of `sealed`.
- Writes more than `sealed` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.
- Branches or picks an address based on key or data bytes.

### Limits

- Stack: 360 bytes on x86-64 (return address included), 448 bytes on ARM64, 544 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_chacha20_aead_encrypt` (`_crypto_chacha20_aead_encrypt` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `key`, `nonce`, `plaintext`, `aad`, `sealed`.

## Function `crypto_chacha20_aead_decrypt`

Checks the tag of C || T and writes the plaintext P.

### Signature

```
crypto_chacha20_aead_decrypt(key, nonce, sealed, aad, plaintext) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `key` | input | [`ChaCha20Key`](chacha20.md#type-chacha20key) |
| `nonce` | input | [`ChaCha20Nonce`](chacha20.md#type-chacha20nonce) |
| `sealed` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `aad` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `plaintext` | output | [`ByteList`](sha-256.md#type-bytelist) |

### Returns

- `CRYPTO_OK`: the tag matches, and `plaintext` holds P.
- `CRYPTO_CHACHA20_POLY1305_FAIL`: `sealed` has fewer than 16 bytes, or the tag does not match. Nothing is written.
- `CRYPTO_BUFFER_TOO_SMALL`: `plaintext` holds fewer than 24 + `count` of `sealed` - 16 bytes. Nothing is written.

### Caller must

- Pass valid `ByteList` values in `sealed` and `aad`. They are not checked.
- Set the `size` field of `plaintext` to its buffer size.
- Keep `plaintext` apart from the inputs.
- Pass at most 274877906880 bytes of ciphertext before the tag.

### Function does

- Checks the length of `sealed`, then `plaintext`.
- Computes the tag of the ciphertext and compares all 16 bytes before it decrypts.
- Sets `offset` of `plaintext` to 24 and `count` to `count` of `sealed` - 16.
- Keeps the `size` field of `plaintext`.

### Function never

- Writes plaintext when the tag does not match.
- Reads more than the two `ByteList` headers and their `count` bytes, `key`, `nonce` and the `size` field of `plaintext`.
- Writes more than `plaintext` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.
- Branches or picks an address based on key or data bytes. Only the result of the whole tag comparison decides a branch.

### Limits

- Stack: 360 bytes on x86-64 (return address included), 448 bytes on ARM64, 544 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_chacha20_aead_decrypt` (`_crypto_chacha20_aead_decrypt` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `key`, `nonce`, `sealed`, `aad`, `plaintext`.

## Constant `CRYPTO_CHACHA20_POLY1305_FAIL`

- Value: 6.
- Status of `crypto_chacha20_aead_decrypt` when the tag does not match, or `sealed` is shorter than a tag.

## Test vectors

- RFC 8439 section 2.8.2 (the AEAD example) and section A.5 (the decryption example)
  - File: [`rfc8439.txt`](https://www.rfc-editor.org/rfc/rfc8439.txt), SHA-256 `25bef70fbf7a07ff45c2fe4cb7c6ce954eac687413d8610603268b4e4415324c`.
  - The generator reads the hex dumps of the two sections.
- Wycheproof ChaCha20-Poly1305, the 256-bit keys with a 96-bit nonce and a 128-bit tag
  - File: [`chacha20_poly1305_test.json`](https://github.com/C2SP/wycheproof/blob/65ca494727a52944c204441c860b039e6786b99b/testvectors_v1/chacha20_poly1305_test.json), SHA-256 `fe61d25f90e1bde4461d00eafe61049e5f29bd999f36b766df9cda90906ad53d`.
  - The invalid cases must give `CRYPTO_CHACHA20_POLY1305_FAIL`.
- Generated cases
  - Plaintexts of 0 to 139 bytes with 0, 1, 15, 16, 17 and 70 bytes of AAD, and of 255, 256, 257, 511, 512, 513, 1000, 1280, 4096, 65535, 65536 and 100000 bytes with 0 and 13 bytes of AAD.
  - Each case again with one bit flipped, which must give `CRYPTO_CHACHA20_POLY1305_FAIL`; `sealed` of 0 to 15 bytes; and a tag checked against other AAD.
  - Expected results: `cryptography` 50.0.2 (OpenSSL), pinned with hashes in [tests/generator/requirements.txt](../../tests/generator/requirements.txt).

## Results

<!-- CI generates the tick table for each function here. -->
