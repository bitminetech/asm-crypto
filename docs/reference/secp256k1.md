# secp256k1

## Contents

### Functions

- [`crypto_secp256k1_public_key`](#function-crypto_secp256k1_public_key): makes the public key of a private key.
- [`crypto_secp256k1_decompress`](#function-crypto_secp256k1_decompress): turns a compressed public key into x and y.
- [`crypto_secp256k1_ecdh`](#function-crypto_secp256k1_ecdh): computes the discv5 ECDH secret.
- [`crypto_secp256k1_sign`](#function-crypto_secp256k1_sign): signs a 32-byte hash with ECDSA.
- [`crypto_secp256k1_verify`](#function-crypto_secp256k1_verify): checks an ECDSA signature.
- [`crypto_secp256k1_lift_x`](#function-crypto_secp256k1_lift_x): finds the point of a compressed public key.
- [`crypto_secp256k1_point_mul`](#function-crypto_secp256k1_point_mul): multiplies a point by a number.
- [`crypto_secp256k1_point_add`](#function-crypto_secp256k1_point_add): adds two points.
- [`crypto_secp256k1_point_double`](#function-crypto_secp256k1_point_double): doubles a point.
- [`crypto_secp256k1_point_affine`](#function-crypto_secp256k1_point_affine): turns a point into x and y.
- [`crypto_secp256k1_mod_pow`](#function-crypto_secp256k1_mod_pow): raises a number to a public power.
- [`crypto_secp256k1_mod_mul`](#function-crypto_secp256k1_mod_mul): multiplies two numbers, Montgomery form.
- [`crypto_secp256k1_mod_add`](#function-crypto_secp256k1_mod_add): adds two numbers.
- [`crypto_secp256k1_mod_sub`](#function-crypto_secp256k1_mod_sub): subtracts two numbers.

### Types

- [`PrivateKey`](#type-privatekey): a private key.
- [`PublicKey`](#type-publickey): a compressed point.
- [`Point`](#type-point): the x and y of a point.
- [`Hash`](#type-hash): the 32-byte hash to sign.
- [`Signature`](#type-signature): r and s.
- [`Valid`](#type-valid): the result of a check.
- [`Number`](#type-number): a number below a modulus, as limbs.
- [`ProjectivePoint`](#type-projectivepoint): X, Y and Z.
- [`Modulus`](#type-modulus): a modulus with its Montgomery constants.

### Constants

- [`CRYPTO_INVALID_PRIVATE_KEY`](#constant-crypto_invalid_private_key): the status for a bad private key.
- [`CRYPTO_INVALID_PUBLIC_KEY`](#constant-crypto_invalid_public_key): the status for a bad public key.

## Spec

- Document: [SEC 2 version 2.0](https://www.secg.org/sec2-v2.pdf), January 2010. Section: 2.4.1, the curve secp256k1.
- Document: [SEC 1 version 2.0](https://www.secg.org/sec1-v2.pdf), May 2009. Sections: 2.3.3 and 2.3.4 (point compression), 3.2.1 (public keys), 4.1.3 and 4.1.4 (ECDSA).
- Document: [RFC 6979](https://www.rfc-editor.org/rfc/rfc6979), August 2013. Section: 3.2, with HMAC-SHA-256 and qlen = 256.
- Document: [discv5-theory.md](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/discv5/discv5-theory.md), the v4 identity scheme: `ecdh` and `id_sign`.
- The signatures and checks match [libsecp256k1 v0.8.0](https://github.com/bitcoin-core/secp256k1/tree/6e2c8bc4ecdc6e71dbe7a368f360d8d453ce435d): the RFC 6979 input is the hash mod n, s is at most (n - 1) / 2, and a check rejects a larger s.

## Function `crypto_secp256k1_public_key`

Writes the compressed public key d * G of a private key d.

### Signature

```
crypto_secp256k1_public_key(private_key, public_key) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `private_key` | input | `PrivateKey` |
| `public_key` | output | `PublicKey` |

### Returns

- `CRYPTO_OK`: `public_key` holds d * G.
- `CRYPTO_INVALID_PRIVATE_KEY`: d is 0, or n or more. Nothing is written.

### Caller must

- Keep `public_key` apart from `private_key`.

### Function does

- Computes d * G with `crypto_secp256k1_point_mul`, and its x and y with `crypto_secp256k1_point_affine`.
- Writes 0x02 for even y or 0x03 for odd y, then x.

### Function never

- Writes more than `public_key` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.
- Branches or picks an address based on the bits of d. Only whether d is valid decides a branch.

### Limits

- Stack: 1272 bytes on x86-64 (return address included), 1312 bytes on ARM64, 1392 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_secp256k1_public_key` (`_crypto_secp256k1_public_key` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `private_key`, `public_key`.

## Function `crypto_secp256k1_decompress`

Writes x and y of the point of a compressed public key.

### Signature

```
crypto_secp256k1_decompress(public_key, point) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `public_key` | input | `PublicKey` |
| `point` | output | `Point` |

### Returns

- `CRYPTO_OK`: `point` holds x and y.
- `CRYPTO_INVALID_PUBLIC_KEY`: the first byte is not 0x02 or 0x03, x is p or more, or x is not the x of a point. Nothing is written.

### Caller must

- Keep `point` apart from `public_key`.

### Function does

- Finds y with `crypto_secp256k1_lift_x`, then writes x and y.

### Function never

- Writes more than `point` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 664 bytes on x86-64 (return address included), 704 bytes on ARM64, 784 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_secp256k1_decompress` (`_crypto_secp256k1_decompress` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `public_key`, `point`.

## Function `crypto_secp256k1_ecdh`

Writes the discv5 secret of a public key Q and a private key d: the compressed point d * Q.

### Signature

```
crypto_secp256k1_ecdh(public_key, private_key, shared) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `public_key` | input | `PublicKey` |
| `private_key` | input | `PrivateKey` |
| `shared` | output | `PublicKey` |

### Returns

- `CRYPTO_OK`: `shared` holds 0x02 or 0x03, then the x of d * Q.
- `CRYPTO_INVALID_PUBLIC_KEY`: `public_key` is not a valid compressed point. Nothing is written.
- `CRYPTO_INVALID_PRIVATE_KEY`: d is 0, or n or more. Nothing is written.

### Caller must

- Keep `shared` apart from the inputs.

### Function does

- Checks `public_key` first, then `private_key`.
- Computes d * Q with `crypto_secp256k1_point_mul`.
- Writes 0x02 for even y or 0x03 for odd y, then x, as discv5's `ecdh` says.

### Function never

- Hashes the secret.
- Writes more than `shared` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.
- Branches or picks an address based on the bits of d.

### Limits

- Stack: 1272 bytes on x86-64 (return address included), 1312 bytes on ARM64, 1392 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_secp256k1_ecdh` (`_crypto_secp256k1_ecdh` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `public_key`, `private_key`, `shared`.

## Function `crypto_secp256k1_sign`

Signs a hash with ECDSA and a nonce from RFC 6979, and writes r and a low s.

### Signature

```
crypto_secp256k1_sign(private_key, hash, signature) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `private_key` | input | `PrivateKey` |
| `hash` | input | `Hash` |
| `signature` | output | `Signature` |

### Returns

- `CRYPTO_OK`: `signature` holds r and s.
- `CRYPTO_INVALID_PRIVATE_KEY`: d is 0, or n or more. Nothing is written.

### Caller must

- Keep `signature` apart from the inputs.

### Function does

- Takes e = the hash as a big-endian number, mod n.
- Draws k by RFC 6979 section 3.2 with key d and input e, with `crypto_hmac_sha256`. It skips a k that is 0 or n or more, and a k that gives r = 0 or s = 0, as step h says.
- Computes r = x(k * G) mod n and s = (e + r * d) / k mod n.
- Writes n - s when s is above (n - 1) / 2.

### Function never

- Writes more than `signature` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.
- Branches or picks an address based on the bits of d or k. Only whether a k is usable decides a branch.

### Limits

- Stack: 1992 bytes on x86-64 (return address included), 2032 bytes on ARM64, 2112 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_secp256k1_sign` (`_crypto_secp256k1_sign` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `private_key`, `hash`, `signature`.

## Function `crypto_secp256k1_verify`

Checks an ECDSA signature of a hash against a public key.

### Signature

```
crypto_secp256k1_verify(public_key, hash, signature, valid) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `public_key` | input | `PublicKey` |
| `hash` | input | `Hash` |
| `signature` | input | `Signature` |
| `valid` | output | `Valid` |

### Returns

- `CRYPTO_OK`: `valid` holds 1 or 0.
- `CRYPTO_INVALID_PUBLIC_KEY`: `public_key` is not a valid compressed point. Nothing is written.

### Caller must

- Keep `valid` apart from the inputs.

### Function does

- Writes 0 when r or s is 0 or n or more, or s is above (n - 1) / 2.
- Otherwise computes R = u1 * G + u2 * Q, with u1 = e / s and u2 = r / s mod n, and writes 1 when R is not the point at infinity and x(R) mod n = r.

### Function never

- Writes more than `valid` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 1816 bytes on x86-64 (return address included), 1856 bytes on ARM64, 1936 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_secp256k1_verify` (`_crypto_secp256k1_verify` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `public_key`, `hash`, `signature`, `valid`.

## Function `crypto_secp256k1_lift_x`

Finds the point of a compressed public key, by SEC 1 section 2.3.4, with Z = 1.

### Signature

```
crypto_secp256k1_lift_x(point, public_key) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `point` | output | `ProjectivePoint` |
| `public_key` | input | `PublicKey` |

### Returns

- `CRYPTO_OK`: `point` holds the point.
- `CRYPTO_INVALID_PUBLIC_KEY`: as in `crypto_secp256k1_decompress`.

### Function does

- Computes y = (x^3 + 7)^((p + 1) / 4) mod p, and checks that y^2 = x^3 + 7.
- Takes p - y when the parity of y differs from the first byte.

### Function never

- Writes more than `point` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 256 bytes on x86-64 (return address included), 288 bytes on ARM64, 304 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_secp256k1_lift_x`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `point`, `public_key`.

## Function `crypto_secp256k1_point_mul`

Computes scalar * base.

### Signature

```
crypto_secp256k1_point_mul(point, scalar, base) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `point` | output | `ProjectivePoint` |
| `scalar` | input | `Number`, plain |
| `base` | input | `ProjectivePoint` |

### Function does

- Starts from the point at infinity. For each bit from 255 down: doubles, adds `base`, and keeps the sum where the bit is 1, through a mask.

### Function never

- Branches or picks an address based on the bits of `scalar`.
- Writes more than `point` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 352 bytes on x86-64 (return address included), 384 bytes on ARM64, 400 bytes on RISC-V.
- Point operations: 256 doublings and 256 additions.

### ABI

- Role: L0.
- Symbol: `crypto_secp256k1_point_mul`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `point`, `scalar`, `base`.

## Function `crypto_secp256k1_point_add`

Computes first + second with algorithm 7 of [Renes, Costello and Batina](https://eprint.iacr.org/2015/1060), a = 0 and b3 = 21.

### Signature

```
crypto_secp256k1_point_add(point, first, second) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `point` | output | `ProjectivePoint` |
| `first` | input | `ProjectivePoint` |
| `second` | input | `ProjectivePoint` |

### Function does

- Copies the inputs first, so `point` may be either input.
- Gives the right sum for every pair of points, the point at infinity and equal points included.

### Function never

- Writes more than `point` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 512 bytes on x86-64 (return address included), 544 bytes on ARM64, 560 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_secp256k1_point_add`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `point`, `first`, `second`.

## Function `crypto_secp256k1_point_double`

Computes 2 * base with algorithm 9 of [Renes, Costello and Batina](https://eprint.iacr.org/2015/1060), a = 0 and b3 = 21.

### Signature

```
crypto_secp256k1_point_double(point, base) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `point` | output | `ProjectivePoint` |
| `base` | input | `ProjectivePoint` |

### Function does

- Copies the input first, so `point` may be `base`.

### Function never

- Writes more than `point` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 352 bytes on x86-64 (return address included), 384 bytes on ARM64, 400 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_secp256k1_point_double`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `point`, `base`.

## Function `crypto_secp256k1_point_affine`

Computes x = X / Z and y = Y / Z as plain numbers.

### Signature

```
crypto_secp256k1_point_affine(xy, point) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `xy` | output | two `Number` values, x then y, plain |
| `point` | input | `ProjectivePoint` |

### Function does

- Computes 1 / Z as Z^(p - 2) with `crypto_secp256k1_mod_pow`.
- Gives 0 and 0 for the point at infinity.

### Function never

- Writes more than `xy` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 128 bytes on x86-64 (return address included), 160 bytes on ARM64, 176 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_secp256k1_point_affine`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `xy`, `point`.

## Function `crypto_secp256k1_mod_pow`

Computes base^exponent in Montgomery form.

### Signature

```
crypto_secp256k1_mod_pow(result, base, exponent, modulus) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `Number`, Montgomery form |
| `base` | input | `Number`, Montgomery form |
| `exponent` | input | `Number`, plain, public |
| `modulus` | input | `Modulus` |

### Function does

- Squares, and multiplies where a bit of the exponent is 1, from bit 255 down.

### Function never

- Writes more than `result` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 128 bytes on x86-64 (return address included), 160 bytes on ARM64, 176 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_secp256k1_mod_pow`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `base`, `exponent`, `modulus`.

## Function `crypto_secp256k1_mod_mul`

Computes a * b / 2^256 mod m, by the CIOS form of Montgomery multiplication.

### Signature

```
crypto_secp256k1_mod_mul(result, a, b, modulus) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `Number` |
| `a` | input | `Number` |
| `b` | input | `Number` |
| `modulus` | input | `Modulus` |

### Caller must

- Pass a and b below m.

### Function does

- Ends with a masked subtraction of m, so the result is below m.
- Writes `result` last, so it may be `a` or `b`.

### Function never

- Branches or picks an address based on a or b.
- Writes more than `result` and its own stack.

### Limits

- Stack of its own: 56 bytes on x86-64 (return address included), none on ARM64, 32 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_secp256k1_mod_mul`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `a`, `b`, `modulus`.

## Function `crypto_secp256k1_mod_add`

Computes a + b mod m.

### Signature

```
crypto_secp256k1_mod_add(result, a, b, modulus) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `Number` |
| `a` | input | `Number` |
| `b` | input | `Number` |
| `modulus` | input | `Modulus` |

### Caller must

- Pass a and b below m.

### Function does

- Subtracts m with a mask when the sum is m or more. `result` may be `a` or `b`.

### Function never

- Branches or picks an address based on a or b.
- Writes more than `result` and its own stack.

### Limits

- Stack of its own: 8 bytes on x86-64, its return address, and none on ARM64 and RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_secp256k1_mod_add`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `a`, `b`, `modulus`.

## Function `crypto_secp256k1_mod_sub`

Computes a - b mod m.

### Signature

```
crypto_secp256k1_mod_sub(result, a, b, modulus) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | `Number` |
| `a` | input | `Number` |
| `b` | input | `Number` |
| `modulus` | input | `Modulus` |

### Caller must

- Pass a and b below m.

### Function does

- Adds m with a mask when the difference borrows. `result` may be `a` or `b`.

### Function never

- Branches or picks an address based on a or b.
- Writes more than `result` and its own stack.

### Limits

- Stack of its own: 8 bytes on x86-64, its return address, and none on ARM64 and RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_secp256k1_mod_sub`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `a`, `b`, `modulus`.

## Type `PrivateKey`

A private key d.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `d` | 32 bytes | A big-endian number |

### Rules

- The buffer starts at a multiple of 8.
- Valid when 1 <= d < n.

## Type `PublicKey`

A compressed point, SEC 1 section 2.3.3.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `prefix` | u8 | 0x02 for even y, 0x03 for odd y |
| 1 | `x` | 32 bytes | x, a big-endian number |

### Rules

- 33 bytes. The buffer starts at a multiple of 8.
- Valid when the prefix is 0x02 or 0x03, x < p, and x^3 + 7 is a square mod p.

## Type `Point`

The x and y of a point, as discv5 node IDs hash them.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `x` | 32 bytes | A big-endian number |
| 32 | `y` | 32 bytes | A big-endian number |

### Rules

- 64 bytes. The buffer starts at a multiple of 8.

## Type `Hash`

The 32-byte hash to sign, such as a SHA-256 or Keccak-256 digest.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `hash` | 32 bytes | A big-endian number; it may be n or more |

### Rules

- The buffer starts at a multiple of 8.

## Type `Signature`

An ECDSA signature, as discv5 `id_sign` and ENR v4 encode it.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `r` | 32 bytes | A big-endian number |
| 32 | `s` | 32 bytes | A big-endian number |

### Rules

- 64 bytes. The buffer starts at a multiple of 8.
- `crypto_secp256k1_sign` writes s of at most (n - 1) / 2.

## Type `Valid`

The result of a check.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `valid` | u64 | 1 when the signature is valid, else 0 |

### Rules

- 8 bytes, at a multiple of 8.

## Type `Number`

A number below a modulus, as limbs.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 8i | `limb[i]` | u64 | Bits 64i to 64i + 63 |

### Rules

- 32 bytes, at a multiple of 8.
- Field elements are in Montgomery form: a * 2^256 mod p.

## Type `ProjectivePoint`

A point in projective coordinates: x = X / Z and y = Y / Z.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `X` | `Number` | Montgomery form |
| 32 | `Y` | `Number` | Montgomery form |
| 64 | `Z` | `Number` | Montgomery form |

### Rules

- 96 bytes, at a multiple of 8.
- Z = 0 is the point at infinity, (0 : 1 : 0).

## Type `Modulus`

A modulus m with its Montgomery constants. The library holds the records for p and n.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `m` | `Number` | The modulus |
| 32 | `inverse` | u64 | -m^-1 mod 2^64 |
| 40 | `one` | `Number` | 2^256 mod m, the number 1 in Montgomery form |
| 72 | `r2` | `Number` | 2^512 mod m |

### Rules

- 104 bytes, at a multiple of 8.

## Constant `CRYPTO_INVALID_PRIVATE_KEY`

- Value: 4.
- Status when a private key is 0, or n or more.

## Constant `CRYPTO_INVALID_PUBLIC_KEY`

- Value: 5.
- Status when a public key is not a valid compressed point.

## Test vectors

- Generated cases
  - Private keys 1, 2, 3, n - 1, n - 2, (n - 1) / 2, (n + 1) / 2, 2^255, 2^128 + 1 and 200 random keys; 0, n, n + 1 and 2^256 - 1 as bad keys.
  - Decompression of every key, bad prefixes, and x of 0, 1, p - 1, p, p + 1, 2^256 - 1 and 40 random values with both prefixes.
  - ECDH of random pairs, with bad private and public keys.
  - Signatures of 155 hashes, among them 0, 2^256 - 1, n, n - 1 and n + 5; each checked as is, with s replaced by n - s, with a flipped bit and against another hash; 10 of them also with r or s replaced by 0, n, or n plus the value.
  - Expected results: [libsecp256k1 v0.8.0](https://github.com/bitcoin-core/secp256k1/tree/6e2c8bc4ecdc6e71dbe7a368f360d8d453ce435d), built by [tests/generator/run.sh](../../tests/generator/run.sh) with the ECDH module, whose ECDH hash function returns the compressed point.
- Wycheproof ECDSA secp256k1 SHA-256, P1363 encoding
  - File: [`ecdsa_secp256k1_sha256_p1363_test.json`](https://github.com/C2SP/wycheproof/blob/65ca494727a52944c204441c860b039e6786b99b/testvectors_v1/ecdsa_secp256k1_sha256_p1363_test.json), SHA-256 `7a339efc7134fb2495cd32afdbd692e0f86427d3c24e9073f6a7d858bb8788d2`.
  - The hash is the SHA-256 of the message. Cases with s above (n - 1) / 2 take the libsecp256k1 result, 0, since Wycheproof accepts them.
- Wycheproof ECDH secp256k1, the valid and acceptable cases whose public key is a point
  - File: [`ecdh_secp256k1_test.json`](https://github.com/C2SP/wycheproof/blob/65ca494727a52944c204441c860b039e6786b99b/testvectors_v1/ecdh_secp256k1_test.json), SHA-256 `049fa2be70e9db836a043aba6132b53cd97de4c0de5277bca6d65a2770075cae`.
  - The x of each result must equal the Wycheproof shared secret.
- devp2p discv5
  - File: [`discv5-wire-test-vectors.md`](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/discv5/discv5-wire-test-vectors.md), SHA-256 `dbcb81f70bc963cad2d5b28fd7ef99e0c4b4ce4d03497f7c75d63ef752115170`.
  - The ECDH vector, the key derivation ECDH, and the ID nonce signature, signed and checked.
- devp2p ENR example
  - File: [`enr.md`](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/enr.md), SHA-256 `29260bceb96e289140dc08c1336e1f26e070613664a7ec6db72fffbfb85cc58d`.
  - The public key of the example private key, its decompression, and the record signature, signed and checked.

## Results

<!-- CI generates the tick table for each function here. -->
