# Hash to curve

## Contents

### Functions

- [`crypto_bls_expand_message_xmd`](#function-crypto_bls_expand_message_xmd): expands a message into uniform bytes with SHA-256.
- [`crypto_bls_hash_to_g2`](#function-crypto_bls_hash_to_g2): hashes a message to a point of G2.
- [`crypto_bls_xmd`](#function-crypto_bls_xmd): computes expand_message_xmd without checks.
- [`crypto_bls_fp_from_bytes64`](#function-crypto_bls_fp_from_bytes64): reads 64 big-endian bytes as an element of Fp.
- [`crypto_bls_fp2_sgn0`](#function-crypto_bls_fp2_sgn0): writes sgn0 of an element of Fp2.
- [`crypto_bls_simple_swu`](#function-crypto_bls_simple_swu): maps an element of Fp2 to E2'.
- [`crypto_bls_swu_g`](#function-crypto_bls_swu_g): computes the curve function of E2'.
- [`crypto_bls_iso_map_g2`](#function-crypto_bls_iso_map_g2): maps a point of E2' to E2.
- [`crypto_bls_psi`](#function-crypto_bls_psi): computes the endomorphism psi of E2.
- [`crypto_bls_psi2`](#function-crypto_bls_psi2): computes psi applied twice.
- [`crypto_bls_g2_mul_neg_x`](#function-crypto_bls_g2_mul_neg_x): multiplies a point of E2 by the BLS parameter.
- [`crypto_bls_clear_cofactor`](#function-crypto_bls_clear_cofactor): clears the cofactor of a point of E2.
- [`crypto_bls_hash_to_g2_point`](#function-crypto_bls_hash_to_g2_point): hashes a message to a point of G2.

### Types

- [`G2Affine`](#type-g2affine): the affine coordinates of a point of E2.
- [`H2cScratch`](#type-h2cscratch): the workspace of the hash.

### Constants

- [`CRYPTO_BLS_H2C_SCRATCH`](#constant-crypto_bls_h2c_scratch): the fixed part of an `H2cScratch`.
- [`CRYPTO_BLS_XMD_LENGTH`](#constant-crypto_bls_xmd_length): the length is above 8160.
- [`CRYPTO_BLS_POINT_AT_INFINITY`](#constant-crypto_bls_point_at_infinity): the point has no affine form.

## Spec

- Document: [cryptography-specs v0.3.0](https://github.com/ethereum/cryptography-specs/blob/bb6dfe55198243682bc2eaf94611af2dbce1be6f/EthLib/Cryptography/Bls/HashToCurve.lean), commit `bb6dfe55198243682bc2eaf94611af2dbce1be6f`, `EthLib/Cryptography/Bls/HashToCurve.lean`, and `Exports/Bls.lean` (`expandMessageXmdExport`, `hashToG2Export`).
- It follows [RFC 9380](https://www.rfc-editor.org/rfc/rfc9380), the suite `BLS12381G2_XMD:SHA-256_SSWU_RO_`: `expand_message_xmd` (section 5.3.1, with section 5.3.3 for a DST above 255 bytes), `hash_to_field` with count 2 and L = 64 (section 5.2), the simplified SWU map (section 6.6.2) onto the curve E2' with A' = 240 u, B' = 1012 (1 + u) and Z = -(2 + u), the 3-isogeny of appendix E.3, and the cofactor clearing of appendix G.3.
- SHA-256 is `crypto_sha256` ([sha-256.md](sha-256.md)).

## Function `crypto_bls_expand_message_xmd`

Expands a message and a DST into `length` uniform bytes (`expandMessageXmd`).

### Signature

```
crypto_bls_expand_message_xmd(message, dst, length, scratch, uniform) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `message` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `dst` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `length` | input | [`Length`](hkdf.md#type-length) |
| `scratch` | scratch | `H2cScratch` |
| `uniform` | output | [`ByteList`](sha-256.md#type-bytelist) |

### Returns

- `CRYPTO_OK`: `uniform` holds `length` bytes.
- `CRYPTO_BLS_XMD_LENGTH`: `length` is above 8160. Nothing is written.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_BLS_H2C_SCRATCH` + `count` of `message` + `count` of `dst` bytes, or `uniform` fewer than 24 + `length` bytes. Nothing is written.

### Caller must

- Pass valid `ByteList` values in `message` and `dst`. They are not checked.
- Set the `size` field of `scratch` and of `uniform` to their buffer sizes.
- Keep `scratch` and `uniform` apart from each other and from the inputs.

### Function does

- Checks `length`, then `scratch`, then `uniform`.
- Replaces a DST above 255 bytes with SHA-256("H2C-OVERSIZE-DST-" || DST).
- Computes b_0 = H(Z_pad || message || I2OSP(length, 2) || 0 || DST'), b_1 = H(b_0 || 1 || DST') and b_i = H((b_0 xor b_(i-1)) || i || DST'), with DST' = DST || I2OSP(len(DST), 1).
- Sets `offset` of `uniform` to 24 and `count` to `length`, and writes the first `length` bytes of b_1 || b_2 || ...
- Keeps the `size` field of `uniform`.

### Function never

- Reads more than the `ByteList` headers, their `count` bytes, `length` and the `size` fields.
- Writes more than `scratch`, `uniform` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 656 bytes on x86-64 (return address included), 608 bytes on ARM64, 704 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_bls_expand_message_xmd` (`_crypto_bls_expand_message_xmd` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `message`, `dst`, `length`, `scratch`, `uniform`.

## Function `crypto_bls_hash_to_g2`

Hashes a message to a point of G2 and writes its affine coordinates (`hashToG2`, `hashToG2Export`).

### Signature

```
crypto_bls_hash_to_g2(message, dst, scratch, point) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `message` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `dst` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `scratch` | scratch | `H2cScratch` |
| `point` | output | `G2Affine` |

### Returns

- `CRYPTO_OK`: `point` holds the coordinates.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_BLS_H2C_SCRATCH` + `count` of `message` + `count` of `dst` bytes. Nothing is written.
- `CRYPTO_BLS_POINT_AT_INFINITY`: the point is the point at infinity. Nothing is written.

### Caller must

- Pass valid `ByteList` values in `message` and `dst`. They are not checked.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch` and `point` apart from each other and from the inputs.

### Function does

- Checks `scratch` first.
- Takes u0 and u1 from `hash_to_field` with 256 bytes of `crypto_bls_expand_message_xmd`.
- Maps each with the simplified SWU map and the 3-isogeny, adds the two points, and clears the cofactor.
- Writes x.c0, x.c1, y.c0 and y.c1 of the affine point.

### Function never

- Reads more than the `ByteList` headers, their `count` bytes and the `size` field of `scratch`.
- Writes more than `scratch`, `point` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 2528 bytes on x86-64 (return address included), 2784 bytes on ARM64, 2880 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_bls_hash_to_g2` (`_crypto_bls_hash_to_g2` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `message`, `dst`, `scratch`, `point`.

## Function `crypto_bls_xmd`

Writes the first `length` bytes of `expand_message_xmd` (`expandMessageXmd`), without the checks of `crypto_bls_expand_message_xmd`.

### Signature

```
crypto_bls_xmd(message, dst, length, work, uniform) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `message` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `dst` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `length` | input | [`Length`](hkdf.md#type-length) |
| `work` | scratch | bytes |
| `uniform` | output | `length` bytes |

### Caller must

- Pass `length` at most 8160.
- Pass `work` of at least 360 + max(323 + `count` of `message`, 17 + `count` of `dst`) bytes, at a multiple of 8.
- Keep `work` and `uniform` apart from each other and from the inputs.

### Function does

- Takes DST = SHA-256("H2C-OVERSIZE-DST-" || DST) for a DST above 255 bytes, and DST' = DST || I2OSP(len(DST), 1).
- Computes b_0 = H(Z_pad || message || I2OSP(length, 2) || 0 || DST'), b_1 = H(b_0 || 1 || DST') and b_i = H((b_0 xor b_(i-1)) || i || DST'), with `crypto_sha256`.
- Writes the first `length` bytes of b_1 || b_2 || ...

### Function never

- Reads more than the `ByteList` headers, their `count` bytes and `length`.
- Writes more than `work`, `uniform` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 80 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_xmd`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `message`, `dst`, `length`, `work`, `uniform`.

## Function `crypto_bls_fp_from_bytes64`

Reads 64 big-endian bytes as a number n below 2^512, and writes n mod p (`fpFromBytesL`).

### Signature

```
crypto_bls_fp_from_bytes64(result, bytes) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | [`FpElement`](bls12-381.md#type-fpelement) |
| `bytes` | input | 64 bytes: a big-endian number |

### Caller must

- Keep `result` apart from `bytes`.

### Function does

- Splits n = hi 2^384 + lo, and computes lo * 2^768 / 2^384 + hi * 2^1152 / 2^384 mod p with two Montgomery products.

### Function never

- Writes more than `result` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 208 bytes on x86-64 (return address included), 240 bytes on ARM64, 256 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_fp_from_bytes64`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `bytes`.

## Function `crypto_bls_fp2_sgn0`

Writes sgn0 of RFC 9380 section 4.1 for Fp2 (`sgn0Fp2`): s0 or (c0 = 0 and s1), with s_i the parity of the value of c_i.

### Signature

```
crypto_bls_fp2_sgn0(bit, a) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `bit` | output | [`Valid`](secp256k1.md#type-valid) |
| `a` | input | [`Fp2Element`](bls12-381.md#type-fp2element) |

### Function does

- Reads the values with `crypto_bls_fp_canonical`.

### Function never

- Writes more than `bit` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 112 bytes on x86-64 (return address included), 144 bytes on ARM64, 160 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_fp2_sgn0`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `bit`, `a`.

## Function `crypto_bls_simple_swu`

Maps u to a point (x, y) of E2' by the steps of `simpleSwu` (RFC 9380 section 6.6.2).

### Signature

```
crypto_bls_simple_swu(xy, u) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `xy` | output | [`G2Xy`](bls12-381.md#type-g2xy) |
| `u` | input | [`Fp2Element`](bls12-381.md#type-fp2element) |

### Returns

- `CRYPTO_OK`: `xy` holds the point.
- `CRYPTO_INVALID_ENCODING`: neither g(x1) nor g(x2) is a square, which RFC 9380 rules out. Nothing is written.

### Caller must

- Keep `xy` apart from `u`.

### Function does

- With d = Z^2 u^4 + Z u^2: x1 = B' / (Z A') when d is 0, else x1 = (-B' / A') (1 + 1 / d).
- Takes x1 and y = sqrt(g(x1)) when g(x1) is a square, else x2 = Z u^2 x1 and y = sqrt(g(x2)), with `crypto_bls_swu_g` and `crypto_bls_fp2_sqrt`.
- Negates y when sgn0(u) differs from sgn0(y).

### Function never

- Writes more than `xy` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 944 bytes on x86-64 (return address included), 976 bytes on ARM64, 992 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_simple_swu`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `xy`, `u`.

## Function `crypto_bls_swu_g`

Computes g(x) = x^3 + A' x + B' on E2'.

### Signature

```
crypto_bls_swu_g(result, x) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | [`Fp2Element`](bls12-381.md#type-fp2element) |
| `x` | input | [`Fp2Element`](bls12-381.md#type-fp2element) |

### Caller must

- Keep `result` apart from `x`.

### Function does

- Computes x^3, then adds A' x and B'.

### Function never

- Writes more than `result` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 160 bytes on x86-64 (return address included), 192 bytes on ARM64, 208 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_swu_g`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `x`.

## Function `crypto_bls_iso_map_g2`

Maps a point of E2' to E2 with the 3-isogeny of RFC 9380 appendix E.3 (`isoMapG2`).

### Signature

```
crypto_bls_iso_map_g2(point, xy) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `point` | output | [`G2Point`](bls12-381.md#type-g2point) |
| `xy` | input | [`G2Xy`](bls12-381.md#type-g2xy) |

### Caller must

- Keep `point` apart from `xy`.

### Function does

- Computes x_num = k13 x^3 + k12 x^2 + k11 x + k10, x_den = x^2 + k21 x + k20, y_num = k33 x^3 + k32 x^2 + k31 x + k30 and y_den = x^3 + k42 x^2 + k41 x + k40.
- Writes (x_num / x_den, y y_num / y_den, 1), or the point at infinity when a denominator is 0.

### Function never

- Writes more than `point` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 736 bytes on x86-64 (return address included), 768 bytes on ARM64, 784 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_iso_map_g2`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `point`, `xy`.

## Function `crypto_bls_psi`

Computes psi of RFC 9380 appendix G.3 (`psi`): the affine (c1Psi conj(x), c2Psi conj(y), 1).

### Signature

```
crypto_bls_psi(result, point) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | [`G2Point`](bls12-381.md#type-g2point) |
| `point` | input | [`G2Point`](bls12-381.md#type-g2point) |

### Function does

- Keeps the point at infinity.
- Takes the affine coordinates first, so `result` may be `point`.

### Function never

- Writes more than `result` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 352 bytes on x86-64 (return address included), 384 bytes on ARM64, 400 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_psi`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `point`.

## Function `crypto_bls_psi2`

Computes psi2 of RFC 9380 appendix G.3 (`psi2`): the affine (c1Psi2 x, -y, 1).

### Signature

```
crypto_bls_psi2(result, point) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | [`G2Point`](bls12-381.md#type-g2point) |
| `point` | input | [`G2Point`](bls12-381.md#type-g2point) |

### Function does

- Keeps the point at infinity.
- Takes the affine coordinates first, so `result` may be `point`.

### Function never

- Writes more than `result` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 256 bytes on x86-64 (return address included), 288 bytes on ARM64, 304 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_psi2`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `point`.

## Function `crypto_bls_g2_mul_neg_x`

Computes x P, with the BLS parameter x = -|x| (`mulNegX`).

### Signature

```
crypto_bls_g2_mul_neg_x(result, point) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | [`G2Point`](bls12-381.md#type-g2point) |
| `point` | input | [`G2Point`](bls12-381.md#type-g2point) |

### Function does

- Computes |x| P with `crypto_bls_g2_mul`, then its negation.
- `result` may be `point`.

### Function never

- Writes more than `result` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_g2_mul_neg_x`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `point`.

## Function `crypto_bls_clear_cofactor`

Clears the cofactor of a point of E2 by the steps of RFC 9380 appendix G.3 (`clearCofactor`).

### Signature

```
crypto_bls_clear_cofactor(result, point, work) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `result` | output | [`G2Point`](bls12-381.md#type-g2point) |
| `point` | input | [`G2Point`](bls12-381.md#type-g2point) |
| `work` | scratch | 1152 bytes: t1, t2, t3 and t4 |

### Caller must

- Keep `work` apart from `result` and `point`.

### Function does

- t1 = x P, t2 = psi(P), t3 = psi2(2 P) - t2, t2 = x (t1 + t2), t3 = t3 + t2 - t1.
- Writes t3 - P, last, so `result` may be `point`.

### Function never

- Writes more than `result` and `work` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_clear_cofactor`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `result`, `point`, `work`.

## Function `crypto_bls_hash_to_g2_point`

Hashes a message to a point of G2 (`hashToG2`), without the checks of `crypto_bls_hash_to_g2`.

### Signature

```
crypto_bls_hash_to_g2_point(message, dst, work, point) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `message` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `dst` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `work` | scratch | The `work` part of an `H2cScratch` |
| `point` | output | [`G2Point`](bls12-381.md#type-g2point) |

### Returns

- `CRYPTO_OK`: `point` holds the point.
- `CRYPTO_INVALID_ENCODING`: from `crypto_bls_simple_swu`.

### Caller must

- Pass `work` of at least `CRYPTO_BLS_H2C_SCRATCH` - 8 + `count` of `message` + `count` of `dst` bytes.
- Keep `work` and `point` apart from each other and from the inputs.

### Function does

- Takes 256 bytes from `crypto_bls_xmd`, and u0 and u1 from them with `crypto_bls_fp_from_bytes64` (`hash_to_field`).
- Maps u0 and u1 with `crypto_bls_simple_swu` and `crypto_bls_iso_map_g2`, adds the two points, and clears the cofactor.

### Function never

- Reads more than the `ByteList` headers and their `count` bytes.
- Writes more than `work`, `point` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_hash_to_g2_point`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `message`, `dst`, `work`, `point`.

## Type `G2Affine`

The affine coordinates of a point of E2.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `x0` | 48 bytes | c0 of x, a big-endian number |
| 48 | `x1` | 48 bytes | c1 of x, a big-endian number |
| 96 | `y0` | 48 bytes | c0 of y, a big-endian number |
| 144 | `y1` | 48 bytes | c1 of y, a big-endian number |

### Rules

- 192 bytes. Each number is below p.

## Type `H2cScratch`

The workspace of the hash.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `work` | bytes | Written and read by the function |

### Rules

- The buffer starts at a multiple of 8.
- `size` is at least `CRYPTO_BLS_H2C_SCRATCH` + `count` of the message + `count` of the DST.

## Constant `CRYPTO_BLS_H2C_SCRATCH`

- Value: 4096.
- The fixed part of the `size` of an `H2cScratch`.

## Constant `CRYPTO_BLS_XMD_LENGTH`

- Value: 11.
- `length` is above 255 * 32 = 8160 (RFC 9380 section 5.3.1, ell above 255).

## Constant `CRYPTO_BLS_POINT_AT_INFINITY`

- Value: 12.
- The point is the point at infinity, which has no affine form.

## Test vectors

- cryptography-specs v0.3.0, `tests/cryptography/hash_to_curve`: `expand_message_xmd` and `hash_to_g2`, transcribed from RFC 9380 appendices J.10.1, K.1 and K.2
  - File: `tests/cryptography/hash_to_curve/SHA256SUMS` at commit `bb6dfe55198243682bc2eaf94611af2dbce1be6f`, SHA-256 `53a976d2f3c28548518ead50f32e6ccd4b90f0e969d933060afff157ba875933`, which pins each case file.
- cryptography-specs v0.3.0, `tests/cryptography/bls`, the handler `hash_to_G2`, from bls12-381-tests v0.1.2, with the DST `QUUX-V01-CS02-with-BLS12381G2_XMD:SHA-256_SSWU_RO_`
  - File: `tests/cryptography/bls/SHA256SUMS`, SHA-256 `beab1a4d6a7a32ab411850846500f20d592cacdbf541425efcfa311ac116d3cf`.
- Generated cases
  - `expand_message_xmd` with DSTs of 0, 1, 43, 50, 255, 256 and 300 bytes, and lengths 0, 1, 32, 33, 64, 255, 256, 257 and 8160; 8161 and 65535 as bad lengths. Expected results: RFC 9380 section 5.3.1 and section 5.3.3, written out with Python `hashlib` in [tests/generator/bls.py](../../tests/generator/bls.py).
  - The hash to G2 of 12 messages under those DSTs. Expected results: `py_arkworks_bls12381` 0.5.0, which the script checks against the rule of section 5.3.3 for each DST above 255 bytes.

## Results

<!-- CI generates the tick table for each function here. -->

### `crypto_bls_expand_message_xmd`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_hash_to_g2`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_xmd`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_fp_from_bytes64`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_fp2_sgn0`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_simple_swu`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_swu_g`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_iso_map_g2`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_psi`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_psi2`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_g2_mul_neg_x`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_clear_cofactor`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_hash_to_g2_point`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |
