# BLS signatures

Keys, signing, checking and aggregation.

## Contents

### Functions

- [`crypto_bls_sk_to_pk`](#function-crypto_bls_sk_to_pk): writes the public key of a secret key.
- [`crypto_bls_sign`](#function-crypto_bls_sign): signs a message.
- [`crypto_bls_verify`](#function-crypto_bls_verify): checks a signature of a message.
- [`crypto_bls_aggregate`](#function-crypto_bls_aggregate): adds signatures.
- [`crypto_bls_fast_aggregate_verify`](#function-crypto_bls_fast_aggregate_verify): checks one signature of one message by several keys.
- [`crypto_bls_key_validate`](#function-crypto_bls_key_validate): checks a public key.
- [`crypto_bls_eth_aggregate_pubkeys`](#function-crypto_bls_eth_aggregate_pubkeys): adds public keys.
- [`crypto_bls_eth_fast_aggregate_verify`](#function-crypto_bls_eth_fast_aggregate_verify): the fast aggregate check of Ethereum.
- [`crypto_bls_fast_aggregate_verify_cached`](#function-crypto_bls_fast_aggregate_verify_cached): checks one signature by the keys at several indices, with a cache of checked keys.
- [`crypto_bls_key_cache_fill`](#function-crypto_bls_key_cache_fill): writes the entries of a range of indices of a cache of checked keys.
- [`crypto_bls_secret_key`](#function-crypto_bls_secret_key): reads a secret key as a number.
- [`crypto_bls_key_validate_point`](#function-crypto_bls_key_validate_point): decompresses and checks a public key.
- [`crypto_bls_aggregate_keys`](#function-crypto_bls_aggregate_keys): adds checked public keys.
- [`crypto_bls_core_verify`](#function-crypto_bls_core_verify): checks a signature without the scratch check.
- [`crypto_bls_core_verify_point`](#function-crypto_bls_core_verify_point): checks a signature against a point of G1.
- [`crypto_bls_fast_verify`](#function-crypto_bls_fast_verify): checks one signature by several keys without the scratch check.

### Types

- [`BlsSecretKey`](#type-blssecretkey): a secret key.
- [`BlsPublicKey`](#type-blspublickey): a compressed point of G1.
- [`BlsSignature`](#type-blssignature): a compressed point of G2.
- [`BlsPublicKeyList`](#type-blspublickeylist): a list of public keys.
- [`BlsSignatureList`](#type-blssignaturelist): a list of signatures.
- [`BlsIndexList`](#type-blsindexlist): a list of key indices.
- [`BlsKeyCache`](#type-blskeycache): the checked keys of each index.
- [`BlsKeyEntry`](#type-blskeyentry): one entry of a `BlsKeyCache`.
- [`BlsScratch`](#type-blsscratch): the workspace of the hash and the pairing.

### Constants

- [`CRYPTO_BLS_SCRATCH`](#constant-crypto_bls_scratch): the fixed part of a `BlsScratch`.
- [`CRYPTO_INVALID_SIGNATURE`](#constant-crypto_invalid_signature): a signature does not decode.
- [`CRYPTO_EMPTY_LIST`](#constant-crypto_empty_list): a list has no entry.

## Spec

- Document: [cryptography-specs v0.3.0](https://github.com/ethereum/cryptography-specs/blob/bb6dfe55198243682bc2eaf94611af2dbce1be6f/EthLib/Cryptography/Bls/Signatures.lean), commit `bb6dfe55198243682bc2eaf94611af2dbce1be6f`.
- Section: `EthLib/Cryptography/Bls/Signatures.lean`.
- It follows the proof of possession scheme of [draft-irtf-cfrg-bls-signature-04](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04), sections 2.3 to 2.8 and 3.3, with the ciphersuite `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`, and adds the Ethereum functions `ethAggregatePubkeys` and `ethFastAggregateVerify`.
- DST: the 43 bytes `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`, the message tag of the ciphersuite.
- The points, the pairing and the encodings are in [bls12-381.md](bls12-381.md); the hash to G2 is in [hash-to-curve.md](hash-to-curve.md).
- `crypto_bls_fast_aggregate_verify_cached` is a custom function (ARCHITECTURE.md section 5): functionally equivalent to `fastAggregateVerify`, and to `verify` with one index.
- Use: [consensus-specs](https://github.com/ethereum/consensus-specs/tree/313cbfe561517a81eb11607fea7c6985e562eaa9/specs) `313cbfe` calls `bls.Sign`, `bls.Verify`, `bls.Aggregate`, `bls.FastAggregateVerify`, `bls.KeyValidate`, `eth_aggregate_pubkeys` and `eth_fast_aggregate_verify`.
- Use: a validator client checks that the public key of a keystore is the one of its secret key, with `SkToPk`.
- The spec does not run in constant time. The time of `crypto_bls_sk_to_pk` and `crypto_bls_sign` depends on the secret key.

## Function `crypto_bls_sk_to_pk`

Writes the public key SK * P of a secret key, with P the generator of G1 (`skToPk`).

### Signature

```
crypto_bls_sk_to_pk(secret_key, public_key) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `secret_key` | input | `BlsSecretKey` |
| `public_key` | output | `BlsPublicKey` |

### Returns

- `CRYPTO_OK`: `public_key` holds the key.
- `CRYPTO_INVALID_PRIVATE_KEY`: the secret key is 0, or r or more. Nothing is written.

### Caller must

- Keep `public_key` apart from `secret_key`.

### Function does

- Reads SK as a 32-byte big-endian number.
- Writes the compressed SK * P.

### Function never

- Reads more than `secret_key`.
- Writes more than `public_key` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 1440 bytes on x86-64 (return address included), 1504 bytes on ARM64, 1600 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_bls_sk_to_pk` (`_crypto_bls_sk_to_pk` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `secret_key`, `public_key`.

## Function `crypto_bls_sign`

Signs a message: the compressed SK * H(message), with H the hash to G2 under the DST (`sign`, `coreSign`).

### Signature

```
crypto_bls_sign(secret_key, message, scratch, signature) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `secret_key` | input | `BlsSecretKey` |
| `message` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `scratch` | scratch | `BlsScratch` |
| `signature` | output | `BlsSignature` |

### Returns

- `CRYPTO_OK`: `signature` holds the signature.
- `CRYPTO_INVALID_PRIVATE_KEY`: the secret key is 0, or r or more. Nothing is written.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_BLS_SCRATCH` + `count` of `message` bytes. Nothing is written.

### Caller must

- Pass a valid `ByteList` in `message`. It is not checked.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch` and `signature` apart from each other and from the inputs.

### Function does

- Checks the secret key, then `scratch`.
- Hashes the message to G2 with `crypto_bls_hash_to_g2` and the DST.
- Writes the compressed SK times that point.

### Function never

- Reads more than `secret_key`, the `ByteList` header and its `count` bytes, and the `size` field of `scratch`.
- Writes more than `scratch`, `signature` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Effects

- `scratch` holds the message and values of the hash after the call.

### Limits

- Stack: 2464 bytes on x86-64 (return address included), 2624 bytes on ARM64, 2768 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_bls_sign` (`_crypto_bls_sign` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `secret_key`, `message`, `scratch`, `signature`.

## Function `crypto_bls_verify`

Checks a signature of a message against a public key (`verify`, `coreVerify`).

### Signature

```
crypto_bls_verify(public_key, message, signature, scratch, valid) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `public_key` | input | `BlsPublicKey` |
| `message` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `signature` | input | `BlsSignature` |
| `scratch` | scratch | `BlsScratch` |
| `valid` | output | [`Valid`](secp256k1.md#type-valid) |

### Returns

- `CRYPTO_OK`: `valid` holds 1 or 0.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_BLS_SCRATCH` + `count` of `message` bytes. Nothing is written.

### Caller must

- Pass a valid `ByteList` in `message`. It is not checked.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch` and `valid` apart from each other and from the inputs.

### Function does

- Checks `scratch` first.
- Writes 0 when the signature does not decompress to a point of G2 (`crypto_bls_g2_decode`), or the public key fails `crypto_bls_key_validate`.
- Hashes the message to G2 with `crypto_bls_hash_to_g2` and the DST, giving Q.
- Writes 1 when e(P, R) * e(-PK, Q) is 1, with P the generator of G1 and R the signature point, else 0.

### Function never

- Reads more than `public_key`, `signature`, the `ByteList` header and its `count` bytes, and the `size` field of `scratch`.
- Writes more than `scratch`, `valid` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 3056 bytes on x86-64 (return address included), 3280 bytes on ARM64, 3360 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_bls_verify` (`_crypto_bls_verify` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `public_key`, `message`, `signature`, `scratch`, `valid`.

## Function `crypto_bls_aggregate`

Writes the compressed sum of the signature points (`aggregate`).

### Signature

```
crypto_bls_aggregate(signatures, signature) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `signatures` | input | `BlsSignatureList` |
| `signature` | output | `BlsSignature` |

### Returns

- `CRYPTO_OK`: `signature` holds the sum.
- `CRYPTO_EMPTY_LIST`: `signatures` has no entry. Nothing is written.
- `CRYPTO_INVALID_SIGNATURE`: an entry does not decompress to a point of the curve. Nothing is written.

### Caller must

- Pass a well formed `BlsSignatureList`. It is not checked.
- Keep `signature` apart from `signatures`.

### Function does

- Decompresses each entry, in order, and adds it to the sum, which starts at the point at infinity.
- Does not check that a point lies in the subgroup, as the spec says.

### Function never

- Reads more than the list header and its `count` entries.
- Writes more than `signature` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 3104 bytes on x86-64 (return address included), 3264 bytes on ARM64, 3312 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_bls_aggregate` (`_crypto_bls_aggregate` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `signatures`, `signature`.

## Function `crypto_bls_fast_aggregate_verify`

Checks one signature of one message against the sum of several public keys (`fastAggregateVerify`).

### Signature

```
crypto_bls_fast_aggregate_verify(public_keys, message, signature, scratch, valid) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `public_keys` | input | `BlsPublicKeyList` |
| `message` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `signature` | input | `BlsSignature` |
| `scratch` | scratch | `BlsScratch` |
| `valid` | output | [`Valid`](secp256k1.md#type-valid) |

### Returns

- `CRYPTO_OK`: `valid` holds 1 or 0.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_BLS_SCRATCH` + `count` of `message` bytes. Nothing is written.

### Caller must

- Pass a well formed `BlsPublicKeyList` and a valid `ByteList` in `message`. They are not checked.
- Set the `size` field of `scratch` to its buffer size.
- Keep `scratch` and `valid` apart from each other and from the inputs.
- Check a proof of possession of each key before it uses the key here: the scheme is safe from rogue keys only then (draft section 3.3).

### Function does

- Checks `scratch` first.
- Writes 0 when the list is empty or a key fails `crypto_bls_key_validate`.
- Adds the key points, compresses the sum, and writes the result of `crypto_bls_verify` for that key, the message and the signature.

### Function never

- Reads more than the list header and its `count` entries, `signature`, the `ByteList` header and its `count` bytes, and the `size` field of `scratch`.
- Writes more than `scratch`, `valid` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 3120 bytes on x86-64 (return address included), 3376 bytes on ARM64, 3472 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_bls_fast_aggregate_verify` (`_crypto_bls_fast_aggregate_verify` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `public_keys`, `message`, `signature`, `scratch`, `valid`.

## Function `crypto_bls_key_validate`

Checks a public key, as `KeyValidate` of the draft section 2.5 says (`keyValidate`).

### Signature

```
crypto_bls_key_validate(public_key, valid) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `public_key` | input | `BlsPublicKey` |
| `valid` | output | [`Valid`](secp256k1.md#type-valid) |

### Returns

- `CRYPTO_OK`: `valid` holds 1 or 0.

### Caller must

- Keep `valid` apart from `public_key`.

### Function does

- Writes 1 when the key decompresses to a point of the curve with `crypto_bls_g1_uncompress`, the point is not the point at infinity, and r times the point is the point at infinity; else 0.

### Function never

- Reads more than `public_key`.
- Writes more than `valid` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 2032 bytes on x86-64 (return address included), 2160 bytes on ARM64, 2288 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_bls_key_validate` (`_crypto_bls_key_validate` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `public_key`, `valid`.

## Function `crypto_bls_eth_aggregate_pubkeys`

Writes the compressed sum of public keys that each pass `KeyValidate` (`ethAggregatePubkeys`).

### Signature

```
crypto_bls_eth_aggregate_pubkeys(public_keys, public_key) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `public_keys` | input | `BlsPublicKeyList` |
| `public_key` | output | `BlsPublicKey` |

### Returns

- `CRYPTO_OK`: `public_key` holds the sum.
- `CRYPTO_EMPTY_LIST`: `public_keys` has no entry. Nothing is written.
- `CRYPTO_INVALID_PUBLIC_KEY`: a key fails `crypto_bls_key_validate`. Nothing is written.

### Caller must

- Pass a well formed `BlsPublicKeyList`. It is not checked.
- Keep `public_key` apart from `public_keys`.

### Function does

- Validates and adds the keys in order, from the point at infinity.
- Writes the point at infinity encoding when the sum is that point.

### Function never

- Reads more than the list header and its `count` entries.
- Writes more than `public_key` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 2384 bytes on x86-64 (return address included), 2544 bytes on ARM64, 2688 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_bls_eth_aggregate_pubkeys` (`_crypto_bls_eth_aggregate_pubkeys` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `public_keys`, `public_key`.

## Function `crypto_bls_eth_fast_aggregate_verify`

The fast aggregate check of Ethereum: an empty key list passes exactly with the signature of the point at infinity (`ethFastAggregateVerify`).

### Signature

```
crypto_bls_eth_fast_aggregate_verify(public_keys, message, signature, scratch, valid) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `public_keys` | input | `BlsPublicKeyList` |
| `message` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `signature` | input | `BlsSignature` |
| `scratch` | scratch | `BlsScratch` |
| `valid` | output | [`Valid`](secp256k1.md#type-valid) |

### Returns

- `CRYPTO_OK`: `valid` holds 1 or 0.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_BLS_SCRATCH` + `count` of `message` bytes. Nothing is written.

### Caller must

- Meet the conditions of `crypto_bls_fast_aggregate_verify`.

### Function does

- Checks `scratch` first.
- With no key: writes 1 when the signature is the byte 0xC0 followed by 95 zero bytes, else 0.
- With keys: writes the result of `crypto_bls_fast_aggregate_verify`.

### Function never

- Reads more than the list header and its `count` entries, `signature`, the `ByteList` header and its `count` bytes, and the `size` field of `scratch`.
- Writes more than `scratch`, `valid` and its own stack.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 3120 bytes on x86-64 (return address included), 3376 bytes on ARM64, 3472 bytes on RISC-V, callees included.

### ABI

- Role: L2.
- Symbol: `crypto_bls_eth_fast_aggregate_verify` (`_crypto_bls_eth_fast_aggregate_verify` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `public_keys`, `message`, `signature`, `scratch`, `valid`.

## Function `crypto_bls_fast_aggregate_verify_cached`

Checks one signature of one message against the sum of the keys at several indices, with a cache of checked keys.

### Signature

```
crypto_bls_fast_aggregate_verify_cached(keys, indices, cache, message, signature, scratch, valid) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `keys` | input | Key i: the `BlsPublicKey` at `keys` + i * `key_stride` of `cache` |
| `indices` | input | `BlsIndexList` |
| `cache` | state | `BlsKeyCache` |
| `message` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `signature` | input | `BlsSignature` |
| `scratch` | scratch | `BlsScratch` |
| `valid` | output | [`Valid`](secp256k1.md#type-valid) |

### Returns

- `CRYPTO_OK`: `valid` holds 1 or 0.
- `CRYPTO_BUFFER_TOO_SMALL`: `scratch` holds fewer than `CRYPTO_BLS_SCRATCH` + `count` of `message` bytes. Nothing is written.

### Caller must

- Pass a well formed `BlsIndexList` and `BlsKeyCache`, and a valid `ByteList` in `message`. They are not checked.
- Hold key i at `keys` for each index i of `indices` below `count` of `cache`, with `keys` at a multiple of 8.
- Start each entry of `cache` with status 0. After that, only this function and `crypto_bls_key_cache_fill` write the entries.
- Not pass one `cache` to two calls at the same time, but calls of `crypto_bls_key_cache_fill` as that function allows.
- Set the `size` field of `scratch` to its buffer size.
- Keep `cache`, `scratch` and `valid` apart from each other and from the inputs.
- Check a proof of possession of each key before it uses the key here: the scheme is safe from rogue keys only then (draft section 3.3).

### Function does

- Writes the result of `crypto_bls_fast_aggregate_verify` for the keys of the indices, in order, the message and the signature. With one index, that is the result of `crypto_bls_verify` for its key.
- Checks `scratch` first.
- Writes 0 when `indices` is empty, or an index is at or past `count` of `cache`.
- Takes the point of a key from the entry of its index when the entry's status is not 0 and its key is the same 48 bytes. Else checks the key with `crypto_bls_key_validate_point` and writes the entry: status 1 with the key and its point, or status 2 with the key.
- Writes 0 for a key of status 2.
- On x86-64 and ARM64, before it takes a key, gives the CPU a prefetch hint (`prefetcht0`, `prfm`) for the key and the entry of the next index, when that index is below `count` of `cache`. A hint reads and writes nothing.
- Adds the points with `crypto_bls_g1_add_affine`, and writes 0 when the sum is the point at infinity. The sum is the one `crypto_bls_g1_add` gives, coordinate for coordinate.
- Checks the signature against the sum as `crypto_bls_core_verify` does, without the compressed form and subgroup check of the sum: every point is in G1, so the sum is.

### Function never

- Reads more than the `indices` header and its `count` entries, key i and entry i for each index i read, the fixed fields of `cache`, `signature`, the `ByteList` header and its `count` bytes, and the `size` field of `scratch`.
- Writes more than the entries of the indices it reads, `scratch`, `valid` and its own stack.
- Changes the fixed fields of `cache`.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 3376 bytes on x86-64 (return address included), 3568 bytes on ARM64, 3648 bytes on RISC-V, callees included.

### ABI

- Role: L3.
- Symbol: `crypto_bls_fast_aggregate_verify_cached` (`_crypto_bls_fast_aggregate_verify_cached` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `keys`, `indices`, `cache`, `message`, `signature`, `scratch`, `valid`.

## Function `crypto_bls_key_cache_fill`

Writes the entries of a range of indices of a cache of checked keys, as `crypto_bls_fast_aggregate_verify_cached` writes them.

### Signature

```
crypto_bls_key_cache_fill(keys, first, count, cache) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `keys` | input | Key i: the `BlsPublicKey` at `keys` + i * `key_stride` of `cache` |
| `first` | input | u64 by value: the first index |
| `count` | input | u64 by value: the indices |
| `cache` | state | `BlsKeyCache` |

### Returns

- `CRYPTO_OK`, always.

### Caller must

- Pass a well formed `BlsKeyCache`. It is not checked.
- Hold key i at `keys` for each index i of the range below `count` of `cache`, with `keys` at a multiple of 8.
- Start each entry of `cache` with status 0, as for `crypto_bls_fast_aggregate_verify_cached`.
- Keep `cache` apart from `keys`.
- Run calls on one `cache` at the same time only when their ranges hold no index in common and no `crypto_bls_fast_aggregate_verify_cached` call runs on it.
- Check a proof of possession of each key before it uses the key in a signature check (draft section 3.3).

### Function does

- For each index i from `first` to the lower of `first` + `count` and `count` of `cache` (a sum past 2^64 - 1 takes `count` of `cache`): when entry i has status 0, or its key is not the 48 bytes of key i, checks key i with `crypto_bls_key_validate_point` and writes the entry: status 1 with the key and its point, or status 2 with the key. An entry of status 1 or 2 with the same key stays.
- Each entry it writes is the entry `crypto_bls_fast_aggregate_verify_cached` writes for that key, byte for byte.

### Function never

- Reads more than key i and entry i for each index i of the range below `count` of `cache`, and the fixed fields of `cache`.
- Writes more than the entries of the range and its own stack.
- Changes the fixed fields of `cache`.
- Keeps a pointer after it returns.
- Makes an OS call.

### Limits

- Stack: 2024 bytes on x86-64 (return address included), 2160 bytes on ARM64, 2288 bytes on RISC-V, callees included.

### ABI

- Role: L3.
- Symbol: `crypto_bls_key_cache_fill` (`_crypto_bls_key_cache_fill` on macOS).
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `keys`, `first`, `count`, `cache`.

## Function `crypto_bls_secret_key`

Reads a secret key as a number below r (`SecretKey.fromBytes`).

### Signature

```
crypto_bls_secret_key(scalar, secret_key) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `scalar` | output | [`Scalar`](bls12-381.md#type-scalar) |
| `secret_key` | input | `BlsSecretKey` |

### Returns

- `CRYPTO_OK`: `scalar` holds the number.
- `CRYPTO_INVALID_PRIVATE_KEY`: the number is 0, or r or more. Nothing is written.

### Caller must

- Keep `scalar` apart from `secret_key`.

### Function does

- Reads the 32 big-endian bytes as 4 limbs, and checks that the number is not 0 and is below r.

### Function never

- Writes more than `scalar`.
- Makes an OS call.

### Limits

- Stack of its own: 8 bytes on x86-64 (the return address), 0 bytes on ARM64 and RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_secret_key`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `scalar`, `secret_key`.

## Function `crypto_bls_key_validate_point`

Decompresses a public key and checks it (`G1.keyValidatePoint`).

### Signature

```
crypto_bls_key_validate_point(public_key, point) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `public_key` | input | `BlsPublicKey` |
| `point` | output | [`G1Point`](bls12-381.md#type-g1point) |

### Returns

- `CRYPTO_OK`: `point` holds the point.
- `CRYPTO_INVALID_PUBLIC_KEY`: the key does not decompress, is the point at infinity, or is not in G1. Nothing is written.

### Caller must

- Keep `point` apart from `public_key`.

### Function does

- Decompresses with `crypto_bls_g1_uncompress`, rejects the point at infinity, and checks the subgroup with `crypto_bls_g1_in_subgroup`.

### Function never

- Writes more than `point` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 224 bytes on x86-64 (return address included), 256 bytes on ARM64, 272 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_key_validate_point`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `public_key`, `point`.

## Function `crypto_bls_aggregate_keys`

Adds public keys, each checked by `crypto_bls_key_validate_point`, from the point at infinity.

### Signature

```
crypto_bls_aggregate_keys(public_keys, point) -> status
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `public_keys` | input | `BlsPublicKeyList` |
| `point` | output | [`G1Point`](bls12-381.md#type-g1point) |

### Returns

- `CRYPTO_OK`: `point` holds the sum.
- `CRYPTO_EMPTY_LIST`: the list has no key. Nothing is written.
- `CRYPTO_INVALID_PUBLIC_KEY`: a key fails its check. Nothing is written.

### Caller must

- Pass a valid `BlsPublicKeyList`. It is not checked.
- Keep `point` apart from `public_keys`.

### Function does

- Stops at the first key that fails its check.
- Adds with `crypto_bls_g1_add_affine`: each checked key has Z = 1, so its first 96 bytes are its affine (x, y). The sum is the one `crypto_bls_g1_add` gives, coordinate for coordinate.

### Function never

- Writes more than `point` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 352 bytes on x86-64 (return address included), 384 bytes on ARM64, 400 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_aggregate_keys`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6).
- Argument order: `public_keys`, `point`.

## Function `crypto_bls_core_verify`

Runs `coreVerify` with the DST, without the check of `crypto_bls_verify`.

### Signature

```
crypto_bls_core_verify(public_key, message, signature, work, valid) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `public_key` | input | `BlsPublicKey` |
| `message` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `signature` | input | `BlsSignature` |
| `work` | scratch | The `work` part of a `BlsScratch` |
| `valid` | output | [`Valid`](secp256k1.md#type-valid) |

### Caller must

- Pass a valid `ByteList` in `message`. It is not checked.
- Pass `work` of at least `CRYPTO_BLS_SCRATCH` - 8 + `count` of `message` bytes.
- Keep `work` and `valid` apart from each other and from the inputs.

### Function does

- Writes 0 first.
- Stops when the signature does not decompress to a point R of G2, or the key fails `crypto_bls_key_validate_point`.
- Hashes the message with `crypto_bls_hash_to_g2_point` and the DST, giving Q.
- Writes the result of `crypto_bls_pairing_check` on the pairs (P, R) and (-PK, Q), with P the generator of G1.

### Function never

- Reads more than `public_key`, `signature`, the `ByteList` header and its `count` bytes.
- Writes more than `work`, `valid` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 80 bytes on x86-64 (return address included), 112 bytes on ARM64, 128 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_core_verify`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `public_key`, `message`, `signature`, `work`, `valid`.

## Function `crypto_bls_core_verify_point`

Runs `coreVerify` with the DST, with the key as a point of G1.

### Signature

```
crypto_bls_core_verify_point(point, message, signature, work, valid) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `point` | input | [`G1Point`](bls12-381.md#type-g1point) |
| `message` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `signature` | input | `BlsSignature` |
| `work` | scratch | The `work` part of a `BlsScratch` |
| `valid` | output | [`Valid`](secp256k1.md#type-valid) |

### Caller must

- Pass a point of G1 that is not the point at infinity. It is not checked.
- Pass a valid `ByteList` in `message`. It is not checked.
- Pass `work` of at least `CRYPTO_BLS_SCRATCH` - 8 + `count` of `message` bytes.
- Keep `work` and `valid` apart from each other and from the inputs.

### Function does

- Writes 0 first.
- Stops when the signature does not decompress to a point R of G2.
- Hashes the message with `crypto_bls_hash_to_g2_point` and the DST, giving Q.
- Writes the result of `crypto_bls_pairing_check` on the pairs (P, R) and (-point, Q), with P the generator of G1.

### Function never

- Reads more than `point`, `signature`, the `ByteList` header and its `count` bytes.
- Writes more than `work`, `valid` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 80 bytes on x86-64 (return address included), 112 bytes on ARM64, 128 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_core_verify_point`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `point`, `message`, `signature`, `work`, `valid`.

## Function `crypto_bls_fast_verify`

Runs `fastAggregateVerify`, without the check of `crypto_bls_fast_aggregate_verify`.

### Signature

```
crypto_bls_fast_verify(public_keys, message, signature, work, valid) -> nothing
```

### Arguments

| Name | Role | Type |
|---|---|---|
| `public_keys` | input | `BlsPublicKeyList` |
| `message` | input | [`ByteList`](sha-256.md#type-bytelist) |
| `signature` | input | `BlsSignature` |
| `work` | scratch | The `work` part of a `BlsScratch` |
| `valid` | output | [`Valid`](secp256k1.md#type-valid) |

### Caller must

- Pass a valid `BlsPublicKeyList` and a valid `ByteList` in `message`. They are not checked.
- Pass `work` of at least `CRYPTO_BLS_SCRATCH` - 8 + `count` of `message` bytes.
- Keep `work` and `valid` apart from each other and from the inputs.

### Function does

- Writes 0 first.
- Stops when the list is empty or a key fails its check (`crypto_bls_aggregate_keys`).
- Compresses the sum of the keys, at offset 5488 of `work`, and runs `crypto_bls_core_verify` with it. A sum at the point at infinity fails there.

### Function never

- Reads more than the keys, `signature`, the `ByteList` header and its `count` bytes.
- Writes more than `work`, `valid` and its own stack.
- Makes an OS call.

### Limits

- Stack of its own: 64 bytes on x86-64 (return address included), 96 bytes on ARM64, 112 bytes on RISC-V.

### ABI

- Role: L0.
- Symbol: `crypto_bls_fast_verify`, local to its object.
- Convention: the core ABI for each ISA (ARCHITECTURE.md section 6). It returns no status.
- Argument order: `public_keys`, `message`, `signature`, `work`, `valid`.

## Type `BlsSecretKey`

A secret key SK of the draft section 2.3.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `sk` | 32 bytes | SK, a big-endian number |

### Rules

- 32 bytes.
- A valid key is from 1 to r - 1, with r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001.

## Type `BlsPublicKey`

A point of G1 in the compressed form of [bls12-381.md](bls12-381.md#type-g1compressed).

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `point` | 48 bytes | The compressed point |

### Rules

- 48 bytes.

## Type `BlsSignature`

A point of G2 in the compressed form of [bls12-381.md](bls12-381.md#type-g2compressed).

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `point` | 96 bytes | The compressed point |

### Rules

- 96 bytes.

## Type `BlsPublicKeyList`

A list of public keys.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `offset` | u64 | Where the keys start, from the buffer start |
| 16 | `count` | u64 | Number of keys |

### Rules

- The buffer starts at a multiple of 8.
- `offset` is at least 24 and a multiple of 8.
- The keys follow each other from `offset`, 48 bytes each.
- `offset` + 48 * `count` is at most `size`.

## Type `BlsSignatureList`

A list of signatures.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `offset` | u64 | Where the signatures start, from the buffer start |
| 16 | `count` | u64 | Number of signatures |

### Rules

- The buffer starts at a multiple of 8.
- `offset` is at least 24 and a multiple of 8.
- The signatures follow each other from `offset`, 96 bytes each.
- `offset` + 96 * `count` is at most `size`.

## Type `BlsIndexList`

A list of key indices.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `offset` | u64 | Where the indices start, from the buffer start |
| 16 | `count` | u64 | Number of indices |

### Rules

- The buffer starts at a multiple of 8.
- `offset` is at least 24 and a multiple of 8.
- The indices follow each other from `offset`, a u64 each.
- `offset` + 8 * `count` is at most `size`.

## Type `BlsKeyCache`

The checked keys of each index.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `key_stride` | u64 | Bytes from one key to the next at `keys` |
| 16 | `offset` | u64 | Where the entries start, from the buffer start |
| 24 | `count` | u64 | Number of entries |

### Rules

- The buffer starts at a multiple of 8.
- `key_stride` is a multiple of 8.
- `offset` is at least 32 and a multiple of 8.
- Entry i is the `BlsKeyEntry` at `offset` + 152 * i.
- `offset` + 152 * `count` is at most `size`.

## Type `BlsKeyEntry`

The check of one key.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `status` | u64 | 0 empty; 1 the key passes `crypto_bls_key_validate`; 2 it fails |
| 8 | `key` | `BlsPublicKey` | The key of the entry |
| 56 | `point` | [`G1Xy`](bls12-381.md#type-g1xy) | With status 1: the point of the key |

### Rules

- 152 bytes.

## Type `BlsScratch`

The workspace of the hash to G2 and of the pairing.

### Layout

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `size` | u64 | Total buffer size in bytes |
| 8 | `work` | bytes | Written and read by the function |

### Rules

- The buffer starts at a multiple of 8.
- `size` is at least `CRYPTO_BLS_SCRATCH` + `count` of the message.

## Constant `CRYPTO_BLS_SCRATCH`

The fixed part of the `size` of a `BlsScratch`.

## Constant `CRYPTO_INVALID_SIGNATURE`

A signature does not decompress to a point of the curve.

## Constant `CRYPTO_EMPTY_LIST`

A list that needs at least one entry has none.

## Test vectors

- cryptography-specs v0.3.0, `tests/cryptography/bls`: the handlers `sign`, `verify`, `aggregate` and `fast_aggregate_verify`, from [bls12-381-tests v0.1.2](https://github.com/ethereum/bls12-381-tests/tree/89ff3a86f1a9b89a555495f7535c853cda589320), and `eth_aggregate_pubkeys` and `eth_fast_aggregate_verify`, from [consensus-specs v1.7.0-beta.4](https://github.com/ethereum/consensus-specs/tree/aa16bb4c156184e9548a997d53efaf2a228a6304)
  - File: `tests/cryptography/bls/SHA256SUMS` at commit `bb6dfe55198243682bc2eaf94611af2dbce1be6f`, SHA-256 `beab1a4d6a7a32ab411850846500f20d592cacdbf541425efcfa311ac116d3cf`, which pins each case file.
  - A case whose output is null must give the status of its failure: `CRYPTO_INVALID_PRIVATE_KEY`, `CRYPTO_EMPTY_LIST`, `CRYPTO_INVALID_SIGNATURE` or `CRYPTO_INVALID_PUBLIC_KEY`.
- Generated cases
  - Secret keys 1, 2, 3, r - 1, r - 2, (r - 1) / 2, (r + 1) / 2, 2^128, 2^254 + 1 and 20 random keys; 0, r, r + 1 and 2^256 - 1 as bad keys.
  - Signatures of messages of 0, 1, 31, 32, 33, 55, 56, 63, 64, 65, 100, 128, 200, 255, 256 and 1000 bytes, each checked as is, against another message, against another key and with a flipped bit.
  - Public keys and signatures at infinity, off the subgroup, and with the bad encodings of [bls12-381.md](bls12-381.md#test-vectors).
  - Aggregates of 1, 2, 3, 5 and 12 signatures of one message, checked with their keys and with a missing key; an empty list; lists with the point at infinity, a point off the subgroup and bad encodings.
  - Keys that cancel: a key and its negation, whose sum is the point at infinity.
  - A key twice in one list, checked against the signature of the key twice and of the key once.
- `crypto_bls_fast_aggregate_verify_cached`: every case above of `verify`, `fast_aggregate_verify` and `eth_fast_aggregate_verify` with at least one key, with the keys at a stride of 48 and the indices 0 to n - 1. Each runs with an empty cache, again with the cache it filled, and with a cache filled by the case before. The expected result is that of the case.
- `crypto_bls_key_cache_fill`: the same cases: entries 0 to n - 1 of a new cache of count n filled in two calls split at n / 2, the second asking past the count, then a call past the count. Each entry must hold status 1 when `crypto_bls_key_validate` gives 1 for its key, else 2, and the key; a second fill changes no byte, and one over an entry of another key writes this key back. Then `crypto_bls_fast_aggregate_verify_cached` on that cache must give the case's result and leave each entry of status 1 as it was. Also each `key_validate` case: a cache of one entry must get status 1 when the case gives 1, else 2.
- Built from those cases: the keys at a stride of 128 in another order, an index twice, and an index at `count` of the cache.
  - Expected results: `py_arkworks_bls12381` 0.5.0 for the points, the hash to G2, the subgroup checks and the pairing check, with the steps of `Signatures.lean` written out in [tests/generator/bls.py](../../tests/generator/bls.py).

## Results

<!-- CI generates the tick table for each function here. -->

### `crypto_bls_sk_to_pk`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_sign`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_verify`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_aggregate`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_fast_aggregate_verify`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_key_validate`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_eth_aggregate_pubkeys`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_eth_fast_aggregate_verify`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_fast_aggregate_verify_cached`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_key_cache_fill`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_secret_key`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_key_validate_point`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_aggregate_keys`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_core_verify`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |

### `crypto_bls_core_verify_point`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 |  |  |  |  |
| ARM64 |  |  |  |  |
| RISC-V |  |  |  |  |

### `crypto_bls_fast_verify`

| ISA | Linux | Windows | macOS | `equal` |
|---|---|---|---|---|
| x86-64 | ✅ | ✅ | ✅ |  |
| ARM64 | ✅ | ✅ | ✅ |  |
| RISC-V | ✅ |  |  |  |
