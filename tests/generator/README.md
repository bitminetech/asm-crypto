# Vector generation

Two scripts write binary case files to one output folder, which must be outside this repo. Both check the SHA-256 pin of every file they read from a download.

```bash
python3 -I tests/generator/generate.py ~/.cache/asm-crypto/vectors
```

```bash
tests/generator/run.sh ~/.cache/asm-crypto/vectors
```

| Script | Writes | Needs |
|---|---|---|
| `generate.py` | The SHA-256 files, and `manifest.txt` | Python 3, standard library only |
| `run.sh` | The Keccak-256, HMAC, HKDF, AES, secp256k1, ChaCha20-Poly1305, X25519, P-256, SHA-512 and Ed25519 files, and `manifest-primitives.txt`; the BLS12-381 files, and `manifest-bls.txt`; the KZG files, and `manifest-kzg.txt` | Docker; it runs `primitives.py`, `bls.py` and `kzg.py` in the image of [platform/linux/Dockerfile](../../platform/linux/Dockerfile) |

Each manifest lists each file, its case count and its SHA-256.

`run.sh` keeps its downloads in `sources/`, the libsecp256k1 build, the vector folders of cryptography-specs and the Python environment in the output folder, so a second run downloads and builds nothing again.

| Reference | Pin |
|---|---|
| libsecp256k1 | [v0.8.0](https://github.com/bitcoin-core/secp256k1/tree/6e2c8bc4ecdc6e71dbe7a368f360d8d453ce435d), built with CMake and the ECDH module |
| `cryptography` | 50.0.2 (OpenSSL 4.0.3), with `cffi` 2.1.1 and `pycparser` 3.12, by hash in [requirements.txt](requirements.txt) |
| Keccak | `CompactFIPS202.py` at [XKCP@d20c8fc](https://github.com/XKCP/XKCP/tree/d20c8fcaecc543f816a0721d0dfc13b4cf27c14d) |
| `py_arkworks_bls12381` | 0.5.0, with `pyyaml` 6.0.3, by hash in [requirements.txt](requirements.txt) |
| cryptography-specs | [v0.3.0](https://github.com/ethereum/cryptography-specs/tree/bb6dfe55198243682bc2eaf94611af2dbce1be6f/tests/cryptography), the folders `bls`, `hash_to_curve` and `kzg`, and `EthLib/Cryptography/Kzg/TrustedSetupData.lean`, fetched with git |

`primitives.py` and `bls.py` stop when a reference disagrees with an official result that they use.

## SHA-256 files

| File | Source | Cases |
|---|---|---|
| `acvp-aft.bin` | NIST ACVP SHA2-256 1.0, functional tests | Messages of 215 to 1518 bytes |
| `acvp-mct.bin` | NIST ACVP SHA2-256 1.0, Monte Carlo test (alternate) | One seed, 100 digests |
| `acvp-ldt.bin` | NIST ACVP SHA2-256 1.0, large data tests | Messages of 1, 2, 4 and 8 GiB |
| `cavp-short.bin` | NIST CAVP `SHA256ShortMsg.rsp` | Messages of 0 to 64 bytes |
| `cavp-long.bin` | NIST CAVP `SHA256LongMsg.rsp` | Messages of 163 to 6400 bytes |
| `cavp-monte.bin` | NIST CAVP `SHA256Monte.rsp` | One seed, 100 digests |
| `boundary.bin` | Python `hashlib.sha256` | Every length from 0 to 512 bytes |

## SHA-256 file format

All numbers are unsigned 8-byte little-endian integers.

Each file starts with the 8 bytes `SHA256V1`, then `kind`, then the number of cases. The cases follow.

| `kind` | One case |
|---|---|
| 1, message | `length`, then `length` message bytes, then the 32-byte digest. |
| 2, Monte Carlo | `variant`, then `seed length`, then the seed bytes, then `count`, then `count` digests of 32 bytes. `variant` 1 is the CAVP SHAVS Monte test and `variant` 2 is the ACVP alternate Monte Carlo test. |
| 3, large message | `content length`, then the content bytes, then `full length`, then the 32-byte digest. The message is the content repeated to `full length` bytes. |

## Primitive files

| File | Source | Functions |
|---|---|---|
| `keccak-generated.bin` | Generated messages, `CompactFIPS202.py` | `crypto_keccak256` |
| `hmac-wycheproof.bin` | Wycheproof `hmac_sha256_test.json`, valid cases | `crypto_hmac_sha256` |
| `hmac-generated.bin` | Generated keys and messages, `cryptography` | `crypto_hmac_sha256` |
| `hkdf-wycheproof.bin` | Wycheproof `hkdf_sha256_test.json` | `crypto_hkdf_extract`, `crypto_hkdf_expand` |
| `hkdf-generated.bin` | Generated cases, `cryptography` | `crypto_hkdf_extract`, `crypto_hkdf_expand` |
| `aes-kat.bin` | NIST `KAT_AES.zip`, the 128-bit ECB known answers | `crypto_aes128_ctr` |
| `aes-ctr-generated.bin` | Generated cases, `cryptography` | `crypto_aes128_ctr` |
| `gcm-cavp.bin` | NIST `gcmtestvectors.zip`, 128-bit keys, 96-bit IVs, 128-bit tags | `crypto_aes128_gcm_ae`, `crypto_aes128_gcm_ad` |
| `gcm-wycheproof.bin` | Wycheproof `aes_gcm_test.json`, the same sizes | `crypto_aes128_gcm_ae`, `crypto_aes128_gcm_ad` |
| `gcm-generated.bin` | Generated cases and flipped bits, `cryptography` | `crypto_aes128_gcm_ae`, `crypto_aes128_gcm_ad` |
| `secp256k1-generated.bin` | Generated keys, points, hashes and signatures, libsecp256k1 | the 5 secp256k1 functions |
| `ecdsa-wycheproof.bin` | Wycheproof `ecdsa_secp256k1_sha256_p1363_test.json` | `crypto_secp256k1_verify` |
| `ecdh-wycheproof.bin` | Wycheproof `ecdh_secp256k1_test.json` | `crypto_secp256k1_ecdh` |
| `devp2p.bin` | devp2p `discv5-wire-test-vectors.md` and `enr.md` | ECDH, HKDF, sign, verify, GCM, public key, decompress, Keccak-256 |
| `chacha20-poly1305-rfc.bin` | RFC 8439 sections 2.8.2 and A.5 | `crypto_chacha20_aead_encrypt`, `crypto_chacha20_aead_decrypt` |
| `chacha20-poly1305-wycheproof.bin` | Wycheproof `chacha20_poly1305_test.json` | `crypto_chacha20_aead_encrypt`, `crypto_chacha20_aead_decrypt` |
| `chacha20-poly1305-generated.bin` | Generated cases and flipped bits, `cryptography` | `crypto_chacha20_aead_encrypt`, `crypto_chacha20_aead_decrypt` |
| `poly1305-rfc.bin` | RFC 8439 sections 2.5.2 and A.3 | `crypto_poly1305_mac` |
| `poly1305-generated.bin` | Generated keys and messages, `cryptography` | `crypto_poly1305_mac` |
| `x25519-rfc.bin` | RFC 7748 sections 5.2 and 6.1 | `crypto_x25519` |
| `x25519-wycheproof.bin` | Wycheproof `x25519_test.json` | `crypto_x25519` |
| `x25519-generated.bin` | Generated scalars and points, `cryptography` | `crypto_x25519` |
| `p256-rfc6979.bin` | RFC 6979 section A.2.5, SHA-256 | `crypto_p256_public_key`, `crypto_p256_sign`, `crypto_p256_verify` |
| `p256-cavp.bin` | NIST `186-4ecdsatestvectors.zip`: `KeyPair.rsp`, `PKV.rsp`, `SigGen.rsp`, `SigVer.rsp`, P-256 | `crypto_p256_public_key`, `crypto_p256_sign`, `crypto_p256_verify` |
| `p256-wycheproof.bin` | Wycheproof `ecdsa_secp256r1_sha256_p1363_test.json` | `crypto_p256_verify` |
| `p256-generated.bin` | Generated keys, hashes, signatures and points, `cryptography` | `crypto_p256_public_key`, `crypto_p256_sign`, `crypto_p256_verify` |
| `p256-rfc5903.bin` | RFC 5903 section 8.1 | `crypto_p256_public_key`, `crypto_p256_ecdh` |
| `p256-ecdh-cavp.bin` | NIST `ecccdhtestvectors.zip`: `KAS_ECC_CDH_PrimitiveTest.txt`, P-256 | `crypto_p256_ecdh` |
| `p256-ecdh-wycheproof.bin` | Wycheproof `ecdh_secp256r1_ecpoint_test.json` | `crypto_p256_ecdh` |
| `p256-ecdh-generated.bin` | Generated keys and points, `cryptography` | `crypto_p256_ecdh` |
| `sha512-cavp.bin` | NIST `shabytetestvectors.zip`: `SHA512ShortMsg.rsp` and `SHA512LongMsg.rsp` | the 4 SHA-512 functions |
| `sha512-generated.bin` | Generated messages, Python `hashlib` | the 4 SHA-512 functions |
| `ed25519-rfc8032.bin` | RFC 8032 section 7.1 | the 3 Ed25519 functions |
| `ed25519-wycheproof.bin` | Wycheproof `ed25519_test.json` | `crypto_ed25519_verify` |
| `ed25519-generated.bin` | Generated keys, messages, signatures and public keys, `cryptography` | the 3 Ed25519 functions |
| `bls-official.bin` | cryptography-specs `tests/cryptography/bls` (all but `aggregate_verify`) and `tests/cryptography/hash_to_curve` | the 16 BLS12-381 functions |
| `bls-generated.bin` | Generated keys, messages, signatures, encodings and DSTs, `py_arkworks_bls12381` and the steps of the spec | the 16 BLS12-381 functions |
| `kzg-official.bin` | The trusted setup of `TrustedSetupData.lean`, then cryptography-specs `tests/cryptography/kzg` | the 13 KZG functions |
| `kzg-generated.bin` | Trusted setups with a list of the wrong length or a point that does not decompress | `crypto_kzg_trusted_setup_of_bytes` |

The pins of each source are in the document of its functions in [docs/reference/](../../docs/reference/).

## Primitive file format

All numbers are unsigned 8-byte little-endian integers. A blob is its length, then its bytes.

Each file starts with the 8 bytes `CRYPTOV2`, then the number of cases. Each case is its `kind`, a blob with its name, then the fields of its kind.

| `kind` | Fields |
|---|---|
| 1, Keccak-256 | blob message, 32-byte digest |
| 2, HMAC | blob key, blob message, 32-byte MAC |
| 3, HKDF | blob salt, blob IKM, blob info, `length`, `status`, 32-byte PRK, blob OKM |
| 4, CTR | 16-byte key, 16-byte counter block, blob input, blob output |
| 5, GCM | 16-byte key, 12-byte IV, blob AAD, blob plaintext, blob sealed (C and T), `status` |
| 6, public key | 32-byte private key, `status`, 33-byte public key |
| 7, decompress | 33-byte public key, `status`, 64-byte point |
| 8, ECDH | 33-byte public key, 32-byte private key, `status`, 33-byte secret |
| 9, sign | 32-byte private key, 32-byte hash, `status`, 64-byte signature |
| 10, verify | 33-byte public key, 32-byte hash, 64-byte signature, `status`, `valid` |
| 11, ChaCha20-Poly1305 | 32-byte key, 12-byte nonce, blob AAD, blob plaintext, blob sealed (C and T), `status` |
| 12, X25519 | 32-byte scalar, 32-byte u, `status`, 32-byte result |
| 13, P-256 public key | 32-byte private key, `status`, 65-byte public key |
| 14, P-256 sign | 32-byte private key, 32-byte hash, `status`, 64-byte signature |
| 15, P-256 verify | 65-byte public key, 32-byte hash, 64-byte signature, `status`, `valid` |
| 16, Poly1305 | 32-byte key, blob message, 16-byte tag |
| 17, SHA-512 | blob message, 64-byte digest |
| 18, Ed25519 public key | 32-byte private key, 32-byte public key |
| 19, Ed25519 sign | 32-byte private key, blob message, 64-byte signature |
| 20, Ed25519 verify | 32-byte public key, blob message, 64-byte signature, `status`, `valid` |
| 21, P-256 ECDH | 65-byte public key, 32-byte private key, `status`, 32-byte secret |
| 22, BLS SkToPk | 32-byte secret key, `status`, 48-byte public key |
| 23, BLS sign | 32-byte secret key, blob message, `status`, 96-byte signature |
| 24, BLS verify | 48-byte public key, blob message, 96-byte signature, `valid` |
| 25, BLS aggregate | blob of 96-byte signatures, `status`, 96-byte signature |
| 26, BLS fast aggregate verify | blob of 48-byte public keys, blob message, 96-byte signature, `valid` |
| 27, BLS KeyValidate | 48-byte public key, `valid` |
| 28, BLS eth aggregate pubkeys | blob of 48-byte public keys, `status`, 48-byte public key |
| 29, BLS eth fast aggregate verify | blob of 48-byte public keys, blob message, 96-byte signature, `valid` |
| 30, G1 decode | 48 bytes, `status`, the 48 bytes of `crypto_bls_g1_compress` of the point |
| 31, G2 decode | 96 bytes, `status`, the 96 bytes of `crypto_bls_g2_compress` of the point |
| 32, G1 add | two 48-byte points, the 48-byte compressed sum |
| 33, G1 neg | 48-byte point, the 48-byte compressed negation |
| 34, expand_message_xmd | blob message, blob DST, `length`, `status`, blob uniform bytes |
| 35, hash to G2 | blob message, blob DST, `status`, 192-byte affine point |
| 36, KZG setup | blob of the G1 Lagrange points, blob of the G1 monomial points, blob of the G2 monomial points, `status` |
| 37, blob to commitment | 131072-byte blob, `status`, 48-byte commitment |
| 38, compute KZG proof | 131072-byte blob, 32-byte z, `status`, 48-byte proof, 32-byte y |
| 39, verify KZG proof | 48-byte commitment, 32-byte z, 32-byte y, 48-byte proof, `status`, `valid` |
| 40, compute blob proof | 131072-byte blob, 48-byte commitment, `status`, 48-byte proof |
| 41, verify blob proof | 131072-byte blob, 48-byte commitment, 48-byte proof, `status`, `valid` |
| 42, verify blob proof batch | blob of blobs, blob of 48-byte commitments, blob of 48-byte proofs, `status`, `valid` |
| 43, compute challenge | 131072-byte blob, 48-byte commitment, `status`, 32-byte challenge |
| 44, compute cells | 131072-byte blob, `status`, the 262144 bytes of the 128 cells |
| 45, compute cells and proofs | 131072-byte blob, `status`, the 128 cells, the 6144 bytes of the 128 proofs |
| 46, verify cell proof batch | blob of 48-byte commitments, blob of u64 cell indices, blob of 2048-byte cells, blob of 48-byte proofs, `status`, `valid` |
| 47, recover cells and proofs | blob of u64 cell indices, blob of 2048-byte cells, `status`, the 128 cells, the 128 proofs |
| 48, cell batch challenge | blob of 48-byte commitments, blob of u64 commitment indices, blob of u64 cell indices, blob of 2048-byte cells, blob of 48-byte proofs, `status`, 32-byte challenge |

- `status` is the status code the function must return. When it is not 0, the bytes after it are zero and are not compared.
- An HKDF case also tests Extract: its PRK is HMAC(salt, IKM).
- A GCM case with `status` 3 (`CRYPTO_GCM_FAIL`) tests only `crypto_aes128_gcm_ad`, and its plaintext is empty.
- A ChaCha20-Poly1305 case with `status` 6 (`CRYPTO_CHACHA20_POLY1305_FAIL`) tests only `crypto_chacha20_aead_decrypt`, and its plaintext is empty.
- The points of G1 add and G1 neg cases go through `crypto_bls_g1_decode` first; they are valid.
- A KZG setup case that decodes becomes the trusted setup of the KZG cases after it in its file.
- An official KZG case with no output gets the status of the first check of the spec that fails; `kzg.py` writes the checks out.
