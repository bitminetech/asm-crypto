# Vector generation

Two scripts write binary case files to one output folder, which must be outside this repo. Both check the SHA-256 pin of every file they download.

```bash
python3 -I tests/generator/generate.py ~/.cache/asm-crypto/vectors
```

```bash
tests/generator/run.sh ~/.cache/asm-crypto/vectors
```

| Script | Writes | Needs |
|---|---|---|
| `generate.py` | The SHA-256 files, and `manifest.txt` | Python 3, standard library only |
| `run.sh` | The Keccak-256, HMAC, HKDF, AES and secp256k1 files, and `manifest-primitives.txt` | Docker; it runs `primitives.py` in the image of [platform/linux/Dockerfile](../../platform/linux/Dockerfile) |

Each manifest lists each file, its case count and its SHA-256.

`run.sh` keeps its downloads in `sources/`, the libsecp256k1 build and the Python environment in the output folder, so a second run downloads and builds nothing again.

| Reference | Pin |
|---|---|
| libsecp256k1 | [v0.8.0](https://github.com/bitcoin-core/secp256k1/tree/6e2c8bc4ecdc6e71dbe7a368f360d8d453ce435d), built with CMake and the ECDH module |
| `cryptography` | 50.0.2 (OpenSSL), with `cffi` 2.1.1 and `pycparser` 3.12, by hash in [requirements.txt](requirements.txt) |
| Keccak | `CompactFIPS202.py` at [XKCP@d20c8fc](https://github.com/XKCP/XKCP/tree/d20c8fcaecc543f816a0721d0dfc13b4cf27c14d) |

`primitives.py` stops when a reference disagrees with an official result that it uses.

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

- `status` is the status code the function must return. When it is not 0, the bytes after it are zero and are not compared.
- An HKDF case also tests Extract: its PRK is HMAC(salt, IKM).
- A GCM case with `status` 3 (`CRYPTO_GCM_FAIL`) tests only `crypto_aes128_gcm_ad`, and its plaintext is empty.
