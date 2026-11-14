# asm-crypto

Cryptographic primitives for Ethereum, in assembly.

SHA-256 for SSZ; the primitives of discv5 and ENR: Keccak-256, HMAC and HKDF with SHA-256, AES-128 in CTR and GCM, and secp256k1; and the primitives of libp2p: X25519, ChaCha20-Poly1305 (with Poly1305 on its own), ECDSA P-256, SHA-512 and Ed25519.

Standard: [asm-standard@2a19d3f](https://github.com/bitminetech/asm-standard/blob/2a19d3f7fa737af1c01720b6e891703e53a682aa/ARCHITECTURE.md)

## Reference

| File | Covers |
|---|---|
| [docs/reference/sha-256.md](docs/reference/sha-256.md) | SHA-256 |
| [docs/reference/keccak-256.md](docs/reference/keccak-256.md) | Keccak-256 |
| [docs/reference/hmac.md](docs/reference/hmac.md) | HMAC-SHA-256 |
| [docs/reference/hkdf.md](docs/reference/hkdf.md) | HKDF-SHA-256 |
| [docs/reference/aes.md](docs/reference/aes.md) | AES-128 |
| [docs/reference/ctr.md](docs/reference/ctr.md) | AES-128-CTR |
| [docs/reference/gcm.md](docs/reference/gcm.md) | AES-128-GCM |
| [docs/reference/secp256k1.md](docs/reference/secp256k1.md) | secp256k1 |
| [docs/reference/chacha20.md](docs/reference/chacha20.md) | ChaCha20 |
| [docs/reference/poly1305.md](docs/reference/poly1305.md) | Poly1305 |
| [docs/reference/chacha20-poly1305.md](docs/reference/chacha20-poly1305.md) | ChaCha20-Poly1305 |
| [docs/reference/x25519.md](docs/reference/x25519.md) | X25519 |
| [docs/reference/p256.md](docs/reference/p256.md) | P-256 |
| [docs/reference/sha-512.md](docs/reference/sha-512.md) | SHA-512 |
| [docs/reference/ed25519.md](docs/reference/ed25519.md) | Ed25519 |
| [include/crypto.inc](include/crypto.inc) | Constants: shared, SHA-256, the key status codes |
| [include/keccak.inc](include/keccak.inc) | Constants: Keccak-256 |
| [include/hmac.inc](include/hmac.inc) | Constants: HMAC and HKDF |
| [include/aes.inc](include/aes.inc) | Constants: AES, CTR and GCM |
| [include/secp256k1.inc](include/secp256k1.inc) | Constants: secp256k1 |
| [include/chacha20.inc](include/chacha20.inc) | Constants: ChaCha20, Poly1305 and ChaCha20-Poly1305 |
| [include/x25519.inc](include/x25519.inc) | Constants: X25519 |
| [include/p256.inc](include/p256.inc) | Constants: P-256 |
| [include/sha512.inc](include/sha512.inc) | Constants: SHA-512 |
| [include/ed25519.inc](include/ed25519.inc) | Constants: Ed25519 |

## Targets

| OS | ISAs |
|---|---|
| Linux | x86-64, ARM64, RISC-V |
| Windows | x86-64, ARM64 |
| macOS | x86-64, ARM64 |

## Build tools

| Used for | Tool |
|---|---|
| Library | LLVM 23.1.5, official release (`clang`, `llvm-ar`, `lld`) |
| Windows test runner | [llvm-mingw 20261104](https://github.com/mstorsjo/llvm-mingw/releases/tag/20261104) (LLVM 23.1.5) |
| macOS test runner | The host Xcode clang, because it needs the macOS SDK |
| Build image | [platform/linux/Dockerfile](platform/linux/Dockerfile) on `debian:trixie-slim@sha256:a72b4433de1cf7d6bae0c4cee74d0547f58601a643b3375f070c51600d63b6b2` |

## Tests

| Item | Location |
|---|---|
| Export and frame check | [platform/check.py](platform/check.py) |
| Vector generator | [tests/generator/](tests/generator/) |
| Test runner | [tests/runner/](tests/runner/) |

## Target profile

| ISA | Instructions |
|---|---|
| x86-64 | x86-64-v1 |
| ARM64 | Armv8.0-A |
| RISC-V | RV64GC |

| Item | Value |
|---|---|
| macOS objects | Marked for macOS 11.0 or later |

## Stack

| Item | Value |
|---|---|
| Stack per call | At most 4096 bytes, callees included |

## Lean

| Item | Value |
|---|---|
| Lean | 4.29.1, pinned in [lean-toolchain](lean-toolchain) |
| Imported proofs | [fips-180-4-lean@0018b08](https://github.com/remix7531/fips-180-4-lean/tree/0018b08f3458553ad511e92a96336979c1e0c45a), GPL-3.0-or-later |
| ARM64 ISA | [code-verification@b0f729a](https://github.com/google-deepmind/code-verification/tree/b0f729accbc21a0413e7ca4e1da43fa45b5f2e1b/arm64-semantics/Arm64/Trusted/ISA), Apache-2.0; pinned submodule at [lean/Imports/arm64](lean/Imports/arm64), unchanged ISA source imported by the `ImportedARM64` library |
| Transitive dependencies | Exact commits in [lake-manifest.json](lake-manifest.json) |
| Imported ARM64 model | [docs/models/arm64-imported.md](docs/models/arm64-imported.md) |
| ARM64 native proof profile | [docs/models/arm64-sha256-native-profile.md](docs/models/arm64-sha256-native-profile.md) |
| ARM64 round model | [docs/models/arm64-round.md](docs/models/arm64-round.md) |
| Supporting proof checks | [tests/runner/check_supporting_proofs.sh](tests/runner/check_supporting_proofs.sh) |
| Verification scope | [lean/verification-scope.json](lean/verification-scope.json) |
