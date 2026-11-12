# asm-crypto

Cryptographic primitives for Ethereum, in assembly.

Standard: [asm-standard@90ddb72](https://github.com/bitminetech/asm-standard/blob/90ddb728ec7070b9e1ce4dab44dd48050c3464fd/ARCHITECTURE.md)

## Reference

| File | Covers |
|---|---|
| [docs/reference/sha-256.md](docs/reference/sha-256.md) | SHA-256 |
| [include/crypto.inc](include/crypto.inc) | Constants |

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
| Stack per call | At most 1024 bytes, callees included |

## Lean

| Item | Value |
|---|---|
| Lean | 4.29.1, pinned in [lean-toolchain](lean-toolchain) |
| Imported proofs | [fips-180-4-lean@0018b08](https://github.com/remix7531/fips-180-4-lean/tree/0018b08f3458553ad511e92a96336979c1e0c45a), GPL-3.0-or-later |
| ARM64 ISA | [code-verification@b0f729a](https://github.com/google-deepmind/code-verification/tree/b0f729accbc21a0413e7ca4e1da43fa45b5f2e1b/arm64-semantics/Arm64/Trusted/ISA), Apache-2.0; pinned submodule at [lean/Imports/arm64](lean/Imports/arm64), unchanged ISA source imported by the `ImportedARM64` library |
| Transitive dependencies | Exact commits in [lake-manifest.json](lake-manifest.json) |
| ARM64 round model | [docs/models/arm64-round.md](docs/models/arm64-round.md) |
| Supporting proof checks | [tests/runner/check_supporting_proofs.sh](tests/runner/check_supporting_proofs.sh) |
| Verification scope | [lean/verification-scope.json](lean/verification-scope.json) |
