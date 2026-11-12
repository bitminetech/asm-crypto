# asm-crypto

Assembly implementation of cryptographic primitives for Ethereum. It holds only the primitives that a production Ethereum consensus client needs. Today this is SHA-256, as specified by [FIPS 180-4](https://doi.org/10.6028/NIST.FIPS.180-4).

Architecture: [asm-standard@a289a70](https://github.com/bitminetech/asm-standard/blob/a289a7025ad2e78ebf3f31db84c60d5fa43ac6db/ARCHITECTURE.md)

## Pins

| Dependency | Version |
|---|---|
| Original reference spec | SHA-256 in [FIPS 180-4](https://doi.org/10.6028/NIST.FIPS.180-4), August 2015. |
| Vector generation | NIST ACVP SHA2-256 1.0: `gen-val/json-files/SHA2-256-1.0/internalProjection.json` at [ACVP-Server@975de31](https://github.com/usnistgov/ACVP-Server/tree/975de31eb83d87039ec88934fdc47d8c312b892d) (release v1.1.0.43), SHA-256 `a7e0bf4f5c661f1787b343bf3ae1a809b1e62f8fb2c8a627791510d03a570a6c`. NIST CAVP byte vectors: [`shabytetestvectors.zip`](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip), SHA-256 `929ef80b7b3418aca026643f6f248815913b60e01741a44bba9e118067f4c9b8`. Boundary vectors for every length from 0 to 512 bytes, with expected results from Python `hashlib.sha256`. [tests/generator/](tests/generator/) fetches, checks and converts them; it uses no seed or options. |
| Build tools | LLVM 23.1.5 (`clang`, `llvm-mc`, `lld`) for every target. [llvm-mingw 20261104](https://github.com/mstorsjo/llvm-mingw/releases/tag/20261104) (LLVM 23.1.5) for the Windows test runner. |
| Target profiles | Baseline instructions only, with no extensions and no feature selection: x86-64 (x86-64-v1), ARM64 (Armv8.0-A) and RISC-V (RV64GC). The library makes no OS calls, so it needs no OS or API version. |
| Environment boundaries | None. The library makes no OS calls. |
| Stack limit | Each function uses at most 1024 bytes of stack, including its callees. This is less than one 4 KiB page, so no target needs stack probing. The library makes no native calls and has no handlers. |

## Dependencies

- None.

## Integration

Callers use the common-ABI entry point of each function, as listed in [include/crypto.h](include/crypto.h). The functions are effect-free and have no resource context, startup, wakeup, actions, events or shutdown. The library provides no crash-recovery or persistence guarantees.
