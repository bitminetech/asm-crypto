# ARM64 round model

Model: [ARM64Round.lean](../../lean/Models/ARM64Round.lean).

- The model executes the compression round at offsets `0x124` through `0x198`.
- The fragment contains 30 instructions.
- The loop counter update and branch follow the fragment.
- The recorded program is [ARM64Program.lean](../../lean/Models/ARM64Program.lean).
- [check_arm64_artifacts.py](../../tests/runner/check_arm64_artifacts.py) compares that image with Linux, Windows and macOS objects and archives.
- The full text image is 896 bytes, including alignment and constants.
- Its SHA-256 is `8c341cfdb8ad9f28a3c84008c8993ba79f1059ac316539aee04885fcbb174744`.

## Claims

- [`round_computes`](../../lean/Proofs/ARM64/Round.lean) proves the fragment's working words have the FIPS-shaped round result.
- `round_observations` proves that the fragment preserves memory and SP, advances PC by 120 bytes and reads its two four-byte words.
- [Constants.lean](../../lean/Proofs/ARM64/Constants.lean) proves that the image's constants match the imported reference.
- These supporting theorems do not establish the complete function's `equal` baseline.
- [verification-scope.json](../../lean/verification-scope.json) records the remaining obligations.

## Assumptions

- The local decoder and instruction meanings require independent review against Armv8.0-A before use in a checked `equal` claim.
- The supported instructions are 32-bit ADD with LSL, logical shifted-register operations, EXTR and scaled-register LDR W with UXTX.
- Unsupported instruction encodings return failure in the model.
- Memory is a total map from 64-bit addresses to bytes.
- Address arithmetic wraps modulo 2^64.
- A full entry and safety proof must establish valid, separated, non-wrapping accessible regions for the accesses.
- The model does not implement paging, access faults or physical instruction timing.
- The extraction and archive comparison code is trusted.
- Object and archive identity does not establish final linking or runtime loading.
- Correspondence between the imported Lean FIPS transcription and the English standard requires review.
