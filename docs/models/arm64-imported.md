# Imported ARM64 model

The pinned upstream AArch64 instruction semantics used for the ARM64 proofs.

## Source

- Model: [code-verification@b0f729a](https://github.com/google-deepmind/code-verification/tree/b0f729accbc21a0413e7ca4e1da43fa45b5f2e1b/arm64-semantics/Arm64/Trusted/ISA).
- Local import: [ARM64.lean](../../lean/Models/ARM64.lean).
- Used by: the ARM64 SHA-256 proofs registered in [verification-scope.json](../../lean/verification-scope.json).
- The imported source stays unchanged in the pinned submodule.
- The Lake build adapter selects the ISA and syscall dependency closure without importing upstream proof automation.
- The program has no external or override hooks; supervisor calls fail closed.
- `runToReturn` fetches instructions from memory and returns only after a non-faulting `RET`.
- The `runWords` proof helper executes recorded words without fetching them; its fragment proofs require a separate connection to `runToReturn`.

## Assumptions

- Instruction meanings, decoder and correspondence to the Armv8.0-A profile: trusted upstream model.
- The imported ISA describes single-thread EL0 execution; the local dynamic-environment proofs compose permitted interleavings.
- The native target profile supplies OS loading, ABI and unwind assumptions for Linux, Windows and macOS.
- The pinned Lean 4.29.1 kernel checks the imported ISA closure; upstream targets Lean 4.34.0.
- The full-call proofs derive permission, alignment, address-range and SP guards from the declared entry conditions.
- Physical timing and microarchitectural side channels require their own named models.
- [NativeEqual.lean](../../lean/Proofs/ARM64/NativeEqual.lean) assembles the complete `equal` baseline.
