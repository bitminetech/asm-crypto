# Imported ARM64 model

The pinned upstream AArch64 instruction semantics used for the ARM64 proofs.

## Source

- Model: [code-verification@b0f729a](https://github.com/google-deepmind/code-verification/tree/b0f729accbc21a0413e7ca4e1da43fa45b5f2e1b/arm64-semantics/Arm64/Trusted/ISA).
- Local import: [ARM64.lean](../../lean/Models/ARM64.lean).
- Used by: the supporting ARM64 SHA-256 proofs registered in [verification-scope.json](../../lean/verification-scope.json).
- The imported source stays unchanged in the pinned submodule.
- The Lake build adapter selects the ISA and syscall dependency closure without importing upstream proof automation.
- The program has no external or override hooks; supervisor calls fail closed.
- `runToReturn` fetches instructions from memory and returns only after a non-faulting `RET`.
- The `runWords` proof helper executes recorded words without fetching them; its fragment proofs require a separate connection to `runToReturn`.

## Assumptions

- Instruction meanings, decoder and correspondence to the Armv8.0-A profile: trusted upstream model.
- The upstream model describes single-thread EL0 execution; concurrency needs a separate interference and ownership proof.
- The upstream Linux process and loader model does not establish Windows or macOS loading and ABI obligations.
- The pinned Lean 4.29.1 kernel checks the imported ISA closure; upstream targets Lean 4.34.0.
- Full-call proofs must establish the model's permission, alignment, address-range and SP guards from the declared entry conditions.
- Physical timing and microarchitectural side channels require their own named models.
- The current supporting proofs do not establish the complete `equal` baseline.
