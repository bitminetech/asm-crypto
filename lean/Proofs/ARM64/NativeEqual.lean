import Proofs.ARM64.NativeStatement

/-!
Candidate complete native model baseline. This theorem proves the registered
candidate statement, not its independent approval. A checked §8 verification
mark additionally requires externally pinned expected semantics, fresh replay,
axiom audit and artifact/profile validation for each recorded target.
-/
namespace Crypto.ARM64.sha256

theorem equal : Crypto.Baseline.Stateless.Equal NativeRequirements.requirements := by
  exact ⟨⟨NativeRequirements.referenceConformance, NativeRequirements.serial⟩, NativeRequirements.concurrent,
    NativeRequirements.publicTrace, NativeRequirements.disclosures,
    ⟨NativeRequirements.timing, NativeRequirements.scheduledTiming⟩, NativeRequirements.leafEffects⟩

end Crypto.ARM64.sha256
