import Proofs.ARM64.NativeStatement

/-!
Proves ARM64 SHA-256 satisfies the complete `equal` baseline under the
documented entry and environment assumptions.
-/
namespace Crypto.ARM64.sha256

theorem equal : Crypto.Baseline.Stateless.Equal NativeRequirements.requirements := by
  exact ⟨⟨NativeRequirements.referenceConformance, NativeRequirements.serial⟩, NativeRequirements.concurrent,
    NativeRequirements.publicTrace, NativeRequirements.disclosures,
    ⟨NativeRequirements.timing, NativeRequirements.scheduledTiming⟩, NativeRequirements.leafEffects⟩

end Crypto.ARM64.sha256
