import Proofs.ARM64.NativeProperties
import Proofs.ARM64.ImportedScheduledGuarantees
import Proofs.ARM64.ImportedConcurrentFrame
import Proofs.ARM64.ImportedScheduledReturn
import Proofs.ARM64.ImportedScheduledTiming
import Proofs.ARM64.ImportedPlatformProfile

/-!
Proposed native expected `equal` statement for the pointer-only ARM64 SHA-256
library entry. Unlike the older auxiliary Statement module this uses the pinned
imported ISA's actual loaded fetch/execute updates, bounded first RET, exact
transient observations and a phase-sensitive concurrent environment.

Entry facts are unchanged PermissionViewInputs: independent extent, truthful
layout/bytes, alignment, loading and semantic accessibility/separation. The
dynamic environment permits arbitrary unrelated progress and private stack
reuse outside its active allocation. No final result, execution or trace
equality is an entry condition. Model/hardware, primitive ABI, timing and
deployment assumptions are recorded in arm64-sha256-native-profile.md and its
linked model definitions. They are not physical instances asserted by this file.

The shared wrapper AND every proposition below, together with their relevant
semantic closure, need independent review and an externally selected immutable
pin. This candidate definition cannot itself authorize a checked target.
-/
namespace Crypto.ARM64.NativeRequirements
open Crypto.ARM64.Imported

def Concurrent : Prop :=
  ∀ (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList)
    (extent : Nat) (authority : Crypto.Baseline.Authority),
    PermissionViewInputs base s message extent authority →
    ∀ environment : DynamicEnvironment base s extent,
    ∃ call : ConcurrentCallCore base s message extent authority environment,
      ScheduledCallGuarantees base s message extent authority environment call ∧
      ConcurrentReadonlyBorrows base s message extent authority environment call ∧
      runScheduledToReturn (program base) environment.advance
        (512 + 4000 * ((message.bytes.size + 8) / 64 + 1)) 0 (logicalState base s message) =
        some (call.schedule.actualOut, call.observations)

/-- Actual local-instruction costs under two independently permitted schedules.
Environment work and waiting are outside the declared local cost model. -/
def ScheduledTiming : Prop :=
  ∀ (profile : TimingProfile), profile.ImageCovered →
    ∀ (base : BitVec 64) (left right : Arm64.State)
      (leftMessage rightMessage : Crypto.Reference.ByteList) (leftExtent rightExtent : Nat)
      (leftAuthority rightAuthority : Crypto.Baseline.Authority),
    PermissionViewInputs base left leftMessage leftExtent leftAuthority →
    PermissionViewInputs base right rightMessage rightExtent rightAuthority →
    SameDisclosureContext left right leftMessage rightMessage →
    ∀ (leftEnvironment : DynamicEnvironment base left leftExtent)
      (rightEnvironment : DynamicEnvironment base right rightExtent)
      (leftCall : ConcurrentCallCore base left leftMessage leftExtent leftAuthority leftEnvironment)
      (rightCall : ConcurrentCallCore base right rightMessage rightExtent rightAuthority rightEnvironment),
    ∃ cost,
      runScheduledWordsCosted profile leftEnvironment.advance 0
        (wholeCallCode (BitVec.ofNat 64 leftMessage.bytes.size)) (logicalState base left leftMessage) =
          some (leftCall.schedule.actualOut, cost) ∧
      runScheduledWordsCosted profile rightEnvironment.advance 0
        (wholeCallCode (BitVec.ofNat 64 rightMessage.bytes.size)) (logicalState base right rightMessage) =
          some (rightCall.schedule.actualOut, cost)

def requirements : Crypto.Baseline.Stateless.Requirements where
  referenceAndSafety := ReferenceConformance ∧ Serial
  concurrentExecution := Concurrent
  publicControlAndAddresses := PublicTrace
  permittedDisclosures := Disclosures
  instructionTiming := Timing ∧ ScheduledTiming
  leafAndEffects := LeafEffects

theorem concurrent : Concurrent := by
  intro base s message extent authority entry environment
  obtain ⟨call, guarantees⟩ := sha256_scheduled_guarantees base s message extent authority entry environment
  exact ⟨call, guarantees, concurrent_call_readonly_borrows base s message extent authority entry environment call,
    concurrent_call_evaluated base s message extent authority environment call⟩

theorem scheduledTiming : ScheduledTiming := paired_scheduled_modeled_cost_equal

end Crypto.ARM64.NativeRequirements
