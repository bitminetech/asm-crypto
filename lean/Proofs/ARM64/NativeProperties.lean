import Proofs.StatelessBaseline
import Proofs.Reference
import Proofs.ARM64.ImportedSerialContract
import Proofs.ARM64.ImportedDisclosure
import Proofs.ARM64.ImportedTiming
import Proofs.ARM64.ImportedBorrowAccess

/-!
Native baseline obligations for the single pointer-only crypto_sha256 entry.
The semantic inputs are the caller's ByteList bytes, never capacity, room or
old output/stack contents. Pointers, offset, length, SP and return address are
public. Only digest/status are released; temporary registers and private stack
are not public observations. Callers must protect those residual secrets and
their own preparation/invocation/result-use policy.

These definitions are proposed expected-statement dependencies, not an
independently authenticated verification claim. The ISA, byte loading and
physical timing correspondence retain their explicitly documented trust laws.
-/
namespace Crypto.ARM64.NativeRequirements

open Crypto.ARM64.Imported

def ReferenceConformance : Prop :=
  ∀ (message : Crypto.Reference.ByteList) (bound : message.bytes.size < 2 ^ 61),
    Crypto.Reference.MatchesFIPS message (Crypto.Reference.sha256 message).2 bound ∧
    (Crypto.Reference.sha256 message).1 = 0

def Serial : Prop :=
  ∀ (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList)
    (extent : Nat) (authority : Crypto.Baseline.Authority) (fpcr : BitVec 32),
    PermissionViewInputs base s message extent authority →
    ∃ out observations, SerialCallResult base s message extent authority fpcr out observations

def PublicTrace : Prop :=
  ∀ (base : BitVec 64) (left right : Arm64.State)
    (leftMessage rightMessage : Crypto.Reference.ByteList) (leftExtent rightExtent : Nat)
    (leftAuthority rightAuthority : Crypto.Baseline.Authority),
    PermissionViewInputs base left leftMessage leftExtent leftAuthority →
    PermissionViewInputs base right rightMessage rightExtent rightAuthority →
    SameDisclosureContext left right leftMessage rightMessage →
    ∀ leftOut rightOut leftObs rightObs,
    LogicalCallResult base left leftMessage leftAuthority leftOut leftObs →
    LogicalCallResult base right rightMessage rightAuthority rightOut rightObs →
    leftObs = rightObs ∧ PublicRelation .returned leftOut rightOut

def Disclosures : Prop :=
  ∀ (base : BitVec 64) (left right : Arm64.State)
    (leftMessage rightMessage : Crypto.Reference.ByteList) (leftExtent rightExtent : Nat)
    (leftAuthority rightAuthority : Crypto.Baseline.Authority),
    PermissionViewInputs base left leftMessage leftExtent leftAuthority →
    PermissionViewInputs base right rightMessage rightExtent rightAuthority →
    SameDisclosureContext left right leftMessage rightMessage →
    PublicPreBytesAgree left right leftMessage →
    (Crypto.Reference.sha256 leftMessage).2 = (Crypto.Reference.sha256 rightMessage).2 →
    ∀ leftOut rightOut leftObs rightObs,
    LogicalCallResult base left leftMessage leftAuthority leftOut leftObs →
    LogicalCallResult base right rightMessage rightAuthority rightOut rightObs →
    FinalByteObservationAgree left right leftOut rightOut leftMessage rightMessage

/-- A profile covers every concrete instruction and its costs depend only on
the actual public architectural observation. Physical conformance is a separate
primitive profile obligation, never a SHA execution/result premise. -/
def Timing : Prop :=
  ∀ (profile : TimingProfile), profile.ImageCovered →
    ∀ (base : BitVec 64) (left right : Arm64.State) (leftData rightData : ByteArray),
    CallInputs base left leftData → CallInputs base right rightData →
    SamePublicCall left right → leftData.size = rightData.size →
    ∃ leftOut rightOut observations cost,
      runToReturn (program base) (512 + 4000 * ((leftData.size + 8) / 64 + 1)) left = some leftOut ∧
      runToReturn (program base) (512 + 4000 * ((rightData.size + 8) / 64 + 1)) right = some rightOut ∧
      runWordsObserved (wholeCallCode (BitVec.ofNat 64 leftData.size)) left = some (leftOut, observations) ∧
      runWordsObserved (wholeCallCode (BitVec.ofNat 64 rightData.size)) right = some (rightOut, observations) ∧
      runWordsCosted profile (wholeCallCode (BitVec.ofNat 64 leftData.size)) left = some (leftOut, cost) ∧
      runWordsCosted profile (wholeCallCode (BitVec.ofNat 64 rightData.size)) right = some (rightOut, cost)

/-- The exact fetched domain excludes calls, syscalls, atomics and resource
operations. Its only recorded effects are finite reads/writes; no release or
protection change is generated. Together with bounded first-RET execution this
is the effect-free leaf case of the shared baseline. -/
def LeafEffects : Prop :=
  (∀ index : Fin 151, ∀ instruction,
    Arm64.decode Crypto.ARM64.imageWords[index.val]! = some instruction →
    Crypto.ARM64.CallFrame.Admissible instruction) ∧
  (∀ observation : InstructionObservation, ∀ p,
    ¬(observedAccessEvent observation).releases p ∧
    ¬(observedAccessEvent observation).changesProtection p)

theorem referenceConformance : ReferenceConformance := by
  intro message bound
  exact ⟨Crypto.Reference.sha256_matches_fips message bound, Crypto.Reference.sha256_status message⟩

theorem serial : Serial := sha256_serial_contract

theorem publicTrace : PublicTrace := by
  intro base left right leftMessage rightMessage leftExtent rightExtent leftAuthority rightAuthority
    leftEntry rightEntry context leftOut rightOut leftObs rightObs leftResult rightResult
  have publicInputs : SamePublicCall (logicalState base left leftMessage) (logicalState base right rightMessage) := by
    refine ⟨context.input, context.output, context.stack, context.link, ?_⟩
    change (logicalMemory base left leftMessage).read64 (left.readReg64 .x0 + 8#64) =
      (logicalMemory base right rightMessage).read64 (right.readReg64 .x0 + 8#64)
    rw [logicalMemory_read64, logicalMemory_read64, leftEntry.offsetValue, rightEntry.offsetValue, context.offset]
  exact sha256_observations_equal base (logicalState base left leftMessage) (logicalState base right rightMessage)
    leftMessage.bytes rightMessage.bytes
    (permission_view_inputs base left leftMessage leftExtent leftAuthority leftEntry)
    (permission_view_inputs base right rightMessage rightExtent rightAuthority rightEntry)
    publicInputs context.count leftOut rightOut leftObs rightObs leftResult.observed rightResult.observed

theorem disclosures : Disclosures := by
  intro base left right leftMessage rightMessage leftExtent rightExtent leftAuthority rightAuthority
    leftEntry rightEntry context publicBytes digestEqual leftOut rightOut leftObs rightObs leftResult rightResult
  exact logical_results_disclosure base left right leftOut rightOut leftMessage rightMessage
    leftExtent rightExtent leftAuthority rightAuthority leftObs rightObs leftEntry rightEntry
    context publicBytes digestEqual leftResult rightResult

theorem timing : Timing := sha256_modeled_cost_equal

theorem leafEffects : LeafEffects := by
  constructor
  · intro index instruction decoded
    exact scalar_admissible_image index instruction decoded
  · intro observation p
    exact ⟨id, id⟩

end Crypto.ARM64.NativeRequirements
