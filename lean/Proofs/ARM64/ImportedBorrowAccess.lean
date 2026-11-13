import Proofs.Borrow
import Proofs.ARM64.ImportedSafeCall

/-!
Connect actual SHA-256 fetch/data observations to shared input/image borrows
and exclusive output/stack borrows. Environment events may read immutable
shared bytes and make unrelated progress, but cannot race writable borrows or
release/change protection of borrowed regions. Native interleaving simulation
and physical ownership/address correspondence remain separate obligations.
-/
namespace Crypto.ARM64.Imported
open Crypto.Baseline

def shaBorrowScope (base : BitVec 64) (s : Arm64.State) (extent : Nat) : BorrowScope where
  shared p := (callerInput s extent).Contains p ∨ (callerImage base).Contains p
  exclusive p := (callerOutput s).Contains p ∨ (callerStack s).Contains p

def observedAccessEvent (observation : InstructionObservation) : AccessEvent where
  reads p := (∃ i, i < 4 ∧ p = observation.pc + BitVec.ofNat 64 i) ∨
    ∃ access ∈ observation.accesses, access.write = false ∧
      ∃ i, i < access.bytes ∧ p = access.address + BitVec.ofNat 64 i
  writes p := ∃ access ∈ observation.accesses, access.write = true ∧
    ∃ i, i < access.bytes ∧ p = access.address + BitVec.ofNat 64 i
  releases _ := False
  changesProtection _ := False

theorem view_read_borrowed (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) (p : BitVec 64)
    (read : permissionReadFootprint base s message p) : (shaBorrowScope base s extent).protected p := by
  rcases read with header | payload | image | stack
  · exact Or.inl (Or.inl (view_header_subset s extent entry.headerFits p header))
  · exact Or.inl (Or.inl (view_payload_subset base s message extent authority entry p payload))
  · exact Or.inl (Or.inr image)
  · exact Or.inr (Or.inr stack)

theorem observed_call_access (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (out : Arm64.State) (observations : List InstructionObservation)
    (result : LogicalCallResult base s message authority out observations)
    (observation : InstructionObservation) (member : observation ∈ observations) :
    CallAccess (shaBorrowScope base s extent) (observedAccessEvent observation) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p read
    rcases read with ⟨i, bound, address⟩ | ⟨access, present, writing, i, bound, address⟩
    · subst p
      exact Or.inl (Or.inr (result.fetches observation member i bound))
    · subst p
      have inside := result.confined observation member access present i bound
      have readFootprint : permissionReadFootprint base s message (access.address + BitVec.ofNat 64 i) := by
        simpa only [writing, Bool.false_eq_true, ↓reduceIte] using inside
      exact view_read_borrowed base s message extent authority entry _ readFootprint
  · rintro p ⟨access, present, writing, i, bound, address⟩
    subst p
    have inside := result.confined observation member access present i bound
    simpa only [writing, ↓reduceIte] using inside
  · intro p impossible; exact impossible
  · intro p impossible; exact impossible

theorem sha_borrows_separated (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) :
    ∀ p, ¬((shaBorrowScope base s extent).exclusive p ∧ (shaBorrowScope base s extent).shared p) := by
  rintro p ⟨output | stack, input | image⟩
  · exact entry.outputInput p ⟨output, input⟩
  · exact entry.outputImage p ⟨output, image⟩
  · exact entry.stackInput p ⟨stack, input⟩
  · exact entry.stackImage p ⟨stack, image⟩

theorem observed_environment_race_free (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (out : Arm64.State) (observations : List InstructionObservation)
    (result : LogicalCallResult base s message authority out observations)
    (observation : InstructionObservation) (member : observation ∈ observations)
    (environment : AccessEvent)
    (allowed : EnvironmentAccess (shaBorrowScope base s extent) environment) :
    ¬DataRace (observedAccessEvent observation) environment :=
  borrow_accesses_race_free _ _ _ (observed_call_access base s message extent authority entry out observations result observation member) allowed

end Crypto.ARM64.Imported
