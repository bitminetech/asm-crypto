import Proofs.ARM64.ImportedEntryInterference
import Proofs.ARM64.ImportedInterleavingPaths
import Proofs.ARM64.ImportedConfidentialCall

/-!
Rebase the serial witness after pre-allocation interference. Future stack
bytes and unrelated global state may have changed; only public CPU context,
static borrows and reserved accessibility are preserved. Full native execution
and its exact common access trace are then DERIVED from those entry facts.
-/
namespace Crypto.ARM64.Imported
open Crypto.Baseline

theorem initial_interference_public_context (base : BitVec 64) (s t : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (cpu : CPUProjection t = CPUProjection (logicalState base s message))
    (same : SameCellsOn (entryProtected base s extent) t.mem (logicalState base s message).mem) :
    SamePublicCall t (logicalState base s message) := by
  have context := entryCPUAgreement_of_projection (logicalState base s message) t cpu
  refine ⟨context.read .x0, context.read .x1, context.sp, context.read .x30, ?_⟩
  rw [context.read .x0]
  have cells := entry_input_cells base s t message extent authority entry same 8 8 (by have := entry.headerFits; omega)
  exact entry_read64_cells t.mem (logicalState base s message).mem _ cells

theorem rebased_native_call (base : BitVec 64) (s t : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (cpu : CPUProjection t = CPUProjection (logicalState base s message))
    (same : SameCellsOn (entryProtected base s extent) t.mem (logicalState base s message).mem)
    (stack : EntryStackGrants s t.mem)
    (safeOut : Arm64.State) (observations : List InstructionObservation)
    (safe : LogicalCallResult base s message authority safeOut observations) :
    ∃ serialOut,
      runWords (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) t = some serialOut ∧
      runWordsObserved (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) t = some (serialOut, observations) ∧
      StaticPath base (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) t ∧
      ProtectedPath (shaBorrowScope base s extent).protected (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) t ∧
      serialOut.status = .Running ∧ returnStable serialOut = returnStable t ∧
      nonvolatile serialOut = nonvolatile t ∧ serialOut.sp = t.sp ∧ serialOut.pc = t.readReg64 .x30 ∧
      serialOut.readReg64 .x0 = 0#64 ∧
      memoryBytes32 serialOut.mem (t.readReg64 .x1) = (Crypto.Reference.sha256 message).2.map UInt8.toBitVec := by
  have inputs := permission_view_entry_interference_projected base s t message extent authority entry cpu same stack
  obtain ⟨serialOut, executed, path, state, nv, sp, pc, zero, running, digest⟩ :=
    whole_call_sha256_staticPath base t message.bytes inputs
  obtain ⟨knownObs, observed⟩ := runWords_observed _ t serialOut executed
  have originalInputs := permission_view_inputs base s message extent authority entry
  have publicContext := initial_interference_public_context base s t message extent authority entry cpu same
  have trace := (sha256_observations_equal base t (logicalState base s message) message.bytes message.bytes
    inputs originalInputs publicContext rfl serialOut safeOut knownObs observations observed safe.observed).1
  rw [trace] at observed
  have protectedTrace := safe_observations_protected base s message extent authority entry safeOut observations safe
  have protectedPath := protectedPath_of_observations (shaBorrowScope base s extent).protected _ t serialOut observations observed protectedTrace
  exact ⟨serialOut, executed, observed, path, protectedPath, running, state, nv, sp, pc, zero, digest⟩

end Crypto.ARM64.Imported
