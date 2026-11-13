import Proofs.ARM64.ImportedLabeledExecution
import Proofs.ARM64.ImportedCallerEntry

/-! Actual instruction fetches stay in the604 function bytes, separately from
the literal pool and alignment bytes in the complete896-byte image. -/
namespace Crypto.ARM64.Imported
open Crypto.Baseline

def callerFunction (base : BitVec 64) : Region := ⟨base, 604⟩

theorem function_region_valid (base : BitVec 64) (s : Arm64.State)
    (loaded : (program base).CodeLoaded s.mem) : (callerFunction base).Valid := by
  have image := (codeLoaded_iff.mp loaded).2.1
  rw [program_code_length] at image
  change base.toNat + 604 ≤ 2 ^ 64
  change base.toNat + 896 ≤ 2 ^ 64 at image
  omega

theorem whole_call_function_fetches (base : BitVec 64) (s out : Arm64.State) (data : ByteArray)
    (entry : CallInputs base s data) (observations : List InstructionObservation)
    (observed : runWordsObserved (wholeCallCode (BitVec.ofNat 64 data.size)) s = some (out, observations)) :
    ∀ observation ∈ observations, ∀ byte, byte < 4 →
      (callerFunction base).Contains (observation.pc + BitVec.ofNat 64 byte) := by
  have pcs := whole_call_observed_pc_tape base s out data entry observations observed
  have valid := function_region_valid base s entry.loaded
  intro observation member byte bound
  have pcMember : observation.pc ∈ observations.map InstructionObservation.pc := List.mem_map.mpr ⟨observation, member, rfl⟩
  rw [pcs] at pcMember
  obtain ⟨index, present, address⟩ := List.mem_map.mp pcMember
  have indexBound := wholeCallIndices_bounded (BitVec.ofNat 64 data.size) index present
  have inside := caller_region_contains_offset (callerFunction base) valid (4 * index + byte)
    (by change 4 * index + byte < 604; omega)
  rw [← address]
  simpa only [callerFunction, BitVec.ofNat_add, BitVec.add_assoc] using inside

end Crypto.ARM64.Imported
