import Proofs.ARM64.ImportedHashInit
import Proofs.ARM64.ImportedCellFrame

/-!
The four recorded 64-bit hash stores copy exactly the eight little-endian
32-bit pool words, regardless of the previous hash workspace contents.
Loaded-image/FIPS pool identity and whole-function composition are separate.
-/
namespace Crypto.ARM64.Imported

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem initialHashMemory_words (s : Arm64.State) :
    wordVector 8 (initialHashMemory s) (s.sp + 256#64) =
      wordVector 8 s.mem (s.pc + 732#64) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp (config := { decide := true }) [initialHashMemory, List.range_succ, wordVector,
      Arm64.Memory.read32, Arm64.Memory.write64, read8_write8, BitVec.add_assoc, Arm64.Memory.read64]
  all_goals apply BitVec.eq_of_getLsbD_eq
  all_goals intro k hk
  all_goals
    repeat' first
      | rw [BitVec.getLsbD_append]
      | rw [BitVec.getLsbD_extractLsb']
  all_goals interval_cases k <;> simp (config := { decide := true })


end Crypto.ARM64.Imported
