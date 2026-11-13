import Models.ARM64Machine
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 4096

namespace Crypto.ARM64.Machine

set_option maxHeartbeats 4000000 in
/-- The operational model handles every executable instruction word, for every
register/memory/flag state. NativeEqual proves complete SHA-256 correctness using the pinned imported ISA. -/
theorem program_vocabulary (i : Nat) (hi : i < 151) (s : State) :
    (stepWord imageWords[i]! s).isSome = true := by
  interval_cases i <;>
    simp [stepWord, Round.stepWord, extraStep, imageWords, Round.field]
  all_goals split <;> simp_all

end Crypto.ARM64.Machine
