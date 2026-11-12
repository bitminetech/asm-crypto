import Models.ARM64Machine
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 4096

namespace Crypto.ARM64.Machine

set_option maxHeartbeats 4000000 in
/-- The operational model handles every executable instruction word, for every
register/memory/flag state. This is coverage of the declared model, not a proof
that its instruction meanings agree with hardware or that SHA-256 is correct. -/
theorem program_vocabulary (i : Nat) (hi : i < 151) (s : State) :
    (stepWord imageWords[i]! s).isSome = true := by
  interval_cases i <;>
    simp [stepWord, Round.stepWord, extraStep, imageWords, Round.field]
  all_goals split <;> simp_all

end Crypto.ARM64.Machine
