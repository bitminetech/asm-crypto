import Proofs.HMACSHA256.ARM64Scheduling

namespace Crypto.HMACSHA256.ARM64

open Crypto.Baseline Crypto.ARM64.Imported

/-- A target timing model for the linked HMAC and SHA instructions.
The observation law states the operand-independence assumption on the
modeled pre-instruction state. Hardware correspondence is target-specific. -/
structure LinkedTimingProfile where
  cost : Arm64.Instr → Arm64.State → Nat
  observedCost : InstructionObservation → Nat
  observationLaw : ∀ i s, hmacLocal i = true → cost i s = observedCost (instructionObservation i s)

def LinkedTimingProfile.traceCost (profile : LinkedTimingProfile) : List InstructionObservation → Nat
  | [] => 0
  | event :: rest => profile.observedCost event + profile.traceCost rest

inductive CostedScheduledExecution (base : Addr) (profile : LinkedTimingProfile) {scope : BorrowScope}
    (env : BorrowEnvironment scope (fun _ => True)) :
    Nat → Arm64.State → List InstructionObservation → Arm64.State → Nat → Prop where
  | nil (tick : Nat) (s : Arm64.State) : CostedScheduledExecution base profile env tick s [] s 0
  | step {tick : Nat} {s out : Arm64.State} {p : Arm64.Program} {i : Arm64.Instr}
      {rest : List InstructionObservation} {cost : Nat}
      (image : LinkedImage base p) (allowed : hmacLocal i = true)
      (running : (env.advance tick s).status = .Running)
      (fetched : p.fetchMem (env.advance tick s).mem (env.advance tick s).pc = some i)
      (global : GlobalTail (Arm64.execInstWithSvc Arm64.noSyscalls i (env.advance tick s)) =
        GlobalTail (env.advance tick s))
      (safe : ¬DataRace (observedAccessEvent (instructionObservation i (env.advance tick s))) (env.event tick s))
      (tail : CostedScheduledExecution base profile env (tick + 1)
        (Arm64.execInstWithSvc Arm64.noSyscalls i (env.advance tick s)) rest out cost) :
      CostedScheduledExecution base profile env tick s (instructionObservation i (env.advance tick s) :: rest) out
        (profile.cost i (env.advance tick s) + cost)

theorem ScheduledExecution.costed {base : Addr} {scope : BorrowScope}
    {env : BorrowEnvironment scope (fun _ => True)} {tick : Nat}
    {s out : Arm64.State} {obs : List InstructionObservation}
    (run : ScheduledExecution base env tick s obs out) (profile : LinkedTimingProfile) :
    CostedScheduledExecution base profile env tick s obs out (profile.traceCost obs) := by
  induction run with
  | nil => exact .nil _ _
  | step image allowed running fetched global safe _ ih =>
    simp only [LinkedTimingProfile.traceCost, ← profile.observationLaw _ _ allowed]
    exact .step image allowed running fetched global safe ih

theorem CostedScheduledExecution.erase {base : Addr} {scope : BorrowScope}
    {env : BorrowEnvironment scope (fun _ => True)} {profile : LinkedTimingProfile}
    {tick s out obs cost} (run : CostedScheduledExecution base profile env tick s obs out cost) :
    ScheduledExecution base env tick s obs out := by
  induction run with
  | nil => exact .nil _ _
  | step image allowed running fetched global safe _ ih => exact .step image allowed running fetched global safe ih

def instructionUnits : LinkedTimingProfile where
  cost _ _ := 1
  observedCost _ := 1
  observationLaw _ _ _ := rfl

@[simp] theorem instruction_units_length (trace : List InstructionObservation) :
    instructionUnits.traceCost trace = trace.length := by
  induction trace with
  | nil => rfl
  | cons _ rest ih =>
    change 1 + instructionUnits.traceCost rest = _
    rw [ih, List.length_cons, Nat.add_comm]

end Crypto.HMACSHA256.ARM64
