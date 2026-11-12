import Models.ARM64

namespace Crypto.ARM64.Imported

/-- This program never substitutes a trusted function contract for machine
code: both kinds of upstream external hook are empty at every address. -/
theorem program_no_hooks (base address : BitVec 64) :
    (program base).externAt? address = none := by
  simp [program, Arm64.Program.ofWords, Arm64.Program.externAt?,
    Arm64.Program.hookAtOff?]

/-- A successful evaluator result is an actual execution of the unchanged
imported small-step semantics. No callee contracts or external hooks are used. -/
theorem runToReturn_steps (prog : Arm64.Program) (fuel : Nat)
    (before after : Arm64.State) (h : runToReturn prog fuel before = some after) :
    Arm64.Steps prog before after := by
  induction fuel generalizing before with
  | zero => simp [runToReturn] at h
  | succ fuel ih =>
    simp only [runToReturn] at h
    split at h
    · contradiction
    next hrun =>
      have hr : before.status = .Running := Classical.byContradiction hrun
      cases hf : prog.fetchMem before.mem before.pc with
      | none => simp [hf] at h
      | some instruction =>
        simp only [hf, Bind.bind, Option.bind] at h
        split at h
        · contradiction
        next =>
          have hs := Arm64.Step.exec (prog := prog) hr hf
          cases instruction <;>
            first
            | (simp only [Option.some.injEq] at h; subst after
               exact Arm64.Steps.step hs (Arm64.Steps.refl _))
            | exact Arm64.Steps.step hs (ih _ h)

end Crypto.ARM64.Imported
