import Proofs.HMACSHA256.RISCV64Scheduling

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

private theorem sha_event_fetch {base : Addr} {s next : CPU} {event : List Access} {ret : Bool}
    (step : checkedStep base s = some (next, event, ret)) :
    ∃ width data, event = .fetch s.pc width :: data := by
  unfold checkedStep at step
  split at step
  · contradiction
  · rename_i i _
    dsimp only at step
    split at step
    · have output := Option.some.inj step
      have trace := congrArg (fun p : CPU × List Access × Bool => p.2.1) output
      exact ⟨i.bytes, i.op.accesses s, trace.symm⟩
    · contradiction

theorem ProgramStep.fetch_event {base : Addr} {s next : CPU} {event : List Access}
    (step : ProgramStep base s event next) : ∃ width data, event = .fetch s.pc width :: data := by
  cases step with
  | @hmac _ s i _ _ _ =>
    exact ⟨i.width, (i.accesses s).tail, by cases i <;> rfl⟩
  | sha h => exact sha_event_fetch h

private def firstFetch (events : List (List Access)) (ret : Addr) : Addr :=
  match events with
  | (.fetch pc _ :: _) :: _ => pc
  | _ => ret

private theorem ScheduledExecution.first_fetch {base : Addr} {P : Addr → Prop}
    {env : MemorySchedule P} {tick : Nat} {s out : CPU} {events}
    (run : ScheduledExecution base env tick s events out) :
    firstFetch events out.pc = s.pc := by
  cases run with
  | nil => rfl
  | cons first _ =>
    obtain ⟨width, data, observation⟩ := first.fetch_event
    rw [observation]
    rfl

/-- A target timing profile for the linked instruction vocabulary. The law
rules out costs depending on secret operands. The retired instruction, its
addresses, and its control successor determine the cost in this model. -/
structure LinkedTimingProfile (base : Addr) where
  stepCost : CPU → CPU → Nat
  observedCost : List Access → Addr → Nat
  observationLaw : ∀ {s out : CPU} {event}, ProgramStep base s event out →
    stepCost s out = observedCost event out.pc

def LinkedTimingProfile.traceCost {base : Addr} (profile : LinkedTimingProfile base)
    (returnAddress : Addr) : List (List Access) → Nat
  | [] => 0
  | event :: tail =>
    profile.observedCost event (firstFetch tail returnAddress) + profile.traceCost returnAddress tail

/-- A costed execution allows the same permitted environment update before
every instruction. Only the program's retired instructions contribute cost. -/
inductive CostedScheduledExecution {base : Addr} (profile : LinkedTimingProfile base)
    {P : Addr → Prop} (env : MemorySchedule P) :
    Nat → CPU → List (List Access) → CPU → Nat → Prop where
  | nil (tick : Nat) (s : CPU) : CostedScheduledExecution profile env tick s [] s 0
  | cons {tick : Nat} {s next out : CPU} {event events} {tailCost : Nat}
      (step : ProgramStep base (s.write (env.advance tick s)) event next)
      (tail : CostedScheduledExecution profile env (tick + 1) next events out tailCost) :
      CostedScheduledExecution profile env tick s (event :: events) out
        (profile.stepCost (s.write (env.advance tick s)) next + tailCost)

theorem ScheduledExecution.costed {base : Addr} {P : Addr → Prop}
    {env : MemorySchedule P} {tick : Nat} {s out : CPU} {events}
    (run : ScheduledExecution base env tick s events out) (profile : LinkedTimingProfile base) :
    CostedScheduledExecution profile env tick s events out (profile.traceCost out.pc events) := by
  induction run with
  | nil => exact .nil _ _
  | cons step tail ih =>
    simp only [LinkedTimingProfile.traceCost]
    rw [tail.first_fetch, ← profile.observationLaw step]
    exact .cons step ih

theorem scheduled_equal_timing {base : Addr} {P Q : Addr → Prop}
    {env : MemorySchedule P} {other : MemorySchedule Q} {s t out endState : CPU} {events}
    (left : ScheduledExecution base env 0 s events out)
    (right : ScheduledExecution base other 0 t events endState)
    (sameReturn : out.pc = endState.pc) (profile : LinkedTimingProfile base) :
    ∃ cost, CostedScheduledExecution profile env 0 s events out cost ∧
      CostedScheduledExecution profile other 0 t events endState cost := by
  exact ⟨_, left.costed profile, sameReturn.symm ▸ right.costed profile⟩

theorem CostedScheduledExecution.erase {base : Addr} {P : Addr → Prop}
    {env : MemorySchedule P} {profile : LinkedTimingProfile base}
    {tick s out events cost} (run : CostedScheduledExecution profile env tick s events out cost) :
    ScheduledExecution base env tick s events out := by
  induction run with
  | nil => exact .nil _ _
  | cons step _ ih => exact .cons step ih

def instructionUnits (base : Addr) : LinkedTimingProfile base where
  stepCost _ _ := 1
  observedCost _ _ := 1
  observationLaw _ := rfl

end Crypto.HMACSHA256.RISCV64
