import Proofs.HMACSHA256.X86Scheduling
import Proofs.X86_64.Timing

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Baseline
open Crypto.ARM64.Imported (DataAccess)

structure LinkedTimingProfile (base : Val) where
  cost : Instr → Cpu → Nat
  observedCost : Val → Val → Instr → List DataAccess → Nat
  localLaw : ∀ {authority s out event}, ProgramStep base authority s event out →
    cost event.2.1 s = observedCost event.1 out.rip event.2.1 event.2.2
  shaLaw : ∀ i s accesses, dataAccesses i s = some accesses →
    cost i s = observedCost s.rip (X86.step i s).rip i accesses

def LinkedTimingProfile.sha {base : Val} (profile : LinkedTimingProfile base) : TimingProfile where
  admits _ := True
  cost := profile.cost
  observedCost := profile.observedCost
  law i s accesses _ reported := profile.shaLaw i s accesses reported

private def firstIP (events : List Event) (last : Val) : Val :=
  match events with
  | [] => last
  | event :: _ => event.1

private theorem first_ip_append (a b : List Event) (last : Val) :
    firstIP (a ++ b) last = firstIP a (firstIP b last) := by cases a <;> rfl

private theorem sha_first_ip {base : Val} {scope : BorrowScope} {env : Environment scope}
    {tick s out seen} (run : ScheduledExecution base env tick s seen out) :
    firstIP seen out.rip = s.rip := by cases run <;> rfl

private theorem LinkedSchedule.first_ip {base : Val} {authority : Authority} {scope : BorrowScope}
    {env : Environment scope} {tick s out seen} (run : LinkedSchedule base authority env tick s seen out) :
    firstIP seen out.rip = s.rip := by
  induction run with
  | nil => rfl
  | localStep step _ _ _ => cases step; rfl
  | hash first _ ih => rw [first_ip_append, ih, sha_first_ip first]

private theorem total_append (profile : TimingProfile) (last : Val) (a b : List Event) :
    profile.total last (a ++ b) = profile.total (firstIP b last) a + profile.total last b := by
  induction a with
  | nil => simp [TimingProfile.total]
  | cons e rest ih =>
    obtain ⟨pc, i, accesses⟩ := e
    change profile.observedCost pc (firstIP (rest ++ b) last) i accesses +
      profile.total last (rest ++ b) = _
    rw [first_ip_append, ih]
    simp only [TimingProfile.total, Nat.add_assoc]
    rfl

/-- Adds costs to actual scheduled states, including every modeled REP
iteration and all instructions in each linked SHA callee. -/
inductive CostedLinkedSchedule {base : Val} (profile : LinkedTimingProfile base) (authority : Authority)
    {scope : BorrowScope} (env : Environment scope) : Nat → Cpu → List Event → Cpu → Nat → Prop where
  | nil (tick : Nat) (s : Cpu) : CostedLinkedSchedule profile authority env tick s [] s 0
  | localStep {tick : Nat} {s next out : Cpu} {event : Event} {rest : List Event} {cost : Nat}
      (run : ProgramStep base authority {s with mem := env.memory tick s} event next)
      (raceFree : ¬DataRace (ReportedAccess event.1 event.2.1 event.2.2) (env.event tick s))
      (tail : CostedLinkedSchedule profile authority env (tick + 1) next rest out cost) :
      CostedLinkedSchedule profile authority env tick s (event :: rest) out
        (profile.cost event.2.1 {s with mem := env.memory tick s} + cost)
  | hash {tick : Nat} {s mid out : Cpu} {seen rest : List Event} {a b : Nat}
      (first : ScheduledCost (shaAddress base) profile.sha env tick s seen mid a)
      (scheduled : ScheduledExecution (shaAddress base) env tick s seen mid)
      (tail : CostedLinkedSchedule profile authority env (tick + seen.length) mid rest out b) :
      CostedLinkedSchedule profile authority env tick s (seen ++ rest) out (a + b)

theorem LinkedSchedule.costed {base : Val} {authority : Authority} {scope : BorrowScope}
    {env : Environment scope} {tick s out seen} (run : LinkedSchedule base authority env tick s seen out)
    (profile : LinkedTimingProfile base) :
    CostedLinkedSchedule profile authority env tick s seen out (profile.sha.total out.rip seen) := by
  induction run with
  | nil => exact .nil _ _
  | @localStep tick s next out event rest hd free tail ih =>
    obtain ⟨pc, instruction, accesses⟩ := event
    have price := profile.localLaw hd
    rw [← tail.first_ip] at price
    change profile.cost instruction {s with mem := env.memory tick s} =
      profile.sha.observedCost pc (firstIP rest out.rip) instruction accesses at price
    change CostedLinkedSchedule profile authority env tick s ((pc, instruction, accesses) :: rest) out
      (profile.sha.observedCost pc (firstIP rest out.rip) instruction accesses + profile.sha.total out.rip rest)
    rw [← price]
    exact .localStep hd free ih
  | hash first following ih =>
    rw [total_append, following.first_ip]
    exact .hash (first.cost (fun _ _ => trivial)) first ih

theorem CostedLinkedSchedule.erase {base : Val} {authority : Authority} {scope : BorrowScope}
    {env : Environment scope} {profile : LinkedTimingProfile base} {tick s out events cost}
    (run : CostedLinkedSchedule profile authority env tick s events out cost) :
    LinkedSchedule base authority env tick s events out := by
  induction run with
  | nil => exact .nil _ _
  | localStep step safe _ ih => exact .localStep step safe ih
  | hash _ scheduled _ ih => exact .hash scheduled ih

def instructionUnits (base : Val) : LinkedTimingProfile base where
  cost _ _ := 1
  observedCost _ _ _ _ := 1
  localLaw _ := rfl
  shaLaw _ _ _ _ := rfl

@[simp] theorem instruction_units_length (base last : Val) (events : List Event) :
    (instructionUnits base).sha.total last events = events.length := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    obtain ⟨pc, i, accesses⟩ := event
    change 1 + (instructionUnits base).sha.total last rest = _
    rw [ih, List.length_cons, Nat.add_comm]

end Crypto.HMACSHA256.X86_64
