import Proofs.X86_64.Interleaving

namespace Crypto.X86_64
open X86 Crypto.Baseline
open Crypto.ARM64.Imported (DataAccess)

/-- A target timing model supplies a cost on actual pre-instruction states
and a primitive law for every admitted instruction. The law permits cost
variation with public control and operand addresses. Hardware correspondence
to the chosen model is a separate target condition. -/
structure TimingProfile where
  admits : Instr → Prop
  cost : Instr → Cpu → Nat
  observedCost : Val → Val → Instr → List DataAccess → Nat
  law : ∀ i s accesses, admits i → dataAccesses i s = some accesses →
    cost i s = observedCost s.rip (X86.step i s).rip i accesses

private def nextIP (trace : List Event) (last : Val) : Val :=
  match trace with
  | [] => last
  | e::_ => e.1

def TimingProfile.total (profile : TimingProfile) (last : Val) : List Event → Nat
  | [] => 0
  | (pc,i,accesses)::rest =>
    profile.observedCost pc (nextIP rest last) i accesses + profile.total last rest

private theorem ScheduledExecution.entry_ip {base scope} {env : Environment scope}
    {tick start trace out} (run : ScheduledExecution base env tick start trace out) :
    start.rip = nextIP trace out.rip := by
  cases run <;> rfl

/-- This relation charges the pre-state after the environment boundary. -/
inductive ScheduledCost (base : Val) (profile : TimingProfile) {scope : BorrowScope} (env : Environment scope) :
    Nat → Cpu → List (Val × Instr × List DataAccess) → Cpu → Nat → Prop where
  | nil (tick s) : ScheduledCost base profile env tick s [] s 0
  | cons {tick : Nat} {s next out : Cpu} {i accesses tail n}
      (fetched : fetch base {s with mem := env.memory tick s} = some i)
      (executed : stepLoaded base {s with mem := env.memory tick s} = some next)
      (observed : dataAccesses i {s with mem := env.memory tick s} = some accesses)
      (rest : ScheduledCost base profile env (tick+1) next tail out n) :
      ScheduledCost base profile env tick s ((s.rip,i,accesses) :: tail) out
        (profile.cost i {s with mem := env.memory tick s} + n)

theorem ScheduledExecution.cost {base profile scope} {env : Environment scope}
    {tick s trace out} (run : ScheduledExecution base env tick s trace out)
    (covered : ∀ event ∈ trace, profile.admits event.2.1) :
    ScheduledCost base profile env tick s trace out (profile.total out.rip trace) := by
  induction run with
  | nil => exact .nil _ _
  | @cons tick s next out i accesses tail fetch executes obs frame noRace rest ih =>
    have admission := covered (s.rip,i,accesses) List.mem_cons_self
    have one := profile.law i {s with mem := env.memory tick s} accesses admission obs
    have live : ({s with mem := env.memory tick s} : Cpu).stopped = false := by
      cases stopped : ({s with mem := env.memory tick s} : Cpu).stopped
      · rfl
      · simp [stepLoaded, stopped, guard] at executes
    have step : X86.step i {s with mem := env.memory tick s} = next := by
      simpa [stepLoaded, live, fetch, guard] using executes
    have observedNext : next.rip = nextIP tail out.rip := rest.entry_ip
    rw [step,observedNext] at one
    have after := ih (fun e h => covered e (List.mem_cons_of_mem _ h))
    simpa only [one, TimingProfile.total] using ScheduledCost.cons fetch executes obs after

/-- Both permitted schedules have equal modeled local cost whenever their
public architectural observations agree. -/
theorem scheduled_cost_equal {base profile lscope rscope}
    {lenv : Environment lscope} {renv : Environment rscope}
    {lt rt l r a b trace}
    (left : ScheduledExecution base lenv lt l trace a)
    (right : ScheduledExecution base renv rt r trace b)
    (returned : a.rip = b.rip)
    (covered : ∀ event ∈ trace, profile.admits event.2.1) :
    ∃ cost, ScheduledCost base profile lenv lt l trace a cost ∧
      ScheduledCost base profile renv rt r trace b cost := by
  refine ⟨profile.total a.rip trace, left.cost covered, ?_⟩
  rw [returned]
  exact right.cost covered

end Crypto.X86_64
