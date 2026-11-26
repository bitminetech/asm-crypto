import Proofs.RISCV64.Locality
import Proofs.RISCV64.Timing

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (SameCellsOn)

/-- An environment supplies the memory before each modeled instruction. Its
steps can change cells outside the live borrow, including their permissions. -/
structure MemorySchedule (P : Addr → Prop) where
  advance : Nat → CPU → Memory
  preserves : ∀ tick s, SameCellsOn P s.mem (advance tick s)

def runScheduledUntilReturn {P : Addr → Prop} (base : Addr) (env : MemorySchedule P) :
    Nat → CPU → Nat → Option (CPU × List Access)
  | _, _, 0 => none
  | tick, s, fuel + 1 => do
    let (next, observed, returning) ← checkedStep base (s.write (env.advance tick s))
    if returning then some (next, observed)
    else
      let (out, rest) ← runScheduledUntilReturn base env (tick + 1) next fuel
      pure (out, observed ++ rest)

def runScheduledCosted {P : Addr → Prop} (base : Addr) (env : MemorySchedule P) (profile : TimingProfile) :
    Nat → CPU → Nat → Option (CPU × Nat)
  | _, _, 0 => none
  | tick, s, fuel + 1 => do
    let current := s.write (env.advance tick s)
    let inst ← fetched base current
    let (next, _, returning) ← checkedStep base current
    let cost := profile.cost inst current
    if returning then some (next, cost)
    else
      let (out, rest) ← runScheduledCosted base env profile (tick + 1) next fuel
      pure (out, cost + rest)

theorem ImageExecution.scheduled {base : Addr} {s out : CPU} {code : List Instruction}
    (path : ImageExecution base s code out) (permitted : PermittedPath base s code)
    (returned : ∃ i ∈ code, i.op = .ret)
    {P : Addr → Prop} (env : MemorySchedule P) (profile : TimingProfile)
    (imageWithin : ∀ j < image.size, P (base + BitVec.ofNat 64 j))
    (footprint : ∀ a ∈ accessTrace code s, a.Within P)
    (tick : Nat) (t : CPU) (agree : BorrowAgreement P s t) :
    ∃ actual, runScheduledUntilReturn base env tick t code.length = some (actual, accessTrace code s) ∧
      runScheduledCosted base env profile tick t code.length = some (actual, profile.runCost code s) ∧
      BorrowAgreement P out actual := by
  induction path generalizing tick t with
  | nil => simp at returned
  | @cons s out i tail decoded last rest ih =>
    cases permitted with
    | cons loaded localAllowed later =>
      let current := t.write (env.advance tick t)
      have before : BorrowAgreement P s current :=
        agree.trans ⟨rfl, rfl, env.preserves tick t⟩
      have obs := before.observations i
      have one (a : Access) (h : a ∈ i.observations s) : a.Within P :=
        footprint a (List.mem_append_left _ h)
      have loaded' : ImageLoaded base current.mem :=
        loaded.of_cells (fun j hj => (before.memory _ (imageWithin j hj)).symm)
      have decoded' : decodeAt (current.pc-base).toNat = some i := by rw [← before.pc]; exact decoded
      have allowed' : (i.observations current).all (Access.permitted current.mem) = true := by
        rw [← obs]
        apply List.all_eq_true.mpr
        intro a member
        rw [← a.permitted_agrees s.mem current.mem P before.memory (one a member)]
        exact List.all_eq_true.mp localAllowed a member
      have executed : checkedStep base (t.write (env.advance tick t)) =
          some (i.step current, i.observations current, i.op == .ret) :=
        checked_step_loaded base current i loaded' decoded' allowed'
      have after := i.step_local before (fun a ha => one a (List.mem_cons_of_mem _ ha))
      have instr : fetched base (t.write (env.advance tick t)) = some i :=
        (fetch_loaded base current loaded').trans decoded'
      have cost : profile.cost i (t.write (env.advance tick t)) = profile.cost i s := by
        change profile.cost i current = profile.cost i s
        rw [profile.observationLaw i current, ← obs, ← after.pc, ← profile.observationLaw i s]
      by_cases ret : i.op = .ret
      · obtain rfl := last ret
        cases rest
        refine ⟨i.step current, ?_, ?_, after⟩
        · simp [runScheduledUntilReturn, executed, ret, accessTrace, obs]
        · simp [runScheduledCosted, instr, executed, ret, TimingProfile.runCost, cost]
      · have inTail : ∃ j ∈ tail, j.op = .ret := by
          obtain ⟨j, jIn, isReturn⟩ := returned
          rcases List.mem_cons.mp jIn with same | inTail
          · subst j; exact (ret isReturn).elim
          · exact ⟨j, inTail, isReturn⟩
        have tailWithin : ∀ a ∈ accessTrace tail (i.step s), a.Within P :=
          fun a ha => footprint a (List.mem_append_right _ ha)
        obtain ⟨actual, tailRun, tailCost, agreeOut⟩ := ih later inTail tailWithin (tick+1) (i.step current) after
        refine ⟨actual, ?_, ?_, agreeOut⟩
        · simp [runScheduledUntilReturn, executed, ret, tailRun, accessTrace, obs]
        · simp [runScheduledCosted, instr, executed, ret, tailCost, TimingProfile.runCost, cost]

end Crypto.RISCV64
