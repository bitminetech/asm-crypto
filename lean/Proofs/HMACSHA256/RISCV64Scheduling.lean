import Proofs.HMACSHA256.RISCV64Borrowing

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64
open Crypto.Baseline (BorrowScope CallAccess)
open Crypto.ARM64.Imported (allPerm_true_iff)

private theorem fetch_congr {P : Addr → Prop} {s t : CPU} (agree : BorrowAgreement P s t)
    {r : Routine} {base : Addr} {op : Op}
    (fetch : r.fetch (decodeAt r) Op.width base s.pc s.mem.read8 = some op)
    (within : (Access.fetch s.pc op.width).Within P) :
    r.fetch (decodeAt r) Op.width base t.pc t.mem.read8 = some op := by
  rw [← agree.pc]
  let off := (s.pc - base).toNat
  by_cases inside : off < r.image.size
  · cases instruction : decodeAt r off with
    | none => simp [Routine.fetch, show (s.pc - base).toNat = off from rfl, inside, instruction, guard] at fetch
    | some inst =>
      by_cases fits : 0 < inst.width ∧ off + inst.width ≤ r.image.size
      · let loaded := ∀ j < inst.width, s.mem.read8 (s.pc + BitVec.ofNat 64 j) =
            r.image[off + j]!.toBitVec
        have sourceFetch : ((if loaded then some () else none).bind fun _ => some inst) = some op := by
          simpa [Routine.fetch, show (s.pc - base).toNat = off from rfl, inside, instruction,
            fits, guard, loaded] using fetch
        by_cases source : loaded
        · rw [if_pos source] at sourceFetch
          have eq : inst = op := Option.some.inj sourceFetch
          subst inst
          have bytes : ∀ j < op.width, t.mem.read8 (s.pc + BitVec.ofNat 64 j) =
              r.image[off + j]!.toBitVec := by
            intro j hj
            have same := agree.memory _ (within j hj)
            change s.mem.cells (s.pc + BitVec.ofNat 64 j) = t.mem.cells (s.pc + BitVec.ofNat 64 j) at same
            unfold Arm64.Memory.read8
            rw [← same]
            exact source j hj
          simp [Routine.fetch, show (s.pc - base).toNat = off from rfl, inside, instruction, fits, guard]
          rw [if_pos bytes]
          rfl
        · simp [source] at sourceFetch
      · simp [Routine.fetch, show (s.pc - base).toNat = off from rfl, inside, instruction, fits, guard] at fetch
  · simp [Routine.fetch, show (s.pc - base).toNat = off from rfl, inside, guard] at fetch

private theorem fetched_sha_agrees {P : Addr → Prop} {s t : CPU} (agree : BorrowAgreement P s t)
    (base : Addr) (imageProtected : ∀ j < codeEnd, P (base + BitVec.ofNat 64 j)) :
    fetched base t = fetched base s := by
  unfold fetched
  rw [← agree.pc]
  let off := (s.pc - base).toNat
  change decodeBytes (fun j => t.mem.read8 (base + BitVec.ofNat 64 j)) off =
    decodeBytes (fun j => s.mem.read8 (base + BitVec.ofNat 64 j)) off
  have byte (j : Nat) (inside : j < codeEnd) :
      t.mem.read8 (base + BitVec.ofNat 64 j) = s.mem.read8 (base + BitVec.ofNat 64 j) := by
    unfold Arm64.Memory.read8
    rw [← agree.memory _ (imageProtected j inside)]
  unfold decodeBytes
  by_cases half : off % 2 = 0 ∧ off + 2 ≤ codeEnd
  · simp only [half, guard, pure, bind, byte off (by omega),
      byte (off + 1) (by omega)]
    split
    · by_cases word : off + 4 ≤ codeEnd
      · simp only [word, if_true, littleWord,
          byte (off + 3) (by omega), byte (off + 2) (by omega),
          byte (off + 1) (by omega), byte off (by omega)]
      · simp [word]
    · rfl
  · simp [guard, half]

private theorem Op.accesses_agree {P : Addr → Prop} {s t : CPU} (op : Op)
    (agree : BorrowAgreement P s t) : op.accesses s = op.accesses t := by
  cases op
  · exact agree.observations _
  all_goals simp [Op.accesses, agree.pc]

private theorem Op.step_agree {P : Addr → Prop} {s t : CPU} (op : Op)
    (agree : BorrowAgreement P s t) (inside : ∀ a ∈ op.accesses s, a.Within P) :
    BorrowAgreement P (op.step s) (op.step t) := by
  have rt : ∀ r, s.reg r = t.reg r := by intro r; simp [CPU.reg, agree.registers]
  cases op with
  | scalar instr =>
    exact instr.step_local agree (fun a h => inside a (List.mem_cons_of_mem _ h))
  | sub d x y =>
    exact ⟨by simp [Op.step, agree.pc],
      by simp [Op.step, CPU.advance, CPU.put, agree.registers, rt], agree.memory⟩
  | lui d imm =>
    exact ⟨by simp [Op.step, agree.pc],
      by simp [Op.step, CPU.advance, CPU.put, agree.registers], agree.memory⟩
  | jal d imm =>
    exact ⟨by simp [Op.step, agree.pc],
      by simp [Op.step, CPU.put, agree.registers, agree.pc], agree.memory⟩

private theorem allowed_agrees {P : Addr → Prop} {s t : CPU} {events : List Access}
    (agree : BorrowAgreement P s t) (inside : ∀ a ∈ events, a.Within P)
    (allowed : events.all (Access.permitted s.mem) = true) :
    events.all (Access.permitted t.mem) = true := by
  apply List.all_eq_true.mpr
  intro a seen
  rw [← a.permitted_agrees s.mem t.mem P agree.memory (inside a seen)]
  exact List.all_eq_true.mp allowed a seen

private theorem replay_hmac {base : Addr} {r : Routine} {s t : CPU} {op : Op}
    (routine : r = entry ∨ r = key ∨ r = finish)
    (fetched : r.fetch (decodeAt r) Op.width (routineAddress base r) s.pc s.mem.read8 = some op)
    (permitted : (op.accesses s).all (Access.permitted s.mem) = true)
    {P : Addr → Prop} (agree : BorrowAgreement P s t)
    (within : ∀ a ∈ op.accesses s, a.Within P) :
    ∃ next', ProgramStep base t (op.accesses s) next' ∧ BorrowAgreement P (op.step s) next' := by
  have same := op.accesses_agree agree
  have fetched' := fetch_congr agree fetched (within _ (List.mem_cons_self ..))
  have allowed' := allowed_agrees agree within permitted
  rw [same] at allowed' ⊢
  exact ⟨op.step t, .hmac (r := r) routine fetched' allowed', op.step_agree agree within⟩

private theorem checked_step_replay {base : Addr} {s next t : CPU} {event : List Access} {ret : Bool}
    (run : checkedStep base s = some (next, event, ret))
    {P : Addr → Prop} (agree : BorrowAgreement P s t)
    (within : ∀ a ∈ event, a.Within P)
    (shaImage : ∀ j < codeEnd, P (base + BitVec.ofNat 64 j)) :
    ∃ next', checkedStep base t = some (next', event, ret) ∧ BorrowAgreement P next next' := by
  have same := fetched_sha_agrees agree base shaImage
  cases inst : fetched base s with
  | none =>
    have invalid : checkedStep base s = none := by simp only [checkedStep, inst]
    rw [invalid] at run
    contradiction
  | some i =>
    by_cases allowed : (i.observations s).all (Access.permitted s.mem) = true
    · have executed : checkedStep base s = some (i.step s, i.observations s, i.op == .ret) := by
        simp only [checkedStep, inst, allowed, if_true]
      have result := Option.some.inj (executed.symm.trans run)
      have state : i.step s = next := congrArg Prod.fst result
      have observed : i.observations s = event := congrArg (fun v : CPU × List Access × Bool => v.2.1) result
      have returned : (i.op == .ret) = ret := congrArg (fun v : CPU × List Access × Bool => v.2.2) result
      have localWithin : ∀ a ∈ i.observations s, a.Within P := by rw [observed]; exact within
      have obs := agree.observations i
      have permitted := allowed_agrees agree localWithin allowed
      have actual : checkedStep base t = some (i.step t, i.observations s, i.op == .ret) := by
        simp only [checkedStep, same, inst, ← obs, permitted, if_true]
      exact ⟨i.step t, by rwa [← observed, ← returned], state ▸
        i.step_local agree (fun a h => localWithin a (List.mem_cons_of_mem _ h))⟩
    · have invalid : checkedStep base s = none := by simp only [checkedStep, inst, allowed, Bool.false_eq_true, if_false]
      rw [invalid] at run
      contradiction

theorem ProgramStep.replay {base : Addr} {s next t : CPU} {event : List Access}
    (step : ProgramStep base s event next) {P : Addr → Prop}
    (agree : BorrowAgreement P s t)
    (within : ∀ a ∈ event, a.Within P)
    (shaImage : ∀ j < codeEnd, P (shaAddress base + BitVec.ofNat 64 j)) :
    ∃ next', ProgramStep base t event next' ∧ BorrowAgreement P next next' := by
  cases step with
  | hmac routine fetched permitted => exact replay_hmac routine fetched permitted agree within
  | sha run =>
    obtain ⟨next', step, after⟩ := checked_step_replay run agree within shaImage
    exact ⟨next', .sha step, after⟩

/-- Environment updates can precede every HMAC or SHA-256 instruction. -/
inductive ScheduledExecution (base : Addr) {P : Addr → Prop} (schedule : MemorySchedule P) :
    Nat → CPU → List (List Access) → CPU → Prop where
  | nil (tick : Nat) (s : CPU) : ScheduledExecution base schedule tick s [] s
  | cons {tick : Nat} {s next out : CPU} {event : List Access} {events : List (List Access)}
      (head : ProgramStep base (s.write (schedule.advance tick s)) event next)
      (tail : ScheduledExecution base schedule (tick + 1) next events out) :
      ScheduledExecution base schedule tick s (event :: events) out

theorem ProgramExecution.scheduled {base : Addr} {s out t : CPU} {events : List (List Access)}
    (run : ProgramExecution base s events out) {P : Addr → Prop}
    (schedule : MemorySchedule P) (tick : Nat)
    (agreement : BorrowAgreement P s t)
    (within : ∀ event ∈ events, ∀ a ∈ event, a.Within P)
    (shaImage : ∀ j < codeEnd, P (shaAddress base + BitVec.ofNat 64 j)) :
    ∃ actual, ScheduledExecution base schedule tick t events actual ∧ BorrowAgreement P out actual := by
  induction run generalizing tick t with
  | nil => exact ⟨t, .nil tick t, agreement⟩
  | cons head _ ih =>
    have before : BorrowAgreement P _ (t.write (schedule.advance tick t)) :=
      agreement.trans ⟨rfl, rfl, schedule.preserves tick t⟩
    obtain ⟨next, step, after⟩ := head.replay before
      (fun a h => within _ (List.mem_cons_self ..) a h) shaImage
    obtain ⟨actual, tail, final⟩ := ih (tick + 1) after
      (fun event seen a h => within event (List.mem_cons_of_mem _ seen) a h)
    exact ⟨actual, .cons step tail, final⟩


private theorem within_scope {scope : BorrowScope} {access : Access}
    (borrowed : CallAccess scope (memoryEvent access)) : access.Within scope.protected := by
  intro i within
  cases access with
  | fetch | read => exact borrowed.1 _ ⟨i, within, rfl⟩
  | write => exact Or.inr (borrowed.2.1 _ ⟨i, within, rfl⟩)

/-- An execution that stays in its borrowed scope can run under any schedule
that preserves the current borrowed cells between instructions. It observes
the same access trace and agrees on registers and borrowed memory at return. -/
theorem ProgramExecution.scheduled_borrowed {base : Addr} {s out : CPU} {events : List (List Access)}
    (run : ProgramExecution base s events out) (scope : BorrowScope)
    (permissions : ScopedPermissions scope s.mem)
    (shaExec : s.mem.canExec (shaAddress base) codeEnd = true)
    (schedule : MemorySchedule scope.protected) (tick : Nat) :
    ∃ actual, ScheduledExecution base schedule tick s events actual ∧
      BorrowAgreement scope.protected out actual := by
  apply run.scheduled schedule tick (BorrowAgreement.refl _ _)
  · intro event atStep access atAccess
    exact within_scope (run.borrowed_accesses scope permissions event atStep access atAccess)
  · intro i within
    exact permissions.exec _ ((allPerm_true_iff _ _ _ _).mp shaExec i within)

end Crypto.HMACSHA256.RISCV64
