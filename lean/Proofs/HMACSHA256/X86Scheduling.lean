import Proofs.HMACSHA256.X86Ranges

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Baseline
open Crypto.ARM64.Imported (DataAccess)

private theorem routine_fetch_overlay {r : Routine} {base : Val} {s : Cpu} {i : Instr} {m : Mem}
    (fetched : r.fetch (decodeAt r) Instr.len (routineAddress base r) s.rip s.mem.read = some i)
    (same : ∀ p, DataByte ⟨false, s.rip, i.len⟩ p → m.read p = s.mem.read p) :
    r.fetch (decodeAt r) Instr.len (routineAddress base r) s.rip m.read = some i := by
  unfold Routine.fetch at fetched ⊢
  obtain ⟨_, start, tail⟩ := Option.bind_eq_some_iff.mp fetched
  obtain ⟨op, decoded, tail⟩ := Option.bind_eq_some_iff.mp tail
  obtain ⟨_, complete, tail⟩ := Option.bind_eq_some_iff.mp tail
  obtain ⟨_, bytes, tail⟩ := Option.bind_eq_some_iff.mp tail
  obtain rfl := Option.some.inj tail
  refine Option.bind_eq_some_iff.mpr ⟨_, start, Option.bind_eq_some_iff.mpr ⟨op, decoded,
    Option.bind_eq_some_iff.mpr ⟨_, complete, Option.bind_eq_some_iff.mpr ⟨(), ?_, rfl⟩⟩⟩⟩
  let off := (s.rip - routineAddress base r).toNat
  have agreed : (List.range op.len).all
      (fun j => s.mem.read (s.rip + BitVec.ofNat 64 j) == r.image[off + j]!.toBitVec) = true := by
    change guard ((List.range op.len).all
      (fun j => s.mem.read (s.rip + BitVec.ofNat 64 j) == r.image[off + j]!.toBitVec) = true) =
        some () at bytes
    by_contra rejected
    simp [guard, rejected] at bytes
  have now : (List.range op.len).all
      (fun j => m.read (s.rip + BitVec.ofNat 64 j) == r.image[off + j]!.toBitVec) = true := by
    apply List.all_eq_true.mpr
    intro j seen
    rw [same _ ⟨j, List.mem_range.mp seen, rfl⟩]
    exact List.all_eq_true.mp agreed j seen
  change guard ((List.range op.len).all
    (fun j => m.read (s.rip + BitVec.ofNat 64 j) == r.image[off + j]!.toBitVec) = true) = some ()
  simp only [now, guard, if_true]
  rfl

/-- The same environment boundary is used between HMAC instructions, REP
iterations, and the linked SHA-256 code. The trace counts actual model steps. -/
inductive LinkedSchedule (base : Val) (authority : Authority) {scope : BorrowScope} (env : Environment scope) :
    Nat → Cpu → List Event → Cpu → Prop where
  | nil (tick : Nat) (s : Cpu) : LinkedSchedule base authority env tick s [] s
  | localStep {tick : Nat} {s next out : Cpu} {event : Event} {rest : List Event}
      (run : ProgramStep base authority {s with mem := env.memory tick s} event next)
      (raceFree : ¬ DataRace (ReportedAccess event.1 event.2.1 event.2.2) (env.event tick s))
      (tail : LinkedSchedule base authority env (tick + 1) next rest out) :
      LinkedSchedule base authority env tick s (event :: rest) out
  | hash {tick : Nat} {s mid out : Cpu} {seen rest : List Event}
      (run : ScheduledExecution (shaAddress base) env tick s seen mid)
      (tail : LinkedSchedule base authority env (tick + seen.length) mid rest out) :
      LinkedSchedule base authority env tick s (seen ++ rest) out

theorem LinkedExecution.schedule {base : Val} {authority : Authority} {s out : Cpu} {events : List Event}
    (run : LinkedExecution base authority s events out) {scope : BorrowScope} (env : Environment scope)
    (owned : ∀ e ∈ events, CallAccess scope (ReportedAccess e.1 e.2.1 e.2.2))
    (tick : Nat) (m : Mem) (initial : KeepsBorrowed scope s.mem.read m.read) :
    ∃ final,
      LinkedSchedule base authority env tick {s with mem := m} events {out with mem := final} ∧
      KeepsBorrowed scope out.mem.read final.read := by
  induction run generalizing tick m with
  | nil s => exact ⟨m, .nil _ _, initial⟩
  | @localStep s next out event rest head tail ih =>
    cases head with
    | @localStep routine current instr accesses body fetched form live direction data rights =>
      let currentCpu := { s with mem := m }
      let incoming := env.memory tick currentCpu
      have agreement : KeepsBorrowed scope s.mem.read incoming.read :=
        initial.trans (env.keeps tick currentCpu)
      have access := owned _ List.mem_cons_self
      have ready := routine_fetch_overlay fetched (fun p h => agreement p (access.1 _ (Or.inl h)))
      have values : ReadsAgree accesses s.mem incoming := fun p h =>
        agreement p (access.1 _ (Or.inr h))
      obtain ⟨patch, _, memory, stepState⟩ :=
        local_memory_effect instr s incoming accesses form live direction data values
      have afterCells : KeepsBorrowed scope (step instr s).mem.read (patch.apply incoming).read := by
        rw [memory]
        exact patch.keeps agreement
      obtain ⟨last, remained, same⟩ :=
        ih (fun e h => owned e (List.mem_cons_of_mem _ h)) (tick + 1) (patch.apply incoming) afterCells
      have replay : ProgramStep base authority {currentCpu with mem := incoming} (s.rip, instr, accesses)
          (step instr {currentCpu with mem := incoming}) := by
        change ProgramStep base authority {s with mem := incoming} (s.rip, instr, accesses)
          (step instr {s with mem := incoming})
        exact ProgramStep.localStep (s := {s with mem := incoming}) body ready form live direction
          (by simpa only [localAccesses_overlay] using data) rights
      have eventSafe := env.permitted tick currentCpu
      have free := borrow_accesses_race_free _ _ _ access eventSafe
      change step instr {s with mem := incoming} = _ at stepState
      rw [stepState] at replay
      exact ⟨last, .localStep replay free remained, same⟩
  | @shaCall s mid out message extent seen rest callee tail ih =>
    have before (e : Event) (h : e ∈ seen) : CallAccess scope (ReportedAccess e.1 e.2.1 e.2.2) :=
      owned e (List.mem_append_left _ h)
    obtain ⟨memory, scheduled, keep⟩ := callee.execution.schedule env before tick m initial
    obtain ⟨last, following, same⟩ := ih (fun e h => owned e (List.mem_append_right _ h))
      (tick + seen.length) memory keep
    exact ⟨last, .hash scheduled following, same⟩


structure ScopedAuthority (scope : BorrowScope) (a : Authority) : Prop where
  read : ∀ p, a.readable p → scope.protected p
  write : ∀ p, a.writable p → scope.exclusive p
  exec : ∀ p, a.executable p → scope.protected p

private theorem authorized_event {scope : BorrowScope} {authority : Authority} {event : Event}
    (scopeRights : ScopedAuthority scope authority)
    (fetched : ∀ p, DataByte ⟨false, event.1, event.2.1.len⟩ p → authority.executable p)
    (touch : ∀ a ∈ event.2.2, ∀ p, DataByte a p →
      if a.write then authority.writable p else authority.readable p) :
    CallAccess scope (ReportedAccess event.1 event.2.1 event.2.2) := by
  refine ⟨?_, ?_, fun _ h => h.elim, fun _ h => h.elim⟩
  · rintro p (code | ⟨a, present, reading, hit⟩)
    · exact scopeRights.exec p (fetched p code)
    · exact scopeRights.read p (by simpa only [reading, if_false, Bool.false_eq_true] using touch a present p hit)
  · rintro p ⟨a, present, writing, hit⟩
    exact scopeRights.write p (by simpa only [writing, if_true] using touch a present p hit)

theorem LinkedExecution.borrowed_accesses {base : Val} {authority : Authority} {s out : Cpu} {events : List Event}
    (run : LinkedExecution base authority s events out) {scope : BorrowScope}
    (scopeRights : ScopedAuthority scope authority) :
    ∀ e ∈ events, CallAccess scope (ReportedAccess e.1 e.2.1 e.2.2) := by
  induction run with
  | nil => simp
  | localStep step _ ih =>
    intro e h
    rcases List.mem_cons.mp h with head | tail
    · subst e
      cases step with
      | localStep _ _ _ _ _ _ rights =>
        exact authorized_event scopeRights (fun p hit => (rights.1 p hit).2)
          (fun a seen p hit => (rights.2 a seen p hit).2)
    · exact ih e tail
  | shaCall call _ ih =>
    intro e h
    rcases List.mem_append.mp h with before | after
    · exact authorized_event scopeRights (fun p hit => (call.fetch _ ⟨e, before, hit⟩).1)
        (fun a seen p hit => (call.data _ before a seen p hit).2)
    · exact ih e after

end Crypto.HMACSHA256.X86_64
