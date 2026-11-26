import Proofs.X86_64.MemoryEffect
import Proofs.Borrow
import Proofs.X86_64.ScalarControl

namespace Crypto.X86_64
open X86 Crypto.Baseline
open Crypto.ARM64.Imported (DataAccess)

def ReportedAccess (pc : Val) (i : Instr) (accesses : List DataAccess) : AccessEvent where
  reads p := DataByte ⟨false, pc, i.len⟩ p ∨ ObservedByte accesses false p
  writes := ObservedByte accesses true
  releases _ := False
  changesProtection _ := False

private theorem fetch_replace {base : Val} {s : Cpu} {i : Instr} {m : Mem}
    (fetched : fetch base s = some i)
    (agrees : ∀ p, DataByte ⟨false, s.rip, i.len⟩ p → m.read p = s.mem.read p) :
    fetch base {s with mem := m} = some i := by
  unfold fetch at fetched ⊢
  obtain ⟨_, code, tail⟩ := Option.bind_eq_some_iff.mp fetched
  obtain ⟨decoded, decode, tail⟩ := Option.bind_eq_some_iff.mp tail
  obtain ⟨_, extent, tail⟩ := Option.bind_eq_some_iff.mp tail
  obtain ⟨_, bytes, tail⟩ := Option.bind_eq_some_iff.mp tail
  obtain rfl := Option.some.inj tail
  refine Option.bind_eq_some_iff.mpr ⟨_, code, Option.bind_eq_some_iff.mpr ⟨_, decode,
    Option.bind_eq_some_iff.mpr ⟨_, extent, Option.bind_eq_some_iff.mpr ⟨(), ?_, rfl⟩⟩⟩⟩
  have old : (List.range decoded.len).all (fun j =>
      s.mem.read (s.rip + BitVec.ofNat 64 j) == image[(s.rip-base).toNat+j]!.toBitVec) = true := by
    by_contra fail
    simp only [guard, fail, if_false] at bytes
    cases bytes
  have now : (List.range decoded.len).all (fun j =>
      m.read (s.rip + BitVec.ofNat 64 j) == image[(s.rip-base).toNat+j]!.toBitVec) = true := by
    apply List.all_eq_true.mpr
    intro j member
    rw [agrees _ ⟨j, List.mem_range.mp member, rfl⟩]
    exact List.all_eq_true.mp old j member
  change guard ((List.range decoded.len).all (fun j =>
    m.read (s.rip + BitVec.ofNat 64 j) == image[(s.rip-base).toNat+j]!.toBitVec) = true) = some ()
  simp only [now, guard, if_true]
  rfl

theorem dataAccesses_replace (i : Instr) (s : Cpu) (m : Mem) :
    dataAccesses i {s with mem := m} = dataAccesses i s := by
  cases i with
  | mk op len => cases op <;> rfl

private theorem write_read_agree (a b : Mem) (v addr p : Val) (count : Nat)
    (agree : a.read p = b.read p) : (a.writeN addr v count).read p = (b.writeN addr v count).read p := by
  induction count generalizing a b addr v with
  | zero => exact agree
  | succ n ih =>
    simp only [Mem.writeN]
    apply ih
    by_cases h : p = addr
    · rw [h, Mem.read_write_same, Mem.read_write_same]
    · rw [Mem.read_write_ne _ _ _ _ h, Mem.read_write_ne _ _ _ _ h, agree]

theorem MemoryEffect.keeps {effect : MemoryEffect} {before after : Mem} {scope : BorrowScope}
    (same : KeepsBorrowed scope before.read after.read) :
    KeepsBorrowed scope (effect.apply before).read (effect.apply after).read := by
  intro p owned
  cases effect with
  | none => exact same p owned
  | write sz a v => exact write_read_agree _ _ _ _ _ _ (same p owned)

/-- The environment can progress before every retired local instruction.
Its memory projection leaves shared and exclusively borrowed bytes intact.
The access projection separately excludes reads racing with a local write. -/
structure Environment (scope : BorrowScope) where
  memory : Nat → Cpu → Mem
  event : Nat → Cpu → AccessEvent
  keeps : ∀ tick s, KeepsBorrowed scope s.mem.read (memory tick s).read
  permitted : ∀ tick s, EnvironmentAccess scope (event tick s)

inductive ScheduledExecution (base : Val) {scope : BorrowScope} (env : Environment scope) :
    Nat → Cpu → List (Val × Instr × List DataAccess) → Cpu → Prop where
  | nil (tick s) : ScheduledExecution base env tick s [] s
  | cons {tick : Nat} {s next out : Cpu} {i accesses tail}
      (fetched : fetch base {s with mem := env.memory tick s} = some i)
      (executed : stepLoaded base {s with mem := env.memory tick s} = some next)
      (observed : dataAccesses i {s with mem := env.memory tick s} = some accesses)
      (frame : ∀ p, ¬ObservedByte accesses true p →
        next.mem.read p = (env.memory tick s).read p)
      (raceFree : ¬DataRace (ReportedAccess s.rip i accesses) (env.event tick s))
      (rest : ScheduledExecution base env (tick+1) next tail out) :
      ScheduledExecution base env tick s ((s.rip,i,accesses) :: tail) out

/-- Two calls may share read-only bytes. They cannot share any byte to
which either call has an exclusive borrow. -/
def CompatibleBorrows (outer other : BorrowScope) : Prop :=
  (∀ p, outer.exclusive p → ¬other.protected p) ∧
  (∀ p, other.exclusive p → ¬outer.protected p)

theorem CompatibleBorrows.permits {outer other : BorrowScope} (same : CompatibleBorrows outer other)
    {event : AccessEvent} (access : CallAccess other event) : EnvironmentAccess outer event := by
  refine ⟨?_,?_,fun p _ => access.2.2.1 p,fun p _ => access.2.2.2 p⟩
  · exact fun p owned reading => same.1 p owned (access.1 p reading)
  · exact fun p owned writing => same.2 p (access.2.1 p writing) owned

/-- An actual step of a compatible invocation can be an environment step.
Its writes preserve the first call's current borrowed cells. -/
theorem compatible_call_step {outer other : BorrowScope} (same : CompatibleBorrows outer other)
    {i : Instr} {s : Cpu} {accesses : List DataAccess}
    (leaf : ScalarLeaf i) (operands : dataAccesses i s = some accesses)
    (allowed : CallAccess other (ReportedAccess s.rip i accesses)) :
    KeepsBorrowed outer s.mem.read (X86.step i s).mem.read ∧
      EnvironmentAccess outer (ReportedAccess s.rip i accesses) := by
  have permit := same.permits allowed
  obtain ⟨patch,writes,after,_⟩ := scalar_memory_effect i s s.mem accesses leaf operands (fun _ _ => rfl)
  refine ⟨?_,permit⟩
  intro p inside
  rw [after]
  exact patch.frame _ p (fun hit => permit.2.1 p inside (writes p hit))

private theorem stepLoaded_live {base s next} (h : stepLoaded base s = some next) :
    s.stopped = false := by
  cases stopped : s.stopped
  · rfl
  · simp [stepLoaded, stopped, guard] at h

attribute [local irreducible] fetch X86.step dataAccesses

/-- Lift an access-checked serial execution to arbitrary permitted schedules.
The final CPU and borrowed bytes agree with the serial result. Memory outside
the borrow may include any progress the environment made. -/
theorem ObservedExecution.schedule {base s trace out} (run : ObservedExecution base s trace out)
    {scope : BorrowScope} (env : Environment scope)
    (owned : ∀ e ∈ trace, CallAccess scope (ReportedAccess e.1 e.2.1 e.2.2))
    (tick : Nat) (m : Mem) (initial : KeepsBorrowed scope s.mem.read m.read) :
    ∃ finalMem, ScheduledExecution base env tick {s with mem := m} trace {out with mem := finalMem} ∧
      KeepsBorrowed scope out.mem.read finalMem.read := by
  induction run generalizing tick m with
  | nil => exact ⟨m, .nil _ _, initial⟩
  | @cons s next out i accesses tail fetched executed observed rest ih =>
    let current := {s with mem := m}
    let incoming := env.memory tick current
    have cells : KeepsBorrowed scope s.mem.read incoming.read :=
      initial.trans (env.keeps tick current)
    have localAccess := owned _ List.mem_cons_self
    have nextFetch := fetch_replace fetched (fun p h => cells p (localAccess.1 p (Or.inl h)))
    have live := stepLoaded_live executed
    have one : X86.step i s = next := by simpa [stepLoaded, live, fetched, guard] using executed
    obtain ⟨effect, modifies, memory, replay⟩ := scalar_memory_effect i s incoming accesses
      (fetched_scalar fetched) observed (fun p h => cells p (localAccess.1 p (Or.inr h)))
    have nextMem : KeepsBorrowed scope next.mem.read (effect.apply incoming).read := by
      rw [← one, memory]
      exact MemoryEffect.keeps cells
    obtain ⟨finalMem, scheduled, finalCells⟩ :=
      ih (fun e h => owned e (List.mem_cons_of_mem _ h)) (tick+1) _ nextMem
    refine ⟨finalMem, ?_, finalCells⟩
    refine .cons nextFetch ?_ ?_ ?_
      (borrow_accesses_race_free scope _ _ localAccess (env.permitted tick current)) scheduled
    · change stepLoaded base {s with mem := incoming} = _
      have running : ({s with mem := incoming} : Cpu).stopped = false := live
      simp [stepLoaded, running, guard, nextFetch, replay, one]
    · simpa only [dataAccesses_replace] using observed
    · intro p untouched
      exact effect.frame incoming p (fun h => untouched (modifies p h))

end Crypto.X86_64
