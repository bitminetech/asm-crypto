import Proofs.X86_64.Caller
import Proofs.X86_64.ScalarControl

namespace Crypto.X86_64
open X86

/-- Each entry records the pre-instruction RIP and the operation fetched there.
The relation uses the ordinary loaded step, including its stopped-state guard. -/
inductive Execution (base : Val) : Cpu → List (Val × Instr) → Cpu → Prop where
  | nil (s) : Execution base s [] s
  | cons {s next out i trace} (fetched : fetch base s = some i)
      (executed : stepLoaded base s = some next) (tail : Execution base next trace out) :
      Execution base s ((s.rip,i) :: trace) out

attribute [local irreducible] image X86.step decodeAt

theorem Execution.scalar {base s trace out} (run : Execution base s trace out) :
    ∀ e ∈ trace, ScalarLeaf e.2 := by
  induction run with
  | nil => simp
  | cons fetched _ _ ih =>
    intro e member
    rcases List.mem_cons.mp member with rfl | tail
    · exact fetched_scalar fetched
    · exact ih _ tail

/-- All bytes of a dynamically fetched instruction lie in the executable
prefix of the image, including its final byte. -/
theorem fetched_extent {base : Val} {s : Cpu} {i : Instr} (h : fetch base s = some i) :
    ∃ off, s.rip = base + BitVec.ofNat 64 off ∧ off + i.len ≤ codeEnd := by
  unfold fetch at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨op, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, bound, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  have eq : op = i := Option.some.inj h
  subst op
  refine ⟨(s.rip-base).toNat, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel], ?_⟩
  by_contra outside
  simp only [guard, if_neg outside] at bound
  contradiction

theorem Execution.fetch_authorized {base s trace out} (run : Execution base s trace out)
    (authority : Crypto.Baseline.Authority)
    (code : ∀ j, j < codeEnd → authority.executable (base + BitVec.ofNat 64 j) ∧
      canonical (base + BitVec.ofNat 64 j) = true) :
    ∀ e ∈ trace, ∀ j < e.2.len, authority.executable (e.1 + BitVec.ofNat 64 j) ∧
      canonical (e.1 + BitVec.ofNat 64 j) = true := by
  induction run with
  | nil => simp
  | cons fetched _ _ ih =>
    intro e member j hj
    rcases List.mem_cons.mp member with rfl | tail
    · obtain ⟨off, pc, bound⟩ := fetched_extent fetched
      dsimp only at hj ⊢
      rw [pc, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact code _ (by omega)
    · exact ih _ tail _ hj

/-- The first RET is the last event. No bound is placed on the caller's return
address relative to the function body. -/
theorem returnAt_execution {base n s out} (run : returnAt base n s = some out) :
    ∃ trace, Execution base s trace out ∧ trace.length = n ∧
      trace.getLast?.map (fun e => isReturn e.2) = some true ∧
      ∀ e ∈ trace.dropLast, isReturn e.2 = false := by
  induction n generalizing s with
  | zero => simp [returnAt] at run
  | succ n ih =>
    rw [returnAt] at run
    cases stopped : s.stopped with
    | true => simp [stopped, guard] at run
    | false =>
      cases f : fetch base s with
      | none => simp [stopped, guard, f] at run
      | some i =>
        have one : stepLoaded base s = some (X86.step i s) := by simp [stepLoaded, stopped, guard, f]
        cases ret : isReturn i with
        | true =>
          cases n with
          | zero =>
            have eq : X86.step i s = out := by simpa [stopped, guard, f, ret] using run
            subst out
            exact ⟨[(_,i)], .cons f one (.nil _), rfl, by simpa using ret, by simp⟩
          | succ n => simp [stopped, guard, f, ret] at run
        | false =>
          obtain ⟨trace,tail,len,last,earlier⟩ := ih (by simpa [stopped, guard, f, ret] using run)
          cases trace with
          | nil => simp at last
          | cons j more =>
            exact ⟨(_,i) :: j :: more, .cons f one tail, by simp [len], by simpa using last,
              by intro e member; rcases List.mem_cons.mp member with rfl | h; exact ret; exact earlier e h⟩

theorem sha256_execution (base : Val) (s : Cpu) (message : Crypto.Reference.ByteList) (extent : Nat)
    (entry : CallerEntry base s message extent) :
    ∃ out trace, Execution base s trace out ∧ CallResult s out message ∧
      trace.length = callSteps message.bytes.size ∧
      trace.getLast?.map (fun e => isReturn e.2) = some true ∧
      (∀ e ∈ trace.dropLast, isReturn e.2 = false) ∧ (∀ e ∈ trace, ScalarLeaf e.2) := by
  obtain ⟨out,run,result⟩ := sha256_serial base s message extent entry
  obtain ⟨trace,actual,len,last,earlier⟩ := returnAt_execution run
  exact ⟨out,trace,actual,result,len,last,earlier,actual.scalar⟩

/-- A live loaded transition is deterministic for the oracle in the CPU
state. Two successful first-return evaluations therefore have the same count. -/
theorem returnAt_unique {base n m s a b} (left : returnAt base n s = some a)
    (right : returnAt base m s = some b) : n = m ∧ a = b := by
  induction n generalizing m s with
  | zero => simp [returnAt] at left
  | succ n ih =>
    cases m with
    | zero => simp [returnAt] at right
    | succ m =>
      rw [returnAt] at left right
      cases h : s.stopped with
      | true => simp [h, guard] at left
      | false =>
        cases f : fetch base s with
        | none => simp [h, f, guard] at left
        | some i =>
          cases ret : isReturn i with
          | false =>
            obtain ⟨count,out⟩ := ih (by simpa [h, guard, f, ret] using left)
              (by simpa [h, guard, f, ret] using right)
            exact ⟨congrArg Nat.succ count,out⟩
          | true =>
            cases n <;> cases m <;> simp_all [guard]

/-- Unit instruction cost through the first return is equal for any two valid
serial calls of equal public length, including distinct initial oracles. -/
theorem sha256_unit_cost {base otherBase l r lm rm le re n m a b}
    (leftEntry : CallerEntry base l lm le) (rightEntry : CallerEntry otherBase r rm re)
    (size : lm.bytes.size = rm.bytes.size)
    (left : returnAt base n l = some a) (right : returnAt otherBase m r = some b) : n = m := by
  obtain ⟨_, first, _⟩ := sha256_serial _ _ _ _ leftEntry
  obtain ⟨_, second, _⟩ := sha256_serial _ _ _ _ rightEntry
  exact (returnAt_unique left first).1.trans ((congrArg callSteps size).trans (returnAt_unique second right).1)

end Crypto.X86_64
