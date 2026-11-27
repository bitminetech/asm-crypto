import Proofs.HMACSHA256.RISCV64Program

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

/-- Relative offsets remain well defined if a linked image is rebased near
the end of the address space. The individual instruction starts are disjoint
in the common base-relative coordinates. -/
private theorem linked_interval (base pc offset : Addr) (size : Nat)
    (valid : offset.toNat + size ≤ 2 ^ 64)
    (inside : (pc - (base + offset)).toNat < size) :
    offset.toNat ≤ (pc - base).toNat ∧ (pc - base).toNat < offset.toNat + size := by
  have relative : pc - base = (pc - (base + offset)) + offset := by
    rw [← BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [relative, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

set_option maxRecDepth 8192 in
private theorem hmac_fetch_inside {r : Routine} {base pc : Addr} {read} {op : Op}
    (actual : r.fetch (decodeAt r) Op.width (routineAddress base r) pc read = some op) :
    (pc - routineAddress base r).toNat < r.image.size := by
  by_contra outside
  unfold Routine.fetch at actual
  simp only [guard, if_neg outside, Bind.bind, Option.bind] at actual
  contradiction

private theorem rejected_guard {p : Prop} [Decidable p] {α : Type} (no : ¬ p)
    (next : Unit → Option α) : ((guard p : Option Unit) >>= next) = none := by
  simp [guard, no, Bind.bind, Option.bind]

private theorem sha_decode_inside (read : Nat → BitVec 8) (off : Nat) (i : Instruction)
    (decoded : decodeBytes read off = some i) : off < codeEnd := by
  by_contra outside
  have impossible : ¬ (off % 2 = 0 ∧ off + 2 ≤ codeEnd) := by omega
  have none : decodeBytes read off = Option.none := rejected_guard impossible _
  rw [none] at decoded
  contradiction

private theorem sha_fetch_inside {start : Addr} {s after : CPU} {trace ret}
    (actual : checkedStep start s = some (after, trace, ret)) :
    (s.pc - start).toNat < codeEnd := by
  unfold checkedStep at actual
  split at actual
  · contradiction
  · rename_i i decoded
    exact sha_decode_inside _ _ i decoded

private theorem hmac_interval {r : Routine} {base pc : Addr} {read} {op : Op}
    (kind : r = entry ∨ r = key ∨ r = finish)
    (actual : r.fetch (decodeAt r) Op.width (routineAddress base r) pc read = some op) :
    (BitVec.ofInt 64 r.offset).toNat ≤ (pc - base).toNat ∧
      (pc - base).toNat < (BitVec.ofInt 64 r.offset).toNat + r.image.size := by
  have valid : (BitVec.ofInt 64 r.offset).toNat + r.image.size ≤ 2 ^ 64 := by
    rcases kind with rfl | rfl | rfl <;> decide +kernel
  exact linked_interval _ _ _ _ valid (hmac_fetch_inside actual)

private theorem sha_interval {base : Addr} {s after : CPU} {trace ret}
    (actual : checkedStep (shaAddress base) s = some (after, trace, ret)) :
    (BitVec.ofInt 64 sha256Offset).toNat ≤ (s.pc - base).toNat ∧
      (s.pc - base).toNat < (BitVec.ofInt 64 sha256Offset).toNat + codeEnd :=
  linked_interval _ _ _ _ (by decide +kernel) (sha_fetch_inside actual)

private theorem routines_equal {r q : Routine} {place : Nat}
    (leftKind : r = entry ∨ r = key ∨ r = finish) (rightKind : q = entry ∨ q = key ∨ q = finish)
    (left : (BitVec.ofInt 64 r.offset).toNat ≤ place ∧ place < (BitVec.ofInt 64 r.offset).toNat + r.image.size)
    (right : (BitVec.ofInt 64 q.offset).toNat ≤ place ∧ place < (BitVec.ofInt 64 q.offset).toNat + q.image.size) :
    r = q := by
  rcases leftKind with rfl | rfl | rfl <;> rcases rightKind with rfl | rfl | rfl
  all_goals first | rfl | exfalso
  all_goals
    have zero : (BitVec.ofInt 64 entry.offset).toNat = 0 := by decide +kernel
    have keyBase : (BitVec.ofInt 64 key.offset).toNat = 816 := by decide +kernel
    have finishBase : (BitVec.ofInt 64 finish.offset).toNat = 992 := by decide +kernel
    have entryEnd : entry.image.size ≤ 816 := by decide +kernel
    have keyEnd : key.image.size ≤ 176 := by decide +kernel
    simp only [zero, keyBase, finishBase, Nat.zero_add] at left right
    omega

private theorem hmac_excludes_sha {r : Routine} {base : Addr} {s after : CPU} {read} {op : Op}
    {trace ret}
    (kind : r = entry ∨ r = key ∨ r = finish)
    (hmac : r.fetch (decodeAt r) Op.width (routineAddress base r) s.pc read = some op)
    (sha : checkedStep (shaAddress base) s = some (after, trace, ret)) : False := by
  have upper := (hmac_interval kind hmac).2
  have lower := (sha_interval sha).1
  have far : 4096 ≤ (BitVec.ofInt 64 sha256Offset).toNat := by decide +kernel
  have localBound : (BitVec.ofInt 64 r.offset).toNat + r.image.size ≤ 4096 := by
    rcases kind with rfl | rfl | rfl <;> decide +kernel
  omega

/-- The linked SHA and HMAC code ranges have disjoint instruction addresses.
At an address the executable semantics chooses at most one next state and
one access event. -/
theorem ProgramStep.deterministic {base : Addr} {s u v : CPU} {a b : List Access}
    (left : ProgramStep base s a u) (right : ProgramStep base s b v) :
    a = b ∧ u = v := by
  cases left with
  | hmac kind fetched _ =>
    cases right with
    | hmac other observed _ =>
      have equal := routines_equal kind other (hmac_interval kind fetched) (hmac_interval other observed)
      subst_vars
      have opEq := Option.some.inj (fetched.symm.trans observed)
      subst_vars
      exact ⟨rfl, rfl⟩
    | sha observed =>
      exact (hmac_excludes_sha kind fetched observed).elim
  | sha fetched =>
    cases right with
    | hmac kind observed _ => exact (hmac_excludes_sha kind observed fetched).elim
    | sha observed =>
      have same := Option.some.inj (fetched.symm.trans observed)
      simp only [Prod.mk.injEq] at same
      exact ⟨same.2.1, same.1⟩

theorem ProgramExecution.deterministic {base : Addr} {s u v : CPU} {a b : List (List Access)}
    (left : ProgramExecution base s a u) (right : ProgramExecution base s b v)
    (steps : a.length = b.length) : a = b ∧ u = v := by
  induction left generalizing b v with
  | nil =>
    cases right with
    | nil => exact ⟨rfl, rfl⟩
    | cons => simp at steps
  | cons head _ ih =>
    cases right with
    | nil => simp at steps
    | cons next rest =>
      obtain ⟨rfl, rfl⟩ := head.deterministic next
      obtain ⟨rfl, rfl⟩ := ih rest (Nat.succ.inj steps)
      exact ⟨rfl, rfl⟩

end Crypto.HMACSHA256.RISCV64
