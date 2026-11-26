import Models.RISCV64SHA256Fetch
import Proofs.RISCV64.Fragments
import Proofs.RISCV64.Image

namespace Crypto.RISCV64

def Instruction.linear (i : Instruction) : Bool :=
  match i.op with
  | .branch .. | .jump .. | .ret => false
  | _ => true

theorem Instruction.linear_pc {i : Instruction} (h : i.linear = true) (s : CPU) :
    (i.step s).pc = s.pc + BitVec.ofNat 64 i.bytes := by
  rcases i with ⟨op, bytes⟩
  cases op <;> simp_all [Instruction.linear, Instruction.step]

theorem Instruction.linear_ne_return {i : Instruction} (h : i.linear = true) : i.op ≠ .ret := by
  intro ret
  unfold Instruction.linear at h
  rw [ret] at h
  contradiction

theorem linear_end_pc (code : List Instruction) (s : CPU)
    (linear : code.all Instruction.linear = true) :
    (run code s).pc = s.pc + BitVec.ofNat 64 (code.map Instruction.bytes).sum := by
  induction code generalizing s with
  | nil => simp [run]
  | cons i tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at linear
    change (run tail (i.step s)).pc = s.pc + BitVec.ofNat 64 (i.bytes + (tail.map Instruction.bytes).sum)
    rw [ih _ linear.2, i.linear_pc linear.1, BitVec.ofNat_add, BitVec.add_assoc]

/-- A sequence fetched from the recorded image. This relation accounts for
PC changes between instructions and does not execute past a return. -/
inductive ImageExecution (base : Addr) : CPU → List Instruction → CPU → Prop where
  | nil (s : CPU) : ImageExecution base s [] s
  | cons {s out : CPU} {i : Instruction} {tail : List Instruction}
      (decoded : decodeAt (s.pc - base).toNat = some i)
      (last : i.op = .ret → tail = [])
      (rest : ImageExecution base (i.step s) tail out) :
      ImageExecution base s (i :: tail) out

theorem offset_eq {s : CPU} {base : Addr} {off : Nat}
    (pc : s.pc = base + BitVec.ofNat 64 off) (bound : off < 2^64) :
    (s.pc - base).toNat = off := by
  rw [pc, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

theorem ImageExecution.linear_run (base : Addr) (s : CPU) (code : List Instruction) (off : Nat)
    (pc : s.pc = base + BitVec.ofNat 64 off)
    (wellFormed : off + (code.map Instruction.bytes).sum < 2^64)
    (decoded : decodeSeq off code.length = some code)
    (linear : code.all Instruction.linear = true) :
    ImageExecution base s code (run code s) := by
  induction code generalizing s off with
  | nil => exact .nil s
  | cons i tail ih =>
    change ((decodeAt off).bind fun first =>
      (decodeSeq (off + first.bytes) tail.length).map (List.cons first)) =
      some (i :: tail) at decoded
    cases entry : decodeAt off with
    | none => simp [entry] at decoded
    | some head =>
      cases rest : decodeSeq (off + head.bytes) tail.length with
      | none => simp [entry, rest] at decoded
      | some next =>
        simp only [entry, Option.bind_some, rest, Option.map_some, Option.some.injEq, List.cons.injEq] at decoded
        rcases decoded with ⟨sameHead, sameTail⟩
        subst head
        subst next
        simp only [List.all_cons, Bool.and_eq_true] at linear
        have bound : off + i.bytes + (tail.map Instruction.bytes).sum < 2^64 := by
          simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using wellFormed
        have atPC : (i.step s).pc = base + BitVec.ofNat 64 (off + i.bytes) := by
          rw [i.linear_pc linear.1, pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact .cons (by rw [offset_eq pc (by omega)]; exact entry)
          (by
            intro h
            have accepted := linear.1
            unfold Instruction.linear at accepted
            rw [h] at accepted
            contradiction)
          (ih _ _ atPC bound rest linear.2)

theorem ImageExecution.append {base : Addr} {s mid out : CPU} {left right : List Instruction}
    (a : ImageExecution base s left mid) (b : ImageExecution base mid right out)
    (noReturn : ∀ i ∈ left, i.op ≠ .ret) : ImageExecution base s (left ++ right) out := by
  induction a with
  | nil => exact b
  | cons decoded _ rest ih =>
    apply ImageExecution.cons decoded
    · intro h
      exact False.elim (noReturn _ (by simp) h)
    · exact ih b (fun i hi => noReturn i (List.mem_cons_of_mem _ hi))

end Crypto.RISCV64
