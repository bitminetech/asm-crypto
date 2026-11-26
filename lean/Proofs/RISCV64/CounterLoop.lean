import Proofs.RISCV64.Execution

namespace Crypto.RISCV64

def latch (limit : Addr) (back : Addr) : List Instruction :=
  [⟨.addi 15 15 1, 2⟩, ⟨.addi 5 0 limit, if limit = 16 then 2 else 4⟩,
   ⟨.branch .ltu 15 5 back, 4⟩]

theorem latch_execution (base : Addr) (s : CPU) (off : Nat) (limit back : Addr)
    (pc : s.pc = base + BitVec.ofNat 64 off)
    (bound : off + 6 < 2^64)
    (inc : decodeAt off = some ⟨.addi 15 15 1, 2⟩)
    (loadLimit : decodeAt (off + 2) = some ⟨.addi 5 0 limit, if limit = 16 then 2 else 4⟩)
    (branch : decodeAt (off + 2 + (if limit = 16 then 2 else 4)) =
      some ⟨.branch .ltu 15 5 back, 4⟩) :
    ImageExecution base s (latch limit back) (run (latch limit back) s) := by
  let incInst : Instruction := ⟨.addi 15 15 1, 2⟩
  let limitInst : Instruction := ⟨.addi 5 0 limit, if limit = 16 then 2 else 4⟩
  have first : (s.pc - base).toNat = off := offset_eq pc (by omega)
  have second : ((incInst.step s).pc - base).toNat = off + 2 := by
    apply offset_eq ?_ (by omega)
    simp [incInst, Instruction.step, pc, BitVec.ofNat_add, BitVec.add_assoc]
  have third : ((limitInst.step (incInst.step s)).pc - base).toNat = off + 2 + limitInst.bytes := by
    apply offset_eq ?_ (by dsimp [limitInst]; split <;> omega)
    simp [limitInst, incInst, Instruction.step, pc, BitVec.ofNat_add, BitVec.add_assoc]
  exact .cons (by rw [first]; exact inc) (by simp)
    (.cons (by rw [second]; exact loadLimit) (by simp)
      (.cons (by rw [third]; exact branch) (by simp) (.nil _)))

theorem latch_state (s : CPU) (limit : Nat) (back : Addr) (t : Nat)
    (bound : t + 1 < 2^64) (limitBound : limit < 2^64)
    (counter : s.reg 15 = BitVec.ofNat 64 t) :
    let width := if BitVec.ofNat 64 limit = 16 then 2 else 4
    let out := run (latch (BitVec.ofNat 64 limit) back) s
    out.pc = (if t + 1 < limit then s.pc + (2 + BitVec.ofNat 64 width + back)
      else s.pc + (2 + BitVec.ofNat 64 width + 4)) ∧
      out.reg 15 = BitVec.ofNat 64 (t + 1) ∧ out.mem = s.mem ∧
      (∀ r : Reg, r ≠ 5 → r ≠ 15 → out.reg r = s.reg r) := by
  have increment : s.reg 15#5 + 1#64 = BitVec.ofNat 64 (t + 1) := by
    change s.reg 15#5 = BitVec.ofNat 64 t at counter
    rw [counter, BitVec.ofNat_add]
  have compare : (BitVec.ofNat 64 (t + 1)).ult (BitVec.ofNat 64 limit) =
      decide (t + 1 < limit) := by
    rw [BitVec.ult_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt limitBound]
  dsimp only
  by_cases h : t + 1 < limit <;>
    simp (config := { decide := true }) [run, latch, Instruction.step, Branch.taken,
      increment, compare, h, BitVec.add_assoc] <;>
    simp (config := { decide := true }) [CPU.reg, CPU.put, CPU.advance, Vector.getElem_set]
  all_goals
    intro r a b
    have five : 5 ≠ r.toNat := fun h => a (BitVec.eq_of_toNat_eq h.symm)
    have fifteen : 15 ≠ r.toNat := fun h => b (BitVec.eq_of_toNat_eq h.symm)
    simp_all

end Crypto.RISCV64
