import Proofs.HMACSHA256.Capacity
import Proofs.HMACSHA256.GuardDecoding

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

/-- Execute the checked RV64 capacity-check fragment after the two header
loads. The state at entry has the capacity in x5 and the count in x6. -/
def runGuard (s : CPU) : Option CPU := do
  let loadLimit ← decodeAt entry 0x2e
  let checkCapacity ← decodeAt entry 0x32
  let checked := checkCapacity.step (loadLimit.step s)
  if checked.pc = s.pc + 8 then
    let sub ← decodeAt entry 0x36
    let checkCount ← decodeAt entry 0x3a
    return checkCount.step (sub.step checked)
  else
    return checked

private theorem reg_with_regs (s : CPU) (pc : Addr) (mem : Memory) (r : Reg) :
    (CPU.mk pc s.regs mem).reg r = s.reg r := rfl

theorem runGuard_result (s : CPU) :
    ∃ out, runGuard s = some out ∧ out.mem = s.mem ∧ out.reg 10#5 = s.reg 10#5 ∧ out.reg 2#5 = s.reg 2#5 ∧
      out.reg 9#5 = s.reg 9#5 ∧ out.reg 18#5 = s.reg 18#5 ∧
      out.reg 19#5 = s.reg 19#5 ∧ out.reg 20#5 = s.reg 20#5 ∧
      out.pc = if (s.reg 5#5).toNat < 96 + (s.reg 6#5).toNat then s.pc + 0xe4 else s.pc + 16 := by
  obtain ⟨limit, first, sub, second⟩ := guard_decoded
  unfold runGuard
  rw [limit, first, sub, second]
  have resultSize := capacity_guard (s.reg 5#5) (s.reg 6#5)
  have branch : s.pc + 0xe4#64 ≠ s.pc + 8#64 :=
    fun eq => (by decide : (0xe4#64 : Addr) ≠ 8#64) ((BitVec.add_right_inj s.pc).mp eq)
  have zero : s.reg 0#5 = 0 := reg_zero s
  by_cases short : (s.reg 5#5).toNat < 96
  · have required := resultSize.mp (Or.inl short)
    simp (config := { decide := true }) [-BitVec.toNat_add, -BitVec.toNat_sub,
        Op.step, Instruction.step, Branch.taken, BitVec.ult, zero,
      short, required, branch, BitVec.add_assoc, reg_with_regs]
  · by_cases shortCount : (s.reg 5#5 - 96#64).toNat < (s.reg 6#5).toNat
    · have required := resultSize.mp (Or.inr shortCount)
      simp (config := { decide := true }) [-BitVec.toNat_add, -BitVec.toNat_sub,
        Op.step, Instruction.step, Branch.taken, BitVec.ult, zero,
        short, shortCount, required, BitVec.add_assoc, reg_with_regs]
    · have required : ¬ (s.reg 5#5).toNat < 96 + (s.reg 6#5).toNat :=
        fun h => (resultSize.mpr h).elim short shortCount
      simp (config := { decide := true }) [-BitVec.toNat_add, -BitVec.toNat_sub,
        Op.step, Instruction.step, Branch.taken, BitVec.ult, zero,
        short, shortCount, required, BitVec.add_assoc, reg_with_regs]

end Crypto.HMACSHA256.RISCV64
