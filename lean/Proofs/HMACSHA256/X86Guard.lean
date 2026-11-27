import Proofs.HMACSHA256.Capacity
import Proofs.HMACSHA256.GuardDecoding

namespace Crypto.HMACSHA256.X86_64

open X86

/-- Execute the checked x86-64 capacity-check fragment after the two header
loads. The state at entry has the capacity in RCX and the count in RDX. -/
def runGuard (s : Cpu) : Option Cpu := do
  let sub ← decodeAt entry 0x27
  let checkCapacity ← decodeAt entry 0x2b
  let checked := X86.step checkCapacity (X86.step sub s)
  if checked.rip = s.rip + 10 then
    let cmp ← decodeAt entry 0x31
    let checkCount ← decodeAt entry 0x34
    return X86.step checkCount (X86.step cmp checked)
  else
    return checked

theorem sub_step (s : Cpu) (live : s.ms = none) :
    X86.step ⟨.bin .sub .q (.reg .rcx) (.imm 96), 4⟩ s = { s with
      regs := s.regs.set .rcx (s.regs.get .rcx - 96),
      flags := Flags.sub .q (s.regs.get .rcx) 96 s.flags, rip := s.rip + 4 } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.writeOperand, Cpu.getReg, Cpu.setReg, Cpu.setRip, Cpu.setFlags, Flags.subResult,
    Value.writeView]

theorem cmp_step (s : Cpu) (live : s.ms = none) :
    X86.step ⟨.bin .cmp .q (.reg .rcx) (.reg .rdx), 3⟩ s = { s with
      flags := Flags.sub .q (s.regs.get .rcx) (s.regs.get .rdx) s.flags, rip := s.rip + 3 } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem,
    Cpu.readOperand, Cpu.getReg, Cpu.setRip, Cpu.setFlags]

theorem branch_step (s : Cpu) (disp : Val) (live : s.ms = none)
    (valid : canonical (s.rip + 6 + disp) = true) :
    X86.step ⟨.jcc .b disp, 6⟩ s = { s with
      rip := if s.flags.cf then s.rip + 6 + disp else s.rip + 6 } := by
  cases cf : s.flags.cf <;>
    simp [X86.step, Cpu.stopped, live, Cc.eval, cf, Cpu.setRipChecked, Cpu.setRip]
  simp_all

set_option maxRecDepth 8192 in
theorem runGuard_result (s : Cpu) (live : s.ms = none)
    (target : canonical (s.rip + 0xd9#64) = true) :
    ∃ out, runGuard s = some out ∧ out.mem = s.mem ∧ out.ms = none ∧
      (∀ reg, reg ≠ .rcx → out.regs.get reg = s.regs.get reg) ∧
      out.rip = (if (s.regs.get .rcx).toNat < 96 + (s.regs.get .rdx).toNat then
        s.rip + 0xd9#64 else s.rip + 19#64) ∧ out.flags.df = s.flags.df := by
  obtain ⟨sub, first, cmp, second⟩ := guard_decoded
  unfold runGuard
  rw [sub, first, cmp, second]
  let a := X86.step ⟨.bin .sub .q (.reg .rcx) (.imm 96), 4⟩ s
  have alive : a.ms = none := by simp [a, sub_step s live, live]
  have canonicalA : canonical (a.rip + 6 + 0xcf) = true := by
    simpa [a, sub_step s live, BitVec.add_assoc] using target
  let b := X86.step ⟨.jcc .b 0xcf, 6⟩ a
  have b_eq : b = { a with rip :=
      if (s.regs.get .rcx).toNat < 96 then s.rip + 0xd9#64 else s.rip + 10#64 } := by
    simp [b, branch_step _ _ alive canonicalA, a, sub_step s live, Flags.sub,
      Flags.subCF, Value.uval, BitVec.add_assoc]
  have bLive : b.ms = none := by simpa [b_eq] using alive
  let c := X86.step ⟨.bin .cmp .q (.reg .rcx) (.reg .rdx), 3⟩ b
  have cLive : c.ms = none := by simpa [c, cmp_step b bLive] using bLive
  change (∃ out, (if b.rip = s.rip + 10 then some (X86.step ⟨.jcc .b 0xc6, 6⟩ c)
    else some b) = some out ∧ _)
  have resultSize := capacity_guard (s.regs.get .rcx) (s.regs.get .rdx)
  have ends : s.rip + 0xd9#64 ≠ s.rip + 10#64 :=
    fun eq => (by decide : 0xd9#64 ≠ 10#64) ((BitVec.add_right_inj s.rip).mp eq)
  have sameRegisters (reg : GPR) (other : reg ≠ .rcx) :
      (s.regs.set .rcx (s.regs.get .rcx - 96#64)).get reg = s.regs.get reg :=
    Regs.get_set_ne _ _ _ _ other.symm
  by_cases short : (s.regs.get .rcx).toNat < 96
  · have required := resultSize.mp (Or.inl short)
    simp [b_eq, a, sub_step s live, short, required, ends, live, Flags.sub, Flags.fromResult] <;> exact sameRegisters
  · have canonicalC : canonical (c.rip + 6 + 0xc6) = true := by
      simpa [c, cmp_step b bLive, b_eq, short, BitVec.add_assoc] using target
    rw [branch_step _ _ cLive canonicalC]
    by_cases shortCount : (s.regs.get .rcx - 96#64).toNat < (s.regs.get .rdx).toNat
    · have required := resultSize.mp (Or.inr shortCount)
      simp [-BitVec.toNat_sub, c, cmp_step b bLive, b_eq, a, sub_step s live,
        Flags.sub, Flags.subCF, Flags.fromResult, Value.uval, short, shortCount, required, live, BitVec.add_assoc] <;> exact sameRegisters
    · have required : ¬ (s.regs.get .rcx).toNat < 96 + (s.regs.get .rdx).toNat :=
        fun h => (resultSize.mpr h).elim short shortCount
      simp [-BitVec.toNat_sub, c, cmp_step b bLive, b_eq, a, sub_step s live,
        Flags.sub, Flags.subCF, Flags.fromResult, Value.uval, short, shortCount, required, live, BitVec.add_assoc] <;> exact sameRegisters

end Crypto.HMACSHA256.X86_64
