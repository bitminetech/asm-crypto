import Proofs.RISCV64.Execution

namespace Crypto.RISCV64

def blockGuard : Instruction := ⟨.branch .eq 13 0 516, 4⟩
def startWords : Instruction := ⟨.addi 15 0 0, 2⟩

def advanceBlock : List Instruction :=
  [⟨.addi 12 12 64, 4⟩, ⟨.addi 13 13 (-1), 2⟩, ⟨.jump (-514), 2⟩]

def phaseGuard : Instruction := ⟨.branch .ne 14 0 10, 2⟩

def paddingPhase : List Instruction :=
  [⟨.addi 14 0 1, 2⟩, ⟨.addi 12 2 288, 2⟩, ⟨.add 13 0 16, 2⟩, ⟨.jump (-524), 2⟩]

theorem block_guard (base : Addr) (s : CPU) (pc : s.pc = base + 0xf2) :
    let out := blockGuard.step s
    ImageExecution base s [blockGuard] out ∧
      out.pc = (if s.reg 13#5 = 0 then base + 0x2f6 else base + 0xf6) ∧
      out.mem = s.mem ∧ out.regs = s.regs := by
  refine ⟨.cons (by rw [offset_eq pc (by decide)]; decide +kernel) (by simp) (.nil _), ?_⟩
  have zero : s.reg 0#5 = 0#64 := rfl
  by_cases h : s.reg 13#5 = 0#64 <;>
    simp (config := { decide := true }) [blockGuard, Instruction.step, Branch.taken,
      CPU.advance, pc, BitVec.add_assoc, h, zero]

theorem initialize_words (base : Addr) (s : CPU) (pc : s.pc = base + 0xf6) :
    let out := startWords.step s
    ImageExecution base s [startWords] out ∧ out.pc = base + 0xf8 ∧
      out.reg 15 = 0 ∧ out.mem = s.mem := by
  refine ⟨.cons (by rw [offset_eq pc (by decide)]; decide +kernel) (by simp) (.nil _), ?_⟩
  simp (config := { decide := true }) [startWords, Instruction.step, pc, BitVec.add_assoc, show s.reg 0#5 = 0#64 from rfl]

theorem next_block (base : Addr) (s : CPU) (pc : s.pc = base + 0x2ee) :
    let out := run advanceBlock s
    ImageExecution base s advanceBlock out ∧ out.pc = base + 0xf2 ∧ out.mem = s.mem ∧
      out.reg 12 = s.reg 12 + 64 ∧ out.reg 13 = s.reg 13 - 1 := by
  let add : Instruction := ⟨.addi 12 12 64, 4⟩
  let dec : Instruction := ⟨.addi 13 13 (-1), 2⟩
  have stepPC : (add.step s).pc = base + 0x2f2 := by
    simp [add, Instruction.step, pc, BitVec.add_assoc]
  have jumpPC : (dec.step (add.step s)).pc = base + 0x2f4 := by
    change (add.step s).pc + 2#64 = _
    rw [stepPC, BitVec.add_assoc]; rfl
  refine ⟨.cons (by rw [offset_eq pc (by decide)]; decide +kernel) (by simp)
    (.cons (by rw [offset_eq stepPC (by decide)]; decide +kernel) (by simp)
      (.cons (by rw [offset_eq jumpPC (by decide)]; decide +kernel) (by simp) (.nil _))), ?_⟩
  simp (config := { decide := true }) [advanceBlock, run, Instruction.step, CPU.advance,
    CPU.put, CPU.reg, pc, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem phase_guard (base : Addr) (s : CPU) (pc : s.pc = base + 0x2f6) :
    let out := phaseGuard.step s
    ImageExecution base s [phaseGuard] out ∧
      out.pc = (if s.reg 14#5 = 0 then base + 0x2f8 else base + 0x300) ∧
      out.mem = s.mem ∧ out.regs = s.regs := by
  refine ⟨.cons (by rw [offset_eq pc (by decide)]; decide +kernel) (by simp) (.nil _), ?_⟩
  have zero : s.reg 0#5 = 0#64 := rfl
  by_cases h : s.reg 14#5 = 0#64 <;>
    simp (config := { decide := true }) [phaseGuard, Instruction.step, Branch.taken,
      CPU.advance, pc, BitVec.add_assoc, h, zero]

theorem switch_to_padding (base : Addr) (s : CPU) (pc : s.pc = base + 0x2f8) :
    let out := run paddingPhase s
    ImageExecution base s paddingPhase out ∧ out.pc = base + 0xf2 ∧ out.mem = s.mem ∧
      out.reg 12 = s.reg 2 + 288 ∧ out.reg 13 = s.reg 16 ∧ out.reg 14 = 1 := by
  let phase : Instruction := ⟨.addi 14 0 1, 2⟩
  let ptr : Instruction := ⟨.addi 12 2 288, 2⟩
  let count : Instruction := ⟨.add 13 0 16, 2⟩
  have stepPC : (phase.step s).pc = base + 0x2fa := by
    simp [phase, Instruction.step, pc, BitVec.add_assoc]
  have countPC : (ptr.step (phase.step s)).pc = base + 0x2fc := by
    change (phase.step s).pc + 2#64 = _
    rw [stepPC, BitVec.add_assoc]; rfl
  have jumpPC : (count.step (ptr.step (phase.step s))).pc = base + 0x2fe := by
    change (ptr.step (phase.step s)).pc + 2#64 = _
    rw [countPC, BitVec.add_assoc]; rfl
  refine ⟨.cons (by rw [offset_eq pc (by decide)]; decide +kernel) (by simp)
    (.cons (by rw [offset_eq stepPC (by decide)]; decide +kernel) (by simp)
      (.cons (by rw [offset_eq countPC (by decide)]; decide +kernel) (by simp)
        (.cons (by rw [offset_eq jumpPC (by decide)]; decide +kernel) (by simp) (.nil _)))), ?_⟩
  simp (config := { decide := true }) [paddingPhase, run, Instruction.step, CPU.advance,
    CPU.put, CPU.reg, pc, BitVec.add_assoc]

end Crypto.RISCV64
