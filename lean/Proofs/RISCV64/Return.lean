import Proofs.RISCV64.LoadedExecution

namespace Crypto.RISCV64

def restore : List Instruction :=
  [⟨.addi 10 0 0, 2⟩, ⟨.load .double 8 2 416, 2⟩, ⟨.load .double 9 2 424, 2⟩,
   ⟨.load .double 18 2 432, 2⟩, ⟨.load .double 19 2 440, 2⟩, ⟨.load .double 20 2 448, 2⟩,
   ⟨.load .double 21 2 456, 2⟩, ⟨.load .double 22 2 464, 2⟩, ⟨.load .double 23 2 472, 2⟩,
   ⟨.addi 2 2 480, 2⟩]

def returnInst : Instruction := ⟨.ret, 2⟩

def returnCode : List Instruction := restore ++ [returnInst]

def savedRegisters (s : CPU) : Vector Addr 8 :=
  #v[s.reg 8, s.reg 9, s.reg 18, s.reg 19, s.reg 20, s.reg 21, s.reg 22, s.reg 23]

def savedStackAt (m : Memory) (sp : Addr) : Vector Addr 8 :=
  #v[m.read64 (sp + 416), m.read64 (sp + 424), m.read64 (sp + 432), m.read64 (sp + 440),
     m.read64 (sp + 448), m.read64 (sp + 456), m.read64 (sp + 464), m.read64 (sp + 472)]

def savedStack (s : CPU) : Vector Addr 8 := savedStackAt s.mem (s.reg 2)

private theorem restore_decoded : decodeSeq 0x400 10 = some restore := by decide +kernel

private theorem return_decoded : decodeAt 0x414 = some returnInst := by decide +kernel

/-- The epilogue restores the eight saved registers from the frame, reports
success, releases the frame, and takes the architectural return to ra. -/
theorem return_loaded (base : Addr) (s : CPU) (pc : s.pc = base + 0x400) :
    let out := run returnCode s
    ImageExecution base s returnCode out ∧ out.pc = s.reg 1 &&& ~~~(1 : Addr) ∧
      out.reg 10 = 0 ∧ out.reg 2 = s.reg 2 + 480 ∧ out.mem = s.mem ∧
      savedRegisters out = savedStack s := by
  have straight : restore.all Instruction.linear = true := by decide
  have front := ImageExecution.linear_run base s restore 0x400 pc (by decide) restore_decoded straight
  have endPC : (run restore s).pc = base + 0x414 := by
    simp [run, restore, Instruction.step, pc, BitVec.add_assoc]
  have back : ImageExecution base (run restore s) [returnInst] (returnInst.step (run restore s)) :=
    .cons (by rw [offset_eq endPC (by decide)]; exact return_decoded) (by simp) (.nil _)
  refine ⟨front.append back ?_, ?_⟩
  · have check : restore.all (fun i => !(i.op == .ret)) = true := by decide
    intro i hi
    simpa using List.all_eq_true.mp check i hi
  · simp (config := { decide := true }) [returnCode, returnInst, run, restore,
      Instruction.step, Width.load, savedRegisters, savedStack, savedStackAt, CPU.reg, CPU.put, CPU.advance]

end Crypto.RISCV64
