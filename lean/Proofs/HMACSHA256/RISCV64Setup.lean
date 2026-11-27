import Proofs.HMACSHA256.RISCV64Code
import Proofs.HMACSHA256.ARM64Memory

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64
open Crypto.HMACSHA256.ARM64 (writeWords writeWords_byte writeWords_outside)

def setPC (s : CPU) (p : Addr) : CPU := { s with pc := p }

@[simp] theorem setPC_reg (s : CPU) (p : Addr) (r : Reg) : (setPC s p).reg r = s.reg r := rfl

@[simp] theorem setPC_mem (s : CPU) (p : Addr) : (setPC s p).mem = s.mem := rfl

@[simp] theorem setPC_pc (s : CPU) (p : Addr) : (setPC s p).pc = p := rfl

def decodeRange (routine : Routine) (offset : Nat) : Nat → Option (List Op)
  | 0 => some []
  | count + 1 => do
    let op ← decodeAt routine offset
    return op :: (← decodeRange routine (offset + op.width) count)

def runOps (ops : List Op) (s : CPU) : CPU := ops.foldl (fun st op => op.step st) s

def runRange (routine : Routine) (offset count : Nat) (s : CPU) : Option CPU :=
  (decodeRange routine offset count).map fun ops => runOps ops s

theorem key_zero_decoded :
    decodeRange key 0x20 8 = some (([0, 8, 16, 24, 32, 40, 48, 56] : List Addr).map fun disp =>
      Op.scalar ⟨.store .double 0#5 18#5 disp, 4⟩) := by
  decide +kernel

/-- Eight stores from x0 initialise the complete output block on the
successful-instruction model. The caller must separately justify the accesses. -/
theorem key_zero (s : CPU) :
    runRange key 0x20 8 s =
      some { s with pc := s.pc + 32#64, mem := writeWords s.mem (s.reg 18#5) (fun _ => 0#64) 8 } := by
  unfold runRange
  rw [key_zero_decoded]
  have r0 : s.reg 0#5 = 0#64 := reg_zero s
  simp [runOps, Op.step, Instruction.step, Width.store, writeWords, r0,
    BitVec.add_assoc, CPU.advance, CPU.write]
  rfl

theorem key_zero_byte (s : CPU) :
    ∃ out, runRange key 0x20 8 s = some out ∧
      (∀ i : Fin 64, out.mem.read8 (s.reg 18#5 + BitVec.ofNat 64 i.val) = 0#8) ∧
      (∀ p, 64 ≤ (p - s.reg 18#5).toNat → out.mem.cells p = s.mem.cells p) := by
  refine ⟨_, key_zero s, ?_, ?_⟩
  · intro i
    let byte : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
    have lt : i.val / 8 < 8 := by have := i.isLt; omega
    have wrote := writeWords_byte s.mem (s.reg 18#5) (fun _ => 0#64) 8 (i.val / 8)
      byte lt (by decide)
    have address : 8 * (i.val / 8) + byte.val = i.val := by dsimp [byte]; omega
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, address, BitVec.extractLsb'_zero] using wrote
  · intro p h
    exact writeWords_outside _ _ _ 8 p h

theorem finish_header_decoded :
    decodeRange finish 0x26 6 = some [
      .scalar ⟨.addi 5#5 0#5 120#64, 4⟩,
      .scalar ⟨.store .double 5#5 2#5 0#64, 2⟩,
      .scalar ⟨.addi 5#5 0#5 24#64, 2⟩,
      .scalar ⟨.store .double 5#5 2#5 8#64, 2⟩,
      .scalar ⟨.addi 5#5 0#5 96#64, 4⟩,
      .scalar ⟨.store .double 5#5 2#5 16#64, 2⟩] := by decide +kernel

def finishHeader (s : CPU) : Arm64.Memory :=
  ((s.mem.write64 (s.reg 2#5) 120#64).write64 (s.reg 2#5 + 8#64) 24#64).write64
    (s.reg 2#5 + 16#64) 96#64

theorem finish_header (s : CPU) :
    runRange finish 0x26 6 s =
      some { s.put 5#5 96#64 with pc := s.pc + 16#64, mem := finishHeader s } := by
  unfold runRange
  rw [finish_header_decoded]
  have r0 : s.reg 0#5 = 0#64 := reg_zero s
  simp (config := { decide := true }) [List.foldl, runOps, Op.step, Instruction.step,
    Width.store, r0, BitVec.add_assoc, finishHeader]
  simp [CPU.advance, CPU.write, CPU.put, Vector.set_set, CPU.reg, BitVec.add_assoc]

theorem finish_first_decoded :
    decodeRange finish 0x1c 4 = some [
      .scalar ⟨.add 9#5 0#5 11#5, 2⟩,
      .scalar ⟨.add 18#5 0#5 12#5, 2⟩,
      .scalar ⟨.addi 11#5 2#5 88#64, 2⟩,
      .jal 1#5 0xfffffffffffff09e#64] := by decide +kernel

theorem finish_first_call (s : CPU) :
    runRange finish 0x1c 4 s = some
      { (((s.put 9#5 (s.reg 11#5)).put 18#5 (s.reg 12#5)).put 11#5 (s.reg 2#5 + 88#64)).put
          1#5 (s.pc + 10#64) with pc := s.pc + 0xfffffffffffff0a4#64 } := by
  unfold runRange
  rw [finish_first_decoded]
  have r0 : s.reg 0#5 = 0#64 := reg_zero s
  simp (config := { decide := true }) [List.foldl, runOps, Op.step, Instruction.step,
    r0, BitVec.add_assoc]
  rfl

end Crypto.HMACSHA256.RISCV64
