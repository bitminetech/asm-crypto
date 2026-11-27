import Proofs.HMACSHA256.RISCV64Pad
import Proofs.HMACSHA256.Reference

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64
open Crypto.HMACSHA256.ARM64 (writeWords writeWords_word writeWords_outside)

theorem outer_mask_decoded :
    decodeRange finish 0x36 9 = some [
      .lui 28#5 0x1717000#64,
      .scalar ⟨.addi 28#5 28#5 0x171#64, 4⟩,
      .scalar ⟨.slli 28#5 28#5 12#6, 2⟩,
      .scalar ⟨.addi 28#5 28#5 0x717#64, 4⟩,
      .scalar ⟨.slli 28#5 28#5 13#6, 2⟩,
      .scalar ⟨.addi 28#5 28#5 0x2e3#64, 4⟩,
      .scalar ⟨.slli 28#5 28#5 13#6, 2⟩,
      .scalar ⟨.addi 28#5 28#5 (-0x3a4#64), 4⟩,
      .scalar ⟨.addi 29#5 2#5 24#64, 4⟩] := by decide +kernel

def outerMaskState (s : CPU) : CPU :=
  (((s.put 28#5 0x5c5c5c5c5c5c5c5c#64).put 29#5 (s.reg 2#5 + 24#64)).advance 30)

theorem outer_mask (s : CPU) : runRange finish 0x36 9 s = some (outerMaskState s) := by
  unfold runRange
  rw [outer_mask_decoded]
  simp (config := { decide := true }) [runOps, Op.step, Instruction.step, outerMaskState,
    BitVec.add_assoc]
  simp [CPU.advance, CPU.put, Vector.set_set, CPU.reg, BitVec.add_assoc]

theorem outer_call_decoded :
    decodeRange finish 0xb4 3 = some [
      .scalar ⟨.add 10#5 0#5 2#5, 2⟩,
      .scalar ⟨.add 11#5 0#5 18#5, 2⟩,
      .jal 1#5 0xfffffffffffff008#64] := by decide +kernel

def outerCallState (s : CPU) : CPU :=
  let st := (s.put 10#5 (s.reg 2#5)).put 11#5 (s.reg 18#5)
  setPC (st.put 1#5 (s.pc + 8#64)) (s.pc - 4084#64)

theorem outer_call (s : CPU) : runRange finish 0xb4 3 s = some (outerCallState s) := by
  unfold runRange
  rw [outer_call_decoded]
  have zero : s.reg 0#5 = 0#64 := reg_zero s
  simp (config := { decide := true }) [runOps, Op.step, Instruction.step, outerCallState,
    zero, BitVec.add_assoc, setPC, BitVec.sub_eq_add_neg]
  rfl

private def headerWord (i : Nat) : Addr := if i = 0 then 120#64 else if i = 1 then 24#64 else 96#64

theorem finish_header_memory (s : CPU) :
    finishHeader s = writeWords s.mem (s.reg 2#5) headerWord 3 := by
  simp [finishHeader, writeWords, headerWord]

theorem finish_header_values (s : CPU) :
    (finishHeader s).read64 (s.reg 2#5) = 120#64 ∧
    (finishHeader s).read64 (s.reg 2#5 + 8#64) = 24#64 ∧
    (finishHeader s).read64 (s.reg 2#5 + 16#64) = 96#64 := by
  rw [finish_header_memory]
  refine ⟨?_, ?_, ?_⟩
  · simpa [headerWord] using
      writeWords_word s.mem (s.reg 2#5) headerWord 3 0 (by decide) (by decide)
  · exact writeWords_word s.mem (s.reg 2#5) headerWord 3 1 (by decide) (by decide)
  · exact writeWords_word s.mem (s.reg 2#5) headerWord 3 2 (by decide) (by decide)

theorem finish_header_outside (s : CPU) (p : Addr) (outside : 24 ≤ (p - s.reg 2#5).toNat) :
    (finishHeader s).cells p = s.mem.cells p := by
  rw [finish_header_memory]
  exact writeWords_outside _ _ _ 3 _ outside

end Crypto.HMACSHA256.RISCV64
