import Proofs.HMACSHA256.RISCV64OuterSetup
import Proofs.HMACSHA256.RISCV64Program

set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

private def innerArgs (s : CPU) : CPU :=
  let args := ((s.put 9#5 (s.reg 11#5)).put 18#5 (s.reg 12#5)).put 11#5 (s.reg 2#5 + 88#64)
  args.put 1#5 (s.pc + 10#64)

def innerCallState (s : CPU) : CPU :=
  setPC (innerArgs s) (s.pc - 3932#64)

theorem inner_call (s : CPU) : runRange finish 0x1c 4 s = some (innerCallState s) := by
  rw [finish_first_call]
  unfold innerCallState innerArgs setPC
  rw [BitVec.sub_eq_add_neg]
  rfl

attribute [local irreducible] entry key routineAddress shaAddress

private theorem inner_reg (s : CPU) (r : Reg) (nonzero : r ≠ 0) :
    (innerCallState s).reg r =
      if r = 1#5 then s.pc + 10#64 else if r = 11#5 then s.reg 2#5 + 88#64
      else if r = 18#5 then s.reg 12#5 else if r = 9#5 then s.reg 11#5 else s.reg r := by
  simp only [innerCallState, setPC_reg, innerArgs, reg_put, if_neg nonzero]

private theorem outer_reg (s : CPU) (r : Reg) (nonzero : r ≠ 0) :
    (outerCallState s).reg r =
      if r = 1#5 then s.pc + 8#64 else if r = 11#5 then s.reg 18#5
      else if r = 10#5 then s.reg 2#5 else s.reg r := by
  simp only [outerCallState, setPC_reg, reg_put, if_neg nonzero]

private theorem inner_memory (s : CPU) : (innerCallState s).mem = s.mem := by
  simp only [innerCallState, setPC_mem, innerArgs, memory_put]

private theorem outer_memory (s : CPU) : (outerCallState s).mem = s.mem := by
  simp only [outerCallState, setPC_mem, memory_put]

attribute [local irreducible] innerCallState outerCallState

theorem inner_call_registers (s : CPU) :
    (innerCallState s).reg 10#5 = s.reg 10#5 ∧
    (innerCallState s).reg 11#5 = s.reg 2#5 + 88#64 ∧
    (innerCallState s).reg 9#5 = s.reg 11#5 ∧
    (innerCallState s).reg 18#5 = s.reg 12#5 ∧
    (innerCallState s).reg 2#5 = s.reg 2#5 ∧
    (innerCallState s).reg 1#5 = s.pc + 10#64 ∧ (innerCallState s).mem = s.mem := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, inner_memory s⟩ <;>
    rw [inner_reg _ _ (by decide)] <;> rfl

theorem outer_call_registers (s : CPU) :
    (outerCallState s).reg 10#5 = s.reg 2#5 ∧
    (outerCallState s).reg 11#5 = s.reg 18#5 ∧
    (outerCallState s).reg 2#5 = s.reg 2#5 ∧
    (outerCallState s).reg 1#5 = s.pc + 8#64 ∧ (outerCallState s).mem = s.mem := by
  refine ⟨?_, ?_, ?_, ?_, outer_memory s⟩ <;>
    rw [outer_reg _ _ (by decide)] <;> rfl

private theorem inner_call_relocation :
    BitVec.ofInt 64 finish.offset + (0x1c#64 + (-3932#64)) =
      BitVec.ofInt 64 sha256Offset := by decide +kernel

private theorem outer_call_relocation :
    BitVec.ofInt 64 finish.offset + (0xb4#64 + (-4084#64)) =
      BitVec.ofInt 64 sha256Offset := by decide +kernel

theorem inner_call_target (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base finish + 0x1c#64) :
    (innerCallState s).pc = shaAddress base := by
  simp only [innerCallState, setPC_pc]
  rw [BitVec.sub_eq_add_neg, pc, routineAddress, shaAddress, BitVec.add_assoc, BitVec.add_assoc, inner_call_relocation]

theorem outer_call_target (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base finish + 0xb4#64) :
    (outerCallState s).pc = shaAddress base := by
  simp only [outerCallState, setPC_pc]
  rw [BitVec.sub_eq_add_neg, pc, routineAddress, shaAddress, BitVec.add_assoc, BitVec.add_assoc, outer_call_relocation]

theorem callee_return_at_inner (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base finish + 0x1c#64) :
    (innerCallState s).reg 1#5 = routineAddress base finish + 0x26#64 := by
  rw [inner_call_registers s |>.2.2.2.2.2.1, pc, BitVec.add_assoc]
  rfl

theorem callee_return_at_outer (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base finish + 0xb4#64) :
    (outerCallState s).reg 1#5 = routineAddress base finish + 0xbc#64 := by
  rw [outer_call_registers s |>.2.2.2.1, pc, BitVec.add_assoc]
  rfl

end Crypto.HMACSHA256.RISCV64
