import Proofs.HMACSHA256.RISCV64Ranges
import Proofs.HMACSHA256.RISCV64Setup
import Proofs.HMACSHA256.EncodedByteList

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

theorem entry_key_call_decoded :
    decodeRange entry 0x3e 3 = some [
      .scalar ⟨.add 10#5 0#5 9#5, 2⟩,
      .scalar ⟨.add 11#5 0#5 2#5, 2⟩,
      .jal 1#5 0x2ee#64] := by decide +kernel

def entryKeyCall (s : CPU) : CPU :=
  setPC ((((s.put 10#5 (s.reg 9#5)).put 11#5 (s.reg 2#5))).put 1#5 (s.pc + 8#64))
    (s.pc + 0x2f2#64)

theorem entry_key_call (s : CPU) :
    runRange entry 0x3e 3 s = some (entryKeyCall s) := by
  unfold runRange
  rw [entry_key_call_decoded]
  have zero : s.reg 0#5 = 0#64 := reg_zero s
  simp (config := { decide := true }) [runOps, Op.step, Instruction.step, zero, entryKeyCall,
    setPC, CPU.advance, CPU.put, BitVec.add_assoc]
  simp (config := { decide := true }) [CPU.reg, Vector.getElem_set]

theorem entry_finish_call_decoded :
    decodeRange entry 0x104 4 = some [
      .scalar ⟨.addi 10#5 19#5 8#64, 4⟩,
      .scalar ⟨.add 11#5 0#5 2#5, 2⟩,
      .scalar ⟨.add 12#5 0#5 20#5, 2⟩,
      .jal 1#5 0x2d4#64] := by decide +kernel

def entryFinishCall (s : CPU) : CPU :=
  setPC (((((s.put 10#5 (s.reg 19#5 + 8#64)).put 11#5 (s.reg 2#5))).put
    12#5 (s.reg 20#5)).put 1#5 (s.pc + 12#64)) (s.pc + 0x2dc#64)

theorem entry_finish_call (s : CPU) :
    runRange entry 0x104 4 s = some (entryFinishCall s) := by
  unfold runRange
  rw [entry_finish_call_decoded]
  have zero : s.reg 0#5 = 0#64 := reg_zero s
  simp (config := { decide := true }) [runOps, Op.step, Instruction.step, zero, entryFinishCall,
    setPC, CPU.advance, CPU.put, BitVec.add_assoc]
  simp (config := { decide := true }) [CPU.reg, Vector.getElem_set]

theorem entry_key_target (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base entry + 0x3e#64) :
    (entryKeyCall s).pc = routineAddress base key := by
  have jump : BitVec.ofInt 64 entry.offset + (0x3e#64 + 0x2f2#64) = BitVec.ofInt 64 key.offset := by
    decide +kernel
  change s.pc + 0x2f2#64 = _
  rw [pc, routineAddress, routineAddress, BitVec.add_assoc, BitVec.add_assoc, jump]

theorem entry_finish_target (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base entry + 0x104#64) :
    (entryFinishCall s).pc = routineAddress base finish := by
  have jump : BitVec.ofInt 64 entry.offset + (0x104#64 + 0x2dc#64) = BitVec.ofInt 64 finish.offset := by
    decide +kernel
  change s.pc + 0x2dc#64 = _
  rw [pc, routineAddress, routineAddress, BitVec.add_assoc, BitVec.add_assoc, jump]

theorem entry_finish_arguments (s : CPU) :
    (entryFinishCall s).reg 10#5 = s.reg 19#5 + 8#64 ∧
    (entryFinishCall s).reg 11#5 = s.reg 2#5 ∧ (entryFinishCall s).reg 12#5 = s.reg 20#5 ∧
    (entryFinishCall s).reg 2#5 = s.reg 2#5 ∧ (entryFinishCall s).reg 1#5 = s.pc + 12#64 ∧
    (entryFinishCall s).mem = s.mem := by
  simp (config := { decide := true }) only [entryFinishCall, setPC_reg, setPC_mem, reg_put, memory_put,
    if_true, if_false, and_true]

theorem entry_key_arguments (s : CPU) :
    (entryKeyCall s).reg 10#5 = s.reg 9#5 ∧ (entryKeyCall s).reg 11#5 = s.reg 2#5 ∧
    (entryKeyCall s).reg 2#5 = s.reg 2#5 ∧ (entryKeyCall s).reg 1#5 = s.pc + 8#64 ∧
    (entryKeyCall s).mem = s.mem := by
  simp (config := { decide := true }) only [entryKeyCall, setPC_reg, setPC_mem, reg_put, memory_put,
    if_true, if_false, and_true]

theorem entry_finish_encoding (base : Addr) (s : CPU) (inner : Crypto.Reference.ByteList)
    (pc : s.pc = routineAddress base entry + 0x104#64)
    (typed : EncodedByteList s.mem (s.reg 19#5 + 8#64) inner) :
    runRange entry 0x104 4 s = some (entryFinishCall s) ∧
    (entryFinishCall s).pc = routineAddress base finish ∧
    (entryFinishCall s).reg 1#5 = routineAddress base entry + 0x110#64 ∧
    EncodedByteList (entryFinishCall s).mem ((entryFinishCall s).reg 10#5) inner := by
  obtain ⟨input, _, _, _, link, mem⟩ := entry_finish_arguments s
  refine ⟨entry_finish_call s, entry_finish_target base s pc, ?_, ?_⟩
  · rw [link, pc, BitVec.add_assoc]
    rfl
  · rw [input, mem]
    exact typed

theorem ok_decoded :
    decodeRange entry 0x110 1 = some [.scalar ⟨.addi 10#5 0#5 0#64, 2⟩] := by decide +kernel

theorem entry_ok (s : CPU) : runRange entry 0x110 1 s = some ((s.advance 2).put 10#5 0#64) := by
  have zero : s.reg 0#5 = 0#64 := reg_zero s
  simp [runRange, ok_decoded, runOps, Op.step, Instruction.step, zero]

set_option maxRecDepth 8192
set_option maxHeartbeats 2900000
set_option linter.unusedSimpArgs false in
theorem entry_key_call_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base entry + 0x3e#64)
    (aligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true) :
    RangeAllowed entry base 0x3e 3 s := by
  refine ⟨_, entry_key_call_decoded, ?_⟩
  hmac_range_permissions pc aligned exec pc pc pc pc

set_option linter.unusedSimpArgs false in
theorem entry_finish_call_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base entry + 0x104#64)
    (aligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true) :
    RangeAllowed entry base 0x104 4 s := by
  refine ⟨_, entry_finish_call_decoded, ?_⟩
  hmac_range_permissions pc aligned exec pc pc pc pc

set_option linter.unusedSimpArgs false in
theorem entry_ok_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base entry + 0x110#64)
    (aligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true) :
    RangeAllowed entry base 0x110 1 s := by
  refine ⟨_, ok_decoded, ?_⟩
  hmac_range_permissions pc aligned exec pc pc pc pc

end Crypto.HMACSHA256.RISCV64
