import Proofs.HMACSHA256.RISCV64ShortKey
import Proofs.HMACSHA256.RISCV64LongKey
import Proofs.HMACSHA256.RISCV64CopyExecution
import Proofs.HMACSHA256.RISCV64FinishTrace

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference

set_option maxRecDepth 8192
set_option maxHeartbeats 2600000
set_option linter.unusedSimpArgs false

theorem key_arguments_decoded :
    decodeRange key 0x1c 2 = some [
      .scalar ⟨.add 9#5 0#5 10#5, 2⟩,
      .scalar ⟨.add 18#5 0#5 11#5, 2⟩] := by decide +kernel

theorem jump_after_copy_decoded :
    decodeRange key 0x7e 1 = some [.scalar ⟨.jump 10#64, 2⟩] := by decide +kernel

theorem key_test_decoded :
    decodeRange key 0x40 3 = some [
      .scalar ⟨.load .double 6#5 9#5 16#64, 4⟩,
      .scalar ⟨.addi 5#5 0#5 64#64, 4⟩,
      .scalar ⟨.branch .ltu 5#5 6#5 56#64, 4⟩] := by decide +kernel

def keyArgumentEvents (pc : Addr) : List (List Access) :=
  [[.fetch pc 2], [.fetch (pc + 2#64) 2]]

def keyClearEvents (pc dst : Addr) : List (List Access) :=
  (List.range 8).map fun j => [.fetch (pc + BitVec.ofNat 64 (4 * j)) 4,
    .write (dst + BitVec.ofNat 64 (8 * j)) .double]

def keyTestEvents (pc src : Addr) : List (List Access) :=
  [[.fetch pc 4, .read (src + 16#64) .double], [.fetch (pc + 4#64) 4], [.fetch (pc + 8#64) 4]]

def shortKeySetupEvents (pc src : Addr) : List (List Access) :=
  keyTestEvents pc src ++
    [[.fetch (pc + 12#64) 4, .read (src + 8#64) .double],
      [.fetch (pc + 16#64) 2], [.fetch (pc + 18#64) 2]]

theorem key_arguments_events (s : CPU) :
    runOpsEvents ((decodeRange key 0x1c 2).getD []) s = keyArgumentEvents s.pc := by
  rw [key_arguments_decoded, Option.getD_some]
  rfl

theorem key_clear_events (s : CPU) :
    runOpsEvents ((decodeRange key 0x20 8).getD []) s = keyClearEvents s.pc (s.reg 18#5) := by
  rw [key_zero_decoded, Option.getD_some]
  simp (config := {decide := true}) [keyClearEvents, List.range_succ, runOpsEvents, Op.accesses, Op.width,
    Crypto.RISCV64.Op.accesses, Op.step, Instruction.step, Width.store, BitVec.add_assoc]

theorem key_test_events (s : CPU) :
    runOpsEvents ((decodeRange key 0x40 3).getD []) s = keyTestEvents s.pc (s.reg 9#5) := by
  rw [key_test_decoded, Option.getD_some]
  simp (config := {decide := true}) [keyTestEvents, runOpsEvents, Op.accesses, Op.width,
    Crypto.RISCV64.Op.accesses, Op.step, Instruction.step, Width.load, BitVec.add_assoc]

theorem short_key_setup_events (s : CPU)
    (short : (s.mem.read64 (s.reg 9#5 + 16#64)).toNat ≤ 64) :
    runOpsEvents ((decodeRange key 0x40 6).getD []) s = shortKeySetupEvents s.pc (s.reg 9#5) := by
  rw [key_address_decoded, Option.getD_some]
  have small : ¬64 < (s.mem.read64 (s.reg 9#5 + 16#64)).toNat := by omega
  have small' : ¬64 < (s.mem.read64 (16#64 + s.reg 9#5)).toNat := by rwa [BitVec.add_comm]
  simp (config := {decide := true}) [-BitVec.toNat_add, shortKeySetupEvents, keyTestEvents, runOpsEvents,
    Op.accesses, Op.width, Crypto.RISCV64.Op.accesses, Op.step, Instruction.step, Width.load,
    Branch.taken, BitVec.ult, reg_zero, small, small', reg_put, BitVec.add_assoc]

theorem key_call_events (s : CPU) :
    runOpsEvents ((decodeRange key 0x80 3).getD []) s = finishOuterSetupEvents s.pc := by
  rw [key_call_decoded, Option.getD_some]
  simp (config := {decide := true}) [finishOuterSetupEvents, runOpsEvents, Op.accesses, Op.width,
    Crypto.RISCV64.Op.accesses, Op.step, Instruction.step, BitVec.add_assoc]

def keyPrefixEvents (base : Addr) (s : CPU) : List (List Access) :=
  let text := routineAddress base key
  prologueEvents .key s.pc (s.reg 2#5) ++ keyArgumentEvents (text + 0x1c#64) ++
    keyClearEvents (text + 0x20#64) (s.reg 11#5)

def keyExitEvents (base : Addr) (s : CPU) : List (List Access) :=
  epilogueEvents .key (routineAddress base key + 0x88#64) (s.reg 2#5 - 112#64)

def KeyTrace (base : Addr) (s : CPU) (input : ByteList) (events : List (List Access)) : Prop :=
  let text := routineAddress base key
  if 64 < input.bytes.size then
    ∃ (called : CPU) (extent : Nat), CallerEntry (shaAddress base) called input extent ∧
      called.reg 2#5 = s.reg 2#5 - 112#64 ∧ called.reg 10#5 = s.reg 10#5 ∧
      called.reg 11#5 = s.reg 11#5 ∧ called.reg 1#5 = text + 0x88#64 ∧
      events = keyPrefixEvents base s ++ keyTestEvents (text + 0x40#64) (s.reg 10#5) ++
        finishOuterSetupEvents (text + 0x80#64) ++ shaInstructionEvents (callCode input.bytes.size) called ++
        keyExitEvents base s
  else
    events = keyPrefixEvents base s ++ shortKeySetupEvents (text + 0x40#64) (s.reg 10#5) ++
      copyPayloadEvents (text + 0x54#64) (s.reg 10#5 + BitVec.ofNat 64 input.offset)
        (s.reg 11#5) input.bytes.size ++ [[.fetch (text + 0x7e#64) 2]] ++ keyExitEvents base s

theorem key_same_trace {base : Addr} {s t : CPU} {a b : ByteList} {xs ys : List (List Access)}
    (left : KeyTrace base s a xs) (right : KeyTrace base t b ys)
    (pc : s.pc = t.pc) (sp : s.reg 2#5 = t.reg 2#5) (input : s.reg 10#5 = t.reg 10#5)
    (output : s.reg 11#5 = t.reg 11#5) (offset : a.offset = b.offset) (count : a.bytes.size = b.bytes.size) :
    xs = ys := by
  have front : keyPrefixEvents base s = keyPrefixEvents base t := by unfold keyPrefixEvents; rw [pc, sp, output]
  have exit : keyExitEvents base s = keyExitEvents base t := by unfold keyExitEvents; rw [sp]
  by_cases long : 64 < a.bytes.size
  · have other : 64 < b.bytes.size := count ▸ long
    simp only [KeyTrace, if_pos long] at left
    simp only [KeyTrace, if_pos other] at right
    obtain ⟨callA, n, specA, stackA, inA, outA, linkA, traceA⟩ := left
    obtain ⟨callB, m, specB, stackB, inB, outB, linkB, traceB⟩ := right
    have call := sha_same_public_data specA specB
      (public_sha_registers (specA.pc.trans specB.pc.symm) (linkA.trans linkB.symm)
        (stackA.trans (congrArg (· - 112#64) sp) |>.trans stackB.symm)
        (inA.trans input |>.trans inB.symm) (outA.trans output |>.trans outB.symm)) offset count
    rw [traceA, traceB, front, exit, same_sha_instruction_events specA specB call, input]
  · have other : ¬64 < b.bytes.size := count ▸ long
    simp only [KeyTrace, if_neg long] at left
    simp only [KeyTrace, if_neg other] at right
    rw [left, right, front, exit, input, output, offset, count]

end Crypto.HMACSHA256.RISCV64
