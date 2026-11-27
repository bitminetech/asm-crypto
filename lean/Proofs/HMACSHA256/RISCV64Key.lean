import Proofs.HMACSHA256.RISCV64KeyTrace
import Proofs.HMACSHA256.RISCV64FramePermissions
import Proofs.HMACSHA256.RISCV64ShortKey
import Proofs.HMACSHA256.RISCV64CopyExecution
import Proofs.HMACSHA256.RISCV64LongKey
import Proofs.HMACSHA256.RISCV64ShaEntry

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference
open Crypto.ARM64.Imported (caller_region_contains_offset caller_outside_delta)
open Crypto.Baseline (Region)
open Crypto.HMACSHA256.ARM64 (read64_eq_of_cells)

def keyArguments (s : CPU) : CPU :=
  (((s.put 9#5 (s.reg 10#5)).put 18#5 (s.reg 11#5))).advance 4

theorem key_arguments (s : CPU) : runRange key 0x1c 2 s = some (keyArguments s) := by
  unfold runRange
  rw [key_arguments_decoded]
  have zero : s.reg 0#5 = 0#64 := reg_zero s
  simp [runOps, Op.step, Instruction.step, keyArguments, zero]
  simp [CPU.advance, CPU.put, BitVec.add_assoc]

theorem jump_after_copy (s : CPU) : runRange key 0x7e 1 s = some (setPC s (s.pc + 10#64)) := by
  simp [runRange, jump_after_copy_decoded, runOps, Op.step, Instruction.step, setPC]

set_option maxHeartbeats 1700000 in
/-- Return from the small-key path through the same saved-register frame as
the long-key path. Borrow and permission proofs supply the input layout,
the disjoint output area, and the protected save slots. -/
theorem short_key_return (s : CPU) (input : ByteList) (short : input.bytes.size ≤ 64)
    (returnAligned : (s.reg 1#5).toNat % 2 = 0)
    (offsetAt : (enteredFrame .key s).mem.read64 (s.reg 10#5 + 8#64) = BitVec.ofNat 64 input.offset)
    (countAt : (enteredFrame .key s).mem.read64 (s.reg 10#5 + 16#64) = BitVec.ofNat 64 input.bytes.size)
    (inputAt : ∀ i, i < input.bytes.size →
      (enteredFrame .key s).mem.read8 (s.reg 10#5 + BitVec.ofNat 64 (input.offset + i)) =
        input.bytes[i]!.toBitVec)
    (headerApart : ∀ p, p = s.reg 10#5 + 8#64 ∨ p = s.reg 10#5 + 16#64 →
      ∀ i : Fin 8, 64 ≤ (p + BitVec.ofNat 64 i.val - s.reg 11#5).toNat)
    (bytesApart : ∀ i, i < input.bytes.size →
      64 ≤ (s.reg 10#5 + BitVec.ofNat 64 (input.offset + i) - s.reg 11#5).toNat)
    (savesApart : ∀ i : Fin 104, 64 ≤
      ((enteredFrame .key s).reg 2#5 + BitVec.ofNat 64 i.val - s.reg 11#5).toNat) :
    ∃ saved args cleared prepared atTail copied returning out,
      runRange key 0 14 s = some saved ∧ runRange key 0x1c 2 saved = some args ∧
      runRange key 0x20 8 args = some cleared ∧ runRange key 0x40 6 cleared = some prepared ∧
      wordCycles false prepared (input.bytes.size / 8 + 1) = some atTail ∧
      byteCycles false atTail (input.bytes.size % 8 + 1) = some copied ∧
      runRange key 0x7e 1 copied = some returning ∧ returning.pc = s.pc + 0x88#64 ∧
      runRange key 0x88 15 returning = some out ∧
      out.pc = s.reg 1#5 ∧ out.reg 2#5 = s.reg 2#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      (∀ i : Fin 64, out.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) ∧
      prepared.pc = s.pc + 0x54#64 ∧ prepared.reg 30#5 = s.reg 10#5 + BitVec.ofNat 64 input.offset ∧
      prepared.reg 29#5 = s.reg 11#5 ∧ prepared.reg 6#5 = BitVec.ofNat 64 input.bytes.size ∧
      copied.pc = s.pc + 0x7e#64 ∧ returning.reg 2#5 = s.reg 2#5 - 112#64 ∧
      cleared.mem.read64 (cleared.reg 9#5 + 16#64) = BitVec.ofNat 64 input.bytes.size ∧
      (∀ p, 64 ≤ (p - s.reg 11#5).toNat → 104 ≤ (p - (s.reg 2#5 - 112#64)).toNat →
        out.mem.cells p = s.mem.cells p) := by
  let saved := enteredFrame .key s
  let args := keyArguments saved
  have kp : args.reg 9#5 = s.reg 10#5 := by
    simp (config := { decide := true }) [args, keyArguments]
    exact enteredFrame_reg _ _ _ (by decide)
  have dst : args.reg 18#5 = s.reg 11#5 := by
    simp (config := { decide := true }) [args, keyArguments]
    exact enteredFrame_reg _ _ _ (by decide)
  have mem : args.mem = saved.mem := rfl
  have sp : args.reg 2#5 = saved.reg 2#5 := by
    simp (config := { decide := true }) [args, keyArguments]
  obtain ⟨cleared, prepared, atTail, copied, clear, prep, word, bytes, keyValue, frame, pc, restored,
    preparedPC, source, output, count, clearCount⟩ :=
    short_key_body args input short
      (by rw [kp, mem]; exact offsetAt) (by rw [kp, mem]; exact countAt)
      (by rw [kp, mem]; exact inputAt) (by rw [kp, dst]; exact headerApart)
      (by rw [kp, dst]; exact bytesApart)
  have argsPC : args.pc = s.pc + 32#64 := by
    change saved.pc + 4#64 = _
    rw [enteredFrame_pc, BitVec.add_assoc]
    rfl
  have copiedPC : copied.pc = s.pc + 0x7e#64 := by
    rw [pc, argsPC, BitVec.add_assoc]
    rfl
  let returning := setPC copied (copied.pc + 10#64)
  have atRet : returning.pc = s.pc + 0x88#64 := by
    rw [show returning.pc = copied.pc + 10#64 from rfl, copiedPC, BitVec.add_assoc]
    rfl
  obtain ⟨stack, link, regs⟩ := epilogue_restores .key s returning (restored.trans sp) returnAligned
    (by
      intro i
      have preserved := frame (saved.reg 2#5 + BitVec.ofNat 64 i.val)
        (by rw [dst]; exact savesApart i)
      change copied.mem.cells (copied.reg 2#5 + BitVec.ofNat 64 (0 + i.val)) =
        saved.mem.cells (copied.reg 2#5 + BitVec.ofNat 64 (0 + i.val))
      rw [restored, sp, Nat.zero_add, ← mem]
      exact preserved)
  refine ⟨saved, args, cleared, prepared, atTail, copied, returning, restoredFrame .key returning,
    enter_frame .key s, key_arguments saved, clear, prep, word, bytes, jump_after_copy copied, atRet,
    return_frame .key returning, link, stack, regs, ?_, ?_, ?_, output.trans dst, count,
    copiedPC, (restored.trans sp).trans (enteredFrame_sp .key s), clearCount, ?_⟩
  · rw [restoredFrame_memory, ← dst]
    exact keyValue
  · rw [preparedPC, argsPC, BitVec.add_assoc]
    rfl
  · rw [source, kp]
  · intro p outsideKey outsideStack
    rw [restoredFrame_memory]
    exact (frame p (by rwa [dst])).trans
      (enteredFrame_outside .key s p (by simpa only [HmacRoutine.frameSize, HmacRoutine.savedOffset,
        BitVec.add_zero] using outsideStack))

def longKeyState (s : CPU) : CPU :=
  setPC ((s.put 6#5 (s.mem.read64 (s.reg 9#5 + 16#64))).put 5#5 64#64) (s.pc + 64#64)

theorem key_test_long (s : CPU) (long : 64 < (s.mem.read64 (s.reg 9#5 + 16#64)).toNat) :
    runRange key 0x40 3 s = some (longKeyState s) := by
  unfold runRange
  rw [key_test_decoded]
  have zero : s.reg 0#5 = 0#64 := reg_zero s
  simp (config := { decide := true }) [-BitVec.toNat_add, Op.step, Instruction.step, Width.load,
    runOps, Branch.taken, BitVec.ult, zero, long, longKeyState, setPC, BitVec.add_assoc]
  rfl

/-- The long-key path clears K0, selects SHA-256 from the public count,
and checks that the verified callee leaves the trailing half zero. -/
theorem long_key_body (s : CPU) (input : ByteList) (base : Addr) (extent : Nat)
    (long : 64 < input.bytes.size) (bounded : input.bytes.size < 2 ^ 64)
    (countAt : s.mem.read64 (s.reg 9#5 + 16#64) = BitVec.ofNat 64 input.bytes.size)
    (countOffKey : ∀ i : Fin 8, 64 ≤
      (s.reg 9#5 + 16#64 + BitVec.ofNat 64 i.val - s.reg 18#5).toNat)
    (callee : ∀ cleared tested, runRange key 0x20 8 s = some cleared →
      runRange key 0x40 3 cleared = some tested → CallerEntry base (longKeyCall tested) input extent)
    (nonalias : ∀ cleared tested, runRange key 0x20 8 s = some cleared →
      runRange key 0x40 3 cleared = some tested → ∀ i : Fin 64, 32 ≤ i.val →
      ¬ (callerStack (longKeyCall tested)).Contains (s.reg 18#5 + BitVec.ofNat 64 i.val)) :
    ∃ cleared tested out, runRange key 0x20 8 s = some cleared ∧
      runRange key 0x40 3 cleared = some tested ∧
      runRange key 0x80 3 tested = some (longKeyCall tested) ∧
      runUntilReturn base (longKeyCall tested) (callSteps input.bytes.size) = some out ∧
      CallResult (longKeyCall tested) out input ∧ FrameResult (longKeyCall tested) out ∧
      (∀ i : Fin 64, out.mem.read8 (s.reg 18#5 + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) := by
  obtain ⟨cleared, runClear, zeros, frame⟩ := key_zero_byte s
  have carried : cleared.reg 9#5 = s.reg 9#5 ∧ cleared.reg 18#5 = s.reg 18#5 := by
    have same := Option.some.inj (runClear.symm.trans (key_zero s))
    rw [same]
    exact ⟨rfl, rfl⟩
  have count : cleared.mem.read64 (cleared.reg 9#5 + 16#64) = BitVec.ofNat 64 input.bytes.size := by
    rw [carried.1, ← countAt]
    apply read64_eq_of_cells
    intro i
    exact frame _ (countOffKey i)
  have checked : 64 < (cleared.mem.read64 (cleared.reg 9#5 + 16#64)).toNat := by
    rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
    exact long
  let tested := longKeyState cleared
  have test := key_test_long cleared checked
  have dst : tested.reg 18#5 = s.reg 18#5 := by
    simp (config := { decide := true }) [tested, longKeyState]
    exact carried.2
  obtain ⟨out, setup, run, result, saved, digest⟩ := long_key_after_clear tested input long
    base extent (callee cleared tested runClear test)
    (by
      intro i _
      rw [dst]
      exact zeros i)
    (by
      rw [dst]
      exact nonalias cleared tested runClear test)
  exact ⟨cleared, tested, out, runClear, test, setup, run, result, saved, fun i => by
    rw [← dst]
    exact digest i⟩

private theorem cleared_key_reg {before after : CPU}
    (run : runRange key 0x20 8 before = some after) (r : Reg) :
    after.reg r = before.reg r := by
  have effect := Option.some.inj (run.symm.trans (key_zero before))
  rw [effect]
  rfl

private theorem cleared_key_pc {before after : CPU}
    (run : runRange key 0x20 8 before = some after) :
    after.pc = before.pc + 32#64 := by
  have effect := Option.some.inj (run.symm.trans (key_zero before))
  rw [effect]

private theorem cleared_key_memory {before after : CPU}
    (run : runRange key 0x20 8 before = some after) :
    after.mem = Crypto.HMACSHA256.ARM64.writeWords before.mem
      (before.reg 18#5) (fun _ => 0#64) 8 := by
  have effect := Option.some.inj (run.symm.trans (key_zero before))
  rw [effect]

set_option maxRecDepth 8192 in
private theorem call_state_sp (s : CPU) : (longKeyCall s).reg 2#5 = s.reg 2#5 := by
  rw [longKeyCall, setPC_reg,
    reg_put, if_neg (by decide : (2#5 : Reg) ≠ 0), if_neg (by decide : (2#5 : Reg) ≠ 1#5),
    reg_put, if_neg (by decide : (2#5 : Reg) ≠ 0), if_neg (by decide : (2#5 : Reg) ≠ 11#5),
    reg_put, if_neg (by decide : (2#5 : Reg) ≠ 0), if_neg (by decide : (2#5 : Reg) ≠ 10#5)]

set_option maxRecDepth 8192 in
private theorem call_state_link (s : CPU) : (longKeyCall s).reg 1#5 = s.pc + 8#64 := by
  rw [longKeyCall, setPC_reg, reg_put, if_neg (by decide : (1#5 : Reg) ≠ 0), if_pos rfl]

set_option maxRecDepth 8192 in
private theorem call_state_dest (s : CPU) : (longKeyCall s).reg 11#5 = s.reg 18#5 := by
  rw [longKeyCall, setPC_reg,
    reg_put, if_neg (by decide : (11#5 : Reg) ≠ 0), if_neg (by decide : (11#5 : Reg) ≠ 1#5),
    reg_put, if_neg (by decide : (11#5 : Reg) ≠ 0), if_pos rfl]

set_option maxRecDepth 8192 in
private theorem call_state_memory (s : CPU) : (longKeyCall s).mem = s.mem := by
  rw [longKeyCall, setPC_mem, memory_put, memory_put, memory_put]

set_option maxRecDepth 8192 in
private theorem call_state_source (s : CPU) : (longKeyCall s).reg 10#5 = s.reg 9#5 := by
  rw [longKeyCall, setPC_reg,
    reg_put, if_neg (by decide : (10#5 : Reg) ≠ 0), if_neg (by decide : (10#5 : Reg) ≠ 1#5),
    reg_put, if_neg (by decide : (10#5 : Reg) ≠ 0), if_neg (by decide : (10#5 : Reg) ≠ 11#5),
    reg_put, if_neg (by decide : (10#5 : Reg) ≠ 0), if_pos rfl]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5500000 in
/-- The SHA-256 call on the long-key path returns to the decoded epilogue,
which restores the link, stack pointer and saved registers. -/
theorem long_key_return (base : Addr) (s : CPU) (input : ByteList) (extent : Nat)
    (entryPC : s.pc = routineAddress base key)
    (long : 64 < input.bytes.size) (bounded : input.bytes.size < 2 ^ 64)
    (aligned : (s.reg 1#5).toNat % 2 = 0)
    (reserved : 592 ≤ (s.reg 2#5).toNat)
    (countAt : (enteredFrame .key s).mem.read64 (s.reg 10#5 + 16#64) =
      BitVec.ofNat 64 input.bytes.size)
    (countOffKey : ∀ i : Fin 8, 64 ≤
      (s.reg 10#5 + 16#64 + BitVec.ofNat 64 i.val - s.reg 11#5).toNat)
    (saveOffKey : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Disjoint ⟨s.reg 11#5, 64⟩)
    (keyValid : (⟨s.reg 11#5, 64⟩ : Region).Valid)
    (callee : ∀ cleared tested,
      runRange key 0x20 8 (keyArguments (enteredFrame .key s)) = some cleared →
      runRange key 0x40 3 cleared = some tested →
      CallerEntry (shaAddress base) (longKeyCall tested) input extent)
    (keyOffHashStack : ∀ i : Fin 64, 32 ≤ i.val →
      ¬ (⟨s.reg 2#5 - 112#64 - 480#64, 480⟩ : Region).Contains
        (s.reg 11#5 + BitVec.ofNat 64 i.val)) :
    ∃ saved args cleared tested body out,
      runRange key 0 14 s = some saved ∧
      runRange key 0x1c 2 saved = some args ∧
      runRange key 0x20 8 args = some cleared ∧
      runRange key 0x40 3 cleared = some tested ∧ tested.pc = routineAddress base key + 0x80#64 ∧
      runRange key 0x80 3 tested = some (longKeyCall tested) ∧
      runUntilReturn (shaAddress base) (longKeyCall tested) (callSteps input.bytes.size) = some body ∧
      CallerEntry (shaAddress base) (longKeyCall tested) input extent ∧
      (longKeyCall tested).reg 2#5 = s.reg 2#5 - 112#64 ∧
      (longKeyCall tested).reg 10#5 = s.reg 10#5 ∧ (longKeyCall tested).reg 11#5 = s.reg 11#5 ∧
      body.pc = routineAddress base key + 0x88#64 ∧ body.reg 2#5 = s.reg 2#5 - 112#64 ∧
      runRange key 0x88 15 body = some out ∧
      out.pc = s.reg 1#5 ∧ out.reg 2#5 = s.reg 2#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      (∀ i : Fin 64, out.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) ∧
      (∀ p, ¬ (⟨s.reg 2#5 - 592#64, 592⟩ : Region).Contains p →
        ¬ (⟨s.reg 11#5, 64⟩ : Region).Contains p → out.mem.cells p = s.mem.cells p) := by
  let saved := enteredFrame .key s
  let args := keyArguments saved
  have inputReg : args.reg 9#5 = s.reg 10#5 := by
    simp (config := {decide := true}) only [args, keyArguments, reg_advance, reg_put, if_true, if_false]
    exact enteredFrame_reg .key s 10#5 (by decide)
  have keyReg : args.reg 18#5 = s.reg 11#5 := by
    simp (config := {decide := true}) only [args, keyArguments, reg_advance, reg_put, if_true, if_false]
    exact enteredFrame_reg .key s 11#5 (by decide)
  have argsMem : args.mem = saved.mem := rfl
  have argsStack : args.reg 2#5 = saved.reg 2#5 := by
    simp (config := {decide := true}) only [args, keyArguments, reg_advance, reg_put, if_false]
  have argsPC : args.pc = s.pc + 32#64 := by
    change saved.pc + 4#64 = _
    rw [enteredFrame_pc, BitVec.add_assoc]
    rfl
  have clearedLong {cleared : CPU} (clear : runRange key 0x20 8 args = some cleared) :
      64 < (cleared.mem.read64 (cleared.reg 9#5 + 16#64)).toNat := by
    have preserved : cleared.mem.read64 (cleared.reg 9#5 + 16#64) =
        saved.mem.read64 (s.reg 10#5 + 16#64) := by
      have atKey : cleared.reg 9#5 = s.reg 10#5 := by
        exact (cleared_key_reg clear 9#5).trans inputReg
      rw [atKey, ← argsMem]
      apply Crypto.HMACSHA256.ARM64.read64_eq_of_cells
      intro i
      rw [cleared_key_memory clear]
      apply Crypto.HMACSHA256.ARM64.writeWords_outside
      rw [keyReg]
      exact countOffKey i
    rw [preserved, countAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
    exact long
  have testedEq {cleared tested : CPU} (clear : runRange key 0x20 8 args = some cleared)
      (test : runRange key 0x40 3 cleared = some tested) : tested = longKeyState cleared :=
    Option.some.inj (test.symm.trans (key_test_long cleared (clearedLong clear)))
  have stackCall {cleared tested : CPU} (clear : runRange key 0x20 8 args = some cleared)
      (test : runRange key 0x40 3 cleared = some tested) : (longKeyCall tested).reg 2#5 = saved.reg 2#5 := by
    rw [call_state_sp, testedEq clear test]
    simp (config := {decide := true}) only [reg_put, if_false, longKeyState, setPC_reg]
    exact (cleared_key_reg clear 2#5).trans argsStack
  obtain ⟨cleared, tested, body, clear, test, setup, run, result, frame, value⟩ :=
    long_key_body args input (shaAddress base) extent long bounded
      (by rw [inputReg, argsMem]; exact countAt)
      (by rw [inputReg, keyReg]; exact countOffKey) callee
      (by
        intro a b h j i upper
        change ¬ (⟨(longKeyCall b).reg 2#5 - 480#64, 480⟩ : Region).Contains
          (args.reg 18#5 + BitVec.ofNat 64 i.val)
        rw [stackCall h j, keyReg, enteredFrame_sp]
        exact keyOffHashStack i upper)
  have bodySP : body.reg 2#5 = saved.reg 2#5 := result.sp.trans (stackCall clear test)
  have testedPC : tested.pc = routineAddress base key + 0x80#64 := by
    rw [testedEq clear test]
    change cleared.pc + 64#64 = _
    rw [cleared_key_pc clear, argsPC, entryPC]
    simp only [BitVec.add_assoc]
    rfl
  have bodyPC : body.pc = routineAddress base key + 0x88#64 := by
    rw [show body.pc = (longKeyCall tested).reg 1#5 from result.pc, call_state_link, testedPC]
    simp only [BitVec.add_assoc]
    rfl
  let saves : Region := ⟨s.reg 2#5 - 112#64, 112⟩
  let key64 : Region := ⟨s.reg 11#5, 64⟩
  have savedSP : saved.reg 2#5 = saves.base := enteredFrame_sp .key s
  have savesEnd : saves.base.toNat + 112 = (s.reg 2#5).toNat :=
    frame_base_end _ 112 (by omega)
  have savesValid : saves.Valid := by
    change saves.base.toNat + 112 ≤ 2 ^ 64
    rw [savesEnd]
    exact Nat.le_of_lt (s.reg 2#5).isLt
  have nestedBase : saves.base - 480#64 = s.reg 2#5 - 592#64 := by
    change s.reg 2#5 - 112#64 - 480#64 = s.reg 2#5 - 592#64
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc] <;> rfl
  let fullStack : Region := ⟨s.reg 2#5 - 592#64, 592⟩
  have fullEnd : fullStack.base.toNat + 592 = (s.reg 2#5).toNat :=
    frame_base_end _ 592 reserved
  have lowerTop : fullStack.base.toNat + 480 = saves.base.toNat := by omega
  have callerKeep (p : Addr) (offHash : ¬ (callerStack (longKeyCall tested)).Contains p)
      (offKey : ¬ key64.Contains p) : body.mem.cells p = saved.mem.cells p := by
    have offOut : ¬ (callerOutput (longKeyCall tested)).Contains p := by
      intro h
      have dst : (longKeyCall tested).reg 11#5 = s.reg 11#5 := by
        rw [call_state_dest, testedEq clear test]
        simp (config := {decide := true}) only [longKeyState, setPC_reg, reg_put, if_false]
        exact (cleared_key_reg clear 18#5).trans keyReg
      apply offKey
      change ((longKeyCall tested).reg 11#5).toNat ≤ p.toNat ∧
        p.toNat < ((longKeyCall tested).reg 11#5).toNat + 32 at h
      rw [dst] at h
      change (s.reg 11#5).toNat ≤ p.toNat ∧ p.toNat < (s.reg 11#5).toNat + 64
      exact ⟨h.1, by omega⟩
    have keep := frame p offHash offOut
    have mem : (longKeyCall tested).mem = cleared.mem := by
      rw [call_state_memory, testedEq clear test]
      simp only [longKeyState, setPC_mem, memory_put]
    rw [keep, mem, cleared_key_memory clear]
    change (Crypto.HMACSHA256.ARM64.writeWords args.mem (args.reg 18#5) (fun _ => 0#64) 8).cells p =
      saved.mem.cells p
    rw [argsMem, keyReg]
    exact Crypto.HMACSHA256.ARM64.writeWords_outside _ _ _ 8 _ (caller_outside_delta key64 keyValid p offKey)
  have nestedRegion : callerStack (longKeyCall tested) = ⟨fullStack.base, 480⟩ := by
    unfold callerStack entryStack
    change (Region.mk ((longKeyCall tested).reg 2#5 - 480#64) 480) = _
    rw [stackCall clear test, savedSP, nestedBase] <;> rfl
  have restored (i : Fin 104) :
      body.mem.cells (body.reg 2#5 + BitVec.ofNat 64 (0 + i.val)) =
        saved.mem.cells (body.reg 2#5 + BitVec.ofNat 64 (0 + i.val)) := by
    rw [bodySP, savedSP, Nat.zero_add]
    let p := saves.base + BitVec.ofNat 64 i.val
    have inSaves : saves.Contains p := caller_region_contains_offset saves savesValid i.val
      (by have := i.isLt; change i.val < 112; omega)
    apply callerKeep p _ (fun h => saveOffKey p ⟨inSaves, h⟩)
    rw [nestedRegion]
    intro hit
    have lo := inSaves.1
    have hi := hit.2
    change p.toNat < fullStack.base.toNat + 480 at hi
    omega
  obtain ⟨sp, pc, regs⟩ := epilogue_restores .key s body bodySP aligned restored
  have callInput : (longKeyCall tested).reg 10#5 = s.reg 10#5 := by
    rw [call_state_source, testedEq clear test]
    simp (config := {decide := true}) only [longKeyState, setPC_reg, reg_put, if_false]
    exact (cleared_key_reg clear 9#5).trans inputReg
  have callOutput : (longKeyCall tested).reg 11#5 = s.reg 11#5 := by
    rw [call_state_dest, testedEq clear test]
    simp (config := {decide := true}) only [longKeyState, setPC_reg, reg_put, if_false]
    exact (cleared_key_reg clear 18#5).trans keyReg
  refine ⟨saved, args, cleared, tested, body, restoredFrame .key body,
    enter_frame .key s, key_arguments saved, clear, test, testedPC, setup, run, callee cleared tested clear test,
    (stackCall clear test).trans savedSP, callInput, callOutput, bodyPC, bodySP.trans savedSP,
    return_frame .key body,
    pc, sp, regs, (fun i => by rw [restoredFrame_memory, ← keyReg]; exact value i), ?_⟩
  intro p offStack offKey
  have offHash : ¬ (callerStack (longKeyCall tested)).Contains p := by
    rw [nestedRegion]
    intro hit
    apply offStack
    change fullStack.base.toNat ≤ p.toNat ∧ p.toNat < fullStack.base.toNat + 592
    have hi := hit.2
    change p.toNat < fullStack.base.toNat + 480 at hi
    exact ⟨hit.1, by omega⟩
  have offSaves : ¬ saves.Contains p := by
    intro hit
    apply offStack
    change fullStack.base.toNat ≤ p.toNat ∧ p.toNat < fullStack.base.toNat + 592
    have lo := hit.1
    have hi := hit.2
    change p.toNat < saves.base.toNat + 112 at hi
    omega
  rw [restoredFrame_memory, callerKeep p offHash offKey]
  apply enteredFrame_outside
  have delta := caller_outside_delta saves savesValid p offSaves
  change 112 ≤ (p - (s.reg 2#5 - 112#64)).toNat at delta
  change 104 ≤ (p - (s.reg 2#5 - 112#64 + 0#64)).toNat
  rw [BitVec.add_zero]
  omega

private theorem key_sha_target (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base key + 0x80#64) :
    (longKeyCall s).pc = shaAddress base := by
  unfold longKeyCall
  simp only [setPC_pc, pc, routineAddress, shaAddress, BitVec.add_assoc]
  rfl

private theorem encoded_after_key_clear (s out : CPU) (keyBytes : ByteList) (extent : Nat)
    (clear : runRange key 0x20 8 s = some out)
    (layout : keyBytes.WellFormed) (accessible : keyBytes.size ≤ extent)
    (inputValid : (⟨s.reg 9#5, extent⟩ : Region).Valid)
    (keyValid : (⟨s.reg 18#5, 64⟩ : Region).Valid)
    (apart : (⟨s.reg 18#5, 64⟩ : Region).Disjoint ⟨s.reg 9#5, extent⟩)
    (typed : EncodedByteList s.mem (s.reg 9#5) keyBytes) :
    EncodedByteList out.mem (s.reg 9#5) keyBytes := by
  have keep (i : Nat) (within : i < extent) :
      out.mem.cells (s.reg 9#5 + BitVec.ofNat 64 i) = s.mem.cells (s.reg 9#5 + BitVec.ofNat 64 i) := by
    let address := s.reg 9#5 + BitVec.ofNat 64 i
    have inside : (⟨s.reg 9#5, extent⟩ : Region).Contains address :=
      caller_region_contains_offset _ inputValid i within
    have off := caller_outside_delta ⟨s.reg 18#5, 64⟩ keyValid address
      (fun hit => apart address ⟨hit, inside⟩)
    rw [cleared_key_memory clear]
    exact Crypto.HMACSHA256.ARM64.writeWords_outside _ _ _ 8 _ off
  have fits : 24 ≤ extent := by obtain ⟨min, _, off, _⟩ := layout; omega
  have word (offset : Nat) (bound : offset + 8 ≤ extent) :
      out.mem.read64 (s.reg 9#5 + BitVec.ofNat 64 offset) =
        s.mem.read64 (s.reg 9#5 + BitVec.ofNat 64 offset) := by
    apply Crypto.HMACSHA256.ARM64.read64_eq_of_cells
    intro i
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact keep (offset + i.val) (by have := i.isLt; omega)
  have size := word 0 (by omega)
  change out.mem.read64 (s.reg 9#5 + 0#64) = s.mem.read64 (s.reg 9#5 + 0#64) at size
  rw [BitVec.add_zero] at size
  refine ⟨size.trans typed.size, (word 8 (by omega)).trans typed.offset, (word 16 (by omega)).trans typed.count, ?_⟩
  intro i
  unfold Arm64.Memory.read8
  rw [keep _ (by have := i.isLt; obtain ⟨_, _, _, len⟩ := layout; omega)]
  exact typed.bytes i

set_option maxHeartbeats 2100000 in
/-- Independent input and K0 extents establish the SHA call boundary on
the key helper's long-key path, including preservation through clearing. -/
theorem long_key_sha_entry (base : Addr) (s : CPU) (keyBytes : ByteList) (extent : Nat)
    (pc : s.pc = routineAddress base key + 0x20#64)
    (long : 64 < keyBytes.bytes.size)
    (layout : keyBytes.WellFormed) (accessible : keyBytes.size ≤ extent)
    (sizeBound : keyBytes.size < 2 ^ 64) (lengthBound : keyBytes.bytes.size < 2 ^ 61)
    (typed : EncodedByteList s.mem (s.reg 9#5) keyBytes)
    (keyValid : (⟨s.reg 18#5, 64⟩ : Region).Valid)
    (separate : (⟨s.reg 18#5, 64⟩ : Region).Disjoint ⟨s.reg 9#5, extent⟩)
    (codeSeparate : (⟨s.reg 18#5, 64⟩ : Region).Disjoint (callerImage (shaAddress base)))
    (grants : ShaResources (shaAddress base) ((s.put 10#5 (s.reg 9#5)).put 11#5 (s.reg 18#5)) extent)
    (code : ShaCode (shaAddress base) s.mem)
    (linkAligned : (routineAddress base key + 0x88#64).toNat % 2 = 0)
    {cleared tested : CPU} (clear : runRange key 0x20 8 s = some cleared)
    (test : runRange key 0x40 3 cleared = some tested) :
    CallerEntry (shaAddress base) (longKeyCall tested) keyBytes extent := by
  let boundary := (s.put 10#5 (s.reg 9#5)).put 11#5 (s.reg 18#5)
  have arg0 : boundary.reg 10#5 = s.reg 9#5 := by
    simp (config := {decide := true}) only [boundary, reg_put, if_false, if_true]
  have arg1 : boundary.reg 11#5 = s.reg 18#5 := by
    simp (config := {decide := true}) only [boundary, reg_put, if_false, if_true]
  have stack : boundary.reg 2#5 = s.reg 2#5 := by
    simp (config := {decide := true}) only [boundary, reg_put, if_false]
  have inputValid : (⟨s.reg 9#5, extent⟩ : Region).Valid := by
    have region := grants.inputValid
    change (⟨boundary.reg 10#5, extent⟩ : Region).Valid at region
    rwa [arg0] at region
  have clearedTyped := encoded_after_key_clear s cleared keyBytes extent
    clear layout accessible inputValid keyValid separate typed
  have longCount : 64 < (cleared.mem.read64 (cleared.reg 9#5 + 16#64)).toNat := by
    rw [cleared_key_reg clear, clearedTyped.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    · exact long
    · obtain ⟨_, _, _, len⟩ := layout
      omega
  have testedState := Option.some.inj (test.symm.trans (key_test_long cleared longCount))
  have kept (r : Reg) (other₁ : r ≠ 5#5) (other₂ : r ≠ 6#5) :
      tested.reg r = s.reg r := by
    by_cases zero : r = 0
    · subst r
      exact (reg_zero tested).trans (reg_zero s).symm
    · rw [testedState, longKeyState, setPC_reg, reg_put, if_neg zero, if_neg other₁,
        reg_put, if_neg zero, if_neg other₂]
      exact cleared_key_reg clear r
  have source : (longKeyCall tested).reg 10#5 = s.reg 9#5 :=
    (call_state_source tested).trans (kept _ (by decide) (by decide))
  have dest : (longKeyCall tested).reg 11#5 = s.reg 18#5 :=
    (call_state_dest tested).trans (kept _ (by decide) (by decide))
  have sp : (longKeyCall tested).reg 2#5 = s.reg 2#5 :=
    (call_state_sp tested).trans (kept _ (by decide) (by decide))
  have mem : (longKeyCall tested).mem = cleared.mem := by
    rw [call_state_memory, testedState]
    simp only [longKeyState, setPC_mem, memory_put]
  have perm (p : Addr) : (longKeyCall tested).mem.perm p = boundary.mem.perm p := by
    rw [mem, cleared_key_memory clear]
    exact Crypto.HMACSHA256.ARM64.writeWords_perm _ _ _ _ _
  have read (p : Addr) (n : Nat) (h : boundary.mem.canRead p n = true) :
      (longKeyCall tested).mem.canRead p n = true := by
    rw [mem, cleared_key_memory clear]
    exact Crypto.HMACSHA256.ARM64.writeWords_canRead _ _ _ _ _ _ h
  have shaCode : ShaCode (shaAddress base) (longKeyCall tested).mem :=
    code.preserved (by
      intro p inside
      rw [mem, cleared_key_memory clear]
      exact Crypto.HMACSHA256.ARM64.writeWords_outside _ _ _ 8 _
        (caller_outside_delta ⟨s.reg 18#5, 64⟩ keyValid p (fun hit => codeSeparate p ⟨hit, inside⟩)))
      perm read
  have testPC : tested.pc = routineAddress base key + 0x80#64 := by
    rw [testedState]
    change cleared.pc + 64#64 = _
    rw [cleared_key_pc clear, pc]
    simp only [BitVec.add_assoc]
    rfl
  apply establish_sha_entry layout accessible sizeBound lengthBound (s := longKeyCall tested)
  · change EncodedByteList (longKeyCall tested).mem ((longKeyCall tested).reg 10#5) keyBytes
    rw [source, mem]
    exact clearedTyped
  · exact grants.preserved (source.trans arg0.symm) (dest.trans arg1.symm) (sp.trans stack.symm) perm read
  · exact shaCode
  · exact key_sha_target base tested testPC
  · change ((longKeyCall tested).reg 1#5).toNat % 2 = 0
    rw [call_state_link, testPC, BitVec.add_assoc]
    exact linkAligned


private theorem key_frame_valid (s : CPU) (reserved : 112 ≤ (s.reg 2#5).toNat) :
    (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Valid := by
  change (s.reg 2#5 - 112#64).toNat + 112 ≤ 2^64
  rw [BitVec.toNat_sub]
  change (2^64 - 112 + (s.reg 2#5).toNat) % 2^64 + 112 ≤ 2^64
  have := (s.reg 2#5).isLt
  omega

private theorem key_frame_cells (s : CPU) (available : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Valid)
    (p : Addr) (outside : ¬ (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Contains p) :
    (enteredFrame .key s).mem.cells p = s.mem.cells p := by
  have delta := caller_outside_delta _ available p outside
  apply enteredFrame_outside .key s
  change 104 ≤ (p - (s.reg 2#5 - 112#64 + 0#64)).toNat
  rw [BitVec.add_zero]
  exact le_trans (by decide : 104 ≤ 112) delta

private theorem key_saved_bytes (s : CPU) (input : ByteList) (extent : Nat)
    (layout : input.WellFormed) (accessible : input.size ≤ extent)
    (encoded : EncodedByteList s.mem (s.reg 10#5) input)
    (inputValid : (⟨s.reg 10#5, extent⟩ : Region).Valid)
    (available : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Valid)
    (apart : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Disjoint ⟨s.reg 10#5, extent⟩) :
    EncodedByteList (enteredFrame .key s).mem (s.reg 10#5) input := by
  let saved := enteredFrame .key s
  let source : Region := ⟨s.reg 10#5, extent⟩
  have countSpan : 24 ≤ extent := by
    obtain ⟨a, _, b, _⟩ := layout
    omega
  have inputMem (i : Nat) (h : i < extent) :
      saved.mem.cells (s.reg 10#5 + BitVec.ofNat 64 i) =
        s.mem.cells (s.reg 10#5 + BitVec.ofNat 64 i) := by
    apply key_frame_cells s available
    intro hit
    exact apart _ ⟨hit, caller_region_contains_offset source inputValid i h⟩
  have word (offset : Nat) (h : offset + 8 ≤ extent) :
      saved.mem.read64 (s.reg 10#5 + BitVec.ofNat 64 offset) =
        s.mem.read64 (s.reg 10#5 + BitVec.ofNat 64 offset) := by
    apply read64_eq_of_cells
    intro i
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inputMem _ (by have := i.isLt; omega)
  have first := word 0 (by omega)
  change saved.mem.read64 (s.reg 10#5 + 0#64) = s.mem.read64 (s.reg 10#5 + 0#64) at first
  rw [BitVec.add_zero] at first
  refine ⟨first.trans encoded.size, (word 8 (by omega)).trans encoded.offset,
    (word 16 (by omega)).trans encoded.count, ?_⟩
  intro i
  unfold Arm64.Memory.read8
  rw [inputMem _ (by have := i.isLt; obtain ⟨_, _, _, h⟩ := layout; omega)]
  exact encoded.bytes i

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Run the long-key helper through its restored return from independent
input, K0 and stack extents. The nested SHA-256 safety predicate is derived
at the linked call from those extents and the actual decoded stores. -/
theorem long_key_return_from_grants (base : Addr) (s : CPU) (input : ByteList) (extent : Nat)
    (entryPC : s.pc = routineAddress base key)
    (long : 64 < input.bytes.size)
    (layout : input.WellFormed) (accessible : input.size ≤ extent)
    (sizeBound : input.size < 2 ^ 64) (lengthBound : input.bytes.size < 2 ^ 61)
    (aligned : (s.reg 1#5).toNat % 2 = 0) (nestedLink : (routineAddress base key + 0x88#64).toNat % 2 = 0)
    (reserved : 592 ≤ (s.reg 2#5).toNat)
    (encoded : EncodedByteList s.mem (s.reg 10#5) input)
    (code : ShaCode (shaAddress base) s.mem)
    (grants : ShaResources (shaAddress base) (s.put 2#5 (s.reg 2#5 - 112#64)) extent)
    (keyValid : (⟨s.reg 11#5, 64⟩ : Region).Valid)
    (keyInput : (⟨s.reg 11#5, 64⟩ : Region).Disjoint ⟨s.reg 10#5, extent⟩)
    (keyImage : (⟨s.reg 11#5, 64⟩ : Region).Disjoint (callerImage (shaAddress base)))
    (keyStack : (⟨s.reg 2#5 - 112#64 - 480#64, 480⟩ : Region).Disjoint ⟨s.reg 11#5, 64⟩)
    (saveKey : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Disjoint ⟨s.reg 11#5, 64⟩)
    (saveInput : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Disjoint ⟨s.reg 10#5, extent⟩)
    (saveImage : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Disjoint (callerImage (shaAddress base))) :
    ∃ saved args cleared tested body out,
      runRange key 0 14 s = some saved ∧
      runRange key 0x1c 2 saved = some args ∧
      runRange key 0x20 8 args = some cleared ∧
      runRange key 0x40 3 cleared = some tested ∧ tested.pc = routineAddress base key + 0x80#64 ∧
      runRange key 0x80 3 tested = some (longKeyCall tested) ∧
      runUntilReturn (shaAddress base) (longKeyCall tested) (callSteps input.bytes.size) = some body ∧
      CallerEntry (shaAddress base) (longKeyCall tested) input extent ∧
      (longKeyCall tested).reg 2#5 = s.reg 2#5 - 112#64 ∧
      (longKeyCall tested).reg 10#5 = s.reg 10#5 ∧ (longKeyCall tested).reg 11#5 = s.reg 11#5 ∧
      body.pc = routineAddress base key + 0x88#64 ∧ body.reg 2#5 = s.reg 2#5 - 112#64 ∧
      runRange key 0x88 15 body = some out ∧
      out.pc = s.reg 1#5 ∧ out.reg 2#5 = s.reg 2#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      (∀ i : Fin 64, out.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) ∧
      (∀ p, ¬ (⟨s.reg 2#5 - 592#64, 592⟩ : Region).Contains p →
        ¬ (⟨s.reg 11#5, 64⟩ : Region).Contains p → out.mem.cells p = s.mem.cells p) := by
  let saved := enteredFrame .key s
  let args := keyArguments saved
  let shaFrame := s.put 2#5 (s.reg 2#5 - 112#64)
  let saves : Region := ⟨s.reg 2#5 - 112#64, 112⟩
  let source : Region := ⟨s.reg 10#5, extent⟩
  let output : Region := ⟨s.reg 11#5, 64⟩
  have available : saves.Valid := key_frame_valid s (by omega)
  have sourceValid : source.Valid := by
    have old := grants.inputValid
    change ((shaFrame.reg 10#5).toNat + extent ≤ 2^64) at old
    simpa (config := {decide := true}) only [Region.Valid, source, shaFrame, reg_put, if_false] using old
  have countSpan : 24 ≤ extent := by
    obtain ⟨a, _, b, _⟩ := layout
    omega
  have savedTyped := key_saved_bytes s input extent layout accessible encoded sourceValid available saveInput
  have perms (p : Addr) : saved.mem.perm p = s.mem.perm p := by
    rw [enteredFrame_memory]
    exact Crypto.HMACSHA256.ARM64.writeWords_perm _ _ _ _ _
  have reads (p : Addr) (n : Nat) (h : s.mem.canRead p n = true) : saved.mem.canRead p n = true := by
    rw [enteredFrame_memory]
    exact Crypto.HMACSHA256.ARM64.writeWords_canRead _ _ _ _ _ _ h
  have linked : ShaCode (shaAddress base) saved.mem :=
    code.preserved (fun p inside => key_frame_cells s available p (fun h => saveImage p ⟨h,inside⟩)) perms reads
  have inputReg : args.reg 9#5 = s.reg 10#5 := by
    simp (config := {decide := true}) only [args, keyArguments, reg_advance, reg_put, if_false, if_true]
    exact enteredFrame_reg .key s 10#5 (by decide)
  have outputReg : args.reg 18#5 = s.reg 11#5 := by
    simp (config := {decide := true}) only [args, keyArguments, reg_advance, reg_put, if_false, if_true]
    exact enteredFrame_reg .key s 11#5 (by decide)
  have stackReg : args.reg 2#5 = s.reg 2#5 - 112#64 := by
    simp (config := {decide := true}) only [args, keyArguments, reg_advance, reg_put, if_false]
    exact enteredFrame_sp .key s
  have argsPC : args.pc = routineAddress base key + 0x20#64 := by
    change saved.pc + 4#64 = _
    rw [enteredFrame_pc, entryPC, BitVec.add_assoc]
    rfl
  have argsMem : args.mem = saved.mem := rfl
  let beforeHash := (args.put 10#5 (args.reg 9#5)).put 11#5 (args.reg 18#5)
  have newIn : beforeHash.reg 10#5 = shaFrame.reg 10#5 := by
    simp (config := {decide := true}) only [beforeHash, shaFrame, reg_put, if_true, if_false, inputReg]
  have newOut : beforeHash.reg 11#5 = shaFrame.reg 11#5 := by
    simp (config := {decide := true}) only [beforeHash, shaFrame, reg_put, if_true, if_false, outputReg]
  have newStack : beforeHash.reg 2#5 = shaFrame.reg 2#5 := by
    simp (config := {decide := true}) only [beforeHash, shaFrame, reg_put, if_true, if_false, stackReg]
  have callGrants : ShaResources (shaAddress base) beforeHash extent :=
    grants.preserved newIn newOut newStack (by
      intro p
      simpa only [beforeHash, shaFrame, memory_put, argsMem] using perms p)
      (by
        intro p n h
        simpa only [beforeHash, memory_put, argsMem] using
          reads p n (by simpa only [shaFrame, memory_put] using h))
  have typed : EncodedByteList args.mem (args.reg 9#5) input := by
    rw [argsMem, inputReg]
    exact savedTyped
  have bound : input.bytes.size < 2^64 := by
    obtain ⟨_, _, _, h⟩ := layout
    omega
  refine long_key_return base s input extent entryPC long bound aligned reserved savedTyped.count
    ?_ saveKey keyValid ?_ ?_
  · intro i
    let p := s.reg 10#5 + 16#64 + BitVec.ofNat 64 i.val
    have within : 16 + i.val < source.bytes := by
      change 16 + i.val < extent
      have := i.isLt
      omega
    have inSource : source.Contains p := by
      simpa only [p, source, BitVec.ofNat_add, BitVec.add_assoc] using
        caller_region_contains_offset source sourceValid (16 + i.val) within
    exact caller_outside_delta output keyValid p (fun h => keyInput p ⟨h, inSource⟩)
  · intro cleared tested clear test
    exact long_key_sha_entry base args input extent argsPC long layout accessible sizeBound lengthBound typed
      (by rw [outputReg]; exact keyValid)
      (by rw [outputReg, inputReg]; exact keyInput)
      (by rw [outputReg]; exact keyImage)
      callGrants (by rw [argsMem]; exact linked) nestedLink clear test
  · intro i _ hit
    exact keyStack _ ⟨hit, caller_region_contains_offset output keyValid i.val i.isLt⟩

set_option maxRecDepth 8192

private theorem key_arguments_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base key + 0x1c#64)
    (aligned : (routineAddress base key).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base key) key.image.size = true) :
    RangeAllowed key base 0x1c 2 s := by
  refine ⟨_, key_arguments_decoded, ?_⟩
  hmac_range_permissions pc aligned exec pc pc pc pc

set_option maxHeartbeats 3000000 in
private theorem key_zero_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base key + 0x20#64)
    (aligned : (routineAddress base key).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base key) key.image.size = true)
    (keyAligned : (s.reg 18#5).toNat % 8 = 0)
    (keyWrite : s.mem.canWrite (s.reg 18#5) 64 = true) :
    RangeAllowed key base 0x20 8 s := by
  refine ⟨_, key_zero_decoded, ?_⟩
  simp only [List.map_cons, List.map_nil]
  hmac_range_permissions pc aligned exec pc pc keyAligned keyWrite

private theorem key_test_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base key + 0x40#64)
    (aligned : (routineAddress base key).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base key) key.image.size = true)
    (count : (Access.read (s.reg 9#5 + 16#64) .double).permitted s.mem = true) :
    RangeAllowed key base 0x40 3 s := by
  refine ⟨_, key_test_decoded, ?_⟩
  hmac_range_permissions pc aligned exec pc pc pc pc

private theorem key_call_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base key + 0x80#64)
    (aligned : (routineAddress base key).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base key) key.image.size = true) :
    RangeAllowed key base 0x80 3 s := by
  refine ⟨_, key_call_decoded, ?_⟩
  hmac_range_permissions pc aligned exec pc pc pc pc

private theorem key_prefix_fetched (base : Addr) (s saved args cleared : CPU)
    (enter : runRange key 0 14 s = some saved)
    (arguments : runRange key 0x1c 2 saved = some args)
    (clear : runRange key 0x20 8 args = some cleared)
    (entryPC : s.pc = routineAddress base key)
    (loaded : key.Loaded (routineAddress base key) s.mem.read8)
    (codeAligned : (routineAddress base key).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base key) key.image.size = true)
    (stackAligned : (s.reg 2#5 - 112#64).toNat % 8 = 0)
    (stackWrite : s.mem.canWrite (s.reg 2#5 - 112#64) 112 = true)
    (keyAligned : (s.reg 11#5).toNat % 8 = 0)
    (keyWrite : s.mem.canWrite (s.reg 11#5) 64 = true) :
    ProgramExecution base s (keyPrefixEvents base s) cleared ∧
      (keyPrefixEvents base s).length = 24 ∧
      cleared.pc = routineAddress base key + 0x40#64 ∧ cleared.reg 9#5 = s.reg 10#5 := by
  have savedEq : saved = enteredFrame .key s := Option.some.inj (enter.symm.trans (enter_frame .key s))
  have argsEq : args = keyArguments saved :=
    Option.some.inj (arguments.symm.trans (key_arguments saved))
  have savedPC : saved.pc = routineAddress base key + 0x1c#64 := by
    rw [savedEq, enteredFrame_pc, entryPC]
  have argsPC : args.pc = routineAddress base key + 0x20#64 := by
    rw [argsEq]
    change saved.pc + 4#64 = _
    rw [savedPC, BitVec.add_assoc]
    rfl
  have clearPC : cleared.pc = routineAddress base key + 0x40#64 := by
    rw [cleared_key_pc clear, argsPC, BitVec.add_assoc]
    rfl
  have originalKey : args.reg 18#5 = s.reg 11#5 := by
    rw [argsEq]
    simp (config := {decide := true}) only [keyArguments, reg_advance, reg_put, if_true, if_false]
    rw [savedEq]
    exact enteredFrame_reg .key s 11#5 (by decide)
  have originalInput : cleared.reg 9#5 = s.reg 10#5 := by
    rw [cleared_key_reg clear, argsEq]
    simp (config := {decide := true}) only [keyArguments, reg_advance, reg_put, if_true, if_false]
    rw [savedEq]
    exact enteredFrame_reg .key s 10#5 (by decide)
  have readonly : RoutineReadOnly key base s.mem := routine_readonly_of_exec exec
  have belongs : key = entry ∨ key = key ∨ key = finish := .inr (.inl rfl)
  have keepsExec {final events} (execution : ProgramExecution base s events final) :
      final.mem.canExec (routineAddress base key) key.image.size = true :=
    (allPerm_eq_of_perm execution.perm _ _ _).trans exec
  obtain ⟨pro, na⟩ := run_range_observes belongs enter loaded readonly
    (frame_prologue_allowed .key base s entryPC codeAligned exec stackAligned stackWrite)
    (entered_decoded .key)
  obtain ⟨imageA, roA⟩ := pro.keeps_routine loaded readonly
  obtain ⟨prepare, nb⟩ := run_range_observes belongs arguments imageA roA
    (key_arguments_allowed base saved savedPC codeAligned (keepsExec pro)) key_arguments_decoded
  have throughArgs := pro.append prepare
  obtain ⟨imageB, roB⟩ := throughArgs.keeps_routine loaded readonly
  have outputWrite : args.mem.canWrite (args.reg 18#5) 64 = true := by
    rw [originalKey, (throughArgs.permissions _ _).1]
    exact keyWrite
  obtain ⟨zero, nc⟩ := run_range_observes belongs clear imageB roB
    (key_zero_allowed base args argsPC codeAligned (keepsExec throughArgs)
      (originalKey.symm ▸ keyAligned) outputWrite) key_zero_decoded
  have traceA := key_arguments_events saved
  have traceB := key_clear_events args
  simp only [key_arguments_decoded, key_zero_decoded, Option.getD_some] at traceA traceB
  have events := throughArgs.append zero
  have count := show
      (runOpsEvents (enterCode .key) s ++
        (runOpsEvents ((decodeRange key 0x1c 2).getD []) saved ++
          runOpsEvents ((decodeRange key 0x20 8).getD []) args)).length = 24 from by
    simp only [key_arguments_decoded, key_zero_decoded, Option.getD_some, List.length_append, na, nb, nc]
  rw [enter_events, traceA, traceB, savedPC, argsPC, originalKey, List.append_assoc] at events
  have total : (keyPrefixEvents base s).length = 24 := by
    simp only [key_arguments_decoded, key_zero_decoded, Option.getD_some, enter_events, traceA, traceB,
      savedPC, argsPC, originalKey] at count
    exact count
  exact ⟨events, total, clearPC, originalInput⟩

set_option maxHeartbeats 3500000 in
/-- Fetch the long-key helper through the checked SHA-256 call and return
using the caller's code, stack, input, and key-block grants. -/
theorem long_key_return_fetched (base : Addr) (s : CPU) (input : ByteList) (extent : Nat)
    (entryPC : s.pc = routineAddress base key)
    (long : 64 < input.bytes.size)
    (layout : input.WellFormed) (accessible : input.size ≤ extent)
    (sizeBound : input.size < 2 ^ 64) (lengthBound : input.bytes.size < 2 ^ 61)
    (returnAligned : (s.reg 1#5).toNat % 2 = 0)
    (reserved : 592 ≤ (s.reg 2#5).toNat)
    (encoded : EncodedByteList s.mem (s.reg 10#5) input)
    (code : ShaCode (shaAddress base) s.mem)
    (grants : ShaResources (shaAddress base) (s.put 2#5 (s.reg 2#5 - 112#64)) extent)
    (keyValid : (⟨s.reg 11#5, 64⟩ : Region).Valid)
    (keyInput : (⟨s.reg 11#5, 64⟩ : Region).Disjoint ⟨s.reg 10#5, extent⟩)
    (keyImage : (⟨s.reg 11#5, 64⟩ : Region).Disjoint (callerImage (shaAddress base)))
    (keyStack : (⟨s.reg 2#5 - 112#64 - 480#64, 480⟩ : Region).Disjoint ⟨s.reg 11#5, 64⟩)
    (saveKey : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Disjoint ⟨s.reg 11#5, 64⟩)
    (saveInput : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Disjoint ⟨s.reg 10#5, extent⟩)
    (saveImage : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Disjoint (callerImage (shaAddress base)))
    (loaded : key.Loaded (routineAddress base key) s.mem.read8)
    (codeAligned : (routineAddress base key).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base key) key.image.size = true)
    (stackAligned : (s.reg 2#5 - 112#64).toNat % 8 = 0)
    (stackRead : s.mem.canRead (s.reg 2#5 - 112#64) 112 = true)
    (stackWrite : s.mem.canWrite (s.reg 2#5 - 112#64) 112 = true)
    (keyAligned : (s.reg 11#5).toNat % 8 = 0)
    (keyWrite : s.mem.canWrite (s.reg 11#5) 64 = true)
    (countRead : (Access.read (s.reg 10#5 + 16#64) .double).permitted s.mem = true) :
    ∃ out events,
      ProgramExecution base s events out ∧ events.length ≤ 45 + callSteps input.bytes.size ∧
      out.pc = s.reg 1#5 ∧ out.reg 2#5 = s.reg 2#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      (∀ i : Fin 64, out.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) ∧
      (∀ p, ¬ (⟨s.reg 2#5 - 592#64, 592⟩ : Region).Contains p →
        ¬ (⟨s.reg 11#5, 64⟩ : Region).Contains p → out.mem.cells p = s.mem.cells p) ∧
      KeyTrace base s input events := by
  have nestedLink : (routineAddress base key + 0x88#64).toNat % 2 = 0 := by
    rw [BitVec.toNat_add]
    change ((routineAddress base key).toNat + 136) % 2 ^ 64 % 2 = 0
    omega
  obtain ⟨saved, args, cleared, tested, body, out, enter, arguments, clear, test, testedPC, call,
    hash, callEntry, callSP, callInput, callOutput, bodyPC, bodySP, leave, link, stack, registers, value, outside⟩ :=
    long_key_return_from_grants base s input extent entryPC long layout accessible sizeBound lengthBound
      returnAligned nestedLink reserved encoded code grants keyValid keyInput keyImage keyStack
      saveKey saveInput saveImage
  obtain ⟨throughClear, nfront, clearPC, originalInput⟩ :=
    key_prefix_fetched base s saved args cleared enter arguments clear entryPC loaded codeAligned exec
      stackAligned stackWrite keyAligned keyWrite
  have readonly : RoutineReadOnly key base s.mem := routine_readonly_of_exec exec
  have belongs : key = entry ∨ key = key ∨ key = finish := .inr (.inl rfl)
  have keepsExec {final events} (execution : ProgramExecution base s events final) :
      final.mem.canExec (routineAddress base key) key.image.size = true :=
    (allPerm_eq_of_perm execution.perm _ _ _).trans exec
  obtain ⟨imageC, roC⟩ := throughClear.keeps_routine loaded readonly
  have countOk : (Access.read (cleared.reg 9#5 + 16#64) .double).permitted cleared.mem = true := by
    rw [originalInput]
    simp only [Access.permitted, Bool.and_eq_true] at countRead ⊢
    exact ⟨countRead.1, (throughClear.permissions _ _).2 countRead.2⟩
  obtain ⟨select, nd⟩ := run_range_observes belongs test imageC roC
    (key_test_allowed base cleared clearPC codeAligned (keepsExec throughClear) countOk) key_test_decoded
  have throughTest := throughClear.append select
  obtain ⟨imageD, roD⟩ := throughTest.keeps_routine loaded readonly
  obtain ⟨invoke, ne⟩ := run_range_observes belongs call imageD roD
    (key_call_allowed base tested testedPC codeAligned (keepsExec throughTest)) key_call_decoded
  obtain ⟨hashOut, finished, sha, nf⟩ := sha_execution_observations base _ input extent callEntry
  have result := Option.some.inj (finished.symm.trans hash)
  rw [result] at sha
  have throughHash := throughTest.append (invoke.append sha)
  obtain ⟨imageE, roE⟩ := throughHash.keeps_routine loaded readonly
  have savedRead : body.mem.canRead (body.reg 2#5) 112 = true := by
    rw [bodySP]
    exact (throughHash.permissions _ _).2 stackRead
  obtain ⟨ret, ng⟩ := run_range_observes belongs leave imageE roE
    (frame_epilogue_allowed .key base body bodyPC codeAligned (keepsExec throughHash)
      (bodySP.symm ▸ stackAligned) savedRead) (returned_decoded .key)
  refine ⟨out, _, throughHash.append ret, ?_, link, stack, registers, value, outside, ?_⟩
  · simp only [List.length_append]
    omega
  · simp only [KeyTrace, if_pos long]
    refine ⟨longKeyCall tested, extent, callEntry, callSP, callInput, callOutput, ?_, ?_⟩
    · rw [call_state_link, testedPC, BitVec.add_assoc]
      rfl
    · have traceA := key_test_events cleared
      have traceB := key_call_events tested
      simp only [key_test_decoded, key_call_decoded, Option.getD_some] at traceA traceB
      rw [traceA, traceB, return_events, clearPC, originalInput, testedPC, bodyPC, bodySP]
      simp only [keyExitEvents, List.append_assoc]

set_option maxHeartbeats 2600000 in
private theorem key_short_setup_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base key + 0x40#64)
    (aligned : (routineAddress base key).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base key) key.image.size = true)
    (offset : (Access.read (s.reg 9#5 + 8#64) .double).permitted s.mem = true)
    (count : (Access.read (s.reg 9#5 + 16#64) .double).permitted s.mem = true)
    (short : (s.mem.read64 (s.reg 9#5 + 16#64)).toNat ≤ 64) :
    RangeAllowed key base 0x40 6 s := by
  have zero : s.reg 0#5 = 0#64 := reg_zero s
  have falls : Branch.taken .ltu ((0 : Addr) + 64#64) (s.mem.read64 (s.reg 9#5 + 16#64)) = false := by
    change decide (64 < (s.mem.read64 (s.reg 9#5 + 16#64)).toNat) = false
    simp [Nat.not_lt.mpr short]
  refine ⟨_, key_address_decoded, ?_⟩
  simp (config := {decide := true}) only [RangeReady, Op.accesses, Op.width,
    Crypto.RISCV64.Op.accesses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    Op.step, Instruction.step, Width.load, pc_advance, pc_put, reg_advance, reg_put, memory_advance,
    memory_put, if_false, if_true, zero, BitVec.add_assoc, BitVec.zero_add, BitVec.add_zero,
    pc, falls, Bool.false_eq_true, and_true, true_and]
  repeat' apply And.intro
  all_goals first
    | (guard_target =~ (Access.permitted _ (Access.fetch _ _) = true)
       exact fetch_of_grant aligned (by decide) (by decide) exec)
    | assumption
    | rfl
    | decide +kernel

private theorem key_jump_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base key + 0x7e#64)
    (aligned : (routineAddress base key).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base key) key.image.size = true) :
    RangeAllowed key base 0x7e 1 s := by
  refine ⟨_, jump_after_copy_decoded, ?_⟩
  hmac_range_permissions pc aligned exec pc pc pc pc

set_option maxHeartbeats 5000000 in
/-- Fetch the short-key helper to return, using word and byte grants
derived from the independent input and output allocations. -/
theorem short_key_return_fetched (base : Addr) (s : CPU) (input : ByteList) (extent : Nat)
    (entryPC : s.pc = routineAddress base key)
    (short : input.bytes.size ≤ 64)
    (layout : input.WellFormed) (accessible : input.size ≤ extent)
    (returnAligned : (s.reg 1#5).toNat % 2 = 0) (reserved : 112 ≤ (s.reg 2#5).toNat)
    (encoded : EncodedByteList s.mem (s.reg 10#5) input)
    (inputValid : (⟨s.reg 10#5, extent⟩ : Region).Valid) (inputAligned : (s.reg 10#5).toNat % 8 = 0)
    (inputRead : s.mem.canRead (s.reg 10#5) extent = true)
    (keyValid : (⟨s.reg 11#5, 64⟩ : Region).Valid)
    (keyInput : (⟨s.reg 11#5, 64⟩ : Region).Disjoint ⟨s.reg 10#5, extent⟩)
    (saveKey : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Disjoint ⟨s.reg 11#5, 64⟩)
    (saveInput : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Disjoint ⟨s.reg 10#5, extent⟩)
    (loaded : key.Loaded (routineAddress base key) s.mem.read8)
    (codeAligned : (routineAddress base key).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base key) key.image.size = true)
    (stackAligned : (s.reg 2#5 - 112#64).toNat % 8 = 0)
    (stackRead : s.mem.canRead (s.reg 2#5 - 112#64) 112 = true)
    (stackWrite : s.mem.canWrite (s.reg 2#5 - 112#64) 112 = true)
    (keyAligned : (s.reg 11#5).toNat % 8 = 0)
    (keyWrite : s.mem.canWrite (s.reg 11#5) 64 = true) :
    ∃ out events,
      ProgramExecution base s events out ∧
      events.length = 49 + 8 * (input.bytes.size / 8) + 7 * (input.bytes.size % 8) ∧
      out.pc = s.reg 1#5 ∧ out.reg 2#5 = s.reg 2#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      (∀ i : Fin 64, out.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) ∧
      (∀ p, ¬(⟨s.reg 11#5, 64⟩ : Region).Contains p →
        ¬(⟨s.reg 2#5 - 112#64, 112⟩ : Region).Contains p → out.mem.cells p = s.mem.cells p) ∧
      KeyTrace base s input events := by
  let frame : Region := ⟨s.reg 2#5 - 112#64, 112⟩
  let inputRegion : Region := ⟨s.reg 10#5, extent⟩
  let block : Region := ⟨s.reg 11#5, 64⟩
  have frameValid : frame.Valid := key_frame_valid s reserved
  have typed := key_saved_bytes s input extent layout accessible encoded inputValid frameValid saveInput
  obtain ⟨atLeastHeader, offsetAlign, offsetFits, bytesFit⟩ := layout
  have headerFits : 24 ≤ extent := by omega
  have lenBound : input.bytes.size < 2 ^ 64 := by omega
  have payloadFits : input.offset + input.bytes.size ≤ extent := by omega
  have inputApart (i : Nat) (fits : i < extent) :
      64 ≤ (s.reg 10#5 + BitVec.ofNat 64 i - s.reg 11#5).toNat := by
    have within := caller_region_contains_offset inputRegion inputValid i fits
    exact caller_outside_delta block keyValid _ (fun hit => keyInput _ ⟨hit, within⟩)
  have metadataApart (p : Addr) (whereAt : p = s.reg 10#5 + 8#64 ∨ p = s.reg 10#5 + 16#64)
      (i : Fin 8) : 64 ≤ (p + BitVec.ofNat 64 i.val - s.reg 11#5).toNat := by
    rcases whereAt with rfl | rfl
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact inputApart _ (by have := i.isLt; omega)
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact inputApart _ (by have := i.isLt; omega)
  have bytesApart (i : Nat) (hi : i < input.bytes.size) :
      64 ≤ (s.reg 10#5 + BitVec.ofNat 64 (input.offset + i) - s.reg 11#5).toNat :=
    inputApart _ (by omega)
  have savesApart (i : Fin 104) :
      64 ≤ ((enteredFrame .key s).reg 2#5 + BitVec.ofNat 64 i.val - s.reg 11#5).toNat := by
    rw [enteredFrame_sp]
    have fits : i.val < frame.bytes := by change _ < 112; have := i.isLt; omega
    have within := caller_region_contains_offset frame frameValid i.val fits
    exact caller_outside_delta block keyValid _ (fun hit => saveKey _ ⟨within, hit⟩)
  obtain ⟨saved, args, cleared, prepared, tail, copied, returning, out, enter, arguments, clear,
    setup, words, bytes, jump, atReturn, leave, link, stack, registers, value, preparedPC,
    preparedSource, preparedDest, preparedCount, copiedPC, returnSP, clearCount, unchanged⟩ :=
    short_key_return s input short returnAligned typed.offset typed.count
      (fun i hi => typed.bytes ⟨i, hi⟩) metadataApart bytesApart savesApart
  obtain ⟨throughClear, na, clearPC, clearInput⟩ :=
    key_prefix_fetched base s saved args cleared enter arguments clear entryPC loaded codeAligned exec
      stackAligned stackWrite keyAligned keyWrite
  have readonly : RoutineReadOnly key base s.mem := routine_readonly_of_exec exec
  have belongs : key = entry ∨ key = key ∨ key = finish := .inr (.inl rfl)
  have keepsExec {final events} (execution : ProgramExecution base s events final) :
      final.mem.canExec (routineAddress base key) key.image.size = true :=
    (allPerm_eq_of_perm execution.perm _ _ _).trans exec
  have headerRead (off : Nat) (fits : off + 8 ≤ extent) (align : off % 8 = 0) :
      (Access.read (cleared.reg 9#5 + BitVec.ofNat 64 off) .double).permitted cleared.mem = true := by
    rw [clearInput]
    have grant := read_of_grant inputAligned fits align inputRead
    simp only [Access.permitted, Bool.and_eq_true] at grant ⊢
    exact ⟨grant.1, (throughClear.permissions _ _).2 grant.2⟩
  have selectsShort : (cleared.mem.read64 (cleared.reg 9#5 + 16#64)).toNat ≤ 64 := by
    rw [clearCount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lenBound]
    exact short
  obtain ⟨loadedA, roA⟩ := throughClear.keeps_routine loaded readonly
  obtain ⟨prep, nb⟩ := run_range_observes belongs setup loadedA roA
    (key_short_setup_allowed base cleared clearPC codeAligned (keepsExec throughClear)
      (headerRead 8 (by omega) (by decide)) (headerRead 16 (by omega) (by decide)) selectsShort) key_address_decoded
  have throughSetup := throughClear.append prep
  have apart (i : Nat) (inside : i < input.bytes.size) :
      input.bytes.size ≤ (prepared.reg 30#5 + BitVec.ofNat 64 i - prepared.reg 29#5).toNat := by
    rw [preparedSource, preparedDest, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact short.trans (bytesApart i inside)
  obtain ⟨loadedB, roB⟩ := throughSetup.keeps_routine loaded readonly
  have copyData (w : Bool) (off : Nat) (fits : off + (copyWidth w).bytes ≤ input.bytes.size)
      (align : off % (copyWidth w).bytes = 0) :
      (Access.read (prepared.reg 30#5 + BitVec.ofNat 64 off) (copyWidth w)).permitted prepared.mem = true ∧
      (Access.write (prepared.reg 29#5 + BitVec.ofNat 64 off) (copyWidth w)).permitted prepared.mem = true := by
    rw [preparedSource, preparedDest, BitVec.add_assoc, ← BitVec.ofNat_add]
    apply throughSetup.preserves_copy_accesses
    simpa only [Nat.zero_add] using copy_accesses_of_grants
      inputAligned keyAligned offsetAlign (by decide : 0 % 8 = 0) payloadFits
      (by simpa only [Nat.zero_add] using short) inputRead keyWrite w off fits align
  obtain ⟨c, payload, nc, copyTrace⟩ := copy_payload_fetched false base prepared tail copied input.bytes.size
    (by rw [preparedPC, entryPC]; rfl) loadedB roB codeAligned (keepsExec throughSetup)
    preparedCount lenBound apart copyData words bytes
  have throughBytes := throughSetup.append payload
  obtain ⟨loadedD, roD⟩ := throughBytes.keeps_routine loaded readonly
  obtain ⟨jumpStep, ne⟩ := run_range_observes belongs jump loadedD roD
    (key_jump_allowed base copied (by rw [copiedPC, entryPC]) codeAligned (keepsExec throughBytes))
    jump_after_copy_decoded
  have throughJump := throughBytes.append jumpStep
  obtain ⟨loadedE, roE⟩ := throughJump.keeps_routine loaded readonly
  have savedRead : returning.mem.canRead (returning.reg 2#5) 112 = true := by
    rw [returnSP]
    exact (throughJump.permissions _ _).2 stackRead
  obtain ⟨ret, nf⟩ := run_range_observes belongs leave loadedE roE
    (frame_epilogue_allowed .key base returning (by rw [atReturn, entryPC] <;> rfl) codeAligned
      (keepsExec throughJump) (returnSP.symm ▸ stackAligned) savedRead) (returned_decoded .key)
  refine ⟨out, _, throughJump.append ret, ?_, link, stack, registers, value, ?_, ?_⟩
  · simp only [List.length_append, na, nb, nc, ne, nf]
    omega
  · intro p outsideKey outsideFrame
    exact unchanged p (caller_outside_delta block keyValid p outsideKey)
      (Nat.le_trans (by decide : 104 ≤ 112) (caller_outside_delta frame frameValid p outsideFrame))
  · simp only [KeyTrace, if_neg (Nat.not_lt.mpr short)]
    have traceA := short_key_setup_events cleared selectsShort
    simp only [key_address_decoded, Option.getD_some] at traceA
    have jumpTrace : runOpsEvents [.scalar ⟨.jump 10#64, 2⟩] copied = [[.fetch copied.pc 2]] := rfl
    rw [traceA, copyTrace, jumpTrace, return_events, clearPC, clearInput, preparedPC, preparedSource,
      preparedDest, copiedPC, atReturn, returnSP, entryPC]
    simp only [keyExitEvents, List.append_assoc]


end Crypto.HMACSHA256.RISCV64
