import Proofs.HMACSHA256.ARM64Code
import Proofs.HMACSHA256.ARM64Memory

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

private theorem aligned_setMem (s : Arm64.State) (m : Arm64.Memory) :
    (s.setMem m).spAligned = s.spAligned := rfl

def decodeRange (routine : Routine) (offset count : Nat) : Option (List Arm64.Instr) :=
  (List.range count).mapM fun i => decodeAt routine (offset + 4 * i)

def runRange (routine : Routine) (offset count : Nat) (s : Arm64.State) : Option Arm64.State :=
  (decodeRange routine offset count).map fun instrs => runDecoded instrs s

theorem key_zero_decoded :
    decodeRange key 0x1c 4 = some [
      .stp .W64 .xzr .xzr (.Offset .x1 0#64),
      .stp .W64 .xzr .xzr (.Offset .x1 16#64),
      .stp .W64 .xzr .xzr (.Offset .x1 32#64),
      .stp .W64 .xzr .xzr (.Offset .x1 48#64)] := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- The helper's first four output stores clear all 64 bytes even if the
incoming output contains arbitrary bytes. -/
theorem key_zero (s : Arm64.State)
    (canWrite : ∀ i : Fin 8, s.mem.canWrite
      (s.readReg64 .x1 + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    runRange key 0x1c 4 s = some ((s.setMem
      (writeWords s.mem (s.readReg64 .x1) (fun _ => 0#64) 8)).setPC (s.pc + 16#64)) := by
  have w0 : s.mem.canWrite (s.readReg64 .x1) 8 = true := by simpa using canWrite ⟨0, by decide⟩
  have w1 : s.mem.canWrite (s.readReg64 .x1 + 8#64) 8 = true := canWrite ⟨1, by decide⟩
  have w2 : s.mem.canWrite (s.readReg64 .x1 + 16#64) 8 = true := canWrite ⟨2, by decide⟩
  have w3 : s.mem.canWrite (s.readReg64 .x1 + 24#64) 8 = true := canWrite ⟨3, by decide⟩
  have w4 : s.mem.canWrite (s.readReg64 .x1 + 32#64) 8 = true := canWrite ⟨4, by decide⟩
  have w5 : s.mem.canWrite (s.readReg64 .x1 + 40#64) 8 = true := canWrite ⟨5, by decide⟩
  have w6 : s.mem.canWrite (s.readReg64 .x1 + 48#64) 8 = true := canWrite ⟨6, by decide⟩
  have w7 : s.mem.canWrite (s.readReg64 .x1 + 56#64) 8 = true := canWrite ⟨7, by decide⟩
  unfold runRange
  rw [key_zero_decoded]
  simp (config := { decide := true, maxDischargeDepth := 64 }) [runDecoded,
    Arm64.execInstWithSvc, Arm64.execStp, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned,
    Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.writeSized,
    w0, w1, w2, w3, w4, w5, w6, w7, BitVec.add_assoc, writeWords]
  simp [Arm64.State.setMem, Arm64.State.advancePC, Arm64.State.setPC, BitVec.add_assoc]

theorem key_zero_byte (s : Arm64.State)
    (canWrite : ∀ i : Fin 8, s.mem.canWrite
      (s.readReg64 .x1 + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    ∃ out, runRange key 0x1c 4 s = some out ∧
      (∀ i : Fin 64, out.mem.read8 (s.readReg64 .x1 + BitVec.ofNat 64 i.val) = 0#8) ∧
      (∀ p, 64 ≤ (p - s.readReg64 .x1).toNat → out.mem.cells p = s.mem.cells p) := by
  refine ⟨_, key_zero s canWrite, ?_, ?_⟩
  · intro i
    let byte : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
    have lt : i.val / 8 < 8 := by have := i.isLt; omega
    have wrote := writeWords_byte s.mem (s.readReg64 .x1) (fun _ => 0#64) 8 (i.val / 8)
      byte lt (by decide)
    have address : 8 * (i.val / 8) + byte.val = i.val := by dsimp [byte]; omega
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, address, BitVec.extractLsb'_zero] using wrote
  · intro p h
    exact writeWords_outside _ _ _ 8 p h

private theorem finish_header_decoded :
    decodeRange finish 0x2c 6 = some [
      .moveWide .W64 .MOVZ .x9 120#16 0,
      .str .X64 .x9 (.Offset .sp 96#64),
      .moveWide .W64 .MOVZ .x9 24#16 0,
      .str .X64 .x9 (.Offset .sp 104#64),
      .moveWide .W64 .MOVZ .x9 96#16 0,
      .str .X64 .x9 (.Offset .sp 112#64)] := by decide +kernel

/-- The stack header installed after the inner digest has been written. -/
def finishHeader (s : Arm64.State) : Arm64.Memory :=
  ((s.mem.write64 (s.sp + 96#64) 120#64).write64 (s.sp + 104#64) 24#64).write64
    (s.sp + 112#64) 96#64

theorem finish_header_values (s : Arm64.State) :
    (finishHeader s).read64 (s.sp + 96#64) = 120#64 ∧
    (finishHeader s).read64 (s.sp + 104#64) = 24#64 ∧
    (finishHeader s).read64 (s.sp + 112#64) = 96#64 := by
  let values (i : Nat) : Addr := if i = 0 then 120#64 else if i = 1 then 24#64 else 96#64
  have memory : finishHeader s = writeWords s.mem (s.sp + 96#64) values 3 := by
    simp [finishHeader, writeWords, values, BitVec.add_assoc]
  rw [memory]
  refine ⟨?_, ?_, ?_⟩
  · simpa using writeWords_word s.mem (s.sp + 96#64) values 3 0 (by decide) (by decide)
  · simpa [BitVec.add_assoc] using
      writeWords_word s.mem (s.sp + 96#64) values 3 1 (by decide) (by decide)
  · simpa [BitVec.add_assoc] using
      writeWords_word s.mem (s.sp + 96#64) values 3 2 (by decide) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem finish_header (s : Arm64.State) (align : s.spAligned = true)
    (size : s.mem.canWrite (s.sp + 96#64) 8 = true)
    (offset : s.mem.canWrite (s.sp + 104#64) 8 = true)
    (count : s.mem.canWrite (s.sp + 112#64) 8 = true) :
    runRange finish 0x2c 6 s =
      some ((((s.setMem (finishHeader s)).writeReg64 .x9 96#64)).setPC (s.pc + 24#64)) := by
  unfold runRange
  rw [finish_header_decoded]
  simp (config := { decide := true, maxDischargeDepth := 64 }) [runDecoded, Arm64.execInstWithSvc,
    Arm64.execMoveWide, Arm64.State.writeReg, Arm64.execStr, Arm64.checkAddrSPAligned,
    Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.MemWidth.bytes,
    Arm64.Memory.writeSized, size, offset, count, align, aligned_setMem, BitVec.add_assoc,
    finishHeader, Arm64.Reg.x9]
  simp [Arm64.State.setMem, Arm64.State.advancePC, Arm64.State.setPC,
    Arm64.State.writeReg64, Arm64.RegFile.write, BitVec.add_assoc]
  funext i
  by_cases same : i = 9#5 <;> simp [same]

end Crypto.HMACSHA256.ARM64
