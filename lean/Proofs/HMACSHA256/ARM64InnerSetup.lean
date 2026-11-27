import Proofs.HMACSHA256.ARM64Pad
import Proofs.ARM64.ImportedArithmetic

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

private def innerHeaderStart : List Arm64.Instr := [
  .ldr .W64 .X64 false .x4 (.Offset .x21 0#64),
  .addSubImm .W64 .SUB .x4 .x4 8#12 false,
  .str .X64 .x4 (.Offset .x21 8#64),
  .moveWide .W64 .MOVZ .x4 24#16 0,
  .str .X64 .x4 (.Offset .x21 16#64)]

private def innerHeaderEnd : List Arm64.Instr := [
  .ldr .W64 .X64 false .x5 (.Offset .x20 16#64),
  .addSubImm .W64 .ADD .x4 .x5 64#12 false,
  .str .X64 .x4 (.Offset .x21 24#64)]

private theorem inner_header_decoded :
    decodeRange entry 0x54 8 = some (innerHeaderStart ++ innerHeaderEnd) := by decide +kernel

private def innerHeaderWord (size count : Addr) (i : Nat) : Addr :=
  if i = 0 then size - 8#64 else if i = 1 then 24#64 else count + 64#64

def innerHeaderState (s : Arm64.State) (count : Addr) : Arm64.State :=
  let scratch := s.readReg64 .x21
  let memory := writeWords s.mem (scratch + 8#64) (innerHeaderWord (s.mem.read64 scratch) count) 3
  (((s.setMem memory).writeReg64 .x5 count).writeReg64 .x4 (count + 64#64)).setPC (s.pc + 32#64)

theorem inner_header_outside (s : Arm64.State) (count p : Addr)
    (away : 24 ≤ (p - (s.readReg64 .x21 + 8#64)).toNat) :
    (innerHeaderState s count).mem.cells p = s.mem.cells p :=
  writeWords_outside _ _ _ 3 _ away

set_option maxHeartbeats 1200000 in
theorem inner_header_values (s : Arm64.State) (count : Addr) :
    (innerHeaderState s count).mem.read64 (s.readReg64 .x21 + 8#64) =
        s.mem.read64 (s.readReg64 .x21) - 8#64 ∧
    (innerHeaderState s count).mem.read64 (s.readReg64 .x21 + 16#64) = 24#64 ∧
    (innerHeaderState s count).mem.read64 (s.readReg64 .x21 + 24#64) = count + 64#64 := by
  change (writeWords _ _ _ 3).read64 _ = _ ∧
    (writeWords _ _ _ 3).read64 _ = _ ∧ (writeWords _ _ _ 3).read64 _ = _
  have word (i : Nat) (inside : i < 3) :=
    writeWords_word s.mem (s.readReg64 .x21 + 8#64)
      (innerHeaderWord (s.mem.read64 (s.readReg64 .x21)) count) 3 i inside (by decide)
  refine ⟨?_, ?_, ?_⟩
  · have atZero := word 0 (by decide)
    change (writeWords _ _ _ 3).read64 (_ + 0#64) = _ at atZero
    simpa only [BitVec.add_zero] using atZero
  · have atOffset := word 1 (by decide)
    change (writeWords _ _ _ 3).read64 (s.readReg64 .x21 + 8#64 + 8#64) = 24#64 at atOffset
    rw [BitVec.add_assoc] at atOffset
    exact atOffset
  · have atCount := word 2 (by decide)
    change (writeWords _ _ _ 3).read64 (s.readReg64 .x21 + 8#64 + 16#64) = count + 64#64 at atCount
    rw [BitVec.add_assoc] at atCount
    exact atCount

private def innerHeaderFirstState (s : Arm64.State) (count : Addr) : Arm64.State :=
  let scratch := s.readReg64 .x21
  let memory := writeWords s.mem (scratch + 8#64) (innerHeaderWord (s.mem.read64 scratch) count) 2
  ((s.setMem memory).writeReg64 .x4 24#64).setPC (s.pc + 20#64)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1900000 in
private theorem inner_header_first (s : Arm64.State) (count : Addr)
    (readable : s.mem.canRead (s.readReg64 .x21) 8 = true)
    (first : s.mem.canWrite (s.readReg64 .x21 + 8#64) 8 = true)
    (second : s.mem.canWrite (s.readReg64 .x21 + 16#64) 8 = true) :
    runDecoded innerHeaderStart s = innerHeaderFirstState s count := by
  have sub8 (x : Addr) : (Arm64.AddWithCarry64 x 0xfffffffffffffff7#64 true).1 = x - 8#64 :=
    addWithCarry64_sub x 8#64
  simp (config := {decide := true}) [innerHeaderStart, innerHeaderFirstState, runDecoded,
    Arm64.execInstWithSvc, Arm64.execLdr, Arm64.execStr, Arm64.execAddSubImm, Arm64.execMoveWide,
    Arm64.evalAddSub, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg,
    Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.readSized, Arm64.Memory.writeSized,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.Reg.x4, Arm64.Reg.x21, readable, first, second,
    writeWords, innerHeaderWord, sub8, BitVec.add_assoc]
  simp (config := {decide := true}) [Arm64.State.writeReg64, Arm64.State.setMem, Arm64.State.setPC,
    Arm64.State.advancePC, Arm64.RegFile.read, Arm64.RegFile.write, BitVec.add_assoc]
  funext r
  by_cases same : r = 4#5 <;> simp [same]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem inner_header_last (s : Arm64.State) (count : Addr)
    (value : s.mem.read64 (s.readReg64 .x20 + 16#64) = count)
    (readable : s.mem.canRead (s.readReg64 .x20 + 16#64) 8 = true)
    (writable : s.mem.canWrite (s.readReg64 .x21 + 24#64) 8 = true) :
    runDecoded innerHeaderEnd s =
      let memory := s.mem.write64 (s.readReg64 .x21 + 24#64) (count + 64#64)
      (((s.setMem memory).writeReg64 .x5 count).writeReg64 .x4 (count + 64#64)).setPC (s.pc + 12#64) := by
  simp (config := {decide := true}) [innerHeaderEnd, runDecoded, Arm64.execInstWithSvc,
    Arm64.execLdr, Arm64.execStr, Arm64.execAddSubImm, Arm64.evalAddSub,
    Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg,
    Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.readSized, Arm64.Memory.writeSized,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.Reg.x4, Arm64.Reg.x5, Arm64.Reg.x20, Arm64.Reg.x21,
    value, readable, writable, addWithCarry64_add, BitVec.add_assoc]
  simp (config := {decide := true}) [Arm64.State.setMem, Arm64.State.setPC, Arm64.State.advancePC,
    Arm64.State.writeReg64, Arm64.RegFile.write, BitVec.add_assoc]

private theorem decoded_append (a b : List Arm64.Instr) (s : Arm64.State) :
    runDecoded (a ++ b) s = runDecoded b (runDecoded a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons i a ih => exact ih (Arm64.execInstWithSvc Arm64.noSyscalls i s)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
/-- The entry writes the interior ByteList's header after fetching the
scratch capacity and the message count from their independently lent buffers. -/
theorem entry_inner_header (s : Arm64.State) (count : Addr)
    (metadata : s.mem.read64 (s.readReg64 .x20 + 16#64) = count)
    (separate : ∀ i : Fin 8, 16 ≤
      (s.readReg64 .x20 + 16#64 + BitVec.ofNat 64 i.val - (s.readReg64 .x21 + 8#64)).toNat)
    (scratchRead : s.mem.canRead (s.readReg64 .x21) 8 = true)
    (messageRead : s.mem.canRead (s.readReg64 .x20 + 16#64) 8 = true)
    (first : s.mem.canWrite (s.readReg64 .x21 + 8#64) 8 = true)
    (second : s.mem.canWrite (s.readReg64 .x21 + 16#64) 8 = true)
    (third : s.mem.canWrite (s.readReg64 .x21 + 24#64) 8 = true) :
    runRange entry 0x54 8 s = some (innerHeaderState s count) := by
  let mid := innerHeaderFirstState s count
  have ptrs : mid.readReg64 .x20 = s.readReg64 .x20 ∧ mid.readReg64 .x21 = s.readReg64 .x21 := by
    simp (config := {decide := true}) [mid, innerHeaderFirstState, Arm64.Reg.x4, Arm64.Reg.x20,
      Arm64.Reg.x21, Arm64.State.setPC, Arm64.State.setMem, Arm64.State.readReg64,
      Arm64.State.writeReg64, Arm64.RegFile.read, Arm64.RegFile.write]
  have countAt : mid.mem.read64 (mid.readReg64 .x20 + 16#64) = count := by
    rw [ptrs.1, ← metadata]
    apply read64_eq_of_cells
    intro i
    exact writeWords_outside _ _ _ 2 _ (separate i)
  have reads : mid.mem.canRead (mid.readReg64 .x20 + 16#64) 8 = true := by
    rw [ptrs.1]
    exact writeWords_canRead _ _ _ _ _ _ messageRead
  have writes : mid.mem.canWrite (mid.readReg64 .x21 + 24#64) 8 = true := by
    rw [ptrs.2]
    change (writeWords _ _ _ 2).canWrite _ 8 = true
    rw [writeWords_canWrite]
    exact third
  unfold runRange
  rw [inner_header_decoded, Option.map_some, decoded_append,
    inner_header_first s count scratchRead first second, inner_header_last mid count countAt reads writes]
  change some _ = some (innerHeaderState s count)
  rw [ptrs.2]
  simp (config := {decide := true}) [mid, innerHeaderState, innerHeaderFirstState, writeWords,
    innerHeaderWord, Arm64.State.setMem, Arm64.State.setPC, Arm64.State.writeReg64,
    Arm64.RegFile.write, Arm64.RegFile.read, Arm64.Reg.x4, Arm64.Reg.x5, BitVec.add_assoc]
  funext r
  by_cases a : r = 4#5 <;> by_cases b : r = 5#5 <;> simp [a, b]

private theorem ipad_setup_decoded :
    decodeRange entry 0x74 5 = some [
      .moveWide .W64 .MOVZ .x11 54#16 0,
      .logicalImm .W64 .ORR .x9 .xzr 0x0101010101010101#64,
      .dataProc3 .W64 .MADD .x11 .x11 .x9 .xzr,
      .addSubImm .W64 .ADD .x8 .x21 32#12 false,
      .addSubImm .W64 .ADD .x12 .sp 96#12 false] := by decide +kernel

def ipadStart (s : Arm64.State) : Arm64.State :=
  let a := (s.writeReg64 .x9 0x0101010101010101#64).writeReg64 .x11 0x3636363636363636#64
  let b := (a.writeReg64 .x8 (s.readReg64 .x21 + 32#64)).writeReg64 .x12 (s.sp + 96#64)
  b.setPC (s.pc + 20#64)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
theorem entry_ipad_setup (s : Arm64.State) : runRange entry 0x74 5 s = some (ipadStart s) := by
  unfold runRange
  rw [ipad_setup_decoded]
  simp (config := {decide := true}) [runDecoded, Arm64.execInstWithSvc, Arm64.execMoveWide,
    Arm64.execLogicalImm, Arm64.evalLogical, Arm64.execDataProc3, Arm64.execAddSubImm, Arm64.evalAddSub,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.Reg.x8, Arm64.Reg.x9, Arm64.Reg.x11, Arm64.Reg.x12,
    Arm64.Reg.x21, ipadStart, addWithCarry64_add, BitVec.add_assoc]
  simp (config := {decide := true}) [Arm64.State.writeReg64, Arm64.State.advancePC,
    Arm64.State.setPC, Arm64.RegFile.write, Arm64.RegFile.read, BitVec.add_assoc]
  funext i
  by_cases a : i = 8#5 <;> by_cases b : i = 9#5 <;> by_cases c : i = 11#5 <;> by_cases d : i = 12#5 <;>
    simp [a, b, c, d]

private theorem message_copy_decoded :
    decodeRange entry 0xc8 3 = some [
      .addSubImm .W64 .ADD .x8 .x21 96#12 false,
      .ldr .W64 .X64 false .x6 (.Offset .x20 8#64),
      .addSubShift .W64 .ADD .x6 .x20 .x6 .LSL 0] := by decide +kernel

def messageCopyStart (s : Arm64.State) : Arm64.State :=
  let msg := s.readReg64 .x20
  let src := msg + s.mem.read64 (msg + 8#64)
  ((s.writeReg64 .x8 (s.readReg64 .x21 + 96#64)).writeReg64 .x6 src).setPC (s.pc + 12#64)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1700000 in
theorem entry_copy_setup (s : Arm64.State)
    (offset : s.mem.canRead (s.readReg64 .x20 + 8#64) 8 = true) :
    runRange entry 0xc8 3 s = some (messageCopyStart s) := by
  unfold runRange
  rw [message_copy_decoded]
  simp (config := {decide := true}) [runDecoded, Arm64.execInstWithSvc, Arm64.execAddSubImm,
    Arm64.execLdr, Arm64.execAddSubShift, Arm64.evalAddSub, Arm64.evalAddrMode, Arm64.shiftVal, Arm64.shift64,
    Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg, Arm64.MemWidth.bytes,
    Arm64.Memory.readSized, Arm64.State.readReg, Arm64.State.writeReg, Arm64.Reg.x6, Arm64.Reg.x8,
    Arm64.Reg.x20, Arm64.Reg.x21, messageCopyStart, offset, addWithCarry64_add, BitVec.add_assoc]
  simp (config := {decide := true}) [Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.State.setPC,
    Arm64.RegFile.write, Arm64.RegFile.read, BitVec.add_assoc]
  funext i
  by_cases a : i = 6#5 <;> by_cases b : i = 8#5 <;> simp [a, b]

end Crypto.HMACSHA256.ARM64
