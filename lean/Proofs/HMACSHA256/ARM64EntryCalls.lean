import Proofs.HMACSHA256.ARM64Entry
import Proofs.HMACSHA256.ARM64Ranges

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

private theorem entry_key_decoded : decodeRange entry 0x48 3 = some [
  .logicalShift .W64 .ORR .x0 .xzr .x19 .LSL 0,
  .addSubImm .W64 .ADD .x1 .sp 96#12 false,
  .bl 768#64] := by decide +kernel

def entryKeyCall (s : Arm64.State) : Arm64.State :=
  let args := (s.writeReg64 .x0 (s.readReg64 .x19)).writeReg64 .x1 (s.sp + 96#64)
  (args.writeReg64 .lr (s.pc + 12#64)).setPC (s.pc + 776#64)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1300000 in
theorem entry_key_call (s : Arm64.State) : runRange entry 0x48 3 s = some (entryKeyCall s) := by
  rw [runRange, entry_key_decoded]
  simp (config := {decide := true}) [runDecoded, Arm64.execInstWithSvc, Arm64.execLogicalShift, Arm64.evalLogical,
    Arm64.shiftVal, Arm64.shift64, Arm64.execAddSubImm, Arm64.evalAddSub, addWithCarry64_add,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.State.advancePC, Arm64.State.setPC,
    Arm64.Reg.x0, Arm64.Reg.x1, Arm64.Reg.x19, entryKeyCall, BitVec.add_assoc]
  simp (config := {decide := true}) [Arm64.State.writeReg64, Arm64.State.readReg64,
    Arm64.RegFile.write, Arm64.RegFile.read, Arm64.Reg.lr]

private theorem key_relocation :
    BitVec.ofInt 64 entry.offset + (0x48#64 + 776#64) = BitVec.ofInt 64 key.offset := by decide +kernel

theorem entry_key_target (base : Addr) (s : Arm64.State) (pc : s.pc = routineAddress base entry + 0x48#64) :
    (entryKeyCall s).pc = routineAddress base key ∧
    (entryKeyCall s).readReg64 .lr = routineAddress base entry + 0x54#64 := by
  constructor
  · change s.pc + 776#64 = _
    rw [pc, routineAddress, routineAddress, BitVec.add_assoc, BitVec.add_assoc, key_relocation]
  · have link : (entryKeyCall s).readReg64 .lr = s.pc + 12#64 := by
      simp [entryKeyCall, Arm64.Reg.lr]
    rw [link, pc, BitVec.add_assoc]
    rfl

private theorem entry_finish_decoded : decodeRange entry 0x100 4 = some [
  .addSubImm .W64 .ADD .x0 .x21 8#12 false,
  .addSubImm .W64 .ADD .x1 .sp 96#12 false,
  .logicalShift .W64 .ORR .x2 .xzr .x22 .LSL 0,
  .bl 724#64] := by decide +kernel

def entryFinishCall (s : Arm64.State) : Arm64.State :=
  let args := ((s.writeReg64 .x0 (s.readReg64 .x21 + 8#64)).writeReg64 .x1
    (s.sp + 96#64)).writeReg64 .x2 (s.readReg64 .x22)
  (args.writeReg64 .lr (s.pc + 16#64)).setPC (s.pc + 736#64)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1300000 in
theorem entry_finish_call (s : Arm64.State) : runRange entry 0x100 4 s = some (entryFinishCall s) := by
  rw [runRange, entry_finish_decoded]
  simp (config := {decide := true}) [runDecoded, Arm64.execInstWithSvc, Arm64.execLogicalShift, Arm64.evalLogical,
    Arm64.shiftVal, Arm64.shift64, Arm64.execAddSubImm, Arm64.evalAddSub, addWithCarry64_add,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.State.advancePC, Arm64.State.setPC, reg_write_gpr,
    Arm64.Reg.x0, Arm64.Reg.x1, Arm64.Reg.x2, Arm64.Reg.x21, Arm64.Reg.x22, entryFinishCall, BitVec.add_assoc]
  simp (config := {decide := true}) [Arm64.State.writeReg64, Arm64.State.readReg64,
    Arm64.RegFile.write, Arm64.RegFile.read, Arm64.Reg.lr]

private theorem finish_relocation :
    BitVec.ofInt 64 entry.offset + (0x100#64 + 736#64) = BitVec.ofInt 64 finish.offset := by decide +kernel

theorem entry_finish_target (base : Addr) (s : Arm64.State) (pc : s.pc = routineAddress base entry + 0x100#64) :
    (entryFinishCall s).pc = routineAddress base finish ∧
    (entryFinishCall s).readReg64 .lr = routineAddress base entry + 0x110#64 := by
  constructor
  · change s.pc + 736#64 = _
    rw [pc, routineAddress, routineAddress, BitVec.add_assoc, BitVec.add_assoc, finish_relocation]
  · have link : (entryFinishCall s).readReg64 .lr = s.pc + 16#64 := by
      simp [entryFinishCall, Arm64.Reg.lr]
    rw [link, pc, BitVec.add_assoc]
    rfl

theorem entry_set_success (s : Arm64.State) :
    runRange entry 0x110 1 s = some ((s.writeReg64 .x0 0#64).setPC (s.pc + 4#64)) := by
  have decode : decodeRange entry 0x110 1 = some [.moveWide .W64 .MOVZ .x0 0#16 0] := by decide +kernel
  rw [runRange, decode]
  rfl

def entryKeyCallEvents (base sp : Addr) : List InstructionObservation :=
  let pc := routineAddress base entry + 0x48#64
  [⟨pc, pc + 4#64, sp, sp, []⟩, ⟨pc + 4#64, pc + 8#64, sp, sp, []⟩,
   ⟨pc + 8#64, routineAddress base key, sp, sp, []⟩]

def entryFinishCallEvents (base sp : Addr) : List InstructionObservation :=
  let pc := routineAddress base entry + 0x100#64
  [⟨pc, pc + 4#64, sp, sp, []⟩, ⟨pc + 4#64, pc + 8#64, sp, sp, []⟩,
   ⟨pc + 8#64, pc + 12#64, sp, sp, []⟩, ⟨pc + 12#64, routineAddress base finish, sp, sp, []⟩]

def entrySuccessEvents (base sp : Addr) : List InstructionObservation :=
  [⟨routineAddress base entry + 0x110#64, routineAddress base entry + 0x114#64, sp, sp, []⟩]

theorem entry_key_call_events (base : Addr) (s : Arm64.State) (pc : s.pc = routineAddress base entry + 0x48#64) :
    rangeEvents entry 0x48 3 s = entryKeyCallEvents base s.sp := by
  have target := (entry_key_target base s pc).1
  change s.pc + 776#64 = _ at target
  simp only [rangeEvents, entry_key_decoded, Option.getD_some, decodedEvents, instructionObservation,
    dataAccesses, entryKeyCallEvents]
  change ([⟨s.pc, s.pc + 4#64, s.sp, s.sp, []⟩, ⟨s.pc + 4#64, s.pc + 4#64 + 4#64, s.sp, s.sp, []⟩,
    ⟨s.pc + 4#64 + 4#64, s.pc + 4#64 + 4#64 + 768#64, s.sp, s.sp, []⟩] : List InstructionObservation) = _
  have eq : s.pc + 4#64 + 4#64 + 768#64 = s.pc + 776#64 := by
    simp only [BitVec.add_assoc]
    rfl
  rw [eq, target, pc]
  simp only [BitVec.add_assoc]
  rfl

theorem entry_finish_call_events (base : Addr) (s : Arm64.State)
    (pc : s.pc = routineAddress base entry + 0x100#64) :
    rangeEvents entry 0x100 4 s = entryFinishCallEvents base s.sp := by
  have target := (entry_finish_target base s pc).1
  change s.pc + 736#64 = _ at target
  simp only [rangeEvents, entry_finish_decoded, Option.getD_some, decodedEvents, instructionObservation,
    dataAccesses, entryFinishCallEvents]
  have eq : s.pc + 4#64 + 4#64 + 4#64 + 724#64 = s.pc + 736#64 := by
    simp only [BitVec.add_assoc]
    rfl
  change ([⟨s.pc, s.pc + 4#64, s.sp, s.sp, []⟩, ⟨s.pc + 4#64, s.pc + 4#64 + 4#64, s.sp, s.sp, []⟩,
    ⟨s.pc + 4#64 + 4#64, s.pc + 4#64 + 4#64 + 4#64, s.sp, s.sp, []⟩,
    ⟨s.pc + 4#64 + 4#64 + 4#64, s.pc + 4#64 + 4#64 + 4#64 + 724#64, s.sp, s.sp, []⟩] : List InstructionObservation) = _
  rw [eq, target, pc]
  simp only [BitVec.add_assoc]
  rfl

theorem entry_success_events (base : Addr) (s : Arm64.State)
    (pc : s.pc = routineAddress base entry + 0x110#64) :
    rangeEvents entry 0x110 1 s = entrySuccessEvents base s.sp := by
  have decoded : decodeRange entry 0x110 1 = some [.moveWide .W64 .MOVZ .x0 0#16 0] := by decide +kernel
  simp only [rangeEvents, decoded, Option.getD_some, decodedEvents, instructionObservation,
    dataAccesses, entrySuccessEvents]
  change ([⟨s.pc, s.pc + 4#64, s.sp, s.sp, []⟩] : List InstructionObservation) = _
  rw [pc, BitVec.add_assoc]
  rfl

end Crypto.HMACSHA256.ARM64
