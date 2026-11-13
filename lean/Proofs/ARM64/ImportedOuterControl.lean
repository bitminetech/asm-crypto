import Proofs.ARM64.ImportedArithmetic
import Proofs.ARM64.ImportedCycles

/-!
The recorded outer-block gate, block advance and padding/digest phase controls.
These results cover the remaining loop-control instruction words and their
register/memory frames.
-/
namespace Crypto.ARM64.Imported

@[simp] theorem stable_pc (s : Arm64.State) (pc : BitVec 64) :
    stable (s.setPC pc) = stable s := by cases s; rfl

def blockControlView (s : Arm64.State) :=
  (stable s, nonvolatile s, s.pc, s.readReg64 .x0, s.readReg64 .x1,
    s.readReg64 .x2, s.readReg64 .x3, s.readReg64 .x4,
    s.readReg64 .x5, s.readReg64 .x6)

def blockGateCode : List (BitVec 32) := (imageWords.toList.drop 41).take 2
private theorem block_gate_decoded : blockGateCode.mapM Arm64.decode = some [
  .cbz .W64 false .x3 340#64,
  .moveWide .W64 .MOVZ .x5 0#16 0] := by decide +kernel

theorem block_gate (s : Arm64.State) (h : s.readReg64 .x3 ≠ 0#64) :
    (runWords blockGateCode s).map blockControlView =
      some (stable s, nonvolatile s, s.pc + 8#64,
        s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2,
        s.readReg64 .x3, s.readReg64 .x4, 0#64, s.readReg64 .x6) := by
  rw [runWords_decode, block_gate_decoded]
  simp [runDecoded, Arm64.execInstWithSvc, Arm64.execMoveWide,
    Arm64.State.readReg, Arm64.State.writeReg, h, blockControlView, BitVec.add_assoc]

def blockSkipCode : List (BitVec 32) := (imageWords.toList.drop 41).take 1
private theorem block_skip_decoded : blockSkipCode.mapM Arm64.decode = some [
  .cbz .W64 false .x3 340#64] := by decide +kernel

theorem block_skip (s : Arm64.State) (h : s.readReg64 .x3 = 0#64) :
    runWords blockSkipCode s = some (s.setPC (s.pc + 340#64)) := by
  rw [runWords_decode, block_skip_decoded]
  simp [runDecoded, Arm64.execInstWithSvc, Arm64.State.readReg, h]

def blockAdvanceCode : List (BitVec 32) := (imageWords.toList.drop 123).take 3
private theorem block_advance_decoded : blockAdvanceCode.mapM Arm64.decode = some [
  .addSubImm .W64 .ADD .x2 .x2 64#12 false,
  .addSubImm .W64 .SUB .x3 .x3 1#12 false,
  .b 0xfffffffffffffeb0#64] := by decide +kernel

theorem subtract_one (x : BitVec 64) :
    (Arm64.AddWithCarry64 x 0xfffffffffffffffe#64 true).1 = x - 1#64 :=
  addWithCarry64_sub x 1#64

theorem block_advance (s : Arm64.State) :
    (runWords blockAdvanceCode s).map blockControlView =
      some (stable s, nonvolatile s, s.pc - 328#64,
        s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2 + 64#64,
        s.readReg64 .x3 - 1#64, s.readReg64 .x4,
        s.readReg64 .x5, s.readReg64 .x6) := by
  rw [runWords_decode, block_advance_decoded]
  simp [runDecoded, Arm64.execInstWithSvc, Arm64.execAddSubImm,
    Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.writeReg,
    addWithCarry64_add, subtract_one, blockControlView,
    BitVec.add_assoc, BitVec.sub_eq_add_neg]

def paddingPhaseCode : List (BitVec 32) := (imageWords.toList.drop 126).take 5
private theorem padding_phase_decoded : paddingPhaseCode.mapM Arm64.decode = some [
  .cbz .W64 true .x4 20#64,
  .moveWide .W64 .MOVZ .x4 1#16 0,
  .addSubImm .W64 .ADD .x2 .sp 288#12 false,
  .logicalShift .W64 .ORR .x3 .xzr .x6 .LSL 0,
  .b 0xfffffffffffffe9c#64] := by decide +kernel

theorem padding_phase (s : Arm64.State) (h : s.readReg64 .x4 = 0#64) :
    (runWords paddingPhaseCode s).map blockControlView =
      some (stable s, nonvolatile s, s.pc - 340#64,
        s.readReg64 .x0, s.readReg64 .x1, s.sp + 288#64,
        s.readReg64 .x6, 1#64, s.readReg64 .x5, s.readReg64 .x6) := by
  rw [runWords_decode, padding_phase_decoded]
  simp [runDecoded, Arm64.execInstWithSvc, Arm64.execMoveWide,
    Arm64.execAddSubImm, Arm64.execLogicalShift, Arm64.evalLogical, Arm64.evalAddSub,
    Arm64.shiftVal, Arm64.shift64, Arm64.State.readReg, Arm64.State.writeReg,
    addWithCarry64_add, h, blockControlView, BitVec.add_assoc, BitVec.sub_eq_add_neg]

def digestGateCode : List (BitVec 32) := (imageWords.toList.drop 126).take 1
private theorem digest_gate_decoded : digestGateCode.mapM Arm64.decode = some [
  .cbz .W64 true .x4 20#64] := by decide +kernel

theorem digest_gate (s : Arm64.State) (h : s.readReg64 .x4 ≠ 0#64) :
    runWords digestGateCode s = some (s.setPC (s.pc + 20#64)) := by
  rw [runWords_decode, digest_gate_decoded]
  simp [runDecoded, Arm64.execInstWithSvc, Arm64.State.readReg, h]

end Crypto.ARM64.Imported
