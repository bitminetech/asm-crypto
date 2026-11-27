import Proofs.HMACSHA256.ARM64Setup

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

private theorem finish_inner_call_decoded :
    decodeRange finish 0x1c 4 = some [
      .logicalShift .W64 .ORR .x19 .xzr .x1 .LSL 0,
      .logicalShift .W64 .ORR .x20 .xzr .x2 .LSL 0,
      .addSubImm .W64 .ADD .x1 .sp 184#12 false,
      .bl 0xfffffffffffff1f8#64] := by decide +kernel

private theorem finish_outer_call_decoded :
    decodeRange finish 0x94 3 = some [
      .addSubImm .W64 .ADD .x0 .sp 96#12 false,
      .logicalShift .W64 .ORR .x1 .xzr .x20 .LSL 0,
      .bl 0xfffffffffffff184#64] := by decide +kernel

private theorem key_call_decoded :
    decodeRange key 0x70 1 = some [.bl 0xfffffffffffff240#64] := by decide +kernel

/-- Before entering SHA-256 on the long-key path, X0 is still the key and
X1 is still the beginning of the 64-byte cleared output area. -/
theorem key_call (s : Arm64.State) :
    runRange key 0x70 1 s =
      some ((s.writeReg64 .lr (s.pc + 4#64)).setPC
        (s.pc + 0xfffffffffffff240#64)) := by
  simp [runRange, key_call_decoded, runDecoded, Arm64.execInstWithSvc]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem finish_inner_call (s : Arm64.State) :
    let saved := (s.writeReg64 .x19 (s.readReg64 .x1)).writeReg64 .x20 (s.readReg64 .x2)
    let args := saved.writeReg64 .x1 (s.sp + 184#64)
    runRange finish 0x1c 4 s = some
      ((args.writeReg64 .lr (s.pc + 16#64)).setPC (s.pc + 0xfffffffffffff204#64)) := by
  dsimp only
  unfold runRange
  rw [finish_inner_call_decoded]
  simp (config := { decide := true }) [runDecoded, Arm64.execInstWithSvc, Arm64.evalAddSub,
    Arm64.execAddSubImm, Arm64.execLogicalShift, Arm64.evalLogical, Arm64.shiftVal,
    Arm64.shift64, Arm64.State.readReg, Arm64.State.writeReg, Arm64.State.readReg64,
    Arm64.Reg.x19, Arm64.Reg.x20, Arm64.Reg.x1, Arm64.Reg.x2,
    addWithCarry64_add, BitVec.add_assoc, Arm64.State.setPC, Arm64.State.advancePC]
  simp (config := { decide := true }) [Arm64.State.writeReg64, Arm64.RegFile.write,
    Arm64.RegFile.read, Arm64.Reg.lr]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem finish_outer_call (s : Arm64.State) :
    let args := (s.writeReg64 .x0 (s.sp + 96#64)).writeReg64 .x1 (s.readReg64 .x20)
    runRange finish 0x94 3 s = some
      ((args.writeReg64 .lr (s.pc + 12#64)).setPC (s.pc + 0xfffffffffffff18c#64)) := by
  dsimp only
  unfold runRange
  rw [finish_outer_call_decoded]
  simp (config := { decide := true }) [runDecoded, Arm64.execInstWithSvc, Arm64.evalAddSub,
    Arm64.execAddSubImm, Arm64.execLogicalShift, Arm64.evalLogical, Arm64.shiftVal,
    Arm64.shift64, Arm64.State.readReg, Arm64.State.writeReg, Arm64.State.readReg64,
    Arm64.Reg.x0, Arm64.Reg.x1, Arm64.Reg.x20,
    addWithCarry64_add, BitVec.add_assoc, Arm64.State.setPC, Arm64.State.advancePC]
  simp (config := { decide := true }) [Arm64.State.writeReg64, Arm64.RegFile.write,
    Arm64.RegFile.read, Arm64.Reg.lr]

end Crypto.HMACSHA256.ARM64
