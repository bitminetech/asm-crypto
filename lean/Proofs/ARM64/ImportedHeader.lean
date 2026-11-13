import Proofs.ARM64.ImportedExit
import Proofs.ARM64.ImportedArithmetic

/-!
The first four recorded words subtract the 416-byte frame, read the offset
and count fields, and calculate the payload pointer. Actual header-read guards
remain explicit.
-/
namespace Crypto.ARM64.Imported

def headerCode : List (BitVec 32) := imageWords.toList.take 4
private theorem header_decoded : headerCode.mapM Arm64.decode = some [
  .addSubImm .W64 .SUB .sp .sp 416#12 false,
  .ldr .W64 .X64 false .x5 (.Offset .x0 8#64),
  .ldr .W64 .X64 false .x15 (.Offset .x0 16#64),
  .addSubShift .W64 .ADD .x2 .x0 .x5 .LSL 0] := by decide +kernel

theorem subtract416 (x : BitVec 64) :
    (Arm64.AddWithCarry64 x 0xfffffffffffffe5f#64 true).1 = x - 416#64 :=
  addWithCarry64_sub x 416#64

@[simp] theorem pc_write_sp (s : Arm64.State) (v : BitVec 64) : (s.writeReg64 .sp v).pc = s.pc := by cases s; rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem decode_header (s : Arm64.State)
    (hoff : s.mem.canRead (s.readReg64 .x0 + 8#64) 8 = true)
    (hcount : s.mem.canRead (s.readReg64 .x0 + 16#64) 8 = true) :
    (runWords headerCode s).map (fun out =>
      (returnStable out, out.mem, out.sp, out.pc, nonvolatile out,
        out.readReg64 .x0, out.readReg64 .x1, out.readReg64 .x2,
        out.readReg64 .x5, out.readReg64 .x15)) =
      some (returnStable s, s.mem, s.sp - 416#64, s.pc + 16#64, nonvolatile s,
        s.readReg64 .x0, s.readReg64 .x1,
        s.readReg64 .x0 + s.mem.read64 (s.readReg64 .x0 + 8#64),
        s.mem.read64 (s.readReg64 .x0 + 8#64), s.mem.read64 (s.readReg64 .x0 + 16#64)) := by
  rw [runWords_decode, header_decoded]
  simp (config := { decide := true }) [runDecoded, Arm64.execInstWithSvc,
    Arm64.execAddSubImm, Arm64.execLdr, Arm64.execAddSubShift, Arm64.evalAddSub,
    Arm64.shiftVal, Arm64.shift64, Arm64.State.readReg, Arm64.State.writeReg,
    Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg,
    Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.readSized,
    BitVec.truncate_eq_setWidth, subtract416, addWithCarry64_add, hoff, hcount, BitVec.add_assoc]

end Crypto.ARM64.Imported
