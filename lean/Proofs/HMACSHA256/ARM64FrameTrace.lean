import Proofs.HMACSHA256.ARM64Frame
import Proofs.HMACSHA256.ARM64Ranges

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

private def pairAccesses (write : Bool) (p : Addr) : List DataAccess :=
  [⟨write, p, 8⟩, ⟨write, p + 8#64, 8⟩]

private def stackEvents (pc sp : Addr) (write : Bool) (offsets : List Addr) : List InstructionObservation :=
  match offsets with
  | [] => []
  | d :: rest => ⟨pc, pc + 4#64, sp, sp, pairAccesses write (sp + d)⟩ ::
      stackEvents (pc + 4#64) sp write rest

def frameEnterEvents (pc sp frame : Addr) : List InstructionObservation :=
  let dst := sp - frame
  ⟨pc, pc + 4#64, sp, dst, pairAccesses true dst⟩ ::
    ⟨pc + 4#64, pc + 8#64, dst, dst, []⟩ ::
    stackEvents (pc + 8#64) dst true [16#64, 32#64, 48#64, 64#64, 80#64]

def frameReturnEvents (pc sp frame link : Addr) : List InstructionObservation :=
  stackEvents pc sp false [80#64, 64#64, 48#64, 32#64, 16#64] ++
    [⟨pc + 20#64, pc + 24#64, sp, sp + frame, pairAccesses false sp⟩,
     ⟨pc + 24#64, link, sp + frame, sp + frame, []⟩]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2100000 in
set_option linter.unusedSimpArgs false in
theorem save_code_events (s : Arm64.State) (frame : Addr)
    (aligned : s.spAligned = true) (frameAligned : (s.sp - frame) &&& 15#64 = 0#64)
    (canWrite : ∀ i : Fin 12, s.mem.canWrite (s.sp - frame + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    decodedEvents (saveCode frame) s = frameEnterEvents s.pc s.sp frame := by
  have inputAligned : s.sp &&& 15#64 = 0#64 := by simpa [Arm64.State.spAligned] using aligned
  have w (i : Nat) (hi : i < 12) :
      s.mem.canWrite (s.sp + (-frame + BitVec.ofNat 64 (8 * i))) 8 = true := by
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc] using canWrite ⟨i,hi⟩
  have w0 : s.mem.canWrite (s.sp + -frame) 8 = true := by simpa using w 0 (by decide)
  simp only [BitVec.sub_eq_add_neg] at frameAligned
  simp (config := { decide := true, maxDischargeDepth := 64 }) [decodedEvents, saveCode,
    frameEnterEvents, stackEvents, pairAccesses, instructionObservation, dataAccesses,
    Arm64.execInstWithSvc, Arm64.execStp, Arm64.execAddSubImm, Arm64.evalAddSub,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned,
    Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.writeSized,
    Arm64.State.setPC, Arm64.State.advancePC, Arm64.State.writeReg64, Arm64.State.readReg64,
    Arm64.State.setMem, Arm64.RegFile.write, Arm64.RegFile.read, Arm64.State.spAligned,
    aligned, inputAligned, frameAligned, BitVec.add_assoc, BitVec.sub_eq_add_neg, addWithCarry64_add,
    Arm64.Reg.x29, Arm64.Reg.lr, Arm64.Reg.x19, Arm64.Reg.x20, Arm64.Reg.x21, Arm64.Reg.x22,
    Arm64.Reg.x23, Arm64.Reg.x24, Arm64.Reg.x25, Arm64.Reg.x26, Arm64.Reg.x27, Arm64.Reg.x28,
    w0, w 1 (by decide), w 2 (by decide), w 3 (by decide), w 4 (by decide),
    w 5 (by decide), w 6 (by decide), w 7 (by decide), w 8 (by decide), w 9 (by decide),
    w 10 (by decide), w 11 (by decide)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2100000 in
set_option linter.unusedSimpArgs false in
theorem restore_code_events (s : Arm64.State) (frame : Addr)
    (aligned : s.spAligned = true)
    (canRead : ∀ i : Fin 12, s.mem.canRead (s.sp + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    decodedEvents (restoreCode frame) s = frameReturnEvents s.pc s.sp frame (s.mem.read64 (s.sp + 8#64)) := by
  have inputAligned : s.sp &&& 15#64 = 0#64 := by simpa [Arm64.State.spAligned] using aligned
  have r0 : s.mem.canRead s.sp 8 = true := by simpa using canRead ⟨0, by decide⟩
  have r1 : s.mem.canRead (s.sp + 8#64) 8 = true := canRead ⟨1, by decide⟩
  have r2 : s.mem.canRead (s.sp + 16#64) 8 = true := canRead ⟨2, by decide⟩
  have r3 : s.mem.canRead (s.sp + 24#64) 8 = true := canRead ⟨3, by decide⟩
  have r4 : s.mem.canRead (s.sp + 32#64) 8 = true := canRead ⟨4, by decide⟩
  have r5 : s.mem.canRead (s.sp + 40#64) 8 = true := canRead ⟨5, by decide⟩
  have r6 : s.mem.canRead (s.sp + 48#64) 8 = true := canRead ⟨6, by decide⟩
  have r7 : s.mem.canRead (s.sp + 56#64) 8 = true := canRead ⟨7, by decide⟩
  have r8 : s.mem.canRead (s.sp + 64#64) 8 = true := canRead ⟨8, by decide⟩
  have r9 : s.mem.canRead (s.sp + 72#64) 8 = true := canRead ⟨9, by decide⟩
  have r10 : s.mem.canRead (s.sp + 80#64) 8 = true := canRead ⟨10, by decide⟩
  have r11 : s.mem.canRead (s.sp + 88#64) 8 = true := canRead ⟨11, by decide⟩
  simp (config := { decide := true, maxDischargeDepth := 64 }) [decodedEvents, restoreCode,
    frameReturnEvents, stackEvents, pairAccesses, instructionObservation, dataAccesses,
    Arm64.execInstWithSvc, Arm64.execLdp, Arm64.State.writeReg,
    Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg, Arm64.evalAddrMode,
    Arm64.MemWidth.bytes, Arm64.Memory.readSized, BitVec.add_assoc, Arm64.State.setPC,
    Arm64.State.advancePC, Arm64.State.writeReg64, Arm64.State.readReg64, Arm64.RegFile.read, Arm64.RegFile.write,
    Arm64.Reg.x19, Arm64.Reg.x20, Arm64.Reg.x21, Arm64.Reg.x22, Arm64.Reg.x23, Arm64.Reg.x24,
    Arm64.Reg.x25, Arm64.Reg.x26, Arm64.Reg.x27, Arm64.Reg.x28, Arm64.Reg.x29, Arm64.Reg.lr,
    Arm64.State.spAligned, aligned, inputAligned, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11]

end Crypto.HMACSHA256.ARM64
