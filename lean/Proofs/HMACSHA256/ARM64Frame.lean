import Proofs.HMACSHA256.ARM64Return

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

def saveCode (frame : Addr) : List Arm64.Instr := [
  .stp .W64 .x29 .lr (.PreIndex .sp (-frame)),
  .addSubImm .W64 .ADD .x29 .sp 0#12 false,
  .stp .W64 .x19 .x20 (.Offset .sp 16#64),
  .stp .W64 .x21 .x22 (.Offset .sp 32#64),
  .stp .W64 .x23 .x24 (.Offset .sp 48#64),
  .stp .W64 .x25 .x26 (.Offset .sp 64#64),
  .stp .W64 .x27 .x28 (.Offset .sp 80#64)]

theorem entry_enter_decoded : decodeRange entry 0 7 = some (saveCode 160#64) := by
  decide +kernel

theorem key_enter_decoded : decodeRange key 0 7 = some (saveCode 96#64) := by
  decide +kernel

theorem finish_enter_decoded : decodeRange finish 0 7 = some (saveCode 224#64) := by
  decide +kernel

def savedRegister (i : Nat) : Arm64.Reg :=
  if i = 0 then .x29 else
  if i = 1 then .lr else
    .gpr (BitVec.ofNat 5 (17 + i))

def frameMem (s : Arm64.State) (frame : Addr) : Arm64.Memory :=
  writeWords s.mem (s.sp - frame) (fun i => s.readReg64 (savedRegister i)) 12

def enteredState (s : Arm64.State) (frame : Addr) : Arm64.State :=
  let stack := s.sp - frame
  let saved := (s.setMem (frameMem s frame)).writeReg64 .sp stack
  (saved.writeReg64 .x29 stack).setPC (s.pc + 28#64)

private theorem aligned_setMem (s : Arm64.State) (m : Arm64.Memory) :
    (s.setMem m).spAligned = s.spAligned := rfl

private theorem aligned_stack (s : Arm64.State) (sp : Addr) :
    (s.writeReg64 .sp sp).spAligned = ((sp &&& 15#64) == 0#64) := rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
theorem enter_code (s : Arm64.State) (frame : Addr)
    (aligned : s.spAligned = true) (frameAligned : (s.sp - frame) &&& 15#64 = 0#64)
    (canWrite : ∀ i : Fin 12, s.mem.canWrite (s.sp - frame + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    runDecoded (saveCode frame) s = enteredState s frame := by
  have w0 : s.mem.canWrite (s.sp - frame) 8 = true := by simpa using canWrite ⟨0, by decide⟩
  have w1 : s.mem.canWrite (s.sp - frame + 8#64) 8 = true := canWrite ⟨1, by decide⟩
  have w2 : s.mem.canWrite (s.sp - frame + 16#64) 8 = true := canWrite ⟨2, by decide⟩
  have w3 : s.mem.canWrite (s.sp - frame + 24#64) 8 = true := canWrite ⟨3, by decide⟩
  have w4 : s.mem.canWrite (s.sp - frame + 32#64) 8 = true := canWrite ⟨4, by decide⟩
  have w5 : s.mem.canWrite (s.sp - frame + 40#64) 8 = true := canWrite ⟨5, by decide⟩
  have w6 : s.mem.canWrite (s.sp - frame + 48#64) 8 = true := canWrite ⟨6, by decide⟩
  have w7 : s.mem.canWrite (s.sp - frame + 56#64) 8 = true := canWrite ⟨7, by decide⟩
  have w8 : s.mem.canWrite (s.sp - frame + 64#64) 8 = true := canWrite ⟨8, by decide⟩
  have w9 : s.mem.canWrite (s.sp - frame + 72#64) 8 = true := canWrite ⟨9, by decide⟩
  have w10 : s.mem.canWrite (s.sp - frame + 80#64) 8 = true := canWrite ⟨10, by decide⟩
  have w11 : s.mem.canWrite (s.sp - frame + 88#64) 8 = true := canWrite ⟨11, by decide⟩
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc] at frameAligned w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  simp (config := { decide := true, maxDischargeDepth := 64 }) [saveCode, runDecoded,
    Arm64.execInstWithSvc, Arm64.execStp, Arm64.execAddSubImm, Arm64.evalAddSub,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned,
    Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.writeSized,
    aligned, frameAligned, aligned_stack, aligned_setMem, BitVec.add_assoc, BitVec.sub_eq_add_neg,
    addWithCarry64_add, Arm64.Reg.x29, Arm64.Reg.lr, Arm64.Reg.x19, Arm64.Reg.x20,
    Arm64.Reg.x21, Arm64.Reg.x22, Arm64.Reg.x23, Arm64.Reg.x24, Arm64.Reg.x25, Arm64.Reg.x26,
    Arm64.Reg.x27, Arm64.Reg.x28, enteredState, frameMem, writeWords, savedRegister,
    w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11]
  simp (config := { decide := true }) [Arm64.State.setPC, Arm64.State.advancePC,
    Arm64.State.writeReg64, Arm64.State.readReg64, Arm64.State.setMem, Arm64.RegFile.write,
    Arm64.RegFile.read, BitVec.add_assoc, BitVec.sub_eq_add_neg, Arm64.State.spAligned, frameAligned,
    w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11]

theorem enter_entry (s : Arm64.State) (aligned : s.spAligned = true)
    (frameAligned : (s.sp - 160#64) &&& 15#64 = 0#64)
    (canWrite : ∀ i : Fin 12, s.mem.canWrite (s.sp - 160#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    runRange entry 0 7 s = some (enteredState s 160#64) := by
  simp [runRange, entry_enter_decoded, enter_code _ _ aligned frameAligned canWrite]

theorem enter_key (s : Arm64.State) (aligned : s.spAligned = true)
    (frameAligned : (s.sp - 96#64) &&& 15#64 = 0#64)
    (canWrite : ∀ i : Fin 12, s.mem.canWrite (s.sp - 96#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    runRange key 0 7 s = some (enteredState s 96#64) := by
  simp [runRange, key_enter_decoded, enter_code _ _ aligned frameAligned canWrite]

theorem enter_finish (s : Arm64.State) (aligned : s.spAligned = true)
    (frameAligned : (s.sp - 224#64) &&& 15#64 = 0#64)
    (canWrite : ∀ i : Fin 12, s.mem.canWrite (s.sp - 224#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    runRange finish 0 7 s = some (enteredState s 224#64) := by
  simp [runRange, finish_enter_decoded, enter_code _ _ aligned frameAligned canWrite]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1700000 in
theorem restored_register (s : Arm64.State) (frame : Addr) (i : Fin 12) :
    (restoreState s frame).readReg64 (savedRegister i.val) =
      s.mem.read64 (s.sp + BitVec.ofNat 64 (8 * i.val)) := by
  obtain ⟨i, hi⟩ := i
  interval_cases i <;>
    simp (config := { decide := true }) [savedRegister, restoreState, restoreRegs,
      Arm64.Reg.x19, Arm64.Reg.x20, Arm64.Reg.x21, Arm64.Reg.x22, Arm64.Reg.x23,
      Arm64.Reg.x24, Arm64.Reg.x25, Arm64.Reg.x26, Arm64.Reg.x27, Arm64.Reg.x28,
      Arm64.Reg.x29, Arm64.Reg.lr, Arm64.State.readReg64, Arm64.State.writeReg64,
      Arm64.State.setPC, Arm64.RegFile.read, Arm64.RegFile.write]

end Crypto.HMACSHA256.ARM64
