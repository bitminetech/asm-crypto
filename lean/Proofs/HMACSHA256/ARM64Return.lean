import Proofs.HMACSHA256.ARM64Setup

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

def restoreCode (frame : Addr) : List Arm64.Instr := [
  .ldp .W64 false .x27 .x28 (.Offset .sp 80#64),
  .ldp .W64 false .x25 .x26 (.Offset .sp 64#64),
  .ldp .W64 false .x23 .x24 (.Offset .sp 48#64),
  .ldp .W64 false .x21 .x22 (.Offset .sp 32#64),
  .ldp .W64 false .x19 .x20 (.Offset .sp 16#64),
  .ldp .W64 false .x29 .lr (.PostIndex .sp frame),
  .ret .lr]

theorem entry_return_decoded :
    decodeRange entry 0x114 7 = some (restoreCode 160#64) := by decide +kernel

theorem key_return_decoded :
    decodeRange key 0x74 7 = some (restoreCode 96#64) := by decide +kernel

theorem finish_return_decoded :
    decodeRange finish 0xa0 7 = some (restoreCode 224#64) := by decide +kernel

def restoreRegs (s : Arm64.State) : Arm64.State :=
  let load (st : Arm64.State) (reg : Arm64.Reg) (disp : Addr) :=
    st.writeReg64 reg (s.mem.read64 (s.sp + disp))
  let st := load (load s .x27 80#64) .x28 88#64
  let st := load (load st .x25 64#64) .x26 72#64
  let st := load (load st .x23 48#64) .x24 56#64
  let st := load (load st .x21 32#64) .x22 40#64
  let st := load (load st .x19 16#64) .x20 24#64
  load (load st .x29 0#64) .lr 8#64

def restoreState (s : Arm64.State) (frame : Addr) : Arm64.State :=
  ((restoreRegs s).writeReg64 .sp (s.sp + frame)).setPC (s.mem.read64 (s.sp + 8#64))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
theorem return_code (s : Arm64.State) (frame : Addr)
    (aligned : s.spAligned = true)
    (canRead : ∀ i : Fin 12, s.mem.canRead (s.sp + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    runDecoded (restoreCode frame) s = restoreState s frame := by
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
  simp (config := { decide := true, maxDischargeDepth := 64 }) [restoreCode, runDecoded,
    Arm64.execInstWithSvc, Arm64.execLdp, Arm64.State.writeReg,
    Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg, Arm64.evalAddrMode,
    Arm64.MemWidth.bytes, Arm64.Memory.readSized, BitVec.add_assoc,
    Arm64.Reg.x19, Arm64.Reg.x20, Arm64.Reg.x21, Arm64.Reg.x22, Arm64.Reg.x23, Arm64.Reg.x24,
    Arm64.Reg.x25, Arm64.Reg.x26, Arm64.Reg.x27, Arm64.Reg.x28, Arm64.Reg.x29, Arm64.Reg.lr,
    aligned, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, restoreState, restoreRegs]
  simp (config := { decide := true }) [Arm64.State.setPC, Arm64.State.advancePC,
    Arm64.State.writeReg64, Arm64.State.readReg64, Arm64.RegFile.read, Arm64.RegFile.write,
    Arm64.Reg.x19, Arm64.Reg.x20, Arm64.Reg.x21, Arm64.Reg.x22, Arm64.Reg.x23, Arm64.Reg.x24,
    Arm64.Reg.x25, Arm64.Reg.x26, Arm64.Reg.x27, Arm64.Reg.x28, Arm64.Reg.x29, Arm64.Reg.lr]

/-- The three routines share the same restoring loads and return instruction.
Each exact body restores SP by its own frame size. -/
theorem returns (s : Arm64.State) (aligned : s.spAligned = true)
    (canRead : ∀ i : Fin 12, s.mem.canRead (s.sp + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    runRange entry 0x114 7 s = some (restoreState s 160#64) ∧
    runRange key 0x74 7 s = some (restoreState s 96#64) ∧
    runRange finish 0xa0 7 s = some (restoreState s 224#64) := by
  simp [runRange, entry_return_decoded, key_return_decoded, finish_return_decoded,
    return_code _ _ aligned canRead]

end Crypto.HMACSHA256.ARM64
