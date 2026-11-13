import Proofs.ARM64.ImportedInitialLoad
import Proofs.ARM64.ImportedMemoryRange

/-!
The 17 recorded feed-forward instructions add each saved hash word to its
working variable and write the resulting eight words. The theorem records
the exact memory transition, RAM snapshot, working variables, PC and state
frame, under all eight read/write permission guards.
-/
namespace Crypto.ARM64.Imported

def feedForwardCode : List (BitVec 32) := (imageWords.toList.drop 106).take 17
private theorem feed_forward_decoded : feedForwardCode.mapM Arm64.decode = some [
  .addSubImm .W64 .ADD .x16 .sp 256#12 false,
  .ldp .W32 false .x15 .x17 (.Offset .x16 0#64),
  .addSubShift .W32 .ADD .x7 .x7 .x15 .LSL 0,
  .addSubShift .W32 .ADD .x8 .x8 .x17 .LSL 0,
  .stp .W32 .x7 .x8 (.Offset .x16 0#64),
  .ldp .W32 false .x15 .x17 (.Offset .x16 8#64),
  .addSubShift .W32 .ADD .x9 .x9 .x15 .LSL 0,
  .addSubShift .W32 .ADD .x10 .x10 .x17 .LSL 0,
  .stp .W32 .x9 .x10 (.Offset .x16 8#64),
  .ldp .W32 false .x15 .x17 (.Offset .x16 16#64),
  .addSubShift .W32 .ADD .x11 .x11 .x15 .LSL 0,
  .addSubShift .W32 .ADD .x12 .x12 .x17 .LSL 0,
  .stp .W32 .x11 .x12 (.Offset .x16 16#64),
  .ldp .W32 false .x15 .x17 (.Offset .x16 24#64),
  .addSubShift .W32 .ADD .x13 .x13 .x15 .LSL 0,
  .addSubShift .W32 .ADD .x14 .x14 .x17 .LSL 0,
  .stp .W32 .x13 .x14 (.Offset .x16 24#64)] := by decide +kernel

def hashSum (s : Arm64.State) : Vector (BitVec 32) 8 :=
  SHS.Equiv.SHA256.Foldl.Sequential.addH (wordVector 8 s.mem (s.sp + 256#64)) (working s)

def storeHashWords (s : Arm64.State) : Arm64.Memory :=
  (List.range 8).foldl (fun m i =>
    m.write32 (s.sp + BitVec.ofNat 64 (256 + 4 * i)) (hashSum s)[i]!) s.mem

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem feed_forward (s : Arm64.State)
    (hr : ∀ i : Fin 8, s.mem.canRead ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hw : ∀ i : Fin 8, s.mem.canWrite ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true) :
    (runWords feedForwardCode s).map (fun out =>
      (wordVector 8 out.mem (out.sp + 256#64), working out, stable out, out.pc, nonvolatile out,
        out.readReg64 .x0, out.readReg64 .x1, out.readReg64 .x2,
        out.readReg64 .x3, out.readReg64 .x4, out.readReg64 .x5, out.readReg64 .x6)) =
      some (hashSum s, hashSum s, { stable s with mem := storeHashWords s },
        s.pc + 68#64, nonvolatile s,
        s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2,
        s.readReg64 .x3, s.readReg64 .x4, s.readReg64 .x5, s.readReg64 .x6) := by
  have r0 := hr ⟨0, by decide⟩
  simp only [BitVec.add_assoc] at r0
  change s.mem.canRead (s.sp + 256#64) 4 = true at r0
  have r1 := hr ⟨1, by decide⟩
  simp only [BitVec.add_assoc] at r1
  change s.mem.canRead (s.sp + 260#64) 4 = true at r1
  have r2 := hr ⟨2, by decide⟩
  simp only [BitVec.add_assoc] at r2
  change s.mem.canRead (s.sp + 264#64) 4 = true at r2
  have r3 := hr ⟨3, by decide⟩
  simp only [BitVec.add_assoc] at r3
  change s.mem.canRead (s.sp + 268#64) 4 = true at r3
  have r4 := hr ⟨4, by decide⟩
  simp only [BitVec.add_assoc] at r4
  change s.mem.canRead (s.sp + 272#64) 4 = true at r4
  have r5 := hr ⟨5, by decide⟩
  simp only [BitVec.add_assoc] at r5
  change s.mem.canRead (s.sp + 276#64) 4 = true at r5
  have r6 := hr ⟨6, by decide⟩
  simp only [BitVec.add_assoc] at r6
  change s.mem.canRead (s.sp + 280#64) 4 = true at r6
  have r7 := hr ⟨7, by decide⟩
  simp only [BitVec.add_assoc] at r7
  change s.mem.canRead (s.sp + 284#64) 4 = true at r7
  have w0 := hw ⟨0, by decide⟩
  simp only [BitVec.add_assoc] at w0
  change s.mem.canWrite (s.sp + 256#64) 4 = true at w0
  have w1 := hw ⟨1, by decide⟩
  simp only [BitVec.add_assoc] at w1
  change s.mem.canWrite (s.sp + 260#64) 4 = true at w1
  have w2 := hw ⟨2, by decide⟩
  simp only [BitVec.add_assoc] at w2
  change s.mem.canWrite (s.sp + 264#64) 4 = true at w2
  have w3 := hw ⟨3, by decide⟩
  simp only [BitVec.add_assoc] at w3
  change s.mem.canWrite (s.sp + 268#64) 4 = true at w3
  have w4 := hw ⟨4, by decide⟩
  simp only [BitVec.add_assoc] at w4
  change s.mem.canWrite (s.sp + 272#64) 4 = true at w4
  have w5 := hw ⟨5, by decide⟩
  simp only [BitVec.add_assoc] at w5
  change s.mem.canWrite (s.sp + 276#64) 4 = true at w5
  have w6 := hw ⟨6, by decide⟩
  simp only [BitVec.add_assoc] at w6
  change s.mem.canWrite (s.sp + 280#64) 4 = true at w6
  have w7 := hw ⟨7, by decide⟩
  simp only [BitVec.add_assoc] at w7
  change s.mem.canWrite (s.sp + 284#64) 4 = true at w7
  rw [runWords_decode, feed_forward_decoded]
  simp (config := { decide := true, maxDischargeDepth := 32 }) [runDecoded, Arm64.execInstWithSvc,
    Arm64.execAddSubImm, Arm64.execAddSubShift, Arm64.execLdp, Arm64.execStp,
    Arm64.evalAddSub, Arm64.shiftVal, Arm64.shift32, Arm64.State.readReg, Arm64.State.writeReg, Arm64.State.readReg32,
    Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg,
    Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.readSized, Arm64.Memory.writeSized,
    addWithCarry32_add, addWithCarry64_add, BitVec.truncate_eq_setWidth,
    r0, r1, r2, r3, r4, r5, r6, r7, w0, w1, w2, w3, w4, w5, w6, w7,
    canRead_write32, read32_write32_disjoint, read32_write32, bv_add_sub_add_left,
    BitVec.add_assoc, working, wordVector_eight, hashSum, storeHashWords, List.range_succ, SHS.Equiv.SHA256.Foldl.Sequential.addH]

end Crypto.ARM64.Imported
