import Proofs.ARM64.ImportedZeroPad

/-!
The eight recorded words copy four PC-relative 64-bit pool words into the
saved hash slots, calculate the K-table pointer and set phase zero. The exact
memory transition and modeled state frame are proved under the read/write
guards. Loaded-pool/FIPS binding, fetching and whole-call equal remain separate.
-/
namespace Crypto.ARM64.Imported

def hashInitCode : List (BitVec 32) := (imageWords.toList.drop 33).take 8
private theorem hash_init_decoded : hashInitCode.mapM Arm64.decode = some [
  .adr false .x0 732#64,
  .ldp .W64 false .x7 .x8 (.Offset .x0 0#64),
  .ldp .W64 false .x9 .x10 (.Offset .x0 16#64),
  .addSubImm .W64 .ADD .x16 .sp 256#12 false,
  .stp .W64 .x7 .x8 (.Offset .x16 0#64),
  .stp .W64 .x9 .x10 (.Offset .x16 16#64),
  .adr false .x0 452#64,
  .moveWide .W64 .MOVZ .x4 0#16 0] := by decide +kernel

def initialHashMemory (s : Arm64.State) : Arm64.Memory :=
  (List.range 4).foldl (fun m i =>
    m.write64 (s.sp + BitVec.ofNat 64 (256 + 8 * i))
      (s.mem.read64 (s.pc + BitVec.ofNat 64 (732 + 8 * i)))) s.mem

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem initialize_hash (s : Arm64.State)
    (hr : ∀ i : Fin 4, s.mem.canRead ((s.pc + 732#64) + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (hw : ∀ i : Fin 4, s.mem.canWrite ((s.sp + 256#64) + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    (runWords hashInitCode s).map (fun out =>
      (stable out, out.mem, out.pc, nonvolatile out,
        out.readReg64 .x0, out.readReg64 .x1, out.readReg64 .x2,
        out.readReg64 .x3, out.readReg64 .x4, out.readReg64 .x6)) =
      some ({ stable s with mem := initialHashMemory s }, initialHashMemory s,
        s.pc + 32#64, nonvolatile s,
        s.pc + 476#64, s.readReg64 .x1, s.readReg64 .x2,
        s.readReg64 .x3, 0#64, s.readReg64 .x6) := by
  have r0 := hr ⟨0, by decide⟩
  have r1 := hr ⟨1, by decide⟩
  have r2 := hr ⟨2, by decide⟩
  have r3 := hr ⟨3, by decide⟩
  have w0 := hw ⟨0, by decide⟩
  have w1 := hw ⟨1, by decide⟩
  have w2 := hw ⟨2, by decide⟩
  have w3 := hw ⟨3, by decide⟩
  simp only [BitVec.add_assoc] at r0 r1 r2 r3 w0 w1 w2 w3
  change s.mem.canRead (s.pc + 732#64) 8 = true at r0
  change s.mem.canRead (s.pc + 740#64) 8 = true at r1
  change s.mem.canRead (s.pc + 748#64) 8 = true at r2
  change s.mem.canRead (s.pc + 756#64) 8 = true at r3
  change s.mem.canWrite (s.sp + 256#64) 8 = true at w0
  change s.mem.canWrite (s.sp + 264#64) 8 = true at w1
  change s.mem.canWrite (s.sp + 272#64) 8 = true at w2
  change s.mem.canWrite (s.sp + 280#64) 8 = true at w3
  rw [runWords_decode, hash_init_decoded]
  simp (config := { decide := true }) [runDecoded, Arm64.execInstWithSvc,
    Arm64.execLdp, Arm64.execStp, Arm64.execAddSubImm, Arm64.execMoveWide,
    Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.writeReg,
    Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg,
    Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.readSized, Arm64.Memory.writeSized,
    addWithCarry64_add, r0, r1, r2, r3, w0, w1, w2, w3,
    initialHashMemory, List.range_succ, BitVec.add_assoc]

end Crypto.ARM64.Imported
