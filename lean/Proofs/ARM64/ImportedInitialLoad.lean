import Proofs.ARM64.ImportedLoops

/-!
The six recorded instructions at 0x10c-0x120 load the eight saved hash words
and set the round counter to zero. Each individual read permission remains
active. The proof records the complete memory/SP and nonvolatile-state frame;
instruction fetching and whole-function correctness are separate.
-/
namespace Crypto.ARM64.Imported

def initialLoadCode : List (BitVec 32) := (imageWords.toList.drop 67).take 6
private theorem initial_load_decoded : initialLoadCode.mapM Arm64.decode = some [
  .addSubImm .W64 .ADD .x16 .sp 256#12 false,
  .ldp .W32 false .x7 .x8 (.Offset .x16 0#64),
  .ldp .W32 false .x9 .x10 (.Offset .x16 8#64),
  .ldp .W32 false .x11 .x12 (.Offset .x16 16#64),
  .ldp .W32 false .x13 .x14 (.Offset .x16 24#64),
  .moveWide .W64 .MOVZ .x5 0#16 0] := by decide +kernel

theorem wordVector_eight (m : Arm64.Memory) (base : BitVec 64) :
    wordVector 8 m base = #v[m.read32 base, m.read32 (base + 4#64),
      m.read32 (base + 8#64), m.read32 (base + 12#64),
      m.read32 (base + 16#64), m.read32 (base + 20#64),
      m.read32 (base + 24#64), m.read32 (base + 28#64)] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [wordVector]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem initial_load (s : Arm64.State)
    (hr : ∀ i : Fin 8, s.mem.canRead ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true) :
    (runWords initialLoadCode s).map (fun out =>
      (working out, stable out, out.pc, nonvolatile out,
        out.readReg64 .x0, out.readReg64 .x1, out.readReg64 .x2,
        out.readReg64 .x3, out.readReg64 .x4, out.readReg64 .x5, out.readReg64 .x6)) =
    some (wordVector 8 s.mem (s.sp + 256#64), stable s, s.pc + 24#64, nonvolatile s,
      s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2, s.readReg64 .x3,
      s.readReg64 .x4, 0#64, s.readReg64 .x6) := by
  have h0 := hr ⟨0, by decide⟩
  have h1 := hr ⟨1, by decide⟩
  have h2 := hr ⟨2, by decide⟩
  have h3 := hr ⟨3, by decide⟩
  have h4 := hr ⟨4, by decide⟩
  have h5 := hr ⟨5, by decide⟩
  have h6 := hr ⟨6, by decide⟩
  have h7 := hr ⟨7, by decide⟩
  simp only [BitVec.add_assoc] at h0 h1 h2 h3 h4 h5 h6 h7
  change s.mem.canRead (s.sp + 256#64) 4 = true at h0
  change s.mem.canRead (s.sp + 260#64) 4 = true at h1
  change s.mem.canRead (s.sp + 264#64) 4 = true at h2
  change s.mem.canRead (s.sp + 268#64) 4 = true at h3
  change s.mem.canRead (s.sp + 272#64) 4 = true at h4
  change s.mem.canRead (s.sp + 276#64) 4 = true at h5
  change s.mem.canRead (s.sp + 280#64) 4 = true at h6
  change s.mem.canRead (s.sp + 284#64) 4 = true at h7
  rw [runWords_decode, initial_load_decoded]
  simp [runDecoded, Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.execLdp,
    Arm64.execMoveWide, Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.writeReg,
    Arm64.State.readReg32, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned,
    Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.MemWidth.bytes,
    Arm64.Memory.readSized, addWithCarry64_add, BitVec.truncate_eq_setWidth,
    h0, h1, h2, h3, h4, h5, h6, h7, BitVec.add_assoc, working, wordVector_eight]

end Crypto.ARM64.Imported
