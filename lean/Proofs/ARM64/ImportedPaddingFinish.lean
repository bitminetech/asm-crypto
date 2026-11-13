import Proofs.ARM64.ImportedTailCopy

/-!
The recorded marker store, one/two-block selection and length store. The
length bytes are exactly the big-endian 64-bit bit length; the shift has no
overflow for byte counts below 2^61. Each word-list fragment retains its
actual guards and modeled state frame.
-/
namespace Crypto.ARM64.Imported

def markerCode : List (BitVec 32) := (imageWords.toList.drop 23).take 2
private theorem marker_decoded : markerCode.mapM Arm64.decode = some [
  .moveWide .W32 .MOVZ .x7 128#16 0,
  .str .B8 .x7 (.RegOffset .x16 .x17 .UXTX 0)] := by decide +kernel

theorem padding_marker (s : Arm64.State)
    (hw : s.mem.canWrite (s.readReg64 .x16 + s.readReg64 .x17) 1 = true) :
    (runWords markerCode s).map (fun out =>
      (stable out, copyRegisters out, out.mem, out.pc, nonvolatile out, out.readReg64 .x6)) =
      some ({ stable s with mem := s.mem.write8 (s.readReg64 .x16 + s.readReg64 .x17) 128#8 },
        copyRegisters s, s.mem.write8 (s.readReg64 .x16 + s.readReg64 .x17) 128#8,
        s.pc + 8#64, nonvolatile s, s.readReg64 .x6) := by
  rw [runWords_decode, marker_decoded]
  simp (config := { decide := true }) [runDecoded, Arm64.execInstWithSvc,
    Arm64.execMoveWide, Arm64.execStr, Arm64.State.writeReg,
    Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg,
    Arm64.evalAddrMode, Arm64.extendVal, Arm64.MemWidth.bytes, Arm64.Memory.writeSized,
    hw, BitVec.truncate_eq_setWidth, BitVec.add_assoc]

def paddingCountCode (small : Bool) : List (BitVec 32) :=
  (imageWords.toList.drop 25).take 3 ++ (if small then [] else (imageWords.toList.drop 28).take 1)
private theorem padding_count_small_decoded : (paddingCountCode true).mapM Arm64.decode = some [
  .moveWide .W64 .MOVZ .x6 1#16 0,
  .addSubImm .W64 .SUBS .xzr .x17 56#12 false,
  .bCond .CC 8#64] := by decide +kernel
private theorem padding_count_large_decoded : (paddingCountCode false).mapM Arm64.decode = some [
  .moveWide .W64 .MOVZ .x6 1#16 0,
  .addSubImm .W64 .SUBS .xzr .x17 56#12 false,
  .bCond .CC 8#64,
  .moveWide .W64 .MOVZ .x6 2#16 0] := by decide +kernel

theorem carry64_cmp56 (x : BitVec 64) :
    (Arm64.AddWithCarry64 x 0xffffffffffffffc7#64 true).2.c = decide (56 ≤ x.toNat) :=
  carry64_sub_ge x 56#64

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem padding_count (s : Arm64.State) :
    (runWords (paddingCountCode (decide ((s.readReg64 .x17).toNat < 56))) s).map (fun out =>
      (controlStable out, copyRegisters out, out.mem, out.pc, nonvolatile out, out.readReg64 .x6)) =
      some (controlStable s, copyRegisters s, s.mem, s.pc + 16#64, nonvolatile s,
        if (s.readReg64 .x17).toNat < 56 then 1#64 else 2#64) := by
  by_cases h : (s.readReg64 .x17).toNat < 56
  · simp only [h, decide_true]
    rw [runWords_decode, padding_count_small_decoded]
    have hn : ¬56 ≤ (s.readReg64 .x17).toNat := by omega
    simp (config := { decide := true }) [runDecoded, Arm64.execInstWithSvc,
      Arm64.execMoveWide, Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.ConditionHolds,
      Arm64.State.readReg, Arm64.State.writeReg, carry64_cmp56, hn, BitVec.add_assoc]
  · simp only [h, decide_false]
    rw [runWords_decode, padding_count_large_decoded]
    have hn : 56 ≤ (s.readReg64 .x17).toNat := by omega
    simp (config := { decide := true }) [runDecoded, Arm64.execInstWithSvc,
      Arm64.execMoveWide, Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.ConditionHolds,
      Arm64.State.readReg, Arm64.State.writeReg, carry64_cmp56, hn, BitVec.add_assoc]

def lengthCode : List (BitVec 32) := (imageWords.toList.drop 29).take 4
private theorem length_decoded : lengthCode.mapM Arm64.decode = some [
  .bitfield .W64 .UBFM .x7 .x15 61 60,
  .dataProc1 .W64 .REV .x7 .x7,
  .addSubShift .W64 .ADD .x8 .x16 .x6 .LSL 6,
  .str .X64 .x7 (.UnscaledOffset .x8 0xfffffffffffffff8#64)] := by decide +kernel

def paddingLengthAddress (s : Arm64.State) : BitVec 64 :=
  s.readReg64 .x16 + (s.readReg64 .x6 <<< 6) + 0xfffffffffffffff8#64

def paddingLengthValue (s : Arm64.State) : BitVec 64 := Arm64.rev64 (s.readReg64 .x15 <<< 3)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem padding_length (s : Arm64.State)
    (hw : s.mem.canWrite (paddingLengthAddress s) 8 = true) :
    (runWords lengthCode s).map (fun out =>
      (stable out, out.mem, out.pc, nonvolatile out,
        out.readReg64 .x0, out.readReg64 .x1, out.readReg64 .x2,
        out.readReg64 .x3, out.readReg64 .x4, out.readReg64 .x5, out.readReg64 .x6,
        out.readReg64 .x15, out.readReg64 .x16, out.readReg64 .x17)) =
      some ({ stable s with mem := s.mem.write64 (paddingLengthAddress s) (paddingLengthValue s) },
        s.mem.write64 (paddingLengthAddress s) (paddingLengthValue s), s.pc + 16#64, nonvolatile s,
        s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2,
        s.readReg64 .x3, s.readReg64 .x4, s.readReg64 .x5, s.readReg64 .x6,
        s.readReg64 .x15, s.readReg64 .x16, s.readReg64 .x17) := by
  simp only [paddingLengthAddress, BitVec.add_assoc] at hw
  rw [runWords_decode, length_decoded]
  simp (config := { decide := true }) [runDecoded, Arm64.execInstWithSvc,
    Arm64.execBitfield, Arm64.execDataProc1, Arm64.execAddSubShift, Arm64.execStr,
    Arm64.evalBitfield, Arm64.evalAddSub, Arm64.shiftVal, Arm64.shift64,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned,
    Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.writeSized,
    addWithCarry64_add, hw,
    paddingLengthAddress, paddingLengthValue, BitVec.add_assoc]

theorem write64_byte (m : Arm64.Memory) (base : BitVec 64) (v : BitVec 64) (k : Fin 8) :
    (m.write64 base v).read8 (base + BitVec.ofNat 64 k.val) = v.extractLsb' (8 * k.val) 8 := by
  rcases k with ⟨k, hk⟩
  interval_cases k <;>
    simp (config := { decide := true }) [Arm64.Memory.write64, read8_write8]

theorem rev64_byte (v : BitVec 64) (k : Fin 8) :
    (Arm64.rev64 v).extractLsb' (8 * k.val) 8 = v.extractLsb' (8 * (7 - k.val)) 8 := by
  rcases k with ⟨k, hk⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases k <;> interval_cases i <;>
    simp only [Arm64.rev64, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  all_goals simp (config := { decide := true })

theorem padding_length_byte (s : Arm64.State) (k : Fin 8) :
    (s.mem.write64 (paddingLengthAddress s) (paddingLengthValue s)).read8
      (paddingLengthAddress s + BitVec.ofNat 64 k.val) =
      (s.readReg64 .x15 <<< 3).extractLsb' (8 * (7 - k.val)) 8 := by
  rw [write64_byte]
  exact rev64_byte _ k

theorem bit_length_shift (count : BitVec 64) (h : count.toNat < 2 ^ 61) :
    (count <<< 3).toNat = count.toNat * 8 := by
  have bound : count.toNat * 8 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 3 = 8 by decide,
    Nat.mod_eq_of_lt bound]

end Crypto.ARM64.Imported
