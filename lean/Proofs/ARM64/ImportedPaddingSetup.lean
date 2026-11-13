import Proofs.ARM64.ImportedArithmetic

/-!
The four recorded instructions calculate the remainder, full-block count,
tail pointer and zero copy counter. Arithmetic lemmas identify the mask/shifts
with modulo/division by 64 for every 64-bit count.
-/
namespace Crypto.ARM64.Imported

def paddingSetupCode : List (BitVec 32) := (imageWords.toList.drop 13).take 4
private theorem padding_setup_decoded : paddingSetupCode.mapM Arm64.decode = some [
  .logicalImm .W64 .AND .x17 .x15 63#64,
  .bitfield .W64 .UBFM .x3 .x15 6 63,
  .addSubShift .W64 .ADD .x5 .x2 .x3 .LSL 6,
  .moveWide .W64 .MOVZ .x6 0#16 0] := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem padding_setup (s : Arm64.State) :
    (runWords paddingSetupCode s).map (fun out =>
      (stable out, out.pc, nonvolatile out,
        out.readReg64 .x0, out.readReg64 .x1, out.readReg64 .x2,
        out.readReg64 .x3, out.readReg64 .x5, out.readReg64 .x6,
        out.readReg64 .x15, out.readReg64 .x16, out.readReg64 .x17)) =
      some (stable s, s.pc + 16#64, nonvolatile s,
        s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2,
        s.readReg64 .x15 >>> 6,
        s.readReg64 .x2 + ((s.readReg64 .x15 >>> 6) <<< 6), 0#64,
        s.readReg64 .x15, s.readReg64 .x16, s.readReg64 .x15 &&& 63#64) := by
  rw [runWords_decode, padding_setup_decoded]
  simp (config := { decide := true }) [runDecoded, Arm64.execInstWithSvc,
    Arm64.execLogicalImm, Arm64.execBitfield, Arm64.execAddSubShift, Arm64.execMoveWide,
    Arm64.evalLogical, Arm64.evalBitfield, Arm64.evalAddSub, Arm64.shiftVal, Arm64.shift64,
    Arm64.State.readReg, Arm64.State.writeReg, BitVec.truncate_eq_setWidth,
    addWithCarry64_add, BitVec.add_assoc]

theorem remainder_mask (count : BitVec 64) : (count &&& 63#64).toNat = count.toNat % 64 := by
  rw [BitVec.toNat_and]
  change count.toNat &&& (2 ^ 6 - 1) = count.toNat % (2 ^ 6)
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem full_blocks_shift (count : BitVec 64) : (count >>> 6).toNat = count.toNat / 64 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem tail_offset_shift (count : BitVec 64) :
    ((count >>> 6) <<< 6).toNat = (count.toNat / 64) * 64 := by
  have bound : count.toNat / 64 * 64 < 2 ^ 64 := by
    have hdiv := Nat.div_mul_le_self count.toNat 64
    have hi := count.isLt
    omega
  simp only [BitVec.toNat_shiftLeft, full_blocks_shift, Nat.shiftLeft_eq,
    show 2 ^ 6 = 64 by decide, Nat.mod_eq_of_lt bound]

end Crypto.ARM64.Imported
