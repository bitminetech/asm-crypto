import Proofs.ARM64.ImportedPreparePadding
import equiv.SHA256.Padding.Layout

/-!
The complete recorded padding buffer agrees byte for byte with the pinned
FIPS implementation's padded-byte definition, for its one/two tail blocks.
The bridge uses the independently supplied byte-count and source-tail mapping;
ByteList extent decoding, fetched execution and whole-function equal remain
separate obligations.
-/
namespace Crypto.ARM64.Imported
open SHS.Equiv.SHA256.Padding.Layout

theorem reference_length_byte (v : BitVec 64) (k : Fin 8) :
    ((lengthBE64 (UInt64.ofBitVec v)).get! k.val).toBitVec =
      v.extractLsb' (8 * (7 - k.val)) 8 := by
  rw [lengthBE64_get!_eq _ _ k.isLt]
  rcases k with ⟨k, hk⟩
  interval_cases k <;>
    simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_and,
      UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat,
      Nat.toUInt64_eq, UInt64.toBitVec_ofNat']
  all_goals apply BitVec.eq_of_getLsbD_eq
  all_goals intro i hi
  all_goals interval_cases i <;>
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and]
  all_goals simp (config := { decide := true })

theorem padded_tail_length_start (data : ByteArray) :
    data.size + 1 + zerosCount data = data.size / 64 * 64 + lengthOffset (data.size % 64) := by
  unfold zerosCount lengthOffset
  split <;> omega

theorem padded_tail_size (data : ByteArray) :
    (implPaddedBytes data).size = data.size / 64 * 64 + lengthOffset (data.size % 64) + 8 := by
  rw [size_implPaddedBytes_eq, padded_tail_length_start]

theorem count_length_bits (count : BitVec 64) :
    UInt64.ofBitVec (count <<< 3) = count.toNat.toUInt64 <<< 3 := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [Nat.toUInt64_eq, UInt64.toBitVec_ofNat',
    UInt64.toBitVec_shiftLeft, UInt64.toBitVec_ofNat,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

theorem paddingByte_matches_reference (s : Arm64.State) (data : ByteArray)
    (hcount : (s.readReg64 .x15).toNat = data.size)
    (tail : ∀ i : Fin (data.size % 64),
      s.mem.read8 (tailPointer s + BitVec.ofNat 64 i.val) =
        (data.get! (data.size / 64 * 64 + i.val)).toBitVec)
    (i : Nat) (hi : i < lengthOffset (data.size % 64) + 8) :
    paddingByte s i = ((implPaddedBytes data).get! (data.size / 64 * 64 + i)).toBitVec := by
  let rem := data.size % 64
  change i < lengthOffset rem + 8 at hi
  have hrem : rem < 64 := Nat.mod_lt _ (by decide)
  have lengthStart : data.size + 1 + zerosCount data =
      data.size / 64 * 64 + lengthOffset rem := padded_tail_length_start data
  have limits := lengthOffset_bounds rem hrem
  have full : data.size / 64 * 64 + rem = data.size := by dsimp [rem]; omega
  have total : data.size / 64 * 64 + i < (implPaddedBytes data).size := by
    rw [padded_tail_size]
    change data.size / 64 * 64 + i < data.size / 64 * 64 + lengthOffset rem + 8
    omega
  rw [get!_implPaddedBytes_eq data _ total]
  unfold paddingByte
  rw [hcount]
  by_cases hd : i < rem
  · have hd' : data.size / 64 * 64 + i < data.size := by omega
    rw [if_pos hd, if_pos hd']
    exact tail ⟨i, hd⟩
  · have hd' : ¬data.size / 64 * 64 + i < data.size := by omega
    rw [if_neg hd, if_neg hd']
    by_cases he : i = rem
    · have he' : data.size / 64 * 64 + i = data.size := by omega
      rw [if_pos he, if_pos he']
      rfl
    · have he' : data.size / 64 * 64 + i ≠ data.size := by omega
      rw [if_neg he, if_neg he']
      by_cases hz : i < lengthOffset rem
      · have hz' : data.size / 64 * 64 + i < data.size + 1 + zerosCount data := by
          rw [lengthStart]
          omega
        have hn : ¬(lengthOffset rem ≤ i ∧ i < lengthOffset rem + 8) := by omega
        rw [if_neg hn, if_pos hz']
        rfl
      · have hz' : ¬data.size / 64 * 64 + i < data.size + 1 + zerosCount data := by
          rw [lengthStart]
          omega
        have hrange : lengthOffset rem ≤ i ∧ i < lengthOffset rem + 8 := by omega
        have offset : data.size / 64 * 64 + i - (data.size + 1 + zerosCount data) = i - lengthOffset rem := by
          rw [lengthStart]
          omega
        rw [if_pos hrange, if_neg hz', offset]
        have kBound : i - lengthOffset rem < 8 := by omega
        have bits := count_length_bits (s.readReg64 .x15)
        rw [hcount] at bits
        rw [← bits]
        exact (reference_length_byte _ ⟨i - lengthOffset rem, kBound⟩).symm

theorem prepare_padding_reference (s : Arm64.State) (data : ByteArray)
    (hcount : (s.readReg64 .x15).toNat = data.size)
    (hw : ∀ i : Fin 16, s.mem.canWrite ((s.sp + 288#64) + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (hb : ∀ i : Fin 128, s.mem.canWrite ((s.sp + 288#64) + BitVec.ofNat 64 i.val) 1 = true)
    (hr : ∀ i : Fin ((s.readReg64 .x15).toNat % 64),
      s.mem.canRead (tailPointer s + BitVec.ofNat 64 i.val) 1 = true)
    (sep : ∀ i : Fin ((s.readReg64 .x15).toNat % 64),
      128 ≤ (tailPointer s + BitVec.ofNat 64 i.val - (s.sp + 288#64)).toNat)
    (tail : ∀ i : Fin (data.size % 64),
      s.mem.read8 (tailPointer s + BitVec.ofNat 64 i.val) =
        (data.get! (data.size / 64 * 64 + i.val)).toBitVec) :
    ∃ out, runWords (preparePaddingCode (s.readReg64 .x15)) s = some out ∧
      ∀ i : Fin (lengthOffset (data.size % 64) + 8),
        out.mem.read8 ((s.sp + 288#64) + BitVec.ofNat 64 i.val) =
          ((implPaddedBytes data).get! (data.size / 64 * 64 + i.val)).toBitVec := by
  obtain ⟨out, he, _, _, _, _, _, _, _, _, _, _, _, bytes, _, _, _⟩ :=
    prepare_padding s hw hb hr sep
  have limits := lengthOffset_bounds (data.size % 64) (Nat.mod_lt _ (by decide))
  refine ⟨out, he, ?_⟩
  intro i
  have hi := i.isLt
  exact (bytes ⟨i.val, by omega⟩).trans
    (paddingByte_matches_reference s data hcount tail i.val hi)

end Crypto.ARM64.Imported
