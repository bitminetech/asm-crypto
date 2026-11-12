import Proofs.ARM64.ImportedPrepareTail
import Proofs.ARM64.ImportedPaddingSuffix

/-!
Complete recorded padding path: zeroing, remainder setup, tail copy, marker,
block-count selection and big-endian length store. Every padding byte is proved
for every 64-bit count, with outside-cell, permission and modeled-state frames.
The FIPS domain additionally requires count < 2^61. Reference padding equality,
fetched execution and whole-call equal remain separate obligations.
-/
namespace Crypto.ARM64.Imported

def preparePaddingCode (count : BitVec 64) :=
  prepareTailCode (count.toNat % 64) ++ paddingSuffixCode (count.toNat % 64)

def paddingByte (s : Arm64.State) (i : Nat) : BitVec 8 :=
  let rem := (s.readReg64 .x15).toNat % 64
  if i < rem then s.mem.read8 (tailPointer s + BitVec.ofNat 64 i)
  else if i = rem then 128#8
  else if lengthOffset rem ≤ i ∧ i < lengthOffset rem + 8 then
    (s.readReg64 .x15 <<< 3).extractLsb' (8 * (7 - (i - lengthOffset rem))) 8
  else 0#8

theorem prepare_padding (s : Arm64.State)
    (hw : ∀ i : Fin 16, s.mem.canWrite ((s.sp + 288#64) + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (hb : ∀ i : Fin 128, s.mem.canWrite ((s.sp + 288#64) + BitVec.ofNat 64 i.val) 1 = true)
    (hr : ∀ i : Fin ((s.readReg64 .x15).toNat % 64),
      s.mem.canRead (tailPointer s + BitVec.ofNat 64 i.val) 1 = true)
    (sep : ∀ i : Fin ((s.readReg64 .x15).toNat % 64),
      128 ≤ (tailPointer s + BitVec.ofNat 64 i.val - (s.sp + 288#64)).toNat) :
    ∃ out, runWords (preparePaddingCode (s.readReg64 .x15)) s = some out ∧
      nonMemory out = nonMemory s ∧ nonvolatile out = nonvolatile s ∧
      out.pc = s.pc + 116#64 ∧
      out.readReg64 .x0 = s.readReg64 .x0 ∧ out.readReg64 .x1 = s.readReg64 .x1 ∧
      out.readReg64 .x2 = s.readReg64 .x2 ∧
      out.readReg64 .x3 = s.readReg64 .x15 >>> 6 ∧
      out.readReg64 .x6 = (if (s.readReg64 .x15).toNat % 64 < 56 then 1#64 else 2#64) ∧
      out.readReg64 .x15 = s.readReg64 .x15 ∧ out.readReg64 .x16 = s.sp + 288#64 ∧
      out.readReg64 .x17 = BitVec.ofNat 64 ((s.readReg64 .x15).toNat % 64) ∧
      (∀ i : Fin 128, out.mem.read8 ((s.sp + 288#64) + BitVec.ofNat 64 i.val) = paddingByte s i.val) ∧
      (∀ p, 128 ≤ (p - (s.sp + 288#64)).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a n, s.mem.canRead a n = true → out.mem.canRead a n = true) ∧
      (∀ a n, out.mem.canWrite a n = s.mem.canWrite a n) := by
  let rem := (s.readReg64 .x15).toNat % 64
  have hrem : rem < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨copied, hc, cnm, cnv, cp, c0, c1, c2, c3, _, c15, c16, c17, bytes, frame, readable, writable⟩ :=
    prepare_tail s hw hb hr sep
  have mw : copied.mem.canWrite (copied.readReg64 .x16 + BitVec.ofNat 64 rem) 1 = true := by
    rw [c16, writable]
    exact hb ⟨rem, by omega⟩
  have lw : copied.mem.canWrite (copied.readReg64 .x16 + BitVec.ofNat 64 (lengthOffset rem)) 8 = true := by
    rw [c16, writable]
    unfold lengthOffset
    by_cases h : rem < 56 <;> simp only [h, if_true, if_false]
    · exact hw ⟨7, by decide⟩
    · exact hw ⟨15, by decide⟩
  obtain ⟨out, hs, snm, snv, spc, smem, s0, s1, s2, s3, s6, s15, s16, s17⟩ :=
    padding_suffix copied rem hrem c17 mw lw
  have whole := runWords_append_success hc hs
  refine ⟨out, whole, snm.trans cnm, snv.trans cnv, ?_, s0.trans c0, s1.trans c1, s2.trans c2,
    s3.trans c3, s6, s15.trans c15, s16.trans c16, s17, ?_, ?_, ?_, ?_⟩
  · rw [spc, cp]
    simp only [BitVec.add_assoc]
    exact congrArg (s.pc + ·) (by decide +kernel)
  · intro i
    have byte := suffixMemory_byte copied rem hrem i
    rw [c16, c15, bytes i] at byte
    change (suffixMemory copied rem).read8 ((s.sp + 288#64) + BitVec.ofNat 64 i.val) =
      (if lengthOffset rem ≤ i.val ∧ i.val < lengthOffset rem + 8 then
        (s.readReg64 .x15 <<< 3).extractLsb' (8 * (7 - (i.val - lengthOffset rem))) 8
      else if i.val = rem then 128#8
      else if i.val < rem then s.mem.read8 (tailPointer s + BitVec.ofNat 64 i.val) else 0#8) at byte
    rw [smem]
    change (suffixMemory copied rem).read8 _ = _
    unfold paddingByte
    change (suffixMemory copied rem).read8 _ =
      if i.val < rem then s.mem.read8 (tailPointer s + BitVec.ofNat 64 i.val)
      else if i.val = rem then 128#8
      else if lengthOffset rem ≤ i.val ∧ i.val < lengthOffset rem + 8 then
        (s.readReg64 .x15 <<< 3).extractLsb' (8 * (7 - (i.val - lengthOffset rem))) 8
      else 0#8
    have limits := lengthOffset_bounds rem hrem
    by_cases range : lengthOffset rem ≤ i.val ∧ i.val < lengthOffset rem + 8
    · have hn : ¬i.val < rem := by omega
      have he : i.val ≠ rem := by omega
      simpa only [if_pos range, if_neg hn, if_neg he] using byte
    · by_cases hd : i.val < rem
      · have he : i.val ≠ rem := by omega
        simpa only [if_neg range, if_pos hd, if_neg he] using byte
      · by_cases he : i.val = rem
        · simpa only [if_neg range, if_neg hd, if_pos he] using byte
        · simpa only [if_neg range, if_neg hd, if_neg he] using byte
  · intro p hp
    rw [smem]
    have dist : 128 ≤ (p - copied.readReg64 .x16).toNat := by rw [c16]; exact hp
    exact (suffixMemory_outside copied rem hrem p dist).trans (frame p hp)
  · intro a n read
    rw [smem]
    exact suffixMemory_readable copied rem a n (readable a n read)
  · intro a n
    rw [smem, suffixMemory_writable, writable]

end Crypto.ARM64.Imported
