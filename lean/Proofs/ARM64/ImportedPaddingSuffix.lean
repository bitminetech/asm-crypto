import Proofs.ARM64.ImportedPaddingFinish
import Proofs.ARM64.ImportedZeroPad
import Proofs.ARM64.ImportedCompression

/-!
Composition of the recorded marker/count/length suffix, including its complete
byte-level memory transition and outside/permission frame. The length tag is
big-endian and the one/two-block branch uses the actual remainder.
-/
namespace Crypto.ARM64.Imported

def lengthOffset (rem : Nat) : Nat := if rem < 56 then 56 else 120

def paddingSuffixCode (rem : Nat) :=
  markerCode ++ (paddingCountCode (decide (rem < 56)) ++ lengthCode)

def suffixMemory (s : Arm64.State) (rem : Nat) : Arm64.Memory :=
  (s.mem.write8 (s.readReg64 .x16 + BitVec.ofNat 64 rem) 128#8).write64
    (s.readReg64 .x16 + BitVec.ofNat 64 (lengthOffset rem))
    (Arm64.rev64 (s.readReg64 .x15 <<< 3))

theorem padding_suffix (s : Arm64.State) (rem : Nat) (hrem : rem < 64)
    (remainder : s.readReg64 .x17 = BitVec.ofNat 64 rem)
    (markerWrite : s.mem.canWrite (s.readReg64 .x16 + BitVec.ofNat 64 rem) 1 = true)
    (lengthWrite : s.mem.canWrite (s.readReg64 .x16 + BitVec.ofNat 64 (lengthOffset rem)) 8 = true) :
    ∃ out, runWords (paddingSuffixCode rem) s = some out ∧
      nonMemory out = nonMemory s ∧ nonvolatile out = nonvolatile s ∧
      out.pc = s.pc + 40#64 ∧ out.mem = suffixMemory s rem ∧
      out.readReg64 .x0 = s.readReg64 .x0 ∧ out.readReg64 .x1 = s.readReg64 .x1 ∧
      out.readReg64 .x2 = s.readReg64 .x2 ∧ out.readReg64 .x3 = s.readReg64 .x3 ∧
      out.readReg64 .x6 = (if rem < 56 then 1#64 else 2#64) ∧
      out.readReg64 .x15 = s.readReg64 .x15 ∧ out.readReg64 .x16 = s.readReg64 .x16 ∧
      out.readReg64 .x17 = BitVec.ofNat 64 rem := by
  obtain ⟨marked, hm, postMarker⟩ := exists_of_map_some _ _ _
    (padding_marker s (by rw [remainder]; exact markerWrite))
  simp only [Prod.mk.injEq] at postMarker
  obtain ⟨mst, mr, mmem, mpc, mnv, _⟩ := postMarker
  have m16 := copyRegisters_read mr 16#5 (by decide)
  have m17 := copyRegisters_read mr 17#5 (by decide)
  have rNat : (marked.readReg64 .x17).toNat = rem := by
    rw [m17, remainder, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : rem < 2 ^ 64)]
  have countExec := padding_count marked
  rw [rNat] at countExec
  obtain ⟨counted, hc, postCount⟩ := exists_of_map_some _ _ _ countExec
  simp only [Prod.mk.injEq] at postCount
  obtain ⟨cst, cr, cmem, cpc, cnv, c6⟩ := postCount
  have c16 := (copyRegisters_read cr 16#5 (by decide)).trans m16
  have c15 := (copyRegisters_read cr 15#5 (by decide)).trans
    (copyRegisters_read mr 15#5 (by decide))
  have address : paddingLengthAddress counted = s.readReg64 .x16 + BitVec.ofNat 64 (lengthOffset rem) := by
    unfold paddingLengthAddress lengthOffset
    rw [c16, c6]
    by_cases h : rem < 56 <;> simp only [h, if_true, if_false]
    all_goals simp (config := { decide := true }) [BitVec.add_assoc]
  have value : paddingLengthValue counted = Arm64.rev64 (s.readReg64 .x15 <<< 3) := by
    simp only [paddingLengthValue, c15]
  have write : counted.mem.canWrite (paddingLengthAddress counted) 8 = true := by
    rw [address, cmem, mmem, canWrite_write8]
    exact lengthWrite
  obtain ⟨out, hl, postLength⟩ := exists_of_map_some _ _ _ (padding_length counted write)
  simp only [Prod.mk.injEq] at postLength
  obtain ⟨lst, lmem, lpc, lnv, l0, l1, l2, l3, _, _, l6, l15, l16, l17⟩ := postLength
  have mnm := congrArg nonMemory mst
  have cnm := congrArg nonMemory cst
  have lnm := congrArg nonMemory lst
  have nonmem : nonMemory out = nonMemory s := by
    simpa only [nonMemory_stable, nonMemory_set_mem, nonMemory_controlStable]
      using lnm.trans (cnm.trans mnm)
  have tail := runWords_append_success hc hl
  have whole := runWords_append_success hm tail
  refine ⟨out, whole, nonmem, lnv.trans (cnv.trans mnv), ?_, ?_, ?_, ?_, ?_, ?_, l6.trans c6,
    l15.trans c15, l16.trans c16, ?_⟩
  · rw [lpc, cpc, mpc]
    simp only [BitVec.add_assoc]
    exact congrArg (s.pc + ·) (by decide +kernel)
  · rw [lmem, address, value, cmem, mmem, remainder]
    rfl
  · exact l0.trans ((copyRegisters_read cr 0#5 (by decide)).trans (copyRegisters_read mr 0#5 (by decide)))
  · exact l1.trans ((copyRegisters_read cr 1#5 (by decide)).trans (copyRegisters_read mr 1#5 (by decide)))
  · exact l2.trans ((copyRegisters_read cr 2#5 (by decide)).trans (copyRegisters_read mr 2#5 (by decide)))
  · exact l3.trans ((copyRegisters_read cr 3#5 (by decide)).trans (copyRegisters_read mr 3#5 (by decide)))
  · exact l17.trans ((copyRegisters_read cr 17#5 (by decide)).trans (m17.trans remainder))

theorem read8_write64_outside_ne (m : Arm64.Memory) (base p : BitVec 64) (v : BitVec 64)
    (h : ∀ k : Fin 8, p ≠ base + BitVec.ofNat 64 k.val) :
    (m.write64 base v).read8 p = m.read8 p := by
  have h0 := h ⟨0, by decide⟩
  have h1 := h ⟨1, by decide⟩
  have h2 := h ⟨2, by decide⟩
  have h3 := h ⟨3, by decide⟩
  have h4 := h ⟨4, by decide⟩
  have h5 := h ⟨5, by decide⟩
  have h6 := h ⟨6, by decide⟩
  have h7 := h ⟨7, by decide⟩
  simp only [BitVec.add_zero] at h0
  simp [Arm64.Memory.write64, h0, h1, h2, h3, h4, h5, h6, h7]

theorem lengthOffset_bounds (rem : Nat) (h : rem < 64) :
    rem < lengthOffset rem ∧ lengthOffset rem + 8 ≤ 128 := by
  unfold lengthOffset
  split <;> omega

theorem suffixMemory_byte (s : Arm64.State) (rem : Nat) (hrem : rem < 64) (i : Fin 128) :
    (suffixMemory s rem).read8 (s.readReg64 .x16 + BitVec.ofNat 64 i.val) =
      if lengthOffset rem ≤ i.val ∧ i.val < lengthOffset rem + 8 then
        (s.readReg64 .x15 <<< 3).extractLsb' (8 * (7 - (i.val - lengthOffset rem))) 8
      else if i.val = rem then 128#8
      else s.mem.read8 (s.readReg64 .x16 + BitVec.ofNat 64 i.val) := by
  have limits := lengthOffset_bounds rem hrem
  have ih := i.isLt
  by_cases range : lengthOffset rem ≤ i.val ∧ i.val < lengthOffset rem + 8
  · rw [if_pos range]
    let k : Fin 8 := ⟨i.val - lengthOffset rem, by omega⟩
    have address : s.readReg64 .x16 + BitVec.ofNat 64 i.val =
        (s.readReg64 .x16 + BitVec.ofNat 64 (lengthOffset rem)) + BitVec.ofNat 64 k.val := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      dsimp [k]
      omega
    unfold suffixMemory
    rw [address, write64_byte, rev64_byte]
  · rw [if_neg range]
    have outside (k : Fin 8) : s.readReg64 .x16 + BitVec.ofNat 64 i.val ≠
        (s.readReg64 .x16 + BitVec.ofNat 64 (lengthOffset rem)) + BitVec.ofNat 64 k.val := by
      have kh := k.isLt
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      have inj := byte128_address_inj (s.readReg64 .x16) i ⟨lengthOffset rem + k.val, by omega⟩
      intro he
      have eqIndex := inj.mp he
      change i.val = lengthOffset rem + k.val at eqIndex
      omega
    unfold suffixMemory
    rw [read8_write64_outside_ne _ _ _ _ outside, read8_write8]
    have inj := byte128_address_inj (s.readReg64 .x16) i ⟨rem, by omega⟩
    simp only [inj]

theorem suffixMemory_outside (s : Arm64.State) (rem : Nat) (hrem : rem < 64) (p : BitVec 64)
    (h : 128 ≤ (p - s.readReg64 .x16).toNat) : (suffixMemory s rem).cells p = s.mem.cells p := by
  let t : Fin 16 := ⟨if rem < 56 then 7 else 15, by split <;> decide⟩
  have dist := byte128_word_delta (s.readReg64 .x16) p t h
  have address : s.readReg64 .x16 + BitVec.ofNat 64 (8 * t.val) =
      s.readReg64 .x16 + BitVec.ofNat 64 (lengthOffset rem) := by
    unfold t lengthOffset
    split <;> rfl
  rw [address] at dist
  exact (write64_cells_outside _ _ _ _ dist).trans
    (byte128_store_outside s.mem (s.readReg64 .x16) p ⟨rem, by omega⟩ 128#8 h)

theorem suffixMemory_readable (s : Arm64.State) (rem : Nat) (p : BitVec 64) (n : Nat)
    (h : s.mem.canRead p n = true) : (suffixMemory s rem).canRead p n = true :=
  canRead_write64 _ _ _ _ _ (canRead_write8 _ _ _ _ _ h)

theorem suffixMemory_writable (s : Arm64.State) (rem : Nat) (p : BitVec 64) (n : Nat) :
    (suffixMemory s rem).canWrite p n = s.mem.canWrite p n := by
  simp only [suffixMemory, canWrite_write64, canWrite_write8]

end Crypto.ARM64.Imported
