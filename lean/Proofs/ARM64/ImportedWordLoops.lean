import Proofs.ARM64.ImportedWordLoad

/-!
All 16 recorded word-load cycles initialize the first 16 schedule words to
the given big-endian message block, preserving source words and read permissions,
workspace write permissions and every cell outside the workspace. The entry
requires the 64 source bytes to be disjoint from the 256-byte workspace.
-/
namespace Crypto.ARM64.Imported
open SHS.Equiv.VecBridge

theorem DataFrame.x2 {a b : Arm64.State} (h : DataFrame a b) :
    b.readReg64 .x2 = a.readReg64 .x2 := h.2.2.2.2.1

theorem DataFrame.aligned {a b : Arm64.State} (h : DataFrame a b) : b.spAligned = a.spAligned := by
  have result := congrArg Arm64.State.spAligned h.1
  exact result

theorem vector_set_get_bang {n : Nat} (W : Vector (BitVec 32) n) (i : Fin n)
    (v : BitVec 32) (j : Nat) (hj : j < n) :
    (W.set! i.val v)[j]! = if i.val = j then v else W[j]! := by
  rw [getElem_bang_eq_getElem (W.set! i.val v) j hj,
    set_bang_eq_set W i.val i.isLt v, Vector.getElem_set,
    getElem_bang_eq_getElem W j hj]

theorem word_loop_prefix (s : Arm64.State) (M : Vector (BitVec 32) 16)
    (hsp : s.spAligned = true) (hc : s.readReg64 .x5 = 0#64)
    (hr : ∀ i : Fin 16, s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hw : ∀ i : Fin 64, s.mem.canWrite (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hM : ∀ i : Fin 16, reverseWord (s.mem.read32 (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val))) = M[i.val]!)
    (hOutside : ∀ (i : Fin 16) (b : Fin 4),
      256 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat)
    (n : Nat) (hn : n ≤ 16) :
    ∃ out, runCycles wordCycleCode n s = some out ∧ DataFrame s out ∧
      out.pc = (if n < 16 then s.pc else s.pc + 24#64) ∧
      out.readReg64 .x5 = BitVec.ofNat 64 n ∧
      (∀ j, j < n → (wordVector 64 out.mem out.sp)[j]! = M[j]!) ∧
      (∀ i : Fin 16, out.mem.canRead (out.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val)) 4 = true) ∧
      (∀ i : Fin 64, out.mem.canWrite (out.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true) ∧
      (∀ i : Fin 16, reverseWord (out.mem.read32 (out.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val))) = M[i.val]!) ∧
      (∀ p, 256 ≤ (p - s.sp).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a count, s.mem.canRead a count = true → out.mem.canRead a count = true) := by
  let P (i : Nat) (mid : Arm64.State) : Prop :=
    DataFrame s mid ∧ mid.pc = (if i < 16 then s.pc else s.pc + 24#64) ∧
    mid.readReg64 .x5 = BitVec.ofNat 64 i ∧
    (∀ j, j < i → (wordVector 64 mid.mem mid.sp)[j]! = M[j]!) ∧
    (∀ j : Fin 16, mid.mem.canRead (mid.readReg64 .x2 + BitVec.ofNat 64 (4 * j.val)) 4 = true) ∧
    (∀ j : Fin 64, mid.mem.canWrite (mid.sp + BitVec.ofNat 64 (4 * j.val)) 4 = true) ∧
    (∀ j : Fin 16, reverseWord (mid.mem.read32 (mid.readReg64 .x2 + BitVec.ofNat 64 (4 * j.val))) = M[j.val]!) ∧
    (∀ p, 256 ≤ (p - s.sp).toNat → mid.mem.cells p = s.mem.cells p) ∧
    (∀ a count, s.mem.canRead a count = true → mid.mem.canRead a count = true)
  have h0 : P 0 s := ⟨DataFrame.refl s, rfl, hc, by intro j hj; omega,
    hr, hw, hM, by intro p hp; rfl, by intro a count read; exact read⟩
  have hs (i : Nat) (hi : i < n) (mid : Arm64.State) (hp : P i mid) :
      ∃ out, runWords wordCycleCode mid = some out ∧ P (i + 1) out := by
    obtain ⟨hf, hp, hc', initialized, hr', hw', hM', outside, readable⟩ := hp
    let t : Fin 16 := ⟨i, by omega⟩
    let t64 : Fin 64 := t.castLE (by decide : 16 ≤ 64)
    have shift : (mid.readReg64 .x5 <<< 2) = BitVec.ofNat 64 (4 * t.val) := by
      rw [hc']
      exact index_shift_two t64
    have read : mid.mem.canRead (mid.readReg64 .x2 + (mid.readReg64 .x5 <<< 2)) 4 = true := by
      rw [shift]
      exact hr' t
    have write : mid.mem.canWrite (mid.sp + (mid.readReg64 .x5 <<< 2)) 4 = true := by
      rw [shift]
      exact hw' t64
    have value : loadedWord mid = M[i]! := by
      unfold loadedWord
      rw [shift]
      exact hM' t
    obtain ⟨out, ho, ff, pc, count, mem, ram⟩ := word_cycle mid t
      (by rw [hf.aligned]; exact hsp) read write hc'
    have wordmem : out.mem = mid.mem.write32 (mid.sp + BitVec.ofNat 64 (4 * t.val)) (loadedWord mid) := by
      simpa only [shift] using mem
    have keepSource (j : Fin 16) :
        (mid.mem.write32 (mid.sp + BitVec.ofNat 64 (4 * t.val)) (loadedWord mid)).read32
          (mid.readReg64 .x2 + BitVec.ofNat 64 (4 * j.val)) =
        mid.mem.read32 (mid.readReg64 .x2 + BitVec.ofNat 64 (4 * j.val)) := by
      apply read32_write32_outside
      intro b
      apply workspace_store_delta mid.sp _ t64
      rw [hf.sp, hf.x2]
      exact hOutside j b
    refine ⟨out, ho, hf.trans ff, ?_, count, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hlt : i < 16 := by omega
      simp only [if_pos hlt] at hp
      simpa only [t, hp] using pc
    · intro j hj
      have j64 : j < 64 := by omega
      have point := vector_set_get_bang (wordVector 64 mid.mem mid.sp) t64 (loadedWord mid) j j64
      have joined := (congrArg (fun W : Vector (BitVec 32) 64 => W[j]!) ram).trans point
      have final : (if i = j then loadedWord mid else (wordVector 64 mid.mem mid.sp)[j]!) = M[j]! := by
        by_cases he : i = j
        · subst j
          simpa only [ite_true] using value
        · rw [if_neg he]
          exact initialized j (by omega)
      exact joined.trans final
    · intro j
      rw [wordmem, ff.x2]
      exact canRead_write32 _ _ _ _ _ (hr' j)
    · intro j
      rw [wordmem, ff.sp, canWrite_write32]
      exact hw' j
    · intro j
      rw [wordmem, ff.x2, keepSource j]
      exact hM' j
    · intro p hp
      rw [wordmem]
      have dist : 256 ≤ (p - mid.sp).toNat := by rw [hf.sp]; exact hp
      exact (workspace_store_outside mid.mem mid.sp p t64 (loadedWord mid) dist).trans (outside p hp)
    · intro a count read
      rw [wordmem]
      exact canRead_write32 _ _ _ _ _ (readable a count read)
  exact iterateStep_invariant (runWords wordCycleCode) P n s h0 hs

theorem word_loop (s : Arm64.State) (M : Vector (BitVec 32) 16)
    (hsp : s.spAligned = true) (hc : s.readReg64 .x5 = 0#64)
    (hr : ∀ i : Fin 16, s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hw : ∀ i : Fin 64, s.mem.canWrite (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hM : ∀ i : Fin 16, reverseWord (s.mem.read32 (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val))) = M[i.val]!)
    (hOutside : ∀ (i : Fin 16) (b : Fin 4),
      256 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat) :
    ∃ out, runCycles wordCycleCode 16 s = some out ∧ DataFrame s out ∧
      out.pc = s.pc + 24#64 ∧ out.readReg64 .x5 = 16#64 ∧
      (∀ j, j < 16 → (wordVector 64 out.mem out.sp)[j]! = M[j]!) ∧
      (∀ i : Fin 16, out.mem.canRead (out.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val)) 4 = true) ∧
      (∀ i : Fin 64, out.mem.canWrite (out.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true) ∧
      (∀ i : Fin 16, reverseWord (out.mem.read32 (out.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val))) = M[i.val]!) ∧
      (∀ p, 256 ≤ (p - s.sp).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a count, s.mem.canRead a count = true → out.mem.canRead a count = true) := by
  obtain ⟨out, he, hf, hp, hc', initialized, hr', hw', words, outside, readable⟩ :=
    word_loop_prefix s M hsp hc hr hw hM hOutside 16 (by decide)
  exact ⟨out, he, hf, hp, hc', initialized, hr', hw', words, outside, readable⟩

end Crypto.ARM64.Imported
