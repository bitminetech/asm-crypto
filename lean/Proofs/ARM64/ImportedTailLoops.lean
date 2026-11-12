import Proofs.ARM64.ImportedTailCopy
import Proofs.ARM64.ImportedCompression

/-!
The complete padding-tail copy loop, for every remainder below 64. The loop
copies the original source bytes, exits at the recorded branch destination,
and preserves source values, permissions, every cell outside the copied
byte prefix, and the stated CPU/state frame. Empty tails require no source read.
Initializing padding, appending the marker/length, fetching and full-call
`equal` remain separate obligations.
-/
namespace Crypto.ARM64.Imported

theorem tail_copy_prefix (s : Arm64.State) (rem : Nat) (hrem : rem < 64)
    (hc : s.readReg64 .x6 = 0#64) (hrm : s.readReg64 .x17 = BitVec.ofNat 64 rem)
    (hr : ∀ i : Fin rem, s.mem.canRead (s.readReg64 .x5 + BitVec.ofNat 64 i.val) 1 = true)
    (hw : ∀ i : Fin 128, s.mem.canWrite (s.readReg64 .x16 + BitVec.ofNat 64 i.val) 1 = true)
    (hout : ∀ i : Fin rem, 128 ≤ (s.readReg64 .x5 + BitVec.ofNat 64 i.val - s.readReg64 .x16).toNat)
    (n : Nat) (hn : n ≤ rem) :
    ∃ out, runCycles tailCopyCycleCode n s = some out ∧
      nonMemory out = nonMemory s ∧ copyRegisters out = copyRegisters s ∧
      nonvolatile out = nonvolatile s ∧ out.pc = s.pc ∧
      out.readReg64 .x6 = BitVec.ofNat 64 n ∧
      (∀ j, j < n → out.mem.read8 (s.readReg64 .x16 + BitVec.ofNat 64 j) =
        s.mem.read8 (s.readReg64 .x5 + BitVec.ofNat 64 j)) ∧
      (∀ j : Fin rem, out.mem.canRead (s.readReg64 .x5 + BitVec.ofNat 64 j.val) 1 = true) ∧
      (∀ j : Fin 128, out.mem.canWrite (s.readReg64 .x16 + BitVec.ofNat 64 j.val) 1 = true) ∧
      (∀ j : Fin rem, out.mem.read8 (s.readReg64 .x5 + BitVec.ofNat 64 j.val) =
        s.mem.read8 (s.readReg64 .x5 + BitVec.ofNat 64 j.val)) ∧
      (∀ p, n ≤ (p - s.readReg64 .x16).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a count, s.mem.canRead a count = true → out.mem.canRead a count = true) := by
  let P (i : Nat) (mid : Arm64.State) : Prop :=
    nonMemory mid = nonMemory s ∧ copyRegisters mid = copyRegisters s ∧
    nonvolatile mid = nonvolatile s ∧ mid.pc = s.pc ∧
    mid.readReg64 .x6 = BitVec.ofNat 64 i ∧
    (∀ j, j < i → mid.mem.read8 (s.readReg64 .x16 + BitVec.ofNat 64 j) =
      s.mem.read8 (s.readReg64 .x5 + BitVec.ofNat 64 j)) ∧
    (∀ j : Fin rem, mid.mem.canRead (s.readReg64 .x5 + BitVec.ofNat 64 j.val) 1 = true) ∧
    (∀ j : Fin 128, mid.mem.canWrite (s.readReg64 .x16 + BitVec.ofNat 64 j.val) 1 = true) ∧
    (∀ j : Fin rem, mid.mem.read8 (s.readReg64 .x5 + BitVec.ofNat 64 j.val) =
      s.mem.read8 (s.readReg64 .x5 + BitVec.ofNat 64 j.val)) ∧
    (∀ p, i ≤ (p - s.readReg64 .x16).toNat → mid.mem.cells p = s.mem.cells p) ∧
    (∀ a count, s.mem.canRead a count = true → mid.mem.canRead a count = true)
  have h0 : P 0 s := ⟨rfl, rfl, rfl, rfl, hc, by intro j hj; omega,
    hr, hw, by intro j; rfl, by intro p hp; rfl, by intro a count read; exact read⟩
  have hs (i : Nat) (hi : i < n) (mid : Arm64.State) (hp : P i mid) :
      ∃ out, runWords tailCopyCycleCode mid = some out ∧ P (i + 1) out := by
    obtain ⟨hm, hregs, hnv, hpc, hc', initialized, hr', hw', source, outside, readable⟩ := hp
    let t : Fin rem := ⟨i, by omega⟩
    let t128 : Fin 128 := ⟨i, by omega⟩
    have src : mid.readReg64 .x5 = s.readReg64 .x5 := copyRegisters_read hregs 5#5 (by decide)
    have dst : mid.readReg64 .x16 = s.readReg64 .x16 := copyRegisters_read hregs 16#5 (by decide)
    have remaining : mid.readReg64 .x17 = BitVec.ofNat 64 rem :=
      (copyRegisters_read hregs 17#5 (by decide)).trans hrm
    have ibound : i < 2 ^ 64 := by omega
    have rbound : rem < 2 ^ 64 := by omega
    have less : (mid.readReg64 .x6).toNat < (mid.readReg64 .x17).toNat := by
      rw [hc', remaining]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ibound, Nat.mod_eq_of_lt rbound]
      omega
    have read : mid.mem.canRead (mid.readReg64 .x5 + mid.readReg64 .x6) 1 = true := by
      rw [src, hc']
      exact hr' t
    have write : mid.mem.canWrite (mid.readReg64 .x16 + mid.readReg64 .x6) 1 = true := by
      rw [dst, hc']
      exact hw' t128
    obtain ⟨out, ho, post⟩ := exists_of_map_some _ _ _ (tail_copy_cycle mid less read write)
    simp only [Prod.mk.injEq] at post
    obtain ⟨fm, fregs, fmem, fpc, fnv, fcount⟩ := post
    have byteMem : out.mem = mid.mem.write8 (s.readReg64 .x16 + BitVec.ofNat 64 i)
        (mid.mem.read8 (s.readReg64 .x5 + BitVec.ofNat 64 i)) := by
      simpa only [dst, src, hc'] using fmem
    refine ⟨out, ho, fm.trans hm, fregs.trans hregs, fnv.trans hnv,
      fpc.trans hpc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hc', BitVec.ofNat_add] using fcount
    · intro j hj
      have j128 : j < 128 := by omega
      have addressEq :
          (s.readReg64 .x16 + BitVec.ofNat 64 j = s.readReg64 .x16 + BitVec.ofNat 64 i) ↔ j = i :=
        byte128_address_inj (s.readReg64 .x16) ⟨j, j128⟩ t128
      rw [byteMem, read8_write8]
      simp only [addressEq]
      by_cases he : j = i
      · subst j
        rw [if_pos rfl]
        exact source t
      · rw [if_neg he]
        exact initialized j (by omega)
    · intro j
      rw [byteMem]
      exact canRead_write8 _ _ _ _ _ (hr' j)
    · intro j
      rw [byteMem, canWrite_write8]
      exact hw' j
    · intro j
      have sep : s.readReg64 .x5 + BitVec.ofNat 64 j.val ≠
          s.readReg64 .x16 + BitVec.ofNat 64 i :=
        byte128_outside (s.readReg64 .x16) _ t128 (hout j)
      rw [byteMem, read8_write8, if_neg sep]
      exact source j
    · intro p hp
      rw [byteMem]
      have neq : p ≠ s.readReg64 .x16 + BitVec.ofNat 64 i := by
        intro he
        rw [he, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ibound] at hp
        omega
      exact (cells_write8_outside _ _ _ _ neq).trans (outside p (by omega))
    · intro a count read
      rw [byteMem]
      exact canRead_write8 _ _ _ _ _ (readable a count read)
  exact iterateStep_invariant (runWords tailCopyCycleCode) P n s h0 hs

def tailCopyCode (rem : Nat) : List (BitVec 32) :=
  (List.replicate rem tailCopyCycleCode).flatten ++ tailCopyEndCode

theorem tail_copy_loop (s : Arm64.State) (rem : Nat) (hrem : rem < 64)
    (hc : s.readReg64 .x6 = 0#64) (hrm : s.readReg64 .x17 = BitVec.ofNat 64 rem)
    (hr : ∀ i : Fin rem, s.mem.canRead (s.readReg64 .x5 + BitVec.ofNat 64 i.val) 1 = true)
    (hw : ∀ i : Fin 128, s.mem.canWrite (s.readReg64 .x16 + BitVec.ofNat 64 i.val) 1 = true)
    (hout : ∀ i : Fin rem, 128 ≤ (s.readReg64 .x5 + BitVec.ofNat 64 i.val - s.readReg64 .x16).toNat) :
    ∃ out, runWords (tailCopyCode rem) s = some out ∧
      nonMemory out = nonMemory s ∧ copyRegisters out = copyRegisters s ∧
      nonvolatile out = nonvolatile s ∧ out.pc = s.pc + 24#64 ∧
      out.readReg64 .x6 = BitVec.ofNat 64 rem ∧
      (∀ j, j < rem → out.mem.read8 (s.readReg64 .x16 + BitVec.ofNat 64 j) =
        s.mem.read8 (s.readReg64 .x5 + BitVec.ofNat 64 j)) ∧
      (∀ j : Fin rem, out.mem.canRead (s.readReg64 .x5 + BitVec.ofNat 64 j.val) 1 = true) ∧
      (∀ j : Fin 128, out.mem.canWrite (s.readReg64 .x16 + BitVec.ofNat 64 j.val) 1 = true) ∧
      (∀ j : Fin rem, out.mem.read8 (s.readReg64 .x5 + BitVec.ofNat 64 j.val) =
        s.mem.read8 (s.readReg64 .x5 + BitVec.ofNat 64 j.val)) ∧
      (∀ p, rem ≤ (p - s.readReg64 .x16).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a count, s.mem.canRead a count = true → out.mem.canRead a count = true) := by
  obtain ⟨mid, he, hm, hregs, hnv, hpc, count, initialized,
    reads, writes, values, outside, readable⟩ := tail_copy_prefix s rem hrem hc hrm hr hw hout rem (by omega)
  have remaining : mid.readReg64 .x17 = BitVec.ofNat 64 rem :=
    (copyRegisters_read hregs 17#5 (by decide)).trans hrm
  have ge : (mid.readReg64 .x17).toNat ≤ (mid.readReg64 .x6).toNat := by
    rw [remaining, count]
  obtain ⟨out, ho, post⟩ := exists_of_map_some _ _ _ (tail_copy_end mid ge)
  simp only [Prod.mk.injEq] at post
  obtain ⟨fm, fregs, fmem, fpc, fnv, fcount⟩ := post
  have cycles := (runCycles_words tailCopyCycleCode rem s).symm.trans he
  have whole := runWords_append_success cycles ho
  refine ⟨out, whole, fm.trans hm, fregs.trans hregs, fnv.trans hnv,
    ?_, fcount.trans count, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fpc.trans (congrArg (· + 24#64) hpc)
  · simpa only [fmem] using initialized
  · simpa only [fmem] using reads
  · simpa only [fmem] using writes
  · simpa only [fmem] using values
  · simpa only [fmem] using outside
  · simpa only [fmem] using readable

end Crypto.ARM64.Imported
