import Proofs.ARM64.ImportedLoadedWords
import Proofs.ARM64.ImportedHashBody

/-!
The recorded hash-initialization execution produces the actual FIPS IV from
loaded image bytes, sets the K pointer and phase, and preserves outside cells
and read/write permissions.
-/
namespace Crypto.ARM64.Imported

theorem region_store_delta (base p : BitVec 64) (offset size width : Nat)
    (ho : offset + width ≤ size) (h : size ≤ (p - base).toNat) :
    width ≤ (p - (base + BitVec.ofNat 64 offset)).toNat := by
  by_contra hn
  let d := (p - (base + BitVec.ofNat 64 offset)).toNat
  have hd : d < width := Nat.lt_of_not_ge hn
  have bound : offset + d < 2 ^ 64 := by omega
  have address : base + BitVec.ofNat 64 (offset + d) = p := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact address_reconstruct (base + BitVec.ofNat 64 offset) p
  have dist : (p - base).toNat = offset + d := by
    rw [← address, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  omega

theorem initialHashMemory_outside (s : Arm64.State) (p : BitVec 64)
    (h : 288 ≤ (p - s.sp).toNat) : (initialHashMemory s).cells p = s.mem.cells p := by
  apply fold_cells_frame
  intro m i hi
  have small : i < 4 := List.mem_range.mp hi
  apply write64_cells_outside
  exact region_store_delta s.sp p (256 + 8 * i) 288 8 (by omega) h

theorem initialHashMemory_readable (s : Arm64.State) (a : BitVec 64) (n : Nat)
    (h : s.mem.canRead a n = true) : (initialHashMemory s).canRead a n = true := by
  simp (config := { maxDischargeDepth := 32 }) [initialHashMemory, List.range_succ, canRead_write64, h]

theorem initialHashMemory_writable (s : Arm64.State) (a : BitVec 64) (n : Nat) :
    (initialHashMemory s).canWrite a n = s.mem.canWrite a n := by
  simp [initialHashMemory, List.range_succ]

theorem initialize_hash_fips (base : BitVec 64) (s : Arm64.State)
    (loaded : (program base).CodeLoaded s.mem) (pc : s.pc = base + 132#64)
    (hr : ∀ i : Fin 4, s.mem.canRead ((s.pc + 732#64) + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (hw : ∀ i : Fin 4, s.mem.canWrite ((s.sp + 256#64) + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    ∃ out, runWords hashInitCode s = some out ∧
      savedHash out = SHS.SHA256.H0_256 ∧ nonMemory out = nonMemory s ∧
      nonvolatile out = nonvolatile s ∧ out.pc = s.pc + 32#64 ∧
      out.readReg64 .x0 = base + 608#64 ∧ out.readReg64 .x1 = s.readReg64 .x1 ∧
      out.readReg64 .x2 = s.readReg64 .x2 ∧ out.readReg64 .x3 = s.readReg64 .x3 ∧
      out.readReg64 .x4 = 0#64 ∧ out.readReg64 .x6 = s.readReg64 .x6 ∧
      (∀ p, 288 ≤ (p - s.sp).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a n, s.mem.canRead a n = true → out.mem.canRead a n = true) ∧
      (∀ a n, out.mem.canWrite a n = s.mem.canWrite a n) := by
  obtain ⟨out, he, post⟩ := exists_of_map_some _ _ _ (initialize_hash s hr hw)
  simp only [Prod.mk.injEq] at post
  obtain ⟨st, mem, opc, nv, x0, x1, x2, x3, x4, x6⟩ := post
  have sp := congrArg Arm64.State.sp st
  change out.sp = s.sp at sp
  have nm := congrArg nonMemory st
  have state : nonMemory out = nonMemory s := by
    simpa only [nonMemory_stable, nonMemory_set_mem] using nm
  refine ⟨out, he, ?_, state, nv, opc, ?_, x1, x2, x3, x4, x6, ?_, ?_, ?_⟩
  · unfold savedHash
    rw [mem, sp]
    exact initialHashMemory_fips base s loaded pc
  · rw [x0, pc, BitVec.add_assoc]
    rfl
  · intro p hp
    rw [mem]
    exact initialHashMemory_outside s p hp
  · intro a n h
    rw [mem]
    exact initialHashMemory_readable s a n h
  · intro a n
    rw [mem, initialHashMemory_writable]

end Crypto.ARM64.Imported
