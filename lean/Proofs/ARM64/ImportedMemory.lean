import Proofs.ARM64.ImportedRound
import Mathlib.Tactic.IntervalCases

/-!
Byte/word layout and permission lemmas for the unchanged upstream memory model.
Stores preserve normalized permissions, affect their modular byte interval,
reconstruct their 32-bit word, and update one slot of a 64-word snapshot.
Existing readable regions remain readable (a store only clears lazy-free bits).
These are layout helpers; whole-call access bounds and ownership remain separate.
-/
namespace Crypto.ARM64.Imported

@[simp] theorem read8_write8 (m : Arm64.Memory) (base p : BitVec 64) (value : BitVec 8) :
    (m.write8 base value).read8 p = if p = base then value else m.read8 p := by
  by_cases h : p = base <;> simp [Arm64.Memory.read8, Arm64.Memory.write8, h]

@[simp] theorem cells_write8_outside (m : Arm64.Memory) (base p : BitVec 64) (value : BitVec 8)
    (h : p ≠ base) : (m.write8 base value).cells p = m.cells p := by
  simp [Arm64.Memory.write8, h]

@[simp] theorem perm_write8 (m : Arm64.Memory) (base p : BitVec 64) (value : BitVec 8) :
    (m.write8 base value).perm p = m.perm p := by
  by_cases hp : p = base
  · subst p
    cases hc : m.cells base with
    | none => simp [Arm64.Memory.perm, Arm64.Memory.write8, Arm64.Memory.rawPerm, hc]
    | some cell =>
      rcases cell with ⟨permission, byte⟩
      cases permission <;>
        simp [Arm64.Memory.perm, Arm64.Memory.write8, Arm64.Memory.rawPerm, hc, Arm64.Perm.rwx]
  · simp [Arm64.Memory.perm, Arm64.Memory.write8, hp]

@[simp] theorem perm_write32 (m : Arm64.Memory) (base p : BitVec 64) (value : BitVec 32) :
    (m.write32 base value).perm p = m.perm p := by
  simp [Arm64.Memory.write32]

theorem join_word_bytes (value : BitVec 32) :
    value.extractLsb' 24 8 ++ value.extractLsb' 16 8 ++ value.extractLsb' 8 8 ++
      value.extractLsb' 0 8 = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  all_goals simp (config := { decide := true })

theorem read32_write32 (m : Arm64.Memory) (base : BitVec 64) (value : BitVec 32) :
    (m.write32 base value).read32 base = value := by
  simpa [Arm64.Memory.write32, Arm64.Memory.read32] using join_word_bytes value

theorem address_delta (base offset : BitVec 64) : base + offset - base = offset := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem write32_cells_outside (m : Arm64.Memory) (base p : BitVec 64) (value : BitVec 32)
    (h : 4 ≤ (p - base).toNat) : (m.write32 base value).cells p = m.cells p := by
  have outside (i : Fin 4) : p ≠ base + BitVec.ofNat 64 i.val := by
    intro heq
    rw [heq, address_delta] at h
    have hi := i.isLt
    have bound : i.val < 2 ^ 64 := by omega
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at h
    omega
  have h0 : p ≠ base := by simpa using outside ⟨0, by decide⟩
  have h1 : p ≠ base + 1#64 := by simpa using outside ⟨1, by decide⟩
  have h2 : p ≠ base + 2#64 := by simpa using outside ⟨2, by decide⟩
  have h3 : p ≠ base + 3#64 := by simpa using outside ⟨3, by decide⟩
  simp [Arm64.Memory.write32, Arm64.Memory.write8, h0, h1, h2, h3]

theorem read8_write32_outside (m : Arm64.Memory) (base p : BitVec 64) (value : BitVec 32)
    (h : 4 ≤ (p - base).toNat) : (m.write32 base value).read8 p = m.read8 p := by
  simp only [Arm64.Memory.read8, write32_cells_outside m base p value h]

theorem read32_write32_outside (m : Arm64.Memory) (base p : BitVec 64) (value : BitVec 32)
    (h : ∀ i : Fin 4, 4 ≤ (p + BitVec.ofNat 64 i.val - base).toNat) :
    (m.write32 base value).read32 p = m.read32 p := by
  have h0 : 4 ≤ (p - base).toNat := by simpa using h ⟨0, by decide⟩
  have h1 : 4 ≤ (p + 1#64 - base).toNat := by simpa using h ⟨1, by decide⟩
  have h2 : 4 ≤ (p + 2#64 - base).toNat := by simpa using h ⟨2, by decide⟩
  have h3 : 4 ≤ (p + 3#64 - base).toNat := by simpa using h ⟨3, by decide⟩
  simp only [Arm64.Memory.read32, BitVec.add_zero,
    read8_write32_outside m base p value h0,
    read8_write32_outside m base (p + 1#64) value h1,
    read8_write32_outside m base (p + 2#64) value h2,
    read8_write32_outside m base (p + 3#64) value h3]

theorem address_reconstruct (base p : BitVec 64) :
    base + BitVec.ofNat 64 (p - base).toNat = p := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [BitVec.add_comm, BitVec.sub_add_cancel]

theorem word_byte_addresses_disjoint (base : BitVec 64) (i j : Fin 64) (a b : Fin 4)
    (hne : i ≠ j) :
    base + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 a.val ≠
      base + BitVec.ofNat 64 (4 * j.val) + BitVec.ofNat 64 b.val := by
  intro heq
  have ia := i.isLt; have ja := j.isLt; have aa := a.isLt; have ba := b.isLt
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add] at heq
  have hc := (BitVec.add_right_inj base).mp heq
  have hn := congrArg BitVec.toNat hc
  have bi : 4 * i.val + a.val < 2 ^ 64 := by omega
  have bj : 4 * j.val + b.val < 2 ^ 64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bi, Nat.mod_eq_of_lt bj] at hn
  exact hne (Fin.ext (by omega))

theorem read_word_store_other (m : Arm64.Memory) (base : BitVec 64)
    (i j : Fin 64) (value : BitVec 32) (hne : i ≠ j) :
    (m.write32 (base + BitVec.ofNat 64 (4 * i.val)) value).read32
      (base + BitVec.ofNat 64 (4 * j.val)) =
    m.read32 (base + BitVec.ofNat 64 (4 * j.val)) := by
  apply read32_write32_outside
  intro a
  by_contra h
  have hs : (base + BitVec.ofNat 64 (4 * j.val) + BitVec.ofNat 64 a.val -
      (base + BitVec.ofNat 64 (4 * i.val))).toNat < 4 := by omega
  let b : Fin 4 := ⟨_, hs⟩
  have eqaddr := address_reconstruct (base + BitVec.ofNat 64 (4 * i.val))
    (base + BitVec.ofNat 64 (4 * j.val) + BitVec.ofNat 64 a.val)
  exact word_byte_addresses_disjoint base j i a b (Ne.symm hne) eqaddr.symm

def wordVector (n : Nat) (m : Arm64.Memory) (base : BitVec 64) : Vector (BitVec 32) n :=
  Vector.ofFn fun i => m.read32 (base + BitVec.ofNat 64 (4 * i.val))

theorem vector_setBang_eq_setIfInBounds {α : Type} {n : Nat} (W : Vector α n) (i : Nat) (value : α) :
    W.set! i value = W.setIfInBounds i value := by cases W; rfl

theorem wordVector_store64 (m : Arm64.Memory) (base : BitVec 64) (t : Fin 64) (value : BitVec 32) :
    wordVector 64 (m.write32 (base + BitVec.ofNat 64 (4 * t.val)) value) base =
      (wordVector 64 m base).set! t.val value := by
  rw [vector_setBang_eq_setIfInBounds]
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_setIfInBounds hj]
  simp only [wordVector, Vector.getElem_ofFn]
  by_cases heq : t.val = j
  · subst j
    simpa only [ite_true] using read32_write32 m (base + BitVec.ofNat 64 (4 * t.val)) value
  · simp only [if_neg heq]
    have hne : t ≠ (⟨j, hj⟩ : Fin 64) := by
      intro he
      exact heq (congrArg Fin.val he)
    exact read_word_store_other m base t ⟨j, hj⟩ value hne

@[simp] theorem allPerm_write8 (m : Arm64.Memory) (base : BitVec 64) (value : BitVec 8)
    (predicate : Option Arm64.Perm → Bool) (address : BitVec 64) (n : Nat) :
    (m.write8 base value).allPerm predicate address n = m.allPerm predicate address n := by
  induction n generalizing address with
  | zero => rfl
  | succ n ih => simp only [Arm64.Memory.allPerm, perm_write8, ih]

@[simp] theorem lazy_write8 (m : Arm64.Memory) (base p : BitVec 64) (value : BitVec 8) :
    (m.write8 base value).isLazyFree p = if p = base then false else m.isLazyFree p := by
  by_cases hp : p = base
  · subst p
    cases hc : m.cells base with
    | none => simp [Arm64.Memory.isLazyFree, Arm64.Memory.write8, Arm64.Memory.rawPerm, hc]
    | some cell =>
      rcases cell with ⟨permission, byte⟩
      cases permission <;>
        simp [Arm64.Memory.isLazyFree, Arm64.Memory.write8, Arm64.Memory.rawPerm, hc]
  · simp [Arm64.Memory.isLazyFree, Arm64.Memory.write8, hp]

theorem noLazy_write8 (m : Arm64.Memory) (base : BitVec 64) (value : BitVec 8)
    (address : BitVec 64) (n : Nat) (h : m.allNoLazyFree address n = true) :
    (m.write8 base value).allNoLazyFree address n = true := by
  induction n generalizing address with
  | zero => rfl
  | succ n ih =>
    have old : m.isLazyFree address = false ∧ m.allNoLazyFree (address + 1#64) n = true := by
      simpa only [Arm64.Memory.allNoLazyFree, Bool.and_eq_true, Bool.not_eq_true'] using h
    have hf : (m.write8 base value).isLazyFree address = false := by simp [old.1]
    simp only [Arm64.Memory.allNoLazyFree, hf, Bool.not_false, Bool.true_and]
    exact ih _ old.2

theorem canRead_write8 (m : Arm64.Memory) (base : BitVec 64) (value : BitVec 8)
    (address : BitVec 64) (n : Nat) (h : m.canRead address n = true) :
    (m.write8 base value).canRead address n = true := by
  simp only [Arm64.Memory.canRead, Bool.and_eq_true] at h ⊢
  constructor
  · simpa only [allPerm_write8] using h.1
  · exact noLazy_write8 m base value address n h.2

theorem canRead_write32 (m : Arm64.Memory) (base : BitVec 64) (value : BitVec 32)
    (address : BitVec 64) (n : Nat) (h : m.canRead address n = true) :
    (m.write32 base value).canRead address n = true := by
  unfold Arm64.Memory.write32
  apply canRead_write8
  apply canRead_write8
  apply canRead_write8
  apply canRead_write8
  exact h

@[simp] theorem canWrite_write32 (m : Arm64.Memory) (base : BitVec 64) (value : BitVec 32)
    (address : BitVec 64) (n : Nat) :
    (m.write32 base value).canWrite address n = m.canWrite address n := by
  simp [Arm64.Memory.canWrite, Arm64.Memory.write32]

@[simp] theorem canExec_write32 (m : Arm64.Memory) (base : BitVec 64) (value : BitVec 32)
    (address : BitVec 64) (n : Nat) :
    (m.write32 base value).canExec address n = m.canExec address n := by
  simp [Arm64.Memory.canExec, Arm64.Memory.write32]

end Crypto.ARM64.Imported
