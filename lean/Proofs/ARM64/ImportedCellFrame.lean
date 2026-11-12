import Proofs.ARM64.ImportedMemoryRange

/-!
Transport word values and four-byte read/write permissions across exact cell
frames. Hash slots at stack offsets 256..287 lie outside the schedule workspace,
so the input/schedule loop frames preserve their values and permissions.
These layout helpers do not establish caller allocation or full-call safety.
-/
namespace Crypto.ARM64.Imported

theorem read32_of_cells {m before : Arm64.Memory} (p : BitVec 64)
    (h : ∀ b : Fin 4, m.cells (p + BitVec.ofNat 64 b.val) = before.cells (p + BitVec.ofNat 64 b.val)) :
    m.read32 p = before.read32 p := by
  have h0 : m.cells (p + 0#64) = before.cells (p + 0#64) := h ⟨0, by decide⟩
  have h1 : m.cells (p + 1#64) = before.cells (p + 1#64) := h ⟨1, by decide⟩
  have h2 : m.cells (p + 2#64) = before.cells (p + 2#64) := h ⟨2, by decide⟩
  have h3 : m.cells (p + 3#64) = before.cells (p + 3#64) := h ⟨3, by decide⟩
  simp only [Arm64.Memory.read32, Arm64.Memory.read8, h0, h1, h2, h3]

theorem canRead32_of_cells {m before : Arm64.Memory} (p : BitVec 64)
    (h : ∀ b : Fin 4, m.cells (p + BitVec.ofNat 64 b.val) = before.cells (p + BitVec.ofNat 64 b.val)) :
    m.canRead p 4 = before.canRead p 4 := by
  have h0 : m.cells p = before.cells p := by simpa using h ⟨0, by decide⟩
  have h1 : m.cells (p + 1#64) = before.cells (p + 1#64) := h ⟨1, by decide⟩
  have h2 : m.cells (p + 2#64) = before.cells (p + 2#64) := h ⟨2, by decide⟩
  have h3 : m.cells (p + 3#64) = before.cells (p + 3#64) := h ⟨3, by decide⟩
  simp [Arm64.Memory.canRead, Arm64.Memory.allPerm, Arm64.Memory.allNoLazyFree,
    Arm64.Memory.perm, Arm64.Memory.isLazyFree,
    h0, h1, h2, h3, BitVec.add_assoc]

theorem canWrite32_of_cells {m before : Arm64.Memory} (p : BitVec 64)
    (h : ∀ b : Fin 4, m.cells (p + BitVec.ofNat 64 b.val) = before.cells (p + BitVec.ofNat 64 b.val)) :
    m.canWrite p 4 = before.canWrite p 4 := by
  have h0 : m.cells p = before.cells p := by simpa using h ⟨0, by decide⟩
  have h1 : m.cells (p + 1#64) = before.cells (p + 1#64) := h ⟨1, by decide⟩
  have h2 : m.cells (p + 2#64) = before.cells (p + 2#64) := h ⟨2, by decide⟩
  have h3 : m.cells (p + 3#64) = before.cells (p + 3#64) := h ⟨3, by decide⟩
  simp [Arm64.Memory.canWrite, Arm64.Memory.allPerm, Arm64.Memory.perm,
    h0, h1, h2, h3, BitVec.add_assoc]

theorem hash_byte_outside (base : BitVec 64) (i : Fin 8) (b : Fin 4) :
    256 ≤ ((base + 256#64 + BitVec.ofNat 64 (4 * i.val)) + BitVec.ofNat 64 b.val - base).toNat := by
  have address : base + 256#64 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val =
      base + BitVec.ofNat 64 (256 + 4 * i.val + b.val) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  have hi := i.isLt
  have hb := b.isLt
  have bound : 256 + 4 * i.val + b.val < 2 ^ 64 := by omega
  rw [address, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  omega

theorem hash_snapshot_of_frame (m before : Arm64.Memory) (base : BitVec 64)
    (h : ∀ p, 256 ≤ (p - base).toNat → m.cells p = before.cells p) :
    wordVector 8 m (base + 256#64) = wordVector 8 before (base + 256#64) := by
  apply Vector.ext
  intro i hi
  simp only [wordVector, Vector.getElem_ofFn]
  apply read32_of_cells
  intro b
  exact h _ (hash_byte_outside base ⟨i, hi⟩ b)

end Crypto.ARM64.Imported
