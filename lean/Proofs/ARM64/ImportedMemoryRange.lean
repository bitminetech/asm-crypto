import Proofs.ARM64.ImportedMemory

/-!
Modular address and store-frame lemmas over the unchanged imported memory.
Every one-word store into the 256-byte schedule workspace preserves cells
outside it. Disjoint word reads also survive a store. Caller allocation and
separation conditions must still be connected to these modular intervals.
-/
namespace Crypto.ARM64.Imported

theorem workspace_store_delta (base p : BitVec 64) (t : Fin 64)
    (h : 256 ≤ (p - base).toNat) :
    4 ≤ (p - (base + BitVec.ofNat 64 (4 * t.val))).toNat := by
  by_contra hn
  let d := (p - (base + BitVec.ofNat 64 (4 * t.val))).toNat
  have hd : d < 4 := Nat.lt_of_not_ge hn
  have small : 4 * t.val + d < 256 := by have := t.isLt; omega
  have bound : 4 * t.val + d < 2 ^ 64 := by omega
  have address : base + BitVec.ofNat 64 (4 * t.val + d) = p := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact address_reconstruct (base + BitVec.ofNat 64 (4 * t.val)) p
  have dist : (p - base).toNat = 4 * t.val + d := by
    rw [← address, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  omega

theorem workspace_store_outside (m : Arm64.Memory) (base p : BitVec 64)
    (t : Fin 64) (value : BitVec 32) (h : 256 ≤ (p - base).toNat) :
    (m.write32 (base + BitVec.ofNat 64 (4 * t.val)) value).cells p = m.cells p :=
  write32_cells_outside m _ p value (workspace_store_delta base p t h)

theorem bv_add_sub_add_left {n : Nat} (base x y : BitVec n) :
    (base + x) - (base + y) = x - y := by
  calc
    (base + x) - (base + y) = (x + (base - base)) - y := by
      simp only [BitVec.sub_eq_add_neg, BitVec.neg_add]
      ac_rfl
    _ = x - y := by simp

theorem bv_add_sub_right {n : Nat} (x y z : BitVec n) :
    x + y - z = (x - z) + y := by
  simp only [BitVec.sub_eq_add_neg]
  ac_rfl

theorem read32_write32_disjoint (m : Arm64.Memory) (base p : BitVec 64) (value : BitVec 32)
    (h : 4 ≤ (p - base).toNat ∧ (p - base).toNat ≤ 2 ^ 64 - 4) :
    (m.write32 base value).read32 p = m.read32 p := by
  apply read32_write32_outside
  intro i
  have hi := i.isLt
  have ibound : i.val < 2 ^ 64 := by omega
  have sumBound : (p - base).toNat + i.val < 2 ^ 64 := by omega
  rw [bv_add_sub_right, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ibound, Nat.mod_eq_of_lt sumBound]
  omega

end Crypto.ARM64.Imported
