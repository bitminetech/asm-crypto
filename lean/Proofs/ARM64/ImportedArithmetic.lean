import Proofs.ARM64.ImportedCounter

/-!
Unsigned 64-bit subtraction and comparison flags over the unchanged upstream
AddWithCarry semantics. These lemmas hold for every 64-bit operand pair;
no finite-input test or additional axiom is used.
-/
namespace Crypto.ARM64.Imported

theorem addWithCarry64_sub (x y : BitVec 64) :
    (Arm64.AddWithCarry64 x (~~~y) true).1 = x - y := by
  simp [Arm64.AddWithCarry64, BitVec.truncate_eq_setWidth, BitVec.setWidth_add,
    BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add,
    BitVec.add_comm, bv_add_left_comm]

theorem carry64_sub_ge (x y : BitVec 64) :
    (Arm64.AddWithCarry64 x (~~~y) true).2.c = decide (y.toNat ≤ x.toNat) := by
  have hx := x.isLt
  have hy := (~~~y).isLt
  have inner : (~~~y).toNat + x.toNat < 2 ^ 65 := by omega
  have outer : 1 + ((~~~y).toNat + x.toNat) < 2 ^ 65 := by omega
  have sum : (1#65 + ((~~~y).setWidth 65 + x.setWidth 65)).toNat =
      1 + ((2 ^ 64 - 1 - y.toNat) + x.toNat) := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 65)]
    rw [Nat.mod_eq_of_lt inner]
    change (1 + ((~~~y).toNat + x.toNat)) % 2 ^ 65 = _
    rw [Nat.mod_eq_of_lt outer, BitVec.toNat_not]
  change (1#65 + ((~~~y).setWidth 65 + x.setWidth 65)).msb = _
  rw [BitVec.msb_eq_decide, sum]
  change decide (2 ^ 64 ≤ 1 + ((2 ^ 64 - 1 - y.toNat) + x.toNat)) = decide (y.toNat ≤ x.toNat)
  have hy' := y.isLt
  by_cases h : y.toNat ≤ x.toNat
  · have high : 2 ^ 64 ≤ 1 + ((2 ^ 64 - 1 - y.toNat) + x.toNat) := by omega
    simp only [h, high, decide_true]
  · have low : ¬2 ^ 64 ≤ 1 + ((2 ^ 64 - 1 - y.toNat) + x.toNat) := by omega
    simp only [h, low, decide_false]

end Crypto.ARM64.Imported
