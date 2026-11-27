import Proofs.HMACSHA256.Reference

namespace Crypto.HMACSHA256

/-- Each assembly entry checks subtraction underflow before comparing the
remaining capacity against the message count. This is the portable rejection
condition even when the required capacity exceeds the machine word range. -/
theorem capacity_guard (capacity count : BitVec 64) :
    (capacity.toNat < 96 ∨ (capacity - 96).toNat < count.toNat) ↔
      capacity.toNat < 96 + count.toNat := by
  by_cases small : capacity.toNat < 96
  · have short : capacity.toNat < 96 + count.toNat := by omega
    simp only [small, true_or, short]
  · have sufficient : 96 ≤ capacity.toNat := by omega
    have shortSub : (capacity - 96).toNat = capacity.toNat - 96 := by
      rw [BitVec.toNat_sub]
      change (2 ^ 64 - 96 + capacity.toNat) % 2 ^ 64 = capacity.toNat - 96
      have below := capacity.isLt
      omega
    simp only [small, false_or, shortSub]
    omega

end Crypto.HMACSHA256
