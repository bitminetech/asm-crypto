import Proofs.ARM64.ImportedFeedForward
import Proofs.ARM64.ImportedZeroPad

/-!
Memory frame and permission facts for the eight feed-forward stores.
They permit composition of consecutive SHA-256 blocks without constraining
old workspace bytes. Caller allocation, fetch binding and equal are separate.
-/
namespace Crypto.ARM64.Imported

theorem region_word_store_delta (base p : BitVec 64) (offset size : Nat)
    (ho : offset + 4 ≤ size)
    (h : size ≤ (p - base).toNat) :
    4 ≤ (p - (base + BitVec.ofNat 64 offset)).toNat := by
  by_contra hn
  let d := (p - (base + BitVec.ofNat 64 offset)).toNat
  have hd : d < 4 := Nat.lt_of_not_ge hn
  have bound : offset + d < 2 ^ 64 := by omega
  have address : base + BitVec.ofNat 64 (offset + d) = p := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact address_reconstruct (base + BitVec.ofNat 64 offset) p
  have dist : (p - base).toNat = offset + d := by
    rw [← address, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  omega

theorem storeHashWords_outside (s : Arm64.State) (p : BitVec 64)
    (h : 288 ≤ (p - s.sp).toNat) : (storeHashWords s).cells p = s.mem.cells p := by
  apply fold_cells_frame
  intro m i hi
  have small : i < 8 := List.mem_range.mp hi
  apply write32_cells_outside
  exact region_word_store_delta s.sp p (256 + 4 * i) 288 (by omega) h

theorem storeHashWords_readable (s : Arm64.State) (p : BitVec 64) (n : Nat)
    (h : s.mem.canRead p n = true) : (storeHashWords s).canRead p n = true := by
  simp (config := { maxDischargeDepth := 32 }) [storeHashWords, List.range_succ, canRead_write32, h]

theorem storeHashWords_writable (s : Arm64.State) (p : BitVec 64) (n : Nat) :
    (storeHashWords s).canWrite p n = s.mem.canWrite p n := by
  simp [storeHashWords, List.range_succ]

end Crypto.ARM64.Imported
